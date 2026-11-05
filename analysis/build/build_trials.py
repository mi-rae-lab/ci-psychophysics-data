# -*- coding: utf-8 -*-
"""Raw app records (data/raw) -> one trial-level CSV per test (data/trials).

    python -I build_trials.py <data/raw> <data/trials>

One row = one trial. Practice, examples, pass-check trials, runs stopped by the participant, trials stopped
before a response and the GDT runs deleted from the app database are all kept and marked excluded=1.
TMTF runs recorded before app 3.1 have no per-trial reversal list (revAt); their reversals are re-derived
here by replaying the app's staircase (js/track.js, unchanged since 2026-10-11) on the recorded responses,
and the replay is checked against the recorded presented levels and reversal values.
"""
import csv, datetime as dt, io, json, os, sys

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
ROOT, OUT = sys.argv[1], sys.argv[2]
os.makedirs(OUT, exist_ok=True)
KST = dt.timezone(dt.timedelta(hours=9))

HEADER = ['test', 'protocol', 'condition', 'ear', 'date_kst', 'time_kst', 'time_source',
          'session_id', 'run_id', 'trial_kind', 'session_trial_no', 'run_trial_no',
          'value', 'unit', 'n_intervals', 'target_interval', 'response_interval', 'scored_interval',
          'correct', 'reversal', 'reversal_no', 'unsure', 'at_limit', 'blocked_at_limit',
          'run_status', 'run_flags', 'excluded', 'exclusion_reason']


def load(app, name='db.json'):
    return json.load(open(os.path.join(ROOT, app, name), encoding='utf-8'))


def log_runs(app):
    out = []
    for line in open(os.path.join(ROOT, app, 'runs-log.jsonl'), encoding='utf-8'):
        line = line.strip()
        if not line:
            continue
        o = json.loads(line)
        if o.get('type') == 'run' and isinstance(o.get('data'), dict):
            out.append(o['data'])
    return out


def kst(iso):
    if not iso:
        return '', ''
    d = dt.datetime.fromisoformat(iso.replace('Z', '+00:00')).astimezone(KST)
    return d.strftime('%Y-%m-%d'), d.strftime('%H:%M:%S.') + f'{d.microsecond // 1000:03d}'


def num(x):
    """숫자를 짧고 정확하게 (부동소수 꼬리 없이)."""
    if x is None or x == '':
        return ''
    if isinstance(x, bool):
        return int(x)
    if isinstance(x, int):
        return x
    r = round(float(x), 6)
    return int(r) if r == int(r) else r


def b01(x):
    return '' if x is None else (1 if x else 0)


def finish(rows, test):
    """회기 안 시행 번호 (시각 순 — 연습 · 예시 · 버린 측정 · 응답 전 중단 포함)."""
    by = {}
    for r in rows:
        if r['session_id']:
            by.setdefault(r['session_id'], []).append(r)
    for sid, rs in by.items():
        rs.sort(key=lambda r: (r['_t'] or '', r['_ord']))
        for i, r in enumerate(rs, 1):
            r['session_trial_no'] = i
    rows.sort(key=lambda r: (r['_t'] or r['_tfallback'] or '', r['_ord']))
    path = os.path.join(OUT, f'{test.lower()}_trials.csv')
    with open(path, 'w', encoding='utf-8', newline='') as f:
        w = csv.DictWriter(f, fieldnames=HEADER, extrasaction='ignore', lineterminator='\n')
        w.writeheader()
        for r in rows:
            w.writerow({k: r.get(k, '') for k in HEADER})
    print(f'{test}: {len(rows)} rows -> {path}')
    return rows


def base(test, **kw):
    r = {k: '' for k in HEADER}
    r['test'] = test
    r['_t'] = None
    r['_tfallback'] = None
    r['_ord'] = (0, 0, 0)
    r.update(kw)
    return r


def set_time(r, iso, source, fallback=None):
    r['date_kst'], r['time_kst'] = kst(iso)
    r['time_source'] = source if iso else ''
    r['_t'] = iso if iso and source != 'run_end' else None
    r['_tfallback'] = iso


def reversals_by_direction(levels):
    """제시 값이 바뀌는 방향이 뒤집힌 시행 (0부터). 마지막 시행 뒤 이동은 모름."""
    rev, last = [], 0
    for i in range(len(levels) - 1):
        m = levels[i + 1] - levels[i]
        if m == 0:
            continue
        s = 1 if m > 0 else -1
        if last and s != last:
            rev.append(i)
        last = s
    return rev


# ───────────────────────────── TMTF ─────────────────────────────
def tmtf_replay(P, T):
    """Replay of the app staircase (js/track.js): 2-down/1-up, depth limited to [-40, 0] dB.
    A requested move whose direction differs from the previous requested move is a reversal, even when the
    depth cannot move (e.g. an error at 0 dB). Returns (reversal trial indices, recorded levels == replayed)."""
    depth, run, last, nrev, rev_at, ok = P.get('startDb', 0) or 0, 0, 0, 0, [], True
    for i, t in enumerate(T):
        if abs(t['d'] - depth) > 1e-9:
            ok = False
        if t['c']:
            run += 1
            d = -1 if run >= 2 else 0
            if d:
                run = 0
        else:
            run, d = 0, +1
        if d:
            if last and d != last:
                rev_at.append(i)
                nrev += 1
            last = d
            step = P['big'] if nrev < P['bigUntil'] else P['small']
            depth = max(-40, min(0, depth + d * step))
    return rev_at, ok


def tmtf():
    app, test = 'tmtf', 'TMTF'
    db = load(app)
    sess = {s['id']: s for s in db['sessions']}
    PNAME = {'uw': 'Won2011/Park2015', 'deruiter': 'DeRuiter2015', 'custom': 'Custom'}
    rows, report = [], {'revcheck_mismatch': []}

    def proto_label(proto, P):
        band = P.get('band') or {}
        bt = 'wideband' if band.get('type') == 'wide' else f"bandpass {band.get('lo')}-{band.get('hi')} Hz" if band else ''
        n = P.get('nAFC')
        return (f"{PNAME.get(proto, proto)} {n}I-{n}AFC adaptive; {P.get('dur')} s; ISI {P.get('isi')} s; {bt}; "
                f"ramp {P.get('rampMs')} ms {P.get('rampShape', 'linear')}; carrier phase {P.get('phase')}; start {P.get('startDb')} dB; "
                f"step {P.get('big')}->{P.get('small')} dB after {P.get('bigUntil')} rev; {P.get('totalRev')} rev, mean of last {P.get('avgLast')}; "
                f"0 dB rule {P.get('ceiling')}")

    for ri_, r in enumerate(db['runs']):
        P = r.get('P') or {}
        T = r['trials']
        d = [t['d'] for t in T]
        # 반전: 3.1+ 은 기록된 revAt. 그 전(revAt 없음)은 앱 Track 이 기록된 정오를 다시 돌려 센 값
        # (앱 ‘시행 CSV’ 의 반전 칸, 같은 db 판 294 에서 11-04 에 내보낸 것). 앱은 0 dB 에서 막힌 이동도 방향으로 셈.
        replay, ok_levels = tmtf_replay(P, T)
        if not ok_levels:
            report['revcheck_mismatch'].append(r['id'] + ':replayed levels != recorded levels')
        if isinstance(r.get('revAt'), list):
            revAt = r['revAt']
            if replay != revAt:
                report['revcheck_mismatch'].append(r['id'] + ':revAt!=replay')
        else:
            revAt = replay
            report['rev_from_replay'] = report.get('rev_from_replay', 0) + 1
        if [d[i] for i in revAt] != (r.get('reversals') or []):
            report['revcheck_mismatch'].append(r['id'] + ':values')
        s = sess.get(r.get('sessionId')) or {}
        status = 'not_measurable_at_0dB' if r.get('ceiling') else ('threshold' if r.get('thr') is not None else 'no_threshold')
        flags = ';'.join(f for f, on in [('at_chance', r.get('atChance')), ('incomplete', r.get('incomplete'))] if on)
        ex_reason = 'test session excluded by participant' if s.get('excluded') else ''
        for i, t in enumerate(T):
            x = base(test, protocol=proto_label(r.get('proto'), P), condition=f"fm={num(r.get('fm'))} Hz",
                     ear=r.get('ear'), session_id=r.get('sessionId') or '', run_id=r['id'], trial_kind='main',
                     run_trial_no=i + 1, value=num(t['d']), unit='dB (20log10 m)', n_intervals=P.get('nAFC'),
                     target_interval=t['tg'] + 1,
                     response_interval='' if t.get('u') else t['a'] + 1, scored_interval=t['a'] + 1,
                     correct=b01(t['c']), reversal=1 if i in revAt else 0,
                     reversal_no=(revAt.index(i) + 1) if i in revAt else '', unsure=1 if t.get('u') else 0,
                     at_limit='easy' if t['d'] == 0 else '', blocked_at_limit='easy' if (t['d'] == 0 and not t['c']) else '',
                     run_status=status, run_flags=flags, excluded=1 if ex_reason else 0, exclusion_reason=ex_reason)
            if t.get('at'):
                set_time(x, t['at'], 'trial_start')
            else:
                set_time(x, r.get('t'), 'run_end')   # 2.x (10-11 오전): 시행 시각 기록 없음 -> 측정 끝난 시각
            x['_ord'] = (ri_, 1, i)
            rows.append(x)
    # 연습 시행 · 버린 측정 (회기 기록 안)
    for si, s in enumerate(db['sessions']):
        for i, t in enumerate(s.get('practiceTrials') or []):
            P = s.get('P') or {}
            x = base(test, protocol=proto_label(s.get('proto'), P), condition=f"fm={num(t.get('fm'))} Hz", ear=s.get('ear'),
                     session_id=s['id'], run_id=f"{s['id']}-practice", trial_kind='practice', run_trial_no=i + 1, value=num(t['d']),
                     unit='dB (20log10 m)', n_intervals=P.get('nAFC'), target_interval=t['tg'] + 1,
                     response_interval='' if t.get('u') else t['a'] + 1, scored_interval=t['a'] + 1, correct=b01(t['c']),
                     reversal='', reversal_no='', unsure=1 if t.get('u') else 0,
                     at_limit='easy' if t['d'] == 0 else '', blocked_at_limit='',
                     run_status='practice', run_flags='', excluded=1, exclusion_reason='practice trial (fixed 0 dB, not part of any track)')
            set_time(x, t.get('at'), 'trial_start')
            x['_ord'] = (10000 + si, 0, i)
            rows.append(x)
        k_ab = 0
        for e in s.get('events') or []:
            if e.get('type') == 'track-abandoned':
                k_ab += 1
                tl = e.get('trialList')
                if not tl:
                    report.setdefault('abandoned_without_trials', []).append((s['id'], e.get('fm'), e.get('trials')))
                    continue
                P = s.get('P') or {}
                for i, t in enumerate(tl):
                    x = base(test, protocol=proto_label(s.get('proto'), P), condition=f"fm={num(e.get('fm'))} Hz", ear=s.get('ear'),
                             session_id=s['id'], run_id=f"{s['id']}-discarded-{k_ab}", trial_kind='main', run_trial_no=i + 1, value=num(t['d']),
                             unit='dB (20log10 m)', n_intervals=P.get('nAFC'), target_interval=t['tg'] + 1,
                             response_interval='' if t.get('u') else t['a'] + 1, scored_interval=t['a'] + 1, correct=b01(t['c']),
                             reversal='', reversal_no='', unsure=1 if t.get('u') else 0,
                             at_limit='easy' if t['d'] == 0 else '', blocked_at_limit='easy' if (t['d'] == 0 and not t['c']) else '',
                             run_status='discarded', run_flags='', excluded=1,
                             exclusion_reason=f"run stopped by participant ({e.get('stopVia', 'stop')}) after {e.get('trials')} trials; discarded by app")
                    set_time(x, t.get('at'), 'trial_start')
                    x['_ord'] = (20000 + si, 0, i)
                    rows.append(x)
    finish(rows, test)
    return report


# ───────────────────────────── SMRT ─────────────────────────────
def smrt():
    app, test = 'smrt', 'SMRT'
    db = load(app)
    dbids = {r['id'] for r in db['runs']}
    deleted = [r for r in log_runs(app) if r['id'] not in dbids]
    rows, report = [], {'runs_log_only_runs': [(r['id'], len(r['trials'])) for r in deleted], 'revcheck_mismatch': []}
    ROVE = {'A': 'rove A (0 dB)', 'B': 'rove B (+/-4 dB, per interval)', 'C': 'rove C (+/-7.5 dB, per interval)'}
    for ri_, (r, is_deleted) in enumerate([(r, False) for r in db['runs']] + [(r, True) for r in deleted]):
        P = r.get('P') or {}
        T = r['trials']
        revAt = r.get('revAt') or []
        idx = [t['i'] for t in T]
        if [idx[i] for i in revAt] != (r.get('reversals') or []):   # 기록된 반전 값 = 표 칸 i (RPO×10)
            report['revcheck_mismatch'].append(r['id'])
        rv = (r.get('rove') or {}).get('cond')
        cond = ROVE.get(rv, f'rove {rv}') if rv else 'no level rove (official SMRT)'
        status = 'stopped_at_20RPO' if r.get('ceiling') else ('threshold' if r.get('thr') is not None else 'no_threshold')
        flags = ';'.join(f for f, on in [('unverified_vs_chance', r.get('unverified')), (f"floor_hits={r.get('floorHits')}", r.get('floorHits')),
                                         ('incomplete', r.get('incomplete'))] if on)
        if r.get('practice'):   # runs-log 에서 가져온 측정도 같은 규칙 (지운 측정 아님 — 사용자 확인 2026-11-04)
            reason = 'practice run'
        else:
            reason = ''
        for i, t in enumerate(T):
            x = base(test, protocol=f"SMRT 1.1.3 official WAVs, {P.get('nAFC')}I-{P.get('nAFC')}AFC adaptive 1-down/1-up, step {P.get('stepIdx', 2) / 10} RPO, "
                                    f"{P.get('totalRev')} rev mean of last {P.get('avgLast')}, ISI {P.get('isiMs')} ms",
                     condition=cond, ear=r.get('ear'), session_id=r.get('sessionId') or '', run_id=r['id'],
                     trial_kind='practice' if r.get('practice') else 'main', run_trial_no=i + 1, value=num(t['i'] / 10), unit='RPO',
                     n_intervals=P.get('nAFC'), target_interval=t['tg'] + 1,
                     response_interval='' if t.get('u') else t['a'] + 1, scored_interval=t['a'] + 1, correct=b01(t['c']),
                     reversal=1 if i in revAt else 0, reversal_no=(revAt.index(i) + 1) if i in revAt else '',
                     unsure=1 if t.get('u') else 0,
                     at_limit='easy' if t['i'] == P.get('minIdx') else ('hard' if t['i'] >= P.get('refIdx', 10 ** 9) else ''),
                     blocked_at_limit='easy' if (t['i'] == P.get('minIdx') and not t['c']) else '',
                     run_status=status, run_flags=flags, excluded=1 if reason else 0, exclusion_reason=reason)
            set_time(x, t.get('at'), 'trial_start')
            x['_ord'] = (ri_, 1, i)
            rows.append(x)
    finish(rows, test)
    return report


# ─────────────────── 새 틀 (STRIPES · STM · SRD · GDT · SMD) ───────────────────
def new_app(app, test, protocol_of, condition_of, value_of, unit, limits_of, blocked_map, nint_of, trial_kind_of=None,
            extra_runs=()):
    db = load(app)
    runs = [(r, None) for r in db['runs']] + list(extra_runs)
    rows, report = [], {'revcheck_mismatch': [], 'abandoned': 0, 'invalid': 0}
    for ri_, (r, forced_reason) in enumerate(runs):
        res = r.get('result') or {}
        st = r.get('state') or {}
        status = res.get('status') or st.get('status') or ''
        flags = ';'.join(res.get('flags') or [])
        aborted = (r.get('endReason') == 'participant_aborted') or (status == 'participant_aborted')
        # 반전 대조: 시행 tr.reversal vs state.reversals 의 trialId
        revIds = [v.get('trialId') for v in (st.get('reversals') or [])]
        trIds = [t['id'] for t in r.get('trials') or [] if (t.get('tr') or {}).get('reversal')]
        if revIds != trIds:
            report['revcheck_mismatch'].append(r['id'])
        lo_hi = limits_of(r)
        items = [(t, False) for t in r.get('trials') or []] + [(a, True) for a in r.get('abandoned') or []]
        for i, (t, is_ab) in enumerate(items):
            tr = t.get('tr') or {}
            kind = trial_kind_of(r, t) if trial_kind_of else ('practice' if r.get('practice') else 'main')
            v = value_of(r, t)
            at = ''
            if lo_hi and v is not None:
                easy, hard = lo_hi
                if abs(v - easy) < 1e-9:
                    at = 'easy'
                elif abs(v - hard) < 1e-9:
                    at = 'hard'
            reasons = []
            if forced_reason:
                reasons.append(forced_reason)
            if kind == 'example':
                reasons.append('example trial (correct answer shown)')
            elif kind == 'screening':
                reasons.append('screening/training trial with feedback (pass check), not part of threshold track')
            elif kind == 'practice':
                reasons.append('practice run')
            if aborted:
                reasons.append('run stopped by participant before its end rule (no threshold)')
            if is_ab:
                reasons.append(f"trial stopped before response ({t.get('how', 'stop')})")
                report['abandoned'] += 1
            if not is_ab and t.get('valid') is False:
                reasons.append(f"invalid trial: {t.get('invalidReason')}")
                report['invalid'] += 1
            resp = '' if is_ab else t.get('response')
            x = base(test, protocol=protocol_of(r), condition=condition_of(r, t), ear=r.get('ear'),
                     session_id=r.get('sessionId') or '', run_id=r['id'], trial_kind=kind, run_trial_no=i + 1,
                     value=num(v), unit=unit, n_intervals=nint_of(r), target_interval=t.get('targetPos'),
                     response_interval=resp, scored_interval=resp,
                     correct='' if is_ab else b01(t.get('correct')),
                     reversal='' if (is_ab or 'reversal' not in tr) else (1 if tr.get('reversal') else 0),
                     reversal_no=tr.get('reversalNo') or '' if not is_ab else '',
                     unsure='', at_limit=at,
                     blocked_at_limit=blocked_map.get(tr.get('blockedAt'), tr.get('blockedAt') or '') if not is_ab else '',
                     run_status=status, run_flags=flags, excluded=1 if reasons else 0, exclusion_reason='; '.join(reasons))
            iso = (t.get('timing') or {}).get('startIso') or t.get('plannedAt') or t.get('stoppedAt')
            set_time(x, iso, 'trial_start' if not is_ab or (t.get('timing') or t.get('plannedAt')) else 'trial_stopped')
            x['_ord'] = (ri_, 1, t.get('attemptNo') or i)
            rows.append(x)
    finish(rows, test)
    return report


def stripes():
    def kind(r, t):
        if t.get('showAnswer'):
            return 'example'
        if t.get('phase') == 'screen' or r.get('kind') == 'gate':
            return 'screening'
        return 'practice' if r.get('practice') else 'main'
    return new_app('stripes', 'STRIPES',
                   protocol_of=lambda r: 'STRIPES 3I-2AFC (A-X-B, target = upward sweeps in A or B), C1 webstripes bank; adaptive 2-down/1-up, 8 reversals mean of last 4'
                   if r.get('kind') != 'gate' else 'STRIPES examples + pass check (C1 webstripes bank)',
                   condition_of=lambda r, t: '',
                   value_of=lambda r, t: (t.get('presentedTicks') if t.get('presentedTicks') is not None else (t.get('tr') or {}).get('presentedTicks')) / 10,
                   unit='D (STRIPES density; RPO = D/5)',
                   limits_of=lambda r: (1.1, 20.0),
                   blocked_map={'lower': 'easy', 'upper': 'hard'},
                   nint_of=lambda r: 3, trial_kind_of=kind)


def stm():
    return new_app('stm', 'STM',
                   protocol_of=lambda r: 'Won2015 STM detection, 2I-2AFC adaptive 2-down/1-up (streamed; not a replication of the original free-field setup)',
                   condition_of=lambda r, t: f"density={num(r['cond']['density'])} c/o; rate={num(r['cond']['rate'])} Hz",
                   value_of=lambda r, t: (t.get('tr') or {}).get('presentedDb', t.get('levelDb')),
                   unit='dB (20log10 A)',
                   limits_of=lambda r: (0.0, -50.0),
                   blocked_map={'ceiling': 'easy', 'floor': 'hard'},
                   nint_of=lambda r: 2)


SRD_DENS = [125, 176, 250, 354, 500, 707, 1000, 1414, 2000, 2828, 4000, 5657, 8000, 11314]


def srd():
    def val(r, t):
        m = t.get('rpoMilli')
        if m is None:
            m = SRD_DENS[t['k']]
        return m / 1000
    def proto(r):
        if r.get('kind') == 'constant':
            return 'Drennan2014 clinical SRD, 3I-3AFC constant stimuli (72 planned trials, inverted ripple)'
        return 'Won2007 SRD, 3I-3AFC adaptive 2-down/1-up (2 correct -> denser), density index, 13 reversals mean of last 8'
    return new_app('srd', 'SRD', protocol_of=proto, condition_of=lambda r, t: '',
                   value_of=val, unit='RPO',
                   limits_of=lambda r: (0.125, 11.314) if r.get('kind') != 'constant' else None,
                   blocked_map={'easy': 'easy', 'hard': 'hard'}, nint_of=lambda r: 3)


GDT_LIM = {'geo20': (226.27416997969522, 0.3125), 'blank': (120.0, 2.0), 'xie': (100.0, 1.0)}   # (긴 끝 = 쉬움, 짧은 끝 = 어려움)
GDT_COND = {'n500': 'broadband noise 20-14000 Hz, 500 ms, gap centred', 'n800': 'noise 800 ms (Xie 2022), target = gap, standard = 4 ms dip',
            't2k': 'tone 2 kHz -> 2 kHz (same-frequency markers)', 't2k1k': 'tone 2 kHz -> 1 kHz (different-frequency markers)'}
GDT_PROTO = {'GDT_WEI2007_ZENG1999_STREAM_v1': 'Wei2007 task / Zeng1999 stimuli, 3I-3AFC adaptive 2-down/1-up on half-octave ladder, 12 rev geometric mean of last 8',
             'GDT_XIE2022_STREAM_v1': 'Xie2022, 2I-2AFC adaptive 2-down/1-up, 10 rev mean of last 6',
             'GDT_BLANKENSHIP2022_STREAM_v1': 'Blankenship2022, 2I-2AFC adaptive 1-up/1-down (value = paper-method value, not a 70.7% threshold)'}


def gdt():
    rm = json.load(open(os.path.join(ROOT, 'gdt', 'deleted_runs_2026-11-03', 'removed.json'), encoding='utf-8'))
    why = 'deleted from app database at participant request (2026-11-03: "program error"); record check that day found no app fault; kept in the app deleted-records folder'
    extra = [(r, why) for r in rm['runs']]
    return new_app('gdt', 'GDT', protocol_of=lambda r: GDT_PROTO.get(r.get('protocolId'), r.get('protocolId')),
                   condition_of=lambda r, t: GDT_COND.get((r.get('cond') or {}).get('id'), (r.get('cond') or {}).get('id')),
                   value_of=lambda r, t: t.get('gapMs'), unit='ms (gap duration)',
                   limits_of=lambda r: GDT_LIM.get(r.get('ladder')),
                   blocked_map={'ceiling': 'easy', 'floor': 'hard'}, nint_of=lambda r: r.get('nAfc'), extra_runs=extra)


def smd():
    def proto(r):
        if r.get('kind') == 'constant':
            return 'QSMD (EasyQSMD 1.0 official Electric WAVs), 3I-3AFC constant stimuli, 60 trials'
        return 'Won2015 SMD, 3I-3AFC adaptive 2-down/1-up, 14 reversals mean of last 10, max depth 60 dB'
    def cond(r, t):
        if r.get('kind') == 'constant':
            return f"density={num(t.get('omega'))} c/o; file={(t.get('file') or {}).get('name', '')}"
        return f"density={num((r.get('cond') or {}).get('omega'))} c/o"
    return new_app('smd', 'SMD', protocol_of=proto, condition_of=cond,
                   value_of=lambda r, t: t.get('h') / 2, unit='dB (peak-to-valley spectral modulation depth)',
                   limits_of=lambda r: (60.0, 0.0) if r.get('kind') != 'constant' else None,
                   blocked_map={'ceiling': 'easy', 'floor': 'hard'}, nint_of=lambda r: 3)


if __name__ == '__main__':
    rep = {}
    for name, fn in [('TMTF', tmtf), ('SMRT', smrt), ('STRIPES', stripes), ('STM', stm), ('SRD', srd), ('GDT', gdt), ('SMD', smd)]:
        rep[name] = fn()
    print(json.dumps(rep, ensure_ascii=False, indent=1))

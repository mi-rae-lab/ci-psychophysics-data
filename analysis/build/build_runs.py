# -*- coding: utf-8 -*-
"""Raw app records (data/raw) + trial CSVs (data/trials) -> one run-level CSV per test (data/runs).

    python -I build_runs.py <data/raw> <data/trials> <data/runs>

One row = one run (one staircase track or one constant-stimuli block). Counts, dates and reversal values are
taken from the trial CSV rows of that run; the threshold, status and flags are the values the app stored.
Rows are also written for things that are not complete runs: TMTF practice blocks (fixed 0 dB), TMTF runs the
participant stopped (the app discarded them), runs stopped by the participant, and the GDT runs deleted from
the app database. They carry included = 0 and the reason.
"""
import csv, datetime as dt, io, json, os, sys

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
RAW, TRI, OUT = sys.argv[1], sys.argv[2], sys.argv[3]
os.makedirs(OUT, exist_ok=True)
KST = dt.timezone(dt.timedelta(hours=9))

HEADER = ['test', 'run_id', 'session_id', 'protocol', 'condition', 'ear', 'run_kind',
          'date_kst', 'start_time_kst', 'end_time_kst',
          'n_trials', 'n_responses', 'n_correct', 'n_unsure', 'n_examples_before',
          'n_reversals', 'reversal_values', 'reversal_trial_nos',
          'threshold_rule', 'n_reversals_used', 'threshold', 'threshold_unit', 'value_kind', 'no_threshold_reason',
          'app_status', 'app_flags', 'included', 'exclusion_reason',
          'audio_sample_rate_hz', 'app_version', 'source']


def load(app, name='db.json'):
    return json.load(open(os.path.join(RAW, app, name), encoding='utf-8'))


def kst(iso):
    if not iso:
        return '', ''
    d = dt.datetime.fromisoformat(iso.replace('Z', '+00:00')).astimezone(KST)
    return d.strftime('%Y-%m-%d'), d.strftime('%H:%M:%S')


def num(x):
    if x is None or x == '':
        return ''
    if isinstance(x, bool):
        return int(x)
    if isinstance(x, int):
        return x
    r = round(float(x), 6)
    return int(r) if r == int(r) else r


def trials_by_run(test):
    by = {}
    with open(os.path.join(TRI, f'{test.lower()}_trials.csv'), encoding='utf-8') as f:
        for row in csv.DictReader(f):
            by.setdefault(row['run_id'], []).append(row)
    for rs in by.values():
        rs.sort(key=lambda r: int(r['run_trial_no']))
    return by


def counts(rows):
    resp = [r for r in rows if r['correct'] != '']
    rev = [r for r in rows if r['reversal'] == '1']
    times = [(r['date_kst'], r['time_kst'][:8]) for r in rows if r['time_source'] in ('trial_start', 'trial_stopped')]
    return {
        'n_trials': len(rows), 'n_responses': len(resp), 'n_correct': sum(r['correct'] == '1' for r in resp),
        'n_unsure': sum(r['unsure'] == '1' for r in rows) if any(r['unsure'] != '' for r in rows) else '',
        'n_reversals': len(rev) if any(r['reversal'] != '' for r in rows) else '',
        'reversal_values': ';'.join(r['value'] for r in rev), 'reversal_trial_nos': ';'.join(r['run_trial_no'] for r in rev),
        '_first': min(times) if times else None, '_last': max(times) if times else None,
        '_excl': sorted({x for r in rows for x in r['exclusion_reason'].split('; ') if x}),
        '_any_incl': any(r['excluded'] == '0' for r in rows),
    }


def finish_row(test, base, rows, start_iso=None, end_iso=None):
    c = counts(rows)
    out = {k: '' for k in HEADER}
    out.update({k: v for k, v in c.items() if not k.startswith('_')})
    out.update(base)
    out['test'] = test
    if start_iso:
        out['date_kst'], out['start_time_kst'] = kst(start_iso)
    elif c['_first']:
        out['date_kst'], out['start_time_kst'] = c['_first']
    if end_iso:
        d, t = kst(end_iso)
        out['end_time_kst'] = t
        if not out['date_kst']:
            out['date_kst'] = d
    if rows and not out['protocol']:
        out['protocol'] = rows[0]['protocol']
    if rows and out['condition'] == '' and len({r['condition'] for r in rows}) == 1:
        out['condition'] = rows[0]['condition']
    if out['included'] == '':
        out['included'] = 0 if c['_excl'] or not rows else 1
    if out['exclusion_reason'] == '' and out['included'] == 0:
        out['exclusion_reason'] = '; '.join(c['_excl'])
    return out


def write(test, rows):
    rows.sort(key=lambda r: (r['date_kst'], r['start_time_kst'] or r['end_time_kst'], r['run_id']))
    with open(os.path.join(OUT, f'{test.lower()}_runs.csv'), 'w', encoding='utf-8', newline='') as f:
        w = csv.DictWriter(f, fieldnames=HEADER, lineterminator='\n')
        w.writeheader()
        w.writerows(rows)
    print(f'{test}: {len(rows)} runs, included {sum(int(r["included"]) for r in rows)}')


# ───────────────────────────── TMTF ─────────────────────────────
def tmtf_proto_label(proto, P):
    """Same text as the protocol column of the trial CSV (build_trials.py)."""
    name = {'uw': 'Won2011/Park2015', 'deruiter': 'DeRuiter2015', 'custom': 'Custom'}.get(proto, proto)
    band = P.get('band') or {}
    bt = 'wideband' if band.get('type') == 'wide' else f"bandpass {band.get('lo')}-{band.get('hi')} Hz" if band else ''
    n = P.get('nAFC')
    return (f"{name} {n}I-{n}AFC adaptive; {P.get('dur')} s; ISI {P.get('isi')} s; {bt}; "
            f"ramp {P.get('rampMs')} ms {P.get('rampShape', 'linear')}; carrier phase {P.get('phase')}; start {P.get('startDb')} dB; "
            f"step {P.get('big')}->{P.get('small')} dB after {P.get('bigUntil')} rev; {P.get('totalRev')} rev, mean of last {P.get('avgLast')}; "
            f"0 dB rule {P.get('ceiling')}")


def tmtf():
    db, T = load('tmtf'), trials_by_run('TMTF')
    out = []
    for r in db['runs']:
        P = r.get('P') or {}
        rows = T.get(r['id'], [])
        rule = (f"arithmetic mean of the last {P.get('avgLast')} of {P.get('totalRev')} reversals (app rounds to 0.01 dB); "
                f"0 dB rule {P.get('ceiling')}" + (' (4 cumulative errors at 0 dB -> not measurable, stored as 0 dB)' if P.get('ceiling') == 'stop4' else ''))
        if r.get('ceiling'):
            thr, kind, why = '', 'none', 'not measurable: 4 cumulative errors at 0 dB (100 % modulation); the app stores 0 dB, which is not a threshold'
        elif r.get('thr') is None:
            thr, kind, why = '', 'none', 'no threshold stored'
        else:
            thr, kind, why = num(r['thr']), 'threshold', ''
        flags = ';'.join(f for f, on in [('at_chance', r.get('atChance')), ('incomplete', r.get('incomplete'))] if on)
        base = dict(run_id=r['id'], session_id=r.get('sessionId') or '', condition=f"fm={num(r.get('fm'))} Hz", ear=r.get('ear'),
                    run_kind='main', threshold_rule=rule, n_reversals_used=P.get('avgLast') if kind == 'threshold' else '',
                    threshold=thr, threshold_unit='dB (20log10 m)', value_kind=kind, no_threshold_reason=why,
                    app_status=rows[0]['run_status'] if rows else '', app_flags=flags,
                    audio_sample_rate_hz=(r.get('audio') or {}).get('sampleRate', ''), app_version=r.get('app', ''), source='db.json runs[]')
        if base['app_version'].startswith('2.x'):
            # app label '2.x (이전 판, 2026-10-11 오전)'; values are kept ASCII. These runs ended 20:06-21:18 KST (evening).
            base['app_version'] = '2.x (version before 3.0, 2026-10-11)'
        out.append(finish_row('TMTF', base, rows, start_iso=r.get('startedAt'), end_iso=r.get('t')))
    for s in db['sessions']:
        P = s.get('P') or {}
        if s.get('practiceTrials'):
            rid = f"{s['id']}-practice"
            rows = T.get(rid, [])
            assert len(rows) == len(s['practiceTrials'])
            base = dict(run_id=rid, session_id=s['id'], ear=s.get('ear'), run_kind='practice', threshold_rule='',
                        threshold_unit='dB (20log10 m)', value_kind='none',
                        no_threshold_reason='practice block at fixed 0 dB (not a staircase)', app_status='practice',
                        source='db.json sessions[].practiceTrials')
            out.append(finish_row('TMTF', base, rows))
        k = 0
        for e in s.get('events') or []:
            if e.get('type') != 'track-abandoned':
                continue
            k += 1
            rid = f"{s['id']}-discarded-{k}"
            rows = T.get(rid, [])
            saved = bool(e.get('trialList'))
            base = dict(run_id=rid, session_id=s['id'], ear=s.get('ear'), run_kind='main', condition=f"fm={num(e.get('fm'))} Hz",
                        protocol='' if rows else tmtf_proto_label(s.get('proto'), s.get('P') or {}),
                        threshold_unit='dB (20log10 m)', value_kind='none',
                        no_threshold_reason=f"run stopped by the participant after {e.get('trials')} trials; discarded by the app",
                        app_status='discarded', included=0,
                        exclusion_reason=(f"run stopped by participant ({e.get('stopVia', 'stop')}) after {e.get('trials')} trials; discarded by app"
                                          + ('' if saved else '; its trials were not saved by this app version (no trial rows)')),
                        source='db.json sessions[].events[type=track-abandoned]')
            row = finish_row('TMTF', base, rows, end_iso=e.get('t') if not rows else None)
            if not rows:
                row['n_trials'] = 0
            out.append(row)
    write('TMTF', out)


# ───────────────────────────── SMRT ─────────────────────────────
def smrt():
    db, T = load('smrt'), trials_by_run('SMRT')
    ids = {r['id'] for r in db['runs']}
    extra = []
    for line in open(os.path.join(RAW, 'smrt', 'runs-log.jsonl'), encoding='utf-8'):
        o = json.loads(line)
        if o.get('type') == 'run' and o['data']['id'] not in ids:
            extra.append(o['data'])
    out = []
    for r in db['runs'] + extra:
        P = r.get('P') or {}
        rows = T[r['id']]
        if r.get('ceiling'):
            thr, kind, why = '', 'none', 'stopped at the 20-RPO limit'
        elif r.get('thr') is None:
            thr, kind, why = '', 'none', 'no threshold stored'
        else:
            thr, kind, why = num(r['thr']), 'threshold', ''
        flags = ';'.join(f for f, on in [('unverified_vs_chance', r.get('unverified')), (f"floor_hits={r.get('floorHits')}", r.get('floorHits')),
                                         ('incomplete', r.get('incomplete'))] if on)
        base = dict(run_id=r['id'], session_id=r.get('sessionId') or '', ear=r.get('ear'),
                    run_kind='practice' if r.get('practice') else 'main',
                    threshold_rule=f"arithmetic mean of the last {P.get('avgLast')} of {P.get('totalRev')} reversals (app rounds to 0.0001 RPO)",
                    n_reversals_used=P.get('avgLast') if kind == 'threshold' else '', threshold=thr, threshold_unit='RPO',
                    value_kind=kind, no_threshold_reason=why, app_status=rows[0]['run_status'], app_flags=flags,
                    audio_sample_rate_hz=(r.get('audio') or {}).get('sampleRate', ''), app_version=r.get('app', ''),
                    source='db.json runs[]' if r['id'] in ids else 'runs-log.jsonl (run line; not in the db.json run list)')
        out.append(finish_row('SMRT', base, rows, start_iso=r.get('startedAt'), end_iso=r.get('t')))
    write('SMRT', out)


# ─────────────────── new framework (STRIPES · STM · SRD · GDT · SMD) ───────────────────
RULES = {
    'STRIPES': lambda r: ('arithmetic mean of the last 4 of 8 reversals (D); moves blocked at a limit are not moves or reversals', 4, 'D (STRIPES density; RPO = D/5)'),
    'STM': lambda r: ('arithmetic mean of the last 10 of 14 reversals (dB); moves blocked at a limit are not moves or reversals', 10, 'dB (20log10 A)'),
    'SRD': lambda r: (('arithmetic mean of the last 8 of 13 reversals (RPO); moves blocked at a limit are not moves or reversals', 8, 'RPO')
                      if r.get('kind') != 'constant' else ('constant stimuli: proportion correct over 72 planned trials', '', '')),
    'GDT': lambda r: {'zeng': ('geometric mean of the last 8 of 12 reversals (ms)', 8, 'ms (gap duration)'),
                      'xie': ('arithmetic mean of the last 6 of 10 reversals (ms)', 6, 'ms (gap duration)'),
                      'blank': ('arithmetic mean of the last 3 of 5 reversals (ms); 1-up/1-down tracks 50 % = 2AFC chance: a paper-method value, not a 70.7 % threshold', 3, 'ms (gap duration)')}[r.get('protocolKey')],
    'SMD': lambda r: (('arithmetic mean of the last 10 of 14 reversals (dB); moves blocked at a limit are not moves or reversals', 10, 'dB (peak-to-valley spectral modulation depth)')
                      if r.get('kind') != 'constant' else ('constant stimuli (QSMD): proportion correct over 60 official files', '', '')),
}
WHY = {
    'threshold_near_easy_end': 'threshold_near_easy_end: the staircase was blocked at the easy end (0.125 RPO) inside the analysis window, so the reversal mean is not a threshold',
    'threshold_near_floor': 'threshold_near_floor: the staircase was held at the shortest gap of the ladder (test floor), so no numeric threshold',
    'threshold_above_window': 'threshold_above_window: accuracy in the analysis window was confirmed below the 70.7 % target, so the track had not converged',
    'participant_aborted': 'run stopped by the participant before its end rule',
    'passed': 'examples and pass check (not a threshold track)',
}


def new_app(app, test, extra_runs=()):
    db, T = load(app), trials_by_run(test)
    out = []
    for r, forced in [(r, None) for r in db['runs']] + list(extra_runs):
        res = r.get('result') or {}
        st = r.get('state') or {}
        rows = T.get(r['id'], [])
        status = res.get('status') or st.get('status') or ''
        rule, used, unit = RULES[test](r)
        vk = res.get('valueKind')
        if r.get('kind') == 'gate':
            run_kind = 'screening'
        else:
            run_kind = 'practice' if r.get('practice') else 'main'
        if res.get('kind') == 'constant' or r.get('kind') == 'constant':
            thr, kind = '', 'none'
            why = ('constant-stimuli test: no threshold; score = n_correct / n_responses' if status == 'complete'
                   else WHY.get(status, status))
        elif res.get('thr') is not None:
            thr, kind, why = num(res['thr']), ('paper_method_value' if vk == 'paper_value' else 'threshold'), ''
        else:
            thr, kind, why = '', 'none', WHY.get(status, status or 'no threshold stored')
        if test == 'STRIPES' and r.get('kind') == 'gate':
            rule, used, unit = '', '', 'D (STRIPES density; RPO = D/5)'
        if test == 'SMD' and r.get('kind') == 'constant':
            cond = 'QSMD 60 official files (densities 0.5/1/2 c/o)'
        else:
            cond = ''
        base = dict(run_id=r['id'], session_id=r.get('sessionId') or '', ear=r.get('ear'), run_kind=run_kind, condition=cond,
                    threshold_rule=rule, n_reversals_used=used if kind != 'none' else '', threshold=thr, threshold_unit=unit,
                    value_kind=kind, no_threshold_reason=why, app_status=status, app_flags=';'.join(res.get('flags') or []),
                    n_examples_before=r.get('examplesBefore', '') if r.get('examplesBefore') is not None else '',
                    audio_sample_rate_hz=(r.get('audio') or {}).get('sampleRate', ''), app_version=r.get('app', ''),
                    source='db.json runs[]' if not forced else 'deleted_runs_2026-11-03/removed.json runs[]')
        if forced:
            base['included'] = 0
            base['exclusion_reason'] = forced
        row = finish_row(test, base, rows, start_iso=r.get('startedAt'), end_iso=r.get('endedAt'))
        out.append(row)
    write(test, out)


GDT_WHY = ('deleted from app database at participant request (2026-11-03: "program error"); record check that day found no app fault; '
           'kept in the app deleted-records folder')

if __name__ == '__main__':
    tmtf()
    smrt()
    new_app('stripes', 'STRIPES')
    new_app('stm', 'STM')
    new_app('srd', 'SRD')
    rm = load('gdt', os.path.join('deleted_runs_2026-11-03', 'removed.json'))
    new_app('gdt', 'GDT', extra_runs=[(r, GDT_WHY) for r in rm['runs']])
    new_app('smd', 'SMD')

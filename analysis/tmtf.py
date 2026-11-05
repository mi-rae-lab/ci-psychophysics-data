# -*- coding: utf-8 -*-
"""TMTF — reproduces TMTF_English / TMTF_Korean: modulation sensitivity (-MDT) by procedure, ear and modulation frequency.

The PDF was made from the records up to 2026-11-03 (142 runs). The eight runs of 2026-11-04 (56-59 Hz) came later;
they are in the CSVs but are left out here with PDF_LAST_DATE. Set PDF_LAST_DATE = None to include them.
"""
import re
import statistics

import matplotlib.pyplot as plt

from common import (C_ACC, C_BAD, C_GRAY, C_L, C_OK, C_R, Pages, answered, by_run, js_round, load, mean,
                    reversal_trial_nos, reversal_values, sd, staircase)

PDF_LAST_DATE = '2026-11-03'
GROUPS = [('two_interval', 'Won2011/Park2015', 'Two-interval (2AFC, Won 2011 / Park 2015 settings)'),
          ('bandpass', 'DeRuiter2015', 'Three-interval bandpass (3AFC, De Ruiter 2015 settings)'),
          ('custom', 'Custom', 'Custom settings (3AFC, broadband, random AM phase)')]
EXAMPLES = [('A', 'two_interval', 10), ('B', 'bandpass', 10), ('C', 'custom', 10), ('D', 'custom', 65), ('E', 'custom', 68), ('F', 'custom', 70)]


def fm_of(r):
    return int(re.match(r'fm=(\d+) Hz', r['condition']).group(1))


def group_of(r):
    for g, pre, _ in GROUPS:
        if (r['protocol'] or '').startswith(pre):
            return g
    return None


def run(outdir):
    trials, runs = load('tmtf')
    tr = by_run(trials)
    cut = (lambda d: d <= PDF_LAST_DATE) if PDF_LAST_DATE else (lambda d: True)
    kept = [r for r in runs if r['included'] == 1 and r['run_kind'] == 'main' and cut(r['date_kst'])]
    kept.sort(key=lambda r: (r['date_kst'], r['end_time_kst'] or '', r['run_id']))
    out, checks = {}, {}
    thr, bad = {}, 0
    for r in kept:
        if r['app_status'] == 'threshold':
            rv = reversal_values(tr[r['run_id']])
            thr[r['run_id']] = js_round(mean(rv[-r['n_reversals_used']:]), 2)     # app: mean of last N reversals, toFixed(2)
            bad += thr[r['run_id']] != r['threshold']
    checks['threshold_recomputed_vs_app_mismatch'] = bad
    unmeas = {r['run_id'] for r in kept if r['app_status'] == 'not_measurable_at_0dB'}
    flagged = {r['run_id'] for r in kept if 'at_chance' in (r['app_flags'] or '')}
    cells = {}
    for r in kept:
        cells.setdefault((group_of(r), r['ear'], fm_of(r)), []).append(r)

    def cell_stats(prefix, rs):
        num = [r for r in rs if r['run_id'] in thr]
        ys = [-thr[r['run_id']] for r in num]
        out[f'{prefix}.mean_neg_mdt'] = mean(ys) if ys else None
        out[f'{prefix}.sd'] = sd(ys)
        out[f'{prefix}.flagged'] = 'yes' if any(r['run_id'] in flagged for r in num) else 'no'
        out[f'{prefix}.n'] = len(num) if rs else None
        out[f'{prefix}.R'] = len(rs) if rs else None
        out[f'{prefix}.N'] = sum(r['n_responses'] for r in rs) if rs else None

    for g, _, _ in GROUPS:
        fms = sorted({fm for (gg, e, fm) in cells if gg == g})
        for e in ('L', 'R'):
            if not any(gg == g and ee == e for (gg, ee, _) in cells):
                continue
            for fm in fms:
                cell_stats(f'{g}.{e}.{fm}Hz', cells.get((g, e, fm), []))
                if g == 'custom' and 55 <= fm <= 70:
                    cell_stats(f'custom_55_70.{e}.{fm}Hz', cells.get((g, e, fm), []))
        rs = [r for r in kept if group_of(r) == g]
        out[f'{g}.total.n'] = sum(r['run_id'] in thr for r in rs)
        out[f'{g}.total.R'] = len(rs)
        out[f'{g}.total.N'] = sum(r['n_responses'] for r in rs)
        for e in ('L', 'R'):
            es = [r for r in rs if r['ear'] == e]
            if not es:
                continue
            k = f'composition.{g}.{e}'
            out[f'{k}.n'] = sum(r['run_id'] in thr for r in es)
            out[f'{k}.R'] = len(es)
            out[f'{k}.N'] = sum(r['n_responses'] for r in es)
            out[f'{k}.U'] = sum(r['run_id'] in unmeas for r in es)
            out[f'{k}.U_pct'] = 100 * out[f'{k}.U'] / len(es)
    det = [r for r in kept if group_of(r) == 'custom' and 55 <= fm_of(r) <= 70]
    out['custom_55_70.total.n'] = sum(r['run_id'] in thr for r in det)
    out['custom_55_70.total.R'] = len(det)
    out['custom_55_70.total.N'] = sum(r['n_responses'] for r in det)
    out['all.n'] = len(thr)
    out['all.R'] = len(kept)
    out['all.N'] = sum(r['n_responses'] for r in kept)
    out['all.practice_trials_excluded'] = sum(1 for t in trials if t['trial_kind'] == 'practice' and cut(t['date_kst']))
    out['all.abandoned_run_trials_excluded'] = sum(1 for t in trials if t['run_status'] == 'discarded' and cut(t['date_kst']))
    out['all.unsure_trials'] = sum(r['n_unsure'] for r in kept)
    out['all.runs_with_48kHz_record'] = sum(r['audio_sample_rate_hz'] == 48000 for r in kept)
    out['all.runs_without_sample_rate'] = sum(r['audio_sample_rate_hz'] is None for r in kept)
    if PDF_LAST_DATE:
        later = [r for r in runs if r['included'] == 1 and r['run_kind'] == 'main' and not cut(r['date_kst'])]
        checks['runs_after_pdf_date_not_used'] = len(later)
    ex_runs = {}
    for lab, g, fm in EXAMPLES:
        cand = sorted([r for r in kept if group_of(r) == g and fm_of(r) == fm and r['ear'] == 'R'],
                      key=lambda r: (r['date_kst'], r['end_time_kst'] or ''))
        r = cand[0]
        ex_runs[lab] = r
        out[f'example.{lab}.run_id'] = r['run_id']
        out[f'example.{lab}.date'] = r['date_kst']
        out[f'example.{lab}.trials'] = r['n_responses']
        out[f'example.{lab}.reversals'] = r['n_reversals']
        out[f'example.{lab}.threshold'] = thr.get(r['run_id'], 'not measurable')
    # ── figures ──
    pg = Pages(outdir, 'tmtf')
    for g, _, title in GROUPS + [('custom_55_70', None, 'Custom settings, 55-70 Hz detail')]:
        gg = 'custom' if g == 'custom_55_70' else g
        fig, axs = plt.subplots(2, 1, figsize=(12, 8.5), gridspec_kw={'height_ratios': [2.2, 1]})
        ax = axs[0]
        table = []
        for e, col, dx in (('L', C_L, -0.015), ('R', C_R, 0.015)):
            fms = sorted({fm for (x, ee, fm) in cells if x == gg and ee == e and (g != 'custom_55_70' or 55 <= fm <= 70)})
            if not fms:
                continue
            mx, my = [], []
            for fm in fms:
                rs = cells[(gg, e, fm)]
                xf = fm * (1 + dx) if g != 'custom_55_70' else fm + dx * 10
                for r in rs:
                    if r['run_id'] in thr:
                        ax.plot(xf, -thr[r['run_id']], 'o', ms=4, color=col, mfc='white' if r['run_id'] in flagged else col, alpha=0.8)
                    else:
                        ax.plot(xf, 0.3, 'x', ms=5, color=col)
                ys = [-thr[r['run_id']] for r in rs if r['run_id'] in thr]
                if ys:
                    mx.append(xf)
                    my.append(mean(ys))
                    ax.errorbar(xf, mean(ys), yerr=sd(ys) or 0, fmt='D', ms=5, color=col, mec='k', capsize=2)
                k = f'{g}.{e}.{fm}Hz'
                m, s = out[k + '.mean_neg_mdt'], out[k + '.sd']
                table.append((e, fm, '—' if m is None else f'{m:.2f}', '—' if s is None else f'{s:.2f}',
                              '†' if out[k + '.flagged'] == 'yes' else '', f"{out[k + '.n']}/{out[k + '.R']}", out[k + '.N']))
            ax.plot(mx, my, '-', color=col, lw=1, label=f"{'Left' if e == 'L' else 'Right'} ear")
        if g != 'custom_55_70':
            ax.set_xscale('log')
            xt = sorted({fm for (x, _, fm) in cells if x == gg})
            show = set(xt) if len(xt) <= 12 else {4, 5, 8, 10, 15, 20, 25, 30, 40, 50, 60, 65, 70, 80, 100, 180, 200, 245, 300} & set(xt)
            ax.set_xticks(xt, [str(v) if v in show else '' for v in xt], fontsize=6.5)
            ax.minorticks_off()
        ax.set_xlabel('modulation frequency (Hz)')
        ax.set_ylabel('modulation sensitivity −MDT (dB)')
        ax.legend(loc='upper right')
        tot = 'custom_55_70' if g == 'custom_55_70' else g
        ax.set_title(f"{title} | n/R = {out[f'{tot}.total.n']}/{out[f'{tot}.total.R']}, N = {out[f'{tot}.total.N']}", loc='left')
        ax = axs[1]
        ax.axis('off')
        lines = ['ear  fm(Hz)  mean   SD     n/R   N']
        lines += [f'{e:3s}  {fm:6d}  {m:>5s}  {s:>5s}{fl:1s} {nr:>5s} {N:4d}' for e, fm, m, s, fl, nr, N in table]
        cols = [lines[0]] + lines[1:]
        per = 14
        for c in range(0, len(cols) - 1, per):
            ax.text(c / per * 0.24, 1, '\n'.join([lines[0]] + lines[1 + c:1 + c + per]), family='monospace', fontsize=6.5, va='top',
                    transform=ax.transAxes)
        fig.text(0.01, 0.005, 'Dots: numeric run thresholds (sign flipped: −MDT). x: unmeasurable runs (4 cumulative errors at 0 dB), '
                 'drawn at the bottom, not a threshold.\nDiamonds: mean ± sample SD of numeric runs. Open dots / †: app flag at_chance. '
                 'n numeric thresholds, R retained runs, N response trials. Ticks without labels: see the table.', fontsize=6.3)
        fig.tight_layout(rect=(0, 0.035, 1, 0.95))
        pg.add(fig, f"TMTF | {title} | records 2026-10-11 to {PDF_LAST_DATE or 'end'}")
    fig, axs = plt.subplots(1, 2, figsize=(12, 5))
    comp = [(g, e) for g, _, _ in GROUPS for e in ('L', 'R') if f'composition.{g}.{e}.R' in out]
    ax = axs[0]
    for i, (g, e) in enumerate(comp):
        k = f'composition.{g}.{e}'
        ax.barh(i, out[k + '.n'], color='#2a9d8f')
        ax.barh(i, out[k + '.U'], left=out[k + '.n'], color='#e9a23b')
        ax.text(out[k + '.R'] + 1, i, f"n/R={out[k + '.n']}/{out[k + '.R']}  N={out[k + '.N']}\nU/R={out[k + '.U']}/{out[k + '.R']} "
                f"({out[k + '.U_pct']:.1f}%)", va='center', fontsize=6.5)
    ax.set_yticks(range(len(comp)), [f"{g.replace('_', '-')} / {'Left' if e == 'L' else 'Right'}" for g, e in comp])
    ax.invert_yaxis()
    ax.set_xlim(0, 150)
    ax.set_xlabel('completed runs (R): numeric threshold (teal) + unmeasurable (ochre)')
    ax = axs[1]
    for i, (g, e) in enumerate(comp):
        rs = [r for r in kept if group_of(r) == g and r['ear'] == e]
        xs = [r['n_responses'] for r in rs]
        ax.scatter(xs, [i + ((j % 7) - 3) * 0.04 for j in range(len(xs))], s=8,
                   c=['#2a9d8f' if r['run_id'] in thr else '#e9a23b' for r in rs])
        ax.plot([statistics.median(xs)] * 2, [i - 0.3, i + 0.3], 'k-', lw=1.2)
    ax.set_yticks(range(len(comp)), ['' for _ in comp])
    ax.invert_yaxis()
    ax.set_xlabel('response trials per run (vertical mark = median)')
    fig.tight_layout(rect=(0, 0.02, 1, 0.93))
    pg.add(fig, f"TMTF | run composition and trial burden | n/R = {out['all.n']}/{out['all.R']}, N = {out['all.N']}")
    fig, axs = plt.subplots(2, 3, figsize=(13, 8))
    for ax, (lab, g, fm) in zip(axs.flat, EXAMPLES):
        r = ex_runs[lab]
        rows = tr[r['run_id']]
        used = reversal_trial_nos(rows)[-r['n_reversals_used']:] if r['run_id'] in thr else []
        res = f"threshold {thr[r['run_id']]:.2f} dB" if r['run_id'] in thr else 'not measurable' + (' †' if r['run_id'] in flagged else '')
        staircase(ax, rows, used, thr.get(r['run_id']), ylabel='presented depth (dB)',
                  title=f"{lab}  {g.replace('_', '-')} · {fm} Hz · {r['run_id']} · {r['date_kst']}\n"
                        f"{r['n_responses']} trials · {r['n_reversals']} reversals · {res}")
    fig.text(0.01, 0.005, 'Right ear, earliest record at each protocol/frequency (not selected for good outcomes). '
             'Filled = correct, open = incorrect, diamonds = reversals (orange = used for the threshold).', fontsize=6.5)
    fig.tight_layout(rect=(0, 0.02, 1, 0.95))
    pg.add(fig, 'TMTF | recorded adaptive staircases')
    checks['figure_pages'] = pg.close()
    return out, checks

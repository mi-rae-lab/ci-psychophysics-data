# -*- coding: utf-8 -*-
"""STM — reproduces STM_Scientific (EN/KO): 27 runs, six density x rate conditions, both ears (2026-10-18/19)."""
import re

import matplotlib.pyplot as plt

from common import (C_GRAY, C_L, C_R, Pages, answered, by_run, load, mean, reversal_trial_nos,
                    reversal_values, sd, staircase)

DENS = ['0.5', '1', '2']
RATES = [5, 10]


def cond_of(r):
    m = re.match(r'density=([\d.]+) c/o; rate=(\d+) Hz', r['condition'])
    return m.group(1), int(m.group(2))


def run(outdir):
    trials, runs = load('stm')
    tr = by_run(trials)
    runs = [r for r in runs if r['included'] == 1]
    runs.sort(key=lambda r: (r['date_kst'], r['start_time_kst']))
    out, checks = {}, {}
    thr, lab = {}, {}
    bad = 0
    for e in ('R', 'L'):
        for i, r in enumerate([r for r in runs if r['ear'] == e], 1):
            lab[r['run_id']] = f'{e}{i:02d}'
    for r in runs:
        rv = reversal_values(tr[r['run_id']])
        thr[r['run_id']] = mean(rv[-10:])                         # mean of the last 10 of 14 reversals
        bad += abs(thr[r['run_id']] - r['threshold']) > 1e-9
    checks['threshold_recomputed_vs_app_mismatch'] = bad
    out['all.n_runs'] = len(runs)
    out['all.n_trials'] = sum(r['n_responses'] for r in runs)
    out['all.n_intervals'] = 2 * out['all.n_trials']
    out['all.n_correct'] = sum(r['n_correct'] for r in runs)
    out['all.technical_failures'] = sum(1 for t in trials if 'invalid trial' in (t['exclusion_reason'] or ''))
    win = init = 0
    for r in runs:
        rows = tr[r['run_id']]
        start = reversal_trial_nos(rows)[4]                          # analysis window = 5th reversal to run end
        for t in rows:
            if t['blocked_at_limit'] == 'easy':
                if t['run_trial_no'] >= start:
                    win += 1
                else:
                    init += 1
    out['all.ceiling_blocked_in_analysis_window'] = win
    out['all.ceiling_blocked_in_initial_segment'] = init
    for e in ('R', 'L'):
        rs = [r for r in runs if r['ear'] == e]
        out[f'ear.{e}.n_runs'] = len(rs)
        out[f'ear.{e}.n_trials'] = sum(r['n_responses'] for r in rs)
        for rate in RATES:
            ps = [r for r in rs if cond_of(r)[1] == rate]
            out[f'panel.{e}.{rate}Hz.n'] = len(ps)
            out[f'panel.{e}.{rate}Hz.T'] = sum(r['n_responses'] for r in ps)
            out[f'panel.{e}.{rate}Hz.I'] = 2 * out[f'panel.{e}.{rate}Hz.T']
    cell = {}
    for e in ('R', 'L'):
        for d in DENS:
            for rate in RATES:
                cs = [r for r in runs if r['ear'] == e and cond_of(r) == (d, rate)]
                cell[(e, d, rate)] = cs
                k = f'cell.{e}.{d}co.{rate}Hz'
                ys = [thr[r['run_id']] for r in cs]
                out[f'{k}.mean'], out[f'{k}.sd'], out[f'{k}.n'] = mean(ys), sd(ys), len(ys)
                out[f'{k}.T'] = sum(r['n_responses'] for r in cs)
                out[f'{k}.I'] = 2 * out[f'{k}.T']
                out[f'{k}.T_per_run'] = ', '.join(str(r['n_responses']) for r in cs)
                rk = f'repeat.{e}.{d}co.{rate}Hz'
                for j in range(3):
                    out[f'{rk}.run{j + 1}'] = ys[j] if j < len(ys) else None
                out[f'{rk}.run2_minus_run1'] = ys[1] - ys[0]
    gt3 = [(e, d, rate) for (e, d, rate) in cell if abs(out[f'repeat.{e}.{d}co.{rate}Hz.run2_minus_run1']) > 3]
    out['repeat.n_cells_absdiff_gt3'] = len(gt3)
    out['repeat.n_cells_absdiff_gt3_with_third_run'] = sum(1 for c in gt3 if len(cell[c]) >= 3)
    nlow = 0
    for d in DENS:
        for rate in RATES:
            rm, lm = out[f'cell.R.{d}co.{rate}Hz.mean'], out[f'cell.L.{d}co.{rate}Hz.mean']
            out[f'cond.{d}co.{rate}Hz.R_mean_1dp'] = rm
            out[f'cond.{d}co.{rate}Hz.L_mean_1dp'] = lm
            out[f'cond.{d}co.{rate}Hz.R_minus_L'] = rm - lm
            nlow += rm < lm
    out['sixcond.n_conditions_R_lower'] = nlow
    for e in ('R', 'L'):
        out[f'sixcond.{e}.mean'] = mean(out[f'cell.{e}.{d}co.{rate}Hz.mean'] for d in DENS for rate in RATES)
    for r in runs:
        k = f"run.{lab[r['run_id']]}"
        d, rate = cond_of(r)
        out[f'{k}.condition'] = f'{d} c/o · {rate} Hz'
        out[f'{k}.threshold'] = thr[r['run_id']]
        out[f'{k}.T'] = r['n_responses']
        fl = (r['app_flags'] or '').split(';')
        out[f'{k}.flags'] = ' '.join(x for x, f in (('IB', 'interval_bias'), ('NC', 'near_ceiling')) if f in fl) or 'none'
        rows = answered(tr[r['run_id']])
        parts = []
        for pos in ('1', '2'):
            p = [t for t in rows if t['target_interval'] == pos]
            parts.append(f"{sum(t['correct'] for t in p)}/{len(p)}")
        out[f'{k}.correct_by_target_interval'] = ' | '.join(parts)
    # ── figures ──
    pg = Pages(outdir, 'stm')
    fig = plt.figure(figsize=(12, 9))
    gs = fig.add_gridspec(3, 2)
    for i, (e, rate) in enumerate([('R', 5), ('L', 5), ('R', 10), ('L', 10)]):
        ax = fig.add_subplot(gs[i // 2, i % 2])
        col = C_R if e == 'R' else C_L
        for j, d in enumerate(DENS):
            cs = cell[(e, d, rate)]
            ys = [thr[r['run_id']] for r in cs]
            for q, (y, r) in enumerate(zip(ys, cs)):
                fl = r['app_flags'] or ''
                ax.plot(j + (q - (len(ys) - 1) / 2) * 0.08, y, 'o', color=col, mfc='white' if 'interval_bias' in fl else col, ms=5)
                if 'near_ceiling' in fl:
                    ax.annotate('+', (j + (q - (len(ys) - 1) / 2) * 0.08, y), xytext=(4, 2), textcoords='offset points')
            ax.errorbar(j + 0.25, mean(ys), yerr=sd(ys), fmt='D', color='k', capsize=3, ms=4)
            ax.text(j, -27.6, f'M±SD {mean(ys):.2f}±{sd(ys):.2f}\nn={len(ys)} T={sum(r["n_responses"] for r in cs)} '
                    f'I={2 * sum(r["n_responses"] for r in cs)}\nT/run: ' + ', '.join(str(r['n_responses']) for r in cs),
                    ha='center', va='bottom', fontsize=6)
        ax.axhline(0, color=C_GRAY, ls='--', lw=0.8)
        ax.set_xticks(range(3), [f'{d} c/o' for d in DENS])
        ax.set_ylim(-28, 0.5)
        ax.set_ylabel('STM threshold (dB)')
        ax.set_title(f"{'ABCD'[i]}  {'Right' if e == 'R' else 'Left'} ear | {rate} Hz | n={out[f'panel.{e}.{rate}Hz.n']} "
                     f"T={out[f'panel.{e}.{rate}Hz.T']} I={out[f'panel.{e}.{rate}Hz.I']}", loc='left')
    ax = fig.add_subplot(gs[2, 0])
    conds = [(d, rate) for d in DENS for rate in RATES]
    for k, (e, col) in enumerate((('R', C_R), ('L', C_L))):
        ax.bar([i + (k - 0.5) * 0.38 for i in range(6)], [out[f'cell.{e}.{d}co.{rate}Hz.mean'] for d, rate in conds], 0.38,
               color=col, label=f"{'Right' if e == 'R' else 'Left'} (six-condition mean {out[f'sixcond.{e}.mean']:.1f} dB)")
    ax.set_xticks(range(6), [f'{d} c/o\n{rate} Hz' for d, rate in conds])
    ax.set_ylabel('condition mean (dB)')
    ax.legend(loc='lower right')
    ax.set_title(f"E  Six-condition ear comparison | right lower in {nlow} of 6 conditions", loc='left')
    ax = fig.add_subplot(gs[2, 1])
    diffs = [out[f'cond.{d}co.{rate}Hz.R_minus_L'] for d, rate in conds]
    ax.barh(range(6), diffs, color=[C_R if x < 0 else C_L for x in diffs])
    for i, x in enumerate(diffs):
        ax.text(x, i, f' {x:+.1f}', va='center', fontsize=7)
    ax.set_yticks(range(6), [f'{d} c/o · {rate} Hz' for d, rate in conds])
    ax.axvline(0, color='k', lw=0.8)
    ax.set_xlabel('R − L (dB)')
    ax.set_title('F  Condition-specific ear differences', loc='left')
    fig.text(0.01, 0.005, 'Thresholds = mean of the last 10 of 14 reversals (recomputed from the trial CSV); dB = 20 log10(A). '
             'Open circles: interval_bias; +: near_ceiling (all retained). Means weight conditions equally.\n'
             'The Won et al. (2015) literature line of the PDF is not part of these data and is not redrawn.', fontsize=6.5)
    fig.tight_layout(rect=(0, 0.02, 1, 0.95))
    pg.add(fig, f"STM | n={out['all.n_runs']} runs · T={out['all.n_trials']} · I={out['all.n_intervals']} | 2026-10-18 to 19 (KST)")
    for e in ('R', 'L'):
        rs = [r for r in runs if r['ear'] == e]
        fig, axs = plt.subplots(4, 4, figsize=(12, 9), sharex=True, sharey=True)
        for ax, r in zip(axs.flat, rs):
            rows = tr[r['run_id']]
            used = reversal_trial_nos(rows)[-10:]
            k = f"run.{lab[r['run_id']]}"
            staircase(ax, rows, used, thr[r['run_id']], ylabel='depth (dB)',
                      title=f"{lab[r['run_id']]} | {out[k + '.condition']} {out[k + '.flags'] if out[k + '.flags'] != 'none' else ''}\n"
                            f"threshold {thr[r['run_id']]:.1f} dB | T={r['n_responses']}")
            ax.axvspan(reversal_trial_nos(rows)[4] - 0.5, r['n_trials'] + 0.5, color='#dddddd', alpha=0.4, zorder=0)
        for ax in list(axs.flat)[len(rs):]:
            ax.axis('off')
        fig.text(0.01, 0.005, 'Shading: 5th reversal to run end; dashed: mean of the final 10 reversals; orange diamonds = reversals used. '
                 'IB = interval_bias, NC = near_ceiling (stored app flags).', fontsize=6.5)
        fig.tight_layout(rect=(0, 0.02, 1, 0.95))
        pg.add(fig, f"STM | all {'right' if e == 'R' else 'left'}-ear staircases | {len(rs)} runs | {out[f'ear.{e}.n_trials']} trials")
    fig, axs = plt.subplots(1, 2, figsize=(12, 6), gridspec_kw={'width_ratios': [1, 1.3]})
    ax = axs[0]
    rows_ = [(e, d, rate) for d in DENS for rate in RATES for e in ('R', 'L')]
    for i, (e, d, rate) in enumerate(rows_):
        v = out[f'repeat.{e}.{d}co.{rate}Hz.run2_minus_run1']
        ax.barh(i, v, color=C_R if e == 'R' else C_L)
        ax.text(v, i, f' {v:+.1f}' + (' (3rd run)' if len(cell[(e, d, rate)]) >= 3 else ''), va='center', fontsize=6.5)
    ax.axvline(3, color=C_GRAY, ls=':')
    ax.axvline(-3, color=C_GRAY, ls=':')
    ax.set_yticks(range(len(rows_)), [f'{d} c/o · {rate} Hz {e}' for e, d, rate in rows_])
    ax.set_xlabel('run 2 − run 1 threshold (dB)')
    ax.set_title(f"A  {out['repeat.n_cells_absdiff_gt3']} of 12 cells with |difference| > 3 dB; "
                 f"{out['repeat.n_cells_absdiff_gt3_with_third_run']} have a third run", loc='left')
    ax = axs[1]
    ax.axis('off')
    lines = ['Condition        Ear n  Run1   Run2   Run3   Mean    SD   R2-R1']
    for e, d, rate in sorted(rows_, key=lambda x: (DENS.index(x[1]), x[2], x[0] == 'L')):
        k = f'repeat.{e}.{d}co.{rate}Hz'
        r3 = out[k + '.run3']
        lines.append(f"{d:>3} c/o {rate:>2} Hz   {e}  {out[f'cell.{e}.{d}co.{rate}Hz.n']}  {out[k + '.run1']:5.1f}  {out[k + '.run2']:5.1f}  "
                     f"{'  —  ' if r3 is None else f'{r3:5.1f}'}  {out[f'cell.{e}.{d}co.{rate}Hz.mean']:6.2f}  "
                     f"{out[f'cell.{e}.{d}co.{rate}Hz.sd']:4.2f}  {out[k + '.run2_minus_run1']:+5.1f}")
    ax.text(0, 1, '\n'.join(lines), family='monospace', fontsize=7.5, va='top')
    ax.set_title('B  Repeat thresholds and descriptive summaries (dB)', loc='left')
    fig.tight_layout(rect=(0, 0.02, 1, 0.95))
    pg.add(fig, 'STM | threshold changes between repeat runs')
    fig, axs = plt.subplots(2, 2, figsize=(12, 9), gridspec_kw={'width_ratios': [1, 1.4]})
    for row, e in enumerate(('R', 'L')):
        rs = [r for r in runs if r['ear'] == e]
        ax = axs[row, 0]
        ax.barh(range(len(rs)), [r['n_responses'] for r in rs], color=C_R if e == 'R' else C_L)
        ax.set_yticks(range(len(rs)), [f"{lab[r['run_id']]} · {out['run.' + lab[r['run_id']] + '.condition']}" for r in rs])
        ax.invert_yaxis()
        ax.set_xlabel('valid trials')
        ax.set_title(f"{'A' if e == 'R' else 'C'} | {'Right' if e == 'R' else 'Left'} ear · T={out[f'ear.{e}.n_trials']}", loc='left')
        ax = axs[row, 1]
        for i, r in enumerate(rs):
            a = out[f"run.{lab[r['run_id']]}.correct_by_target_interval"].split(' | ')
            p = [100 * int(x.split('/')[0]) / int(x.split('/')[1]) for x in a]
            ax.plot(p, [i, i], '-', color=C_GRAY)
            ax.plot(p[0], i, 'o', color='#555555')
            ax.plot(p[1], i, 's', color=C_R if e == 'R' else C_L)
            ax.text(101, i, ' | '.join(a), va='center', fontsize=6.5)
        ax.set_yticks(range(len(rs)), [lab[r['run_id']] for r in rs])
        ax.invert_yaxis()
        ax.set_xlim(0, 125)
        ax.set_xlabel('correct (%)  (circle: target in interval 1; square: target in interval 2)')
        ax.set_title(f"{'B' if e == 'R' else 'D'} | accuracy by target interval", loc='left')
    fig.text(0.01, 0.005, f"{out['all.n_trials']} valid trials, {out['all.n_correct']} correct; {out['all.technical_failures']} technical failures. "
             f"Ceiling-blocked moves: {win} in analysis windows, {init} in an initial segment.", fontsize=7)
    fig.tight_layout(rect=(0, 0.02, 1, 0.95))
    pg.add(fig, 'STM | trial counts and target-interval responses')
    checks['figure_pages'] = pg.close()
    return out, checks

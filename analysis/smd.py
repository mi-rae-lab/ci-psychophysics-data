# -*- coding: utf-8 -*-
"""SMD — reproduces SMD_scientific (EN/KO): 12 adaptive Won 2015 SMD runs of 2026-11-02 (right ear).

The QSMD constant-stimuli block of the same night is not part of that PDF; its score is reported in numbers.csv only.
"""
import re

import matplotlib.pyplot as plt

from common import (C_ACC, C_BAD, C_GRAY, C_OK, C_R, Pages, answered, by_run, load, mean, reversal_trial_nos,
                    reversal_values, sd, staircase)

DENS = ['0.5', '1', '2']
# The SMD PDF prints exact halves rounded up: the 2 c/o mean (25.70 + 16.95) / 2 = 21.325 is shown as 21.33,
# while Python's default formatting of the binary value gives 21.32. Comparisons for this test therefore round half up.
ROUNDING = 'half_up'


def dens_of(r):
    return re.match(r'density=([\d.]+) c/o', r['condition']).group(1)


def run(outdir):
    trials, runs = load('smd')
    tr = by_run(trials)
    runs.sort(key=lambda r: (r['date_kst'], r['start_time_kst']))
    ad = [r for r in runs if r['included'] == 1 and r['protocol'].startswith('Won2015 SMD')]
    q = [r for r in runs if r['protocol'].startswith('QSMD')]
    out, checks = {}, {}
    thr, lab, win = {}, {}, {}
    bad = 0
    for i, r in enumerate(ad, 1):
        lab[r['run_id']] = f'R{i:02d}'
        rows = tr[r['run_id']]
        rt = reversal_trial_nos(rows)
        win[r['run_id']] = [t for t in answered(rows) if t['run_trial_no'] > rt[3]]   # analysis window: after reversal 4
        if r['value_kind'] == 'threshold':
            rv = reversal_values(rows)[-10:]
            thr[r['run_id']] = sum(round(v * 2) for v in rv) / len(rv) / 2              # mean of reversals 5-14 (half-dB units, as the app)
            bad += abs(thr[r['run_id']] - r['threshold']) > 1e-9
    checks['threshold_recomputed_vs_app_mismatch'] = bad
    num = [r for r in ad if r['run_id'] in thr]
    none = [r for r in ad if r['run_id'] not in thr]
    out['all.n_runs'], out['all.n_trials'] = len(ad), sum(r['n_responses'] for r in ad)
    out['numeric.n_runs'], out['numeric.n_trials'] = len(num), sum(r['n_responses'] for r in num)
    out['none.n_runs'], out['none.n_trials'] = len(none), sum(r['n_responses'] for r in none)
    out['all.n_reversals'] = sum(r['n_reversals'] for r in ad)
    for a, b in ((1, 4), (5, 8), (9, 12)):
        out[f'page.R{a:02d}-R{b:02d}.n_trials'] = sum(r['n_responses'] for r in ad[a - 1:b])
    for d in DENS:
        rs = [r for r in ad if dens_of(r) == d]
        k = f'density.{d}co'
        out[f'{k}.n_runs'], out[f'{k}.n_trials'] = len(rs), sum(r['n_responses'] for r in rs)
        nn = [r for r in rs if r in num]
        out[f'{k}.numeric_runs'], out[f'{k}.numeric_trials'] = len(nn), sum(r['n_responses'] for r in nn)
        out[f'{k}.none_runs'] = len(rs) - len(nn)
        out[f'{k}.none_trials'] = out[f'{k}.n_trials'] - out[f'{k}.numeric_trials']
        out[f'{k}.mean'] = mean(thr[r['run_id']] for r in nn)
        out[f'{k}.sd'] = sd(thr[r['run_id']] for r in nn)
    for r in ad:
        k = f"run.{lab[r['run_id']]}"
        rows = answered(tr[r['run_id']])
        out[f'{k}.run_id'] = r['run_id']
        out[f'{k}.start_kst'] = r['start_time_kst']
        out[f'{k}.density'] = dens_of(r)
        out[f'{k}.n_trials'] = len(rows)
        out[f'{k}.n_correct'] = sum(t['correct'] for t in rows)
        out[f'{k}.threshold'] = thr.get(r['run_id'], 'NA')
        w = win[r['run_id']]
        out[f'{k}.window_correct'] = f"{sum(t['correct'] for t in w)}/{len(w)}"
        for pos in ('1', '2', '3'):
            p = [t for t in rows if t['target_interval'] == pos]
            out[f'{k}.target{pos}_correct'] = f"{sum(t['correct'] for t in p)}/{len(p)}"
    for r in q:   # not in the PDF
        out['qsmd.n_correct'], out['qsmd.n_trials'] = r['n_correct'], r['n_responses']
        out['qsmd.pct_correct'] = 100 * r['n_correct'] / r['n_responses']
    # ── figures ──
    pg = Pages(outdir, 'smd')
    fig, axs = plt.subplots(1, 2, figsize=(12, 5.5), gridspec_kw={'width_ratios': [1, 1.6]})
    ax = axs[0]
    for j, d in enumerate(DENS):
        ys = [thr[r['run_id']] for r in num if dens_of(r) == d]
        ax.plot([j] * len(ys), ys, 'o', color=C_R, alpha=0.5)
        ax.errorbar(j + 0.15, mean(ys), yerr=sd(ys), fmt='D', color='k', capsize=3)
        ax.text(j, 2, f"n={out[f'density.{d}co.numeric_runs']} / T={out[f'density.{d}co.numeric_trials']}", ha='center', fontsize=7)
    ax.set_xticks(range(3), DENS)
    ax.set_xlabel('spectral density (cycles/octave)')
    ax.set_ylabel('modulation-depth threshold (dB)')
    ax.set_ylim(0, 35)
    ax.set_title('A  Mean ± sample SD by density (numeric thresholds only)', loc='left')
    ax = axs[1]
    for i, r in enumerate(ad, 1):
        fl = r['app_flags'] or ''
        if r['run_id'] in thr:
            ax.plot(i, thr[r['run_id']], 'o', color=C_R, mfc='white' if ('bias' in fl) else C_R, ms=7)
        else:
            ax.text(i, 3, 'NA', ha='center', color=C_BAD, fontsize=8)
        ax.text(i, 0.6, str(r['n_responses']), ha='center', fontsize=7)
    ax.axvline(3.5, color=C_GRAY, ls=':')
    ax.set_xticks(range(1, len(ad) + 1), [f'{i:02d}\n{dens_of(r)}' for i, r in enumerate(ad, 1)])
    ax.set_ylim(0, 35)
    ax.set_xlabel('run (R01-R12, c/o) | lower row: trial count | dotted line: session 1 | session 2')
    ax.set_title('B  Individual thresholds in run order (open = interval/response-bias flag)', loc='left')
    fig.tight_layout(rect=(0, 0.02, 1, 0.93))
    pg.add(fig, f"Adaptive SMD | {out['all.n_runs']} runs · {out['all.n_trials']} trials | numeric {out['numeric.n_runs']} runs · "
                f"{out['numeric.n_trials']} trials | right ear | 2026-11-02 KST")
    for a in range(0, 12, 4):
        fig, axs = plt.subplots(2, 2, figsize=(12, 8), sharex=True, sharey=True)
        for ax, r in zip(axs.flat, ad[a:a + 4]):
            rows = tr[r['run_id']]
            rt = reversal_trial_nos(rows)
            ax.axvspan(rt[3] + 0.5, r['n_trials'] + 0.5, color='#dddddd', alpha=0.5, zorder=0)
            staircase(ax, rows, rt[-10:] if r['run_id'] in thr else [], thr.get(r['run_id']), ylabel='modulation depth (dB)',
                      title=f"{lab[r['run_id']]} | {dens_of(r)} c/o | {r['n_responses']} trials\n{r['start_time_kst']} KST · "
                            + (f"threshold {thr[r['run_id']]:.2f} dB" if r['run_id'] in thr else 'no numeric threshold'))
            ax.set_ylim(8, 37)
        fig.tight_layout(rect=(0, 0.02, 1, 0.94))
        pg.add(fig, f"Adaptive SMD | staircases {lab[ad[a]['run_id']]}-{lab[ad[a + 3]['run_id']]} | "
                    f"{sum(r['n_responses'] for r in ad[a:a + 4])} trials (shading: analysis window after reversal 4)")
    fig, axs = plt.subplots(2, 1, figsize=(12, 8))
    ax = axs[0]
    for i, r in enumerate(ad):
        w = win[r['run_id']]
        p = 100 * sum(t['correct'] for t in w) / len(w)
        ax.bar(i, p, color=C_R if r['run_id'] in thr else C_BAD)
        ax.text(i, p + 2, out[f"run.{lab[r['run_id']]}.window_correct"], ha='center', fontsize=7)
    ax.axhline(70.7, color=C_ACC, ls='--')
    ax.axhline(100 / 3, color=C_GRAY, ls=':')
    ax.set_xticks(range(len(ad)), [lab[r['run_id']] for r in ad])
    ax.set_ylim(0, 110)
    ax.set_ylabel('accuracy (%)')
    ax.set_title('A  Accuracy in the analysis window (red: no numeric threshold)', loc='left')
    ax = axs[1]
    import numpy as np
    M = np.array([[int(out[f"run.{lab[r['run_id']]}.target{p}_correct"].split('/')[0]) /
                   int(out[f"run.{lab[r['run_id']]}.target{p}_correct"].split('/')[1]) for r in ad] for p in '123'])
    ax.imshow(M, cmap='Blues', vmin=0, vmax=1, aspect='auto')
    for pi, p in enumerate('123'):
        for i, r in enumerate(ad):
            ax.text(i, pi, out[f"run.{lab[r['run_id']]}.target{p}_correct"], ha='center', va='center', fontsize=7,
                    color='white' if M[pi, i] > 0.6 else 'black')
    ax.set_xticks(range(len(ad)), [lab[r['run_id']] for r in ad])
    ax.set_yticks(range(3), ['1', '2', '3'])
    ax.set_ylabel('target interval')
    ax.set_title('B  Correct / trials by target interval', loc='left')
    fig.tight_layout(rect=(0, 0.02, 1, 0.94))
    pg.add(fig, 'Adaptive SMD | response and non-numeric-run diagnostics')
    fig, ax = plt.subplots(figsize=(12, 5))
    ax.axis('off')
    lines = [f"{'Run':5s}{'Start (KST)':13s}{'c/o':6s}{'Trials':8s}{'Correct':9s}{'Threshold (dB)':16s}{'Status':26s}Source run ID"]
    for r in ad:
        k = f"run.{lab[r['run_id']]}"
        t = out[k + '.threshold']
        lines.append(f"{lab[r['run_id']]:5s}{r['start_time_kst']:13s}{dens_of(r):6s}{r['n_responses']:<8d}{out[k + '.n_correct']:<9d}"
                     f"{(f'{t:.2f}' if t != 'NA' else 'NA'):16s}{r['app_status']:26s}{r['run_id']}")
    ax.text(0, 1, '\n'.join(lines), family='monospace', fontsize=8, va='top')
    pg.add(fig, f"Adaptive SMD | run ledger | {out['all.n_reversals']} reversals over {out['all.n_trials']} trials")
    checks['figure_pages'] = pg.close()
    return out, checks

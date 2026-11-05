# -*- coding: utf-8 -*-
"""STRIPES — reproduces STRIPES_scientific_figures (EN/KO): completed main runs of 2026-10-16."""
import matplotlib.pyplot as plt

from common import (C_ACC, C_BAD, C_GRAY, C_L, C_OK, C_R, Pages, answered, by_run, load, mean,
                    reversal_trial_nos, reversal_values, sd, staircase)


def run(outdir):
    trials, runs = load('stripes')
    tr = by_run(trials)
    main = [r for r in runs if r['included'] == 1]          # completed main runs (practice, pass checks, stopped runs excluded)
    main.sort(key=lambda r: (r['date_kst'], r['start_time_kst']))
    out, checks = {}, {}
    lab = {}
    for e in ('R', 'L'):
        for i, r in enumerate([r for r in main if r['ear'] == e], 1):
            lab[r['run_id']] = f'{e}{i}'
    thr = {}
    bad = 0
    for r in main:
        rv = reversal_values(tr[r['run_id']])
        thr[r['run_id']] = mean(rv[-4:])                     # mean of the final 4 of 8 reversal densities (D)
        bad += abs(thr[r['run_id']] - r['threshold']) > 1e-9
    checks['threshold_recomputed_vs_app_mismatch'] = bad
    lower = min(t['value'] for t in trials if t['at_limit'] == 'easy')
    out['all.lower_bound_D'] = lower
    out['all.lower_bound_RPO'] = lower / 5
    out['all.n_runs'] = len(main)
    out['all.n_trials'] = sum(r['n_responses'] for r in main)
    out['all.date'] = ', '.join(sorted({r['date_kst'] for r in main}))
    for e in ('R', 'L'):
        rs = [r for r in main if r['ear'] == e]
        out[f'{e}.n_runs'] = len(rs)
        out[f'{e}.n_trials'] = sum(r['n_responses'] for r in rs)
        if len(rs) > 1:
            out[f'{e}.mean_D'] = mean(thr[r['run_id']] for r in rs)
            out[f'{e}.sd_D'] = sd(thr[r['run_id']] for r in rs)
            out[f'{e}.mean_RPO'] = out[f'{e}.mean_D'] / 5
            out[f'{e}.sd_RPO'] = out[f'{e}.sd_D'] / 5
        else:
            out[f'{e}.threshold_D'] = thr[rs[0]['run_id']]
            out[f'{e}.threshold_RPO'] = thr[rs[0]['run_id']] / 5
    dens = {}
    for r in main:
        L, rows = lab[r['run_id']], answered(tr[r['run_id']])
        k = f'run.{L}'
        out[f'{k}.n_trials'] = len(rows)
        out[f'{k}.threshold_D'] = thr[r['run_id']]
        out[f'{k}.threshold_RPO'] = thr[r['run_id']] / 5
        out[f'{k}.n_reversals'] = r['n_reversals']
        out[f'{k}.n_reversals_retained'] = r['n_reversals_used']
        nlb = sum(1 for t in rows if abs(t['value'] - lower) < 1e-9)
        out[f'{k}.lower_bound_trials'] = nlb
        out[f'{k}.lower_bound_pct'] = 100 * nlb / len(rows)
        out[f'{k}.n_correct'] = sum(t['correct'] for t in rows)
        d = {}
        for t in rows:
            d.setdefault(t['value'], []).append(t['correct'])
        dens[r['run_id']] = d
        out[f'{k}.correct_by_density'] = ' '.join(f'{sum(v)}/{len(v)}' for _, v in sorted(d.items()))
        out[f'{k}.trials_by_density'] = ' '.join(str(len(v)) for _, v in sorted(d.items()))
    # ── figures ──
    pg = Pages(outdir, 'stripes')
    col = lambda r: C_R if r['ear'] == 'R' else C_L  # noqa: E731
    fig, axs = plt.subplots(2, 2, figsize=(11, 8))
    ax = axs[0, 0]
    for j, e in enumerate(('R', 'L')):
        rs = [r for r in main if r['ear'] == e]
        ys = [thr[r['run_id']] for r in rs]
        ax.plot([j + (i - (len(ys) - 1) / 2) * 0.08 for i in range(len(ys))], ys, 'o', color=C_R if e == 'R' else C_L,
                mfc='white' if e == 'L' else None, ms=6)
        if len(ys) > 1:
            ax.errorbar(j + 0.25, mean(ys), yerr=sd(ys), fmt='D', color='k', capsize=3)
            ax.text(j, 4.6, f'{mean(ys):.3f} ± {sd(ys):.3f} D\n{mean(ys) / 5:.3f} ± {sd(ys) / 5:.3f} RPO', ha='center', fontsize=7)
        else:
            ax.text(j, 4.6, f'{ys[0]:.3f} D*\n{ys[0] / 5:.3f} RPO', ha='center', fontsize=7)
    ax.set_xticks([0, 1], [f"Right ear\n{out['R.n_runs']} runs | {out['R.n_trials']} trials",
                           f"Left ear*\n{out['L.n_runs']} run | {out['L.n_trials']} trials"])
    ax.set_xlim(-0.6, 1.6)
    ax.set_ylim(0, 5.4)
    ax.set_ylabel('threshold (D)')
    sec = ax.secondary_yaxis('right', functions=(lambda d: d / 5, lambda p: p * 5))
    sec.set_ylabel('threshold (RPO)')
    ax.set_title(f"A  STRIPES threshold by ear | {out['all.n_runs']} completed runs | {out['all.n_trials']} trials", loc='left')
    for ax, r in zip([axs[0, 1], axs[1, 0], axs[1, 1]], main):
        rows = tr[r['run_id']]
        used = reversal_trial_nos(rows)[-4:]
        staircase(ax, rows, used, thr[r['run_id']], ylabel='presented density (D)', floor=lower,
                  title=f"{lab[r['run_id']][0] == 'R' and 'Right' or 'Left'} ear | run {lab[r['run_id']][1]}  n = {len(answered(rows))} trials | "
                        f"threshold = {thr[r['run_id']]:.3f} D ({thr[r['run_id']] / 5:.3f} RPO)")
        ax.secondary_yaxis('right', functions=(lambda d: d / 5, lambda p: p * 5)).set_ylabel('RPO')
        ax.set_ylim(0.8, 4.6)
    fig.text(0.01, 0.005, 'Threshold = mean of the final four reversal densities (recomputed from the trial CSV). RPO = D/5. '
             'Filled = correct, open = incorrect, diamonds = reversals (orange = the 4 used). * Left run: boundary-affected '
             '(app status analysis_window_boundary_affected), above-chance performance not established. Dotted: lower bound D = 1.1.',
             fontsize=6.5)
    fig.tight_layout(rect=(0, 0.02, 1, 0.95))
    pg.add(fig, f"STRIPES | completed main runs | {out['all.date']} (KST)")
    fig, axs = plt.subplots(2, 2, figsize=(11, 8))
    for ax, r in zip([axs[0, 0], axs[0, 1], axs[1, 0]], main):
        rv = reversal_values(tr[r['run_id']])
        n = len(rv)
        ax.axvspan(n - 3.5, n + 0.5, color=C_ACC, alpha=0.15)
        ax.plot(range(1, n + 1), rv, 'o-', color=col(r))
        ax.axhline(thr[r['run_id']], color=C_ACC, ls='--')
        ax.set_xlabel('reversal number')
        ax.set_ylabel('reversal density (D)')
        ax.set_title(f"{'Right' if r['ear'] == 'R' else 'Left'} ear | run {lab[r['run_id']][1]} | n = {r['n_responses']} trials | "
                     f"{n} reversals; final 4 retained\nthreshold {thr[r['run_id']]:.3f} D / {thr[r['run_id']] / 5:.3f} RPO", loc='left')
    ax = axs[1, 1]
    for i, r in enumerate(main):
        k = f"run.{lab[r['run_id']]}"
        ax.bar(i, out[f'{k}.lower_bound_pct'], color=col(r))
        ax.text(i, out[f'{k}.lower_bound_pct'] + 2, f"{out[k + '.lower_bound_trials']}/{out[k + '.n_trials']}\n"
                f"({out[k + '.lower_bound_pct']:.1f}%)", ha='center', fontsize=7)
    ax.set_xticks(range(len(main)), [f"{lab[r['run_id']]}\nn = {r['n_responses']}" for r in main])
    ax.set_ylim(0, 105)
    ax.set_ylabel('trials at lower bound (%)')
    ax.set_title(f'D  Lower-bound sampling: trials presented at D = {lower} ({lower / 5:.2f} RPO)', loc='left')
    fig.tight_layout(rect=(0, 0.02, 1, 0.95))
    pg.add(fig, 'STRIPES | reversals and lower-bound sampling')
    fig, axs = plt.subplots(2, 3, figsize=(12, 7.5))
    for j, r in enumerate(main):
        d = dens[r['run_id']]
        xs = sorted(d)
        ax = axs[0, j]
        ax.plot(xs, [100 * mean(d[x]) for x in xs], 'o-', color=col(r))
        for x in xs:
            ax.annotate(f'{sum(d[x])}/{len(d[x])}', (x, 100 * mean(d[x])), xytext=(0, 5), textcoords='offset points', ha='center', fontsize=6)
        ax.axhline(50, color=C_GRAY, ls=':')
        ax.set_ylim(-5, 112)
        ax.set_xlabel('presented density (D)')
        ax.set_ylabel('observed correct (%)')
        ax.set_title(f"{'Right' if r['ear'] == 'R' else 'Left'} ear | run {lab[r['run_id']][1]} | correct {out['run.' + lab[r['run_id']] + '.n_correct']}/"
                     f"{r['n_responses']}", loc='left')
        ax = axs[1, j]
        ax.bar(xs, [len(d[x]) for x in xs], width=0.08, color=col(r))
        for x in xs:
            ax.text(x, len(d[x]) + 0.4, str(len(d[x])), ha='center', fontsize=6)
        ax.set_xlabel('presented density (D)')
        ax.set_ylabel('number of trials')
        ax.set_title(f"n = {r['n_responses']} trials; lower bound {out['run.' + lab[r['run_id']] + '.lower_bound_trials']}/{r['n_responses']}", loc='left')
    fig.text(0.01, 0.005, 'Labels: correct/total at each exact density. Chance 50 % (2 alternatives). Descriptive rates only; no psychometric fit.',
             fontsize=6.5)
    fig.tight_layout(rect=(0, 0.02, 1, 0.95))
    pg.add(fig, 'STRIPES | observed responses and sampled densities')
    checks['figure_pages'] = pg.close()
    return out, checks

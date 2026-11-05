# -*- coding: utf-8 -*-
"""SMRT — reproduces Figure1_SMRT_detailed (EN/KO): run thresholds by condition, ear and date."""
import matplotlib.pyplot as plt

from common import C_GRAY, C_L, C_R, Pages, by_run, js_round, load, mean, reversal_values, sd

PANELS = [('A_std_R', 'no level rove', 'R', 'A  Standard | Right ear'),
          ('B_std_L', 'no level rove', 'L', 'B  Standard | Left ear'),
          ('C_roveB_R', 'rove B', 'R', 'C  Roving B (+/-4 dB) | Right ear'),
          ('D_roveC_R', 'rove C', 'R', 'D  Roving C (+/-7.5 dB) | Right ear')]


def run(outdir):
    trials, runs = load('smrt')
    tr = by_run(trials)
    test_runs = [r for r in runs if r['included'] == 1 and r['run_kind'] == 'main']   # practice runs excluded
    test_runs.sort(key=lambda r: (r['date_kst'], r['start_time_kst']))
    out, checks = {}, {}
    thr = {}
    bad = 0
    for r in test_runs:
        rv = reversal_values(tr[r['run_id']])
        # mean of the last 6 of 10 reversals, rounded to 0.0001 RPO as the app stores it (the PDF averaged stored values)
        thr[r['run_id']] = js_round(mean(rv[-r['n_reversals_used']:]), 4)
        if thr[r['run_id']] != r['threshold']:
            bad += 1
    checks['threshold_recomputed_vs_app_mismatch'] = bad
    out['all.n_runs'] = len(test_runs)
    out['all.n_trials'] = sum(r['n_responses'] for r in test_runs)
    out['all.n_intervals'] = 3 * out['all.n_trials']
    out['all.n_unsure'] = sum(r['n_unsure'] for r in test_runs)
    flagged = [r for r in test_runs if 'unverified_vs_chance' in (r['app_flags'] or '')]
    out['all.n_flagged_unverified'] = len(flagged)
    groups = {}
    for key, cond, ear, _ in PANELS:
        rs = [r for r in test_runs if r['condition'].startswith(cond) and r['ear'] == ear]
        groups[key] = rs
        out[f'{key}.n'] = len(rs)
        out[f'{key}.T'] = sum(r['n_responses'] for r in rs)
        out[f'{key}.I'] = 3 * out[f'{key}.T']
        out[f'{key}.mean'] = mean(thr[r['run_id']] for r in rs)
        out[f'{key}.sd'] = sd(thr[r['run_id']] for r in rs)
        for d in sorted({r['date_kst'] for r in rs}):
            ds = [r for r in rs if r['date_kst'] == d]
            out[f'{key}.{d}.mean'] = mean(thr[r['run_id']] for r in ds)
            out[f'{key}.{d}.sd'] = sd(thr[r['run_id']] for r in ds)
            out[f'{key}.{d}.n'] = len(ds)
            out[f'{key}.{d}.T'] = sum(r['n_responses'] for r in ds)
            out[f'{key}.{d}.I'] = 3 * out[f'{key}.{d}.T']
            out[f'{key}.{d}.T_per_run'] = ', '.join(str(r['n_responses']) for r in ds)
    out['ref.std_R_mean'] = out['A_std_R.mean']
    checks['flagged_unverified_runs'] = '; '.join(f"{r['run_id']} ({r['condition'][:6]} {r['ear']} {r['date_kst']})" for r in flagged)
    # ── figure (one page, four panels) ──
    pg = Pages(outdir, 'smrt')
    fig, axs = plt.subplots(2, 2, figsize=(11, 8), sharey=True)
    for ax, (key, cond, ear, title) in zip(axs.flat, PANELS):
        rs = groups[key]
        dates = sorted({r['date_kst'] for r in rs})
        col = C_R if ear == 'R' else C_L
        for i, d in enumerate(dates):
            ds = [r for r in rs if r['date_kst'] == d]
            ys = [thr[r['run_id']] for r in ds]
            xs = [i + (j - (len(ys) - 1) / 2) * 0.08 for j in range(len(ys))]
            for x, y, r in zip(xs, ys, ds):
                fl = 'unverified_vs_chance' in (r['app_flags'] or '')
                ax.plot(x, y, 'o', ms=5, mfc='white' if fl else col, mec=col)
                if fl:
                    ax.annotate('†', (x, y), xytext=(4, 4), textcoords='offset points')
            m, s = mean(ys), sd(ys)
            ax.errorbar(i + 0.3, m, yerr=s, fmt='D', color='k', ms=5, capsize=3)
            ax.text(i, 5.15, f"M±SD {m:.3f}±{s:.3f}\nn={len(ys)} T={sum(r['n_responses'] for r in ds)} "
                    f"I={3 * sum(r['n_responses'] for r in ds)}\nT/run: " + ', '.join(str(r['n_responses']) for r in ds),
                    ha='center', va='top', fontsize=6.5)
        if key.startswith(('C', 'D')):
            ax.axhline(out['ref.std_R_mean'], color=C_GRAY, ls='--', lw=0.8)
            ax.text(len(dates) - 0.5, out['ref.std_R_mean'] + 0.08, f"standard right mean {out['ref.std_R_mean']:.3f} RPO",
                    ha='right', fontsize=6.5, color=C_GRAY)
        ax.set_xticks(range(len(dates)), [d[5:].replace('-', '/') for d in dates])
        ax.set_xlim(-0.6, len(dates) - 0.4)
        ax.set_ylim(0, 5.6)
        ax.set_ylabel('SMRT threshold (RPO)')
        ax.set_title(f"{title}\nn={out[key + '.n']} T={out[key + '.T']} I={out[key + '.I']} | mean±SD "
                     f"{out[key + '.mean']:.3f}±{out[key + '.sd']:.3f} RPO", loc='left')
    fig.text(0.01, 0.005, 'Dots: run thresholds (mean of the last 6 of 10 reversals, recomputed from the trial CSV). '
             'Diamonds: daily mean ± sample SD. † app flag unverified_vs_chance. Practice runs excluded; '
             f"'unsure' trials ({out['all.n_unsure']}) are counted in T. I = 3 T.", fontsize=6.5)
    fig.tight_layout(rect=(0, 0.02, 1, 0.95))
    pg.add(fig, f"SMRT | {out['all.n_runs']} test runs | {out['all.n_trials']} trials | {out['all.n_intervals']} intervals")
    checks['figure_pages'] = pg.close()
    return out, checks

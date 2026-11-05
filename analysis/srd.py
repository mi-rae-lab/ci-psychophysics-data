# -*- coding: utf-8 -*-
"""SRD — reproduces SRD_scientific (EN/KO): Won 2007 adaptive runs (numeric, status-only) and the stopped clinical run."""
import matplotlib.pyplot as plt

from common import (C_ACC, C_BAD, C_GRAY, C_L, C_R, Pages, answered, by_run, load, mean, reversal_trial_nos,
                    reversal_values, sd, staircase)

YT = [0.125, 0.25, 0.5, 1, 2]


def run(outdir):
    trials, runs = load('srd')
    tr = by_run(trials)
    runs.sort(key=lambda r: (r['date_kst'], r['start_time_kst']))
    out, checks = {}, {}
    completed = [r for r in runs if r['included'] == 1]                     # 13 reversals reached
    numeric = [r for r in completed if r['value_kind'] == 'threshold']
    status = [r for r in completed if r['value_kind'] == 'none']
    aborted = [r for r in runs if r['app_status'] == 'participant_aborted']
    thr = {}
    bad = 0
    for r in completed:
        rv = reversal_values(tr[r['run_id']])
        # arithmetic mean of reversals 6-13, summed in milli-RPO integers as the app does (sumMilli / 8 / 1000)
        thr[r['run_id']] = sum(round(v * 1000) for v in rv[-8:]) / len(rv[-8:]) / 1000
        if r in numeric:
            bad += abs(thr[r['run_id']] - r['threshold']) > 1e-9
    checks['threshold_recomputed_vs_app_mismatch'] = bad
    for name, rs in (('source', runs), ('completed', completed), ('numeric', numeric), ('status_only', status), ('aborted', aborted)):
        out[f'{name}.n_runs'] = len(rs)
        out[f'{name}.n_trials'] = sum(r['n_responses'] for r in rs)
    out['numeric.n_retained_reversals'] = sum(len(reversal_values(tr[r['run_id']])[-8:]) for r in numeric)
    for e in ('R', 'L'):
        rs = [r for r in numeric if r['ear'] == e]
        ys = [thr[r['run_id']] for r in rs]
        out[f'{e}.n'], out[f'{e}.T'], out[f'{e}.mean'], out[f'{e}.sd'] = len(rs), sum(r['n_responses'] for r in rs), mean(ys), sd(ys)
        for d in sorted({r['date_kst'] for r in rs}):
            ds = [r for r in rs if r['date_kst'] == d]
            k = f'{e}.{d}'
            out[f'{k}.mean'] = mean(thr[r['run_id']] for r in ds)
            out[f'{k}.sd'] = sd(thr[r['run_id']] for r in ds)
            out[f'{k}.n'] = len(ds)
            out[f'{k}.T'] = sum(r['n_responses'] for r in ds)
            out[f'{k}.T_per_run'] = ', '.join(str(r['n_responses']) for r in ds)
    c22 = [r for r in completed if r['ear'] == 'R' and r['date_kst'] == '2026-10-22']
    out['completed.R.2026-10-22.n'] = len(c22)
    out['completed.R.2026-10-22.T'] = sum(r['n_responses'] for r in c22)
    sess = {}
    for r in numeric:
        sess.setdefault(r['session_id'], []).append(r)
    qual = {s: rs for s, rs in sess.items() if len(rs) >= 6}                # session mean needs 6 numeric thresholds
    out['session_mean_6run.n_qualifying'] = len(qual)
    for s, rs in qual.items():
        v = mean(thr[r['run_id']] for r in rs)
        out['session_mean_6run.value'] = v
        out[f"session_mean_6run.{rs[0]['ear']}.{rs[0]['date_kst']}"] = v
    ex = [r for r in numeric if r['ear'] == 'R' and r['date_kst'] == '2026-11-02'][0]
    out['example.threshold'], out['example.T'] = thr[ex['run_id']], ex['n_responses']
    for r in numeric:
        rows = answered(tr[r['run_id']])
        k = f"run.{r['ear']}.{r['date_kst']}.{r['start_time_kst']}"
        out[f'{k}.T'] = len(rows)
        out[f'{k}.threshold'] = thr[r['run_id']]
        out[f'{k}.reversals_6_13'] = ' · '.join(f'{v:.3f}' for v in reversal_values(rows)[-8:])
        c = sum(t['correct'] for t in rows)
        out[f'{k}.correct'] = f'{c}/{len(rows)}'
        out[f'{k}.pct_correct'] = 100 * c / len(rows)
    for r in status:
        rows = tr[r['run_id']]
        k = f"status_run.{r['ear']}.{r['date_kst']}.{r['start_time_kst']}"
        out[f'{k}.T'] = r['n_responses']
        out[f'{k}.correct'] = f"{r['n_correct']}/{r['n_responses']}"
        w0 = reversal_trial_nos(rows)[5]                                     # analysis window starts at reversal 6
        blk = [t['run_trial_no'] for t in rows if t['blocked_at_limit'] == 'easy' and t['run_trial_no'] >= w0]
        out[f'{k}.first_easy_block_in_window_trial'] = blk[0] if blk else None
        out[f'{k}.status'] = r['app_status']
    groups = [('R', '2026-10-21'), ('R', '2026-10-22'), ('L', '2026-10-22'), ('R', '2026-11-02')]
    bydens = {}
    for e, d in groups:
        acc = {}
        for r in numeric:
            if r['ear'] == e and r['date_kst'] == d:
                for t in answered(tr[r['run_id']]):
                    acc.setdefault(t['value'], []).append(t['correct'])
        bydens[(e, d)] = acc
        out[f'by_density.{e}.{d}'] = ' '.join(f'{sum(v)}/{len(v)}' for _, v in sorted(acc.items()))
    # ── figures ──
    pg = Pages(outdir, 'srd')
    fig, axs = plt.subplots(1, 3, figsize=(13, 5), gridspec_kw={'width_ratios': [1.4, 1, 0.6]})
    rows = tr[ex['run_id']]
    staircase(axs[0], rows, reversal_trial_nos(rows)[-8:], thr[ex['run_id']], log=True, ylabel='presented density (RPO, log2)',
              title=f"B  Recorded example | 2026-11-02 right run 1 | T={ex['n_responses']} | threshold {thr[ex['run_id']]:.4f} RPO")
    axs[0].set_yticks(YT, [str(v) for v in YT])
    for ax, e in zip(axs[1:], ('R', 'L')):
        rs = [r for r in numeric if r['ear'] == e]
        dates = sorted({r['date_kst'] for r in rs})
        col = C_R if e == 'R' else C_L
        for i, d in enumerate(dates):
            ys = [thr[r['run_id']] for r in rs if r['date_kst'] == d]
            ax.plot([i + (j - (len(ys) - 1) / 2) * 0.07 for j in range(len(ys))], ys, 'o', color=col)
            if len(ys) > 1:
                ax.errorbar(i + 0.25, mean(ys), yerr=sd(ys), fmt='D', color='k', capsize=3, ms=4)
            ax.text(i, 1.02, f"M±SD {out[f'{e}.{d}.mean']:.3f}±{out[f'{e}.{d}.sd']:.3f}\nn={out[f'{e}.{d}.n']} T={out[f'{e}.{d}.T']}",
                    ha='center', fontsize=6.5)
        ax.axhline(out[f'{e}.mean'], color=C_GRAY, ls='--', lw=0.8)
        ax.set_xticks(range(len(dates)), dates)
        ax.set_xlim(-0.6, len(dates) - 0.4)
        ax.set_ylim(0, 1.15)
        ax.set_ylabel('SRD threshold (RPO)')
        ax.set_title(f"{'C' if e == 'R' else 'D'}  {'Right' if e == 'R' else 'Left'} ear | n={out[e + '.n']} · T={out[e + '.T']}\n"
                     f"M±SD {out[e + '.mean']:.3f}±{out[e + '.sd']:.3f} RPO", loc='left')
    fig.tight_layout(rect=(0, 0.02, 1, 0.93))
    pg.add(fig, f"SRD | n={out['numeric.n_runs']} · T={out['numeric.n_trials']} (numeric runs) | dates KST")
    fig, ax = plt.subplots(figsize=(12, 5))
    x = 0
    ticks = []
    for e, d in groups:
        for r in [r for r in completed if r['ear'] == e and r['date_kst'] == d]:
            col = C_R if e == 'R' else C_L
            if r in numeric:
                lb = any(t['at_limit'] == 'easy' for t in tr[r['run_id']] if t['run_trial_no'] >= reversal_trial_nos(tr[r['run_id']])[5])
                ax.plot(x, thr[r['run_id']], 'o', color=col, mfc='white' if lb else col, ms=6)
                ax.text(x, thr[r['run_id']] * 1.08, f"{thr[r['run_id']]:.4f}", ha='center', fontsize=6, rotation=90)
            else:
                ax.plot(x, 0.11, 'v', color=col, ms=7)
            ticks.append((x, f"{e} {d[5:]}\nT={r['n_responses']}"))
            x += 1
        x += 0.6
    for s, rs in qual.items():
        ax.axhline(out['session_mean_6run.value'], color=C_L, ls=':', lw=0.8)
        ax.text(x - 0.5, out['session_mean_6run.value'], f"6-run mean {out['session_mean_6run.value']:.3f}", fontsize=7, ha='right', va='bottom')
    ax.set_yscale('log')
    ax.set_yticks(YT, [str(v) for v in YT])
    ax.set_ylim(0.1, 2.5)
    ax.set_xticks([t[0] for t in ticks], [t[1] for t in ticks], fontsize=6)
    ax.set_ylabel('SRD threshold (RPO, log2)')
    ax.set_title(f"Completed {out['completed.n_runs']} runs / {out['completed.n_trials']} trials | numeric {out['numeric.n_runs']} / "
                 f"{out['numeric.n_trials']} | status only {out['status_only.n_runs']} / {out['status_only.n_trials']} (triangles, no RPO value) | "
                 f"stopped clinical run {out['aborted.n_runs']} / {out['aborted.n_trials']} omitted. Open circles: easy-end contact in the window.",
                 loc='left', fontsize=7)
    fig.tight_layout(rect=(0, 0.02, 1, 0.93))
    pg.add(fig, 'SRD | thresholds and measurement status across sessions')
    fig, axs = plt.subplots(1, 2, figsize=(12, 6))
    for ax, e in zip(axs, ('R', 'L')):
        rs = [r for r in numeric if r['ear'] == e]
        for i, r in enumerate(rs):
            rv = reversal_values(tr[r['run_id']])[-8:]
            ax.plot([min(rv), max(rv)], [i, i], '-', color='#cccccc', lw=4)
            ax.plot(rv, [i + 0.06 * (rv[:j].count(v)) for j, v in enumerate(rv)], 'o', color=C_R if e == 'R' else C_L, ms=4)
            ax.plot(thr[r['run_id']], i, 'D', color='k', ms=5)
            ax.text(2.3, i, f"{thr[r['run_id']]:.4f}", va='center', fontsize=7)
        ax.set_yticks(range(len(rs)), [f"{r['date_kst']} {r['start_time_kst'][:5]} T={r['n_responses']}" for r in rs], fontsize=7)
        ax.invert_yaxis()
        ax.set_xscale('log')
        ax.set_xticks(YT, [str(v) for v in YT])
        ax.set_xlabel('ripple density (RPO, log2)')
        ax.set_title(f"{'A' if e == 'R' else 'B'}  {'Right' if e == 'R' else 'Left'} ear | n={out[e + '.n']} · T={out[e + '.T']}", loc='left')
    fig.tight_layout(rect=(0, 0.02, 1, 0.93))
    pg.add(fig, f"SRD | the final 8 reversals per run ({out['numeric.n_retained_reversals']} values); diamond = threshold")
    fig, axs = plt.subplots(1, 2, figsize=(12, 6))
    for ax, e in zip(axs, ('R', 'L')):
        rs = [r for r in numeric if r['ear'] == e]
        ks = [f"run.{e}.{r['date_kst']}.{r['start_time_kst']}" for r in rs]
        ax.barh(range(len(rs)), [out[k + '.pct_correct'] for k in ks], color=C_R if e == 'R' else C_L)
        for i, k in enumerate(ks):
            ax.text(101, i, f"{out[k + '.correct']}  {out[k + '.pct_correct']:.1f}%", va='center', fontsize=7)
        ax.axvline(100 / 3, color=C_GRAY, ls=':')
        ax.axvline(70.7, color=C_ACC, ls='--')
        ax.set_yticks(range(len(rs)), [f"{r['date_kst']} {r['start_time_kst'][:5]}" for r in rs], fontsize=7)
        ax.invert_yaxis()
        ax.set_xlim(0, 130)
        ax.set_xlabel('observed correct responses (%)')
        ax.set_title(f"{'A' if e == 'R' else 'B'}  {'Right' if e == 'R' else 'Left'} ear", loc='left')
    fig.tight_layout(rect=(0, 0.02, 1, 0.93))
    pg.add(fig, 'SRD | observed correct responses by run (chance 33.3 %, staircase target 70.7 %)')
    fig, axs = plt.subplots(2, 2, figsize=(12, 8))
    for ax, (e, d) in zip(axs.flat, groups):
        acc = bydens[(e, d)]
        xs = sorted(acc)
        ax.plot(xs, [100 * mean(acc[v]) for v in xs], 'o-', color=C_R if e == 'R' else C_L)
        for v in xs:
            ax.annotate(f'{sum(acc[v])}/{len(acc[v])}', (v, 100 * mean(acc[v])), xytext=(0, 5), textcoords='offset points', ha='center', fontsize=6.5)
        ax.axhline(100 / 3, color=C_GRAY, ls=':')
        ax.axhline(70.7, color=C_ACC, ls='--')
        ax.set_xscale('log')
        ax.set_xticks([0.125, 0.176, 0.25, 0.354, 0.5, 0.707, 1, 1.414, 2], ['0.125', '0.176', '0.25', '0.354', '0.5', '0.707', '1', '1.414', '2'], fontsize=6)
        ax.set_ylim(-5, 112)
        ax.set_xlabel('presented ripple density (RPO, log2)')
        ax.set_ylabel('observed correct (%)')
        ax.set_title(f"{d} | {'Right' if e == 'R' else 'Left'} | n={out[f'{e}.{d}.n']}, T={out[f'{e}.{d}.T']}", loc='left')
    fig.tight_layout(rect=(0, 0.02, 1, 0.93))
    pg.add(fig, 'SRD | observed accuracy by presented ripple density (no curve fitted)')
    allr = numeric + status
    allr.sort(key=lambda r: (r['ear'] == 'L', r['date_kst'], r['start_time_kst']))
    for p in range(0, len(allr), 9):
        fig, axs = plt.subplots(3, 3, figsize=(12, 9), sharex=True, sharey=True)
        for ax, r in zip(axs.flat, allr[p:p + 9]):
            rows = tr[r['run_id']]
            if r in numeric:
                staircase(ax, rows, reversal_trial_nos(rows)[-8:], thr[r['run_id']], log=True, ylabel='density (RPO)',
                          title=f"{r['ear']} {r['date_kst']} {r['start_time_kst']} | T={r['n_responses']} | threshold {thr[r['run_id']]:.4f}")
            else:
                k = f"status_run.{r['ear']}.{r['date_kst']}.{r['start_time_kst']}"
                staircase(ax, rows, reversal_trial_nos(rows)[-8:], None, log=True, ylabel='density (RPO)',
                          title=f"{r['ear']} {r['date_kst']} {r['start_time_kst']} | T={r['n_responses']} | {r['app_status']}\n"
                                f"no numeric threshold; easy-end block in window at trial {out[k + '.first_easy_block_in_window_trial']}")
                ax.axvline(out[k + '.first_easy_block_in_window_trial'], color=C_BAD, ls=':')
            ax.set_yticks(YT, [str(v) for v in YT])
        for ax in list(axs.flat)[len(allr[p:p + 9]):]:
            ax.axis('off')
        fig.tight_layout(rect=(0, 0.02, 1, 0.94))
        pg.add(fig, 'SRD | adaptive tracks (orange diamonds = reversals 6-13; dashed = threshold)')
    checks['figure_pages'] = pg.close()
    return out, checks

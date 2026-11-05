# -*- coding: utf-8 -*-
"""GDT — reproduces GDT_scientific (EN/KO): 25 retained right-ear runs, six protocol x stimulus panels (2026-11-01 to 03)."""
import matplotlib.pyplot as plt

from common import (C_ACC, C_GRAY, C_R, Pages, answered, by_run, geomean, load, mean, reversal_trial_nos,
                    reversal_values, staircase)

PANELS = [('A', 'Wei2007', 'broadband noise', 'Wei / Zeng | 500-ms noise', 1 / 3),
          ('B', 'Wei2007', 'tone 2 kHz -> 2 kHz', 'Wei / Zeng | 2 -> 2 kHz tones', 1 / 3),
          ('C', 'Wei2007', 'tone 2 kHz -> 1 kHz', 'Wei / Zeng | 2 -> 1 kHz tones', 1 / 3),
          ('D', 'Xie2022', 'noise 800 ms', 'Xie 2022 | 800-ms noise', 1 / 2),
          ('E', 'Blankenship2022', 'tone 2 kHz -> 2 kHz', 'Blankenship 2022 | 2 -> 2 kHz tones', 1 / 2),
          ('F', 'Blankenship2022', 'tone 2 kHz -> 1 kHz', 'Blankenship 2022 | 2 -> 1 kHz tones', 1 / 2)]
YT = [0.3, 1, 3, 10, 30, 100]


def value_of(r, rows):
    """Recompute the stored result from the reversals: Wei/Zeng geometric mean of the last 8 of 12,
    Xie arithmetic mean of the last 6 of 10, Blankenship arithmetic mean of the last 3 of 5 (paper-method value)."""
    rv = reversal_values(rows)
    if r['protocol'].startswith('Wei2007'):
        return geomean(rv[-8:])
    if r['protocol'].startswith('Xie2022'):
        return mean(rv[-6:])
    return mean(rv[-3:])


def run(outdir):
    trials, runs = load('gdt')
    tr = by_run(trials)
    runs.sort(key=lambda r: (r['date_kst'], r['start_time_kst']))
    kept = [r for r in runs if r['included'] == 1]
    out, checks = {}, {}
    val, lab, panel_runs = {}, {}, {}
    bad = 0
    for p, proto, cond, _, _ in PANELS:
        rs = [r for r in kept if r['protocol'].startswith(proto) and r['condition'].startswith(cond)]
        panel_runs[p] = rs
        for i, r in enumerate(rs, 1):
            lab[r['run_id']] = f'{p}{i}'
            if r['value_kind'] != 'none':
                val[r['run_id']] = value_of(r, tr[r['run_id']])
                bad += abs(val[r['run_id']] - r['threshold']) > 1e-5
    checks['threshold_recomputed_vs_app_mismatch'] = bad
    assert sum(len(v) for v in panel_runs.values()) == len(kept)
    out['all.n_runs'] = len(kept)
    out['all.n_trials'] = sum(r['n_responses'] for r in kept)
    out['all.n_numeric'] = sum(r['value_kind'] != 'none' for r in kept)
    out['all.n_floor_limited'] = sum(r['app_status'] == 'threshold_near_floor' for r in kept)
    out['all.n_reversals'] = sum(r['n_reversals'] for r in kept)
    out['all.n_reversals_used'] = sum(r['n_reversals_used'] for r in kept if r['value_kind'] != 'none')
    dele = [r for r in runs if 'deleted' in (r['source'] or '')]
    abo = [r for r in runs if r['app_status'] == 'participant_aborted']
    out['deleted.n_runs'], out['deleted.n_trials'] = len(dele), sum(r['n_responses'] for r in dele)
    out['aborted.n_runs'], out['aborted.n_responses'] = len(abo), sum(r['n_responses'] for r in abo)
    out['practice.n_runs'] = sum(r['run_kind'] == 'practice' for r in runs)
    out['examples.n'] = sum(r['n_examples_before'] or 0 for r in kept)
    for p, *_ in PANELS:
        rs = panel_runs[p]
        out[f'panel.{p}.n_runs'] = len(rs)
        out[f'panel.{p}.n_trials'] = sum(r['n_responses'] for r in rs)
        fl = [t['value'] for r in rs for t in tr[r['run_id']] if t['at_limit'] == 'hard']
        if fl and p in ('B', 'D', 'E'):
            out[f'floor.{p}'] = min(fl)
        for r in rs:
            k = f"run.{lab[r['run_id']]}"
            rows = answered(tr[r['run_id']])
            out[f'{k}.n_trials'] = len(rows)
            out[f'{k}.value'] = val[r['run_id']] if r['run_id'] in val else 'floor'
            out[f'{k}.correct'] = f"{sum(t['correct'] for t in rows)}/{len(rows)}"
            out[f'{k}.n_reversals'] = r['n_reversals']
            out[f'{k}.start_kst'] = f"{r['date_kst']} {r['start_time_kst'][:5]}"
    # ── figures ──
    pg = Pages(outdir, 'gdt')
    floor_of = {p: min((t['value'] for r in panel_runs[p] for t in tr[r['run_id']] if t['value']), default=None) for p, *_ in PANELS}
    fig, axs = plt.subplots(2, 3, figsize=(13, 8.5))
    for ax, (p, proto, cond, title, ch) in zip(axs.flat, PANELS):
        rs = panel_runs[p]
        for i, r in enumerate(rs, 1):
            if r['run_id'] in val:
                ax.plot(i, val[r['run_id']], 'o', color=C_R, ms=6)
                ax.annotate(f"{val[r['run_id']]:.2f}", (i, val[r['run_id']]), xytext=(0, 6), textcoords='offset points', ha='center', fontsize=6.5)
            else:
                ax.plot(i, floor_of[p], '^', mfc='white', mec=C_R, ms=7)
        ax.set_yscale('log')
        ax.set_yticks(YT, [str(v) for v in YT])
        ax.set_ylim(0.25, 200)
        ax.set_xticks(range(1, len(rs) + 1), [f"{i}\nn={r['n_responses']}" for i, r in enumerate(rs, 1)], fontsize=6.5)
        ax.set_xlim(0.4, len(rs) + 0.6)
        ax.set_ylabel('paper-method value (ms)' if proto.startswith('Blank') else 'gap detection threshold (ms)')
        ax.set_title(f"{p}  {title}\n{len(rs)} runs · {out[f'panel.{p}.n_trials']} valid trials", loc='left')
    fig.text(0.01, 0.005, 'Open triangles: floor-limited status (app status threshold_near_floor) drawn at the lowest presented gap, not a threshold. '
             'E-F: Blankenship 1-up/1-down tracks 50 % (= 2AFC chance), stored as a paper-method value. Run order within panel; '
             'deleted, stopped, practice runs and example presentations excluded.', fontsize=6.5)
    fig.tight_layout(rect=(0, 0.02, 1, 0.95))
    pg.add(fig, f"GDT | individual run results | right ear | {out['all.n_runs']} runs · {out['all.n_trials']} valid trials")
    fig, axs = plt.subplots(2, 3, figsize=(13, 8.5))
    for ax, (p, proto, cond, title, ch) in zip(axs.flat, PANELS):
        x0 = 0
        for r in panel_runs[p]:
            rows = answered(tr[r['run_id']])
            ax.plot([x0 + t['run_trial_no'] for t in rows], [t['value'] for t in rows], '-', color=C_R, lw=0.9)
            ax.axvline(x0 + 0.5, color=C_GRAY, ls=':', lw=0.6)
            ax.text(x0 + 1, 150, f"{lab[r['run_id']][1:]}\nn={len(rows)}", fontsize=5.5, va='top')
            x0 += len(rows)
        ax.set_yscale('log')
        ax.set_yticks(YT, [str(v) for v in YT])
        ax.set_ylim(0.25, 230)
        ax.set_xlabel('cumulative valid trial count')
        ax.set_ylabel('nominal gap (ms)')
        ax.set_title(f"{p}  {title}\n{len(panel_runs[p])} runs · {out[f'panel.{p}.n_trials']} valid trials", loc='left')
    fig.tight_layout(rect=(0, 0.02, 1, 0.95))
    pg.add(fig, 'GDT | cumulative staircase traces (not connected across runs)')
    fig, axs = plt.subplots(2, 3, figsize=(13, 8.5))
    for ax, (p, proto, cond, title, ch) in zip(axs.flat, PANELS):
        rs = panel_runs[p]
        acc = []
        for r in rs:
            rows = answered(tr[r['run_id']])
            acc.append(100 * sum(t['correct'] for t in rows) / len(rows))
        ax.bar(range(len(rs)), acc, color=C_R)
        for i, r in enumerate(rs):
            ax.text(i, acc[i] + 2, out[f"run.{lab[r['run_id']]}.correct"], ha='center', fontsize=6.5)
        ax.axhline(100 * ch, color=C_GRAY, ls=':')
        ax.axhline(50 if proto.startswith('Blank') else 70.7, color=C_ACC, ls='--')
        ax.set_xticks(range(len(rs)), [lab[r['run_id']] for r in rs])
        ax.set_ylim(0, 110)
        ax.set_ylabel('correct responses (%)')
        ax.set_title(f"{p}  {title}\nchance {100 * ch:.1f}% (dotted) | target {'= chance: 50' if proto.startswith('Blank') else '70.7'}% (dashed)",
                     loc='left')
    fig.tight_layout(rect=(0, 0.02, 1, 0.95))
    pg.add(fig, 'GDT | run-level response accuracy (descriptive; difficulty changes adaptively)')
    fig, axs = plt.subplots(2, 3, figsize=(13, 8.5))
    for ax, (p, proto, cond, title, ch) in zip(axs.flat, PANELS):
        acc = {}
        for r in panel_runs[p]:
            for t in answered(tr[r['run_id']]):
                acc.setdefault(t['value'], []).append(t['correct'])
        xs = sorted(acc)
        ax.scatter(xs, [100 * mean(acc[x]) for x in xs], s=[12 * len(acc[x]) for x in xs], color=C_R, alpha=0.6)
        ax.axhline(100 * ch, color=C_GRAY, ls=':')
        ax.axhline(50 if proto.startswith('Blank') else 70.7, color=C_ACC, ls='--')
        ax.set_xscale('log')
        ax.set_xticks(YT, [str(v) for v in YT])
        ax.set_xlim(0.25, 230)
        ax.set_ylim(-5, 108)
        ax.set_xlabel('nominal gap duration (ms; log)')
        ax.set_ylabel('observed correct (%)')
        ax.set_title(f'{p}  {title}', loc='left')
    fig.text(0.01, 0.005, 'Each point pools responses at one ladder level within a panel; marker area proportional to the number of trials. No curve fitted.',
             fontsize=6.5)
    fig.tight_layout(rect=(0, 0.02, 1, 0.95))
    pg.add(fig, 'GDT | empirical response fractions by gap')
    allr = [r for p, *_ in PANELS for r in panel_runs[p]]
    for s in range(0, len(allr), 9):
        fig, axs = plt.subplots(3, 3, figsize=(12, 9), sharey=True)
        for ax, r in zip(axs.flat, allr[s:s + 9]):
            rows = tr[r['run_id']]
            nu = r['n_reversals_used'] if r['run_id'] in val else 0
            used = reversal_trial_nos(rows)[-nu:] if nu else []
            res = f"{val[r['run_id']]:.2f} ms" + (' (paper value)' if r['value_kind'] == 'paper_method_value' else '') if r['run_id'] in val else 'floor-limited'
            staircase(ax, answered(rows), used, val.get(r['run_id']), log=True, ylabel='nominal gap (ms)',
                      floor=floor_of[lab[r['run_id']][0]] if r['run_id'] not in val else None,
                      title=f"{lab[r['run_id']]} | {dict((p, t) for p, _, _, t, _ in PANELS)[lab[r['run_id']][0]]} | n={r['n_responses']}\n"
                            f"{r['n_reversals']} reversals | {res} | {r['date_kst']} {r['start_time_kst'][:5]} KST")
            ax.set_yticks(YT, [str(v) for v in YT])
            ax.set_ylim(0.25, 230)
        for ax in list(axs.flat)[len(allr[s:s + 9]):]:
            ax.axis('off')
        fig.tight_layout(rect=(0, 0.02, 1, 0.95))
        pg.add(fig, f"GDT | individual adaptive staircases | {out['all.n_reversals']} recorded reversals; "
                    f"{out['all.n_reversals_used']} used by the {out['all.n_numeric']} numeric results")
    fig, ax = plt.subplots(figsize=(12, 5))
    ax.axis('off')
    lines = [f"{'panel':6s}{'protocol / stimulus':42s}{'rule':66s}"]
    for p, proto, cond, title, ch in PANELS:
        r = panel_runs[p][0]
        lines.append(f"{p:6s}{title:42s}{r['threshold_rule'][:66]}")
    lines += ['', f"Excluded: {out['deleted.n_runs']} deleted runs ({out['deleted.n_trials']} trials), {out['aborted.n_runs']} stopped runs "
              f"({out['aborted.n_responses']} completed responses). Practice runs: {out['practice.n_runs']}. "
              f"Example presentations before runs: {out['examples.n']} (not trials)."]
    ax.text(0, 1, '\n'.join(lines), family='monospace', fontsize=8, va='top')
    pg.add(fig, 'GDT | methods and counting (from the run CSV)')
    checks['figure_pages'] = pg.close()
    return out, checks

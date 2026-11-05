# -*- coding: utf-8 -*-
"""Shared helpers: read the public CSVs, simple statistics, comparison with the PDF values, figure output.

All values are computed only from the CSV files in data/trials and data/runs; analysis/pdf_values/<test>.csv
(the numbers printed in the PDFs) is read only to compare with them. No raw JSON is used by the analysis.
"""
import csv
import math
import os
import re

import matplotlib

matplotlib.use('Agg')
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.backends.backend_pdf import PdfPages  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
DATA = os.path.join(ROOT, 'data')

INT_COLS = {'session_trial_no', 'run_trial_no', 'n_intervals', 'reversal_no', 'excluded', 'correct', 'reversal', 'unsure',
            'n_trials', 'n_responses', 'n_correct', 'n_unsure', 'n_examples_before', 'n_reversals', 'n_reversals_used',
            'included', 'audio_sample_rate_hz'}
FLOAT_COLS = {'value', 'threshold'}


def _conv(row):
    out = {}
    for k, v in row.items():
        if v == '':
            out[k] = None
        elif k in INT_COLS:
            out[k] = int(v)
        elif k in FLOAT_COLS:
            out[k] = float(v)
        else:
            out[k] = v
    return out


def read_csv(path):
    with open(path, encoding='utf-8', newline='') as f:
        return [_conv(r) for r in csv.DictReader(f)]


def load(test):
    """Return (trials, runs) for one test, as lists of dicts. Empty cells are None."""
    t = read_csv(os.path.join(DATA, 'trials', f'{test}_trials.csv'))
    r = read_csv(os.path.join(DATA, 'runs', f'{test}_runs.csv'))
    return t, r


def by_run(trials):
    out = {}
    for t in trials:
        out.setdefault(t['run_id'], []).append(t)
    for v in out.values():
        v.sort(key=lambda x: x['run_trial_no'])
    return out


def answered(rows):
    """Trials with a scored response (correct is 0 or 1)."""
    return [t for t in rows if t['correct'] is not None]


def reversal_values(rows):
    return [t['value'] for t in rows if t['reversal'] == 1]


def reversal_trial_nos(rows):
    return [t['run_trial_no'] for t in rows if t['reversal'] == 1]


def mean(xs):
    xs = list(xs)
    return sum(xs) / len(xs) if xs else None


def sd(xs):
    """Sample standard deviation (ddof = 1); None for fewer than 2 values."""
    xs = list(xs)
    if len(xs) < 2:
        return None
    m = mean(xs)
    return math.sqrt(sum((x - m) ** 2 for x in xs) / (len(xs) - 1))


def geomean(xs):
    xs = list(xs)
    return math.exp(sum(math.log(x) for x in xs) / len(xs))


def js_round(x, nd):
    """Round like JavaScript Number.prototype.toFixed (the apps' rounding): ties go away from zero."""
    if x is None:
        return None
    q = 10 ** nd
    y = abs(x) * q
    f = math.floor(y)
    r = f + 1 if (y - f) >= 0.5 - 1e-12 else f
    return math.copysign(r / q, x) if r else 0.0


def frac(rows):
    a = answered(rows)
    return f"{sum(t['correct'] for t in a)}/{len(a)}"


def hhmm(run):
    return f"{run['date_kst']} {run['start_time_kst'][:5]}"


# ───────────────────────── comparison with the PDF ─────────────────────────
_NUM = re.compile(r'^[+-]?\d+(\.\d+)?$')


def fmt_like(value, expected, rounding='float'):
    """Format a computed value the way the PDF printed the expected value.

    rounding='float'  : Python's correctly rounded formatting of the binary value (f'{x:.2f}')
    rounding='half_up': round the shortest decimal form of the value half up (21.325 -> 21.33); used for the SMD PDF
    """
    exp = expected.strip().replace('−', '-')
    if value is None:
        return '—'
    if isinstance(value, str):
        return value
    if _NUM.match(exp):
        nd = len(exp.split('.')[1]) if '.' in exp else 0
        if rounding == 'half_up' and isinstance(value, float):
            from decimal import ROUND_HALF_UP, Decimal
            value = float(Decimal(repr(value)).quantize(Decimal(1).scaleb(-nd), rounding=ROUND_HALF_UP))
        s = f'{value:+.{nd}f}' if exp.startswith('+') else f'{value:.{nd}f}'
        if re.match(r'^-0(\.0+)?$', s):
            s = s[1:]
        return s
    return str(value)


def compare(test, computed, outdir, rounding='float'):
    """Compare a dict of computed values with analysis/pdf_values/<test>.csv. Returns list of result rows."""
    exp_rows = read_csv(os.path.join(HERE, 'pdf_values', f'{test}.csv'))
    res = []
    for e in exp_rows:
        key, expected = e['key'], (e['expected'] or '').replace('−', '-')
        if key not in computed:
            res.append(dict(test=test, key=key, pdf=expected, computed='(not computed)', match=0, where=e['where']))
            continue
        got = fmt_like(computed[key], expected, rounding)
        res.append(dict(test=test, key=key, pdf=expected, computed=got, match=int(got == expected), where=e['where']))
    with open(os.path.join(outdir, 'pdf_comparison.csv'), 'w', encoding='utf-8', newline='') as f:
        w = csv.DictWriter(f, fieldnames=['test', 'key', 'pdf', 'computed', 'match', 'where'], lineterminator='\n')
        w.writeheader()
        w.writerows(res)
    return res


def write_numbers(computed, outdir):
    with open(os.path.join(outdir, 'numbers.csv'), 'w', encoding='utf-8', newline='') as f:
        w = csv.writer(f, lineterminator='\n')
        w.writerow(['key', 'value'])
        for k in sorted(computed):
            v = computed[k]
            w.writerow([k, '' if v is None else (repr(v) if isinstance(v, float) else v)])


# ───────────────────────── figures ─────────────────────────
plt.rcParams.update({'font.size': 8, 'axes.titlesize': 8.5, 'axes.labelsize': 8, 'legend.fontsize': 7,
                     'axes.spines.top': False, 'axes.spines.right': False, 'figure.dpi': 100,
                     'pdf.fonttype': 42, 'font.family': 'DejaVu Sans'})
C_R, C_L, C_GRAY, C_OK, C_BAD, C_ACC = '#1f6fb2', '#c0392b', '#888888', '#2b8a3e', '#d9480f', '#e69f00'


class Pages:
    """Collect figures into one multi-page PDF and one PNG per page."""

    def __init__(self, outdir, name):
        self.dir = os.path.join(outdir, 'figures')
        os.makedirs(self.dir, exist_ok=True)
        self.name = name
        # no creation date in the PDF, so that re-running gives byte-identical files
        self.pdf = PdfPages(os.path.join(self.dir, f'{name}_figures.pdf'), metadata={'CreationDate': None})
        self.n = 0

    def add(self, fig, title):
        self.n += 1
        fig.suptitle(title, fontsize=10, fontweight='bold')
        self.pdf.savefig(fig)
        fig.savefig(os.path.join(self.dir, f'{self.name}_p{self.n:02d}.png'), dpi=110)
        plt.close(fig)

    def close(self):
        self.pdf.close()
        return self.n


def staircase(ax, rows, used_trial_nos=(), thr=None, log=False, ylabel='', floor=None, title=''):
    """Presented value per trial; filled = correct, open = incorrect; reversals ringed, used reversals highlighted."""
    rows = [t for t in rows if t['value'] is not None]
    x = [t['run_trial_no'] for t in rows]
    y = [t['value'] for t in rows]
    ax.step(x, y, where='mid', color=C_GRAY, lw=0.8, zorder=1)
    for t in rows:
        c = t['correct']
        ax.plot(t['run_trial_no'], t['value'], 'o', ms=3.2, zorder=3,
                mfc=(C_OK if c == 1 else 'white'), mec=(C_OK if c == 1 else C_BAD if c == 0 else C_GRAY), mew=0.8)
        if t['reversal'] == 1:
            used = t['run_trial_no'] in used_trial_nos
            ax.plot(t['run_trial_no'], t['value'], 'D' if used else 'd', ms=6.5 if used else 5.5, zorder=2,
                    mfc='none', mec=(C_ACC if used else C_GRAY), mew=1.1)
    if thr is not None:
        ax.axhline(thr, color=C_ACC, ls='--', lw=1)
    if floor is not None:
        ax.axhline(floor, color=C_GRAY, ls=':', lw=0.8)
    if log:
        ax.set_yscale('log')
    ax.set_xlabel('trial number')
    ax.set_ylabel(ylabel)
    ax.set_title(title, loc='left')

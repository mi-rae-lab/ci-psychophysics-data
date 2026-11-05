# -*- coding: utf-8 -*-
"""Copy the seven apps' raw records into data/raw/ and remove identifying values.

    python -I sanitize_raw.py <snapshot_root> <data_raw_out> <redaction_log.csv>

<snapshot_root> holds one folder per app (와우TMTF, 와우SMRT, ...), each a copy of the app's data/ folder.
Only text substitutions listed in RULES are made, so every other byte of every file stays as the app wrote it.
After substitution every file is parsed again and compared leaf by leaf with the original: any difference
that no rule explains stops the script. Counts per file / JSON path / rule go to the redaction log.

Not copied: backup/ (older copies of db.json), db.prev.json (previous revision), and the GDT
deleted-records db.before.json (full database copy taken just before the deletion; the deleted runs
themselves are in removed.json).
"""
import csv, io, json, os, re, sys

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
SNAP, OUT, LOG = sys.argv[1], sys.argv[2], sys.argv[3]

APPS = [('와우TMTF', 'tmtf'), ('와우SMRT', 'smrt'), ('와우STRIPES', 'stripes'), ('와우STM', 'stm'),
        ('와우SRD', 'srd'), ('와우GDT', 'gdt'), ('와우SMD', 'smd')]
GDT_DELETED = ('지운기록/2026-11-03_Xie_11-01_2226', 'deleted_runs_2026-11-03')

# (rule id, what it removes, regex on the file text (JSON-escaped), replacement, regex on a parsed string value, replacement)
# The patterns are generic: no removed value is written in this file.
LABEL = 'P01'   # neutral public participant label
GUID = r'[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}'
RULES = [
    ('audio_endpoint_guid', 'Windows audio endpoint ID (unique to this computer\'s output device)',
     re.compile(r'(\{0\.0\.[01]\.00000000\}\.\{)' + GUID + r'(\})'), r'\1redacted-audio-endpoint-guid\2',
     re.compile(r'(\{0\.0\.[01]\.00000000\}\.\{)' + GUID + r'(\})'), r'\1redacted-audio-endpoint-guid\2'),
    ('usb_instance_id', 'USB device instance ID inside the Windows hardware ID (unique to this adapter/computer)',
     re.compile(r'(VID_[0-9A-Fa-f]{4}&PID_[0-9A-Fa-f]{4}(?:&MI_[0-9A-Fa-f]{2})?\\\\)[^"\\]+'), r'\1redacted-usb-instance-id',
     re.compile(r'(VID_[0-9A-Fa-f]{4}&PID_[0-9A-Fa-f]{4}(?:&MI_[0-9A-Fa-f]{2})?\\)[^"\\]+'), r'\1redacted-usb-instance-id'),
    # every "code" key in these records belongs to a participant object and is followed by "group"
    ('participant_code', 'participant code typed in the apps -> the neutral public label "' + LABEL + '"',
     re.compile(r'("code"\s*:\s*)"[^"]*"(?=\s*,\s*"group")'), r'\1"' + LABEL + '"',
     None, LABEL),
    ('user_name_in_path', 'Windows user name inside a folder path',
     re.compile(r'(?i)c-users-(?!\[redacted\])[^-/\\"]+-'), 'c-users-[redacted]-',
     re.compile(r'(?i)c-users-(?!\[redacted\])[^-/\\"]+-'), 'c-users-[redacted]-'),
    ('user_home_path', 'absolute Windows user-profile path',
     re.compile(r'(?i)[A-Z]:(\\\\|/)Users(\\\\|/)(?!\[redacted\])[^\\/"]+'), r'C:\1Users\2[redacted]',
     re.compile(r'(?i)[A-Z]:(\\|/)Users(\\|/)(?!\[redacted\])[^\\/"]+'), r'C:\1Users\2[redacted]'),
    ('email', 'e-mail address',
     re.compile(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}'), '[redacted-email]',
     re.compile(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}'), '[redacted-email]'),
]
USER = os.environ.get('USERNAME') or os.environ.get('USER') or ''
LEFTOVER = [  # must not appear anywhere after sanitising
    re.compile(r'\{0\.0\.[01]\.00000000\}\.\{' + GUID + r'\}'), re.compile(r'VID_[0-9A-Fa-f]{4}&PID_[0-9A-Fa-f]{4}(?:&MI_[0-9A-Fa-f]{2})?\\\\(?!redacted)'),
    re.compile(r'"code"\s*:\s*"(?!' + LABEL + '")'), re.compile(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}'),
] + ([re.compile(re.escape(USER), re.I)] if len(USER) >= 3 else [])


def sanitize_text(s):
    hits = {}
    for rid, _, rx, rep, _, _ in RULES:
        s, n = rx.subn(rep, s)
        if n:
            hits[rid] = n
    return s, hits


def leaves(o, path='$'):
    if isinstance(o, dict):
        for k, v in o.items():
            yield from leaves(v, f'{path}.{k}')
    elif isinstance(o, list):
        for i, v in enumerate(o):
            yield from leaves(v, f'{path}[{i}]')
    else:
        yield path, o


def generic(path):
    return re.sub(r'\[\d+\]', '[]', path)


def explain(a, b, path):
    """Which rule turns leaf value a into b (strings only)."""
    if not (isinstance(a, str) and isinstance(b, str)):
        return None
    if path.endswith('.code') and b == LABEL:
        return ['participant_code']
    out = []
    for rid, _, _, _, vrx, vrep in RULES:
        if vrx is None:
            continue
        a2, n = vrx.subn(vrep, a)
        if n:
            out.append(rid)
            a = a2
    return out if a == b and out else None


def parse(text, jsonl):
    if jsonl:
        return [json.loads(line) for line in text.splitlines() if line.strip()]
    return json.loads(text)


CODE = re.compile(r'"code"\s*:\s*"([^"]*)"(?=\s*,\s*"group")')
ORIGINAL_CODES = set()
for app, _ in APPS:
    for dp, dn, fn in os.walk(os.path.join(SNAP, app)):
        dn[:] = [d for d in dn if d != 'backup']
        for f in fn:
            if f.endswith(('.json', '.jsonl')) and f not in ('db.prev.json', 'db.before.json'):
                ORIGINAL_CODES.update(CODE.findall(open(os.path.join(dp, f), encoding='utf-8').read()))
ORIGINAL_CODES.discard(LABEL)
LEFTOVER += [re.compile(re.escape(c), re.I) for c in ORIGINAL_CODES if len(c) >= 3]

log = {}
files_done = []
for app, short in APPS:
    src_root = os.path.join(SNAP, app)
    jobs = [('db.json', 'db.json'), ('runs-log.jsonl', 'runs-log.jsonl')]
    jdir = os.path.join(src_root, 'journal')
    if os.path.isdir(jdir):
        jobs += [(f'journal/{f}', f'journal/{f}') for f in sorted(os.listdir(jdir))]
    if app == '와우GDT':
        d, newd = GDT_DELETED
        jobs += [(f'{d}/removed.json', f'{newd}/removed.json'), (f'{d}/README.txt', f'{newd}/README.txt')]
        jobs += [(f'{d}/journal/{f}', f'{newd}/journal/{f}') for f in sorted(os.listdir(os.path.join(src_root, d, 'journal')))]
    for rel_src, rel_dst in jobs:
        src = os.path.join(src_root, rel_src)
        dst = os.path.join(OUT, short, rel_dst)
        raw = open(src, 'rb').read()
        text = raw.decode('utf-8')
        new, hits = sanitize_text(text)
        # check: still valid JSON and only explained differences
        if rel_src.endswith(('.json', '.jsonl')):
            jl = rel_src.endswith('.jsonl')
            A, B = parse(text, jl), parse(new, jl)
            la, lb = list(leaves(A)), list(leaves(B))
            assert [p for p, _ in la] == [p for p, _ in lb], f'structure changed: {src}'
            for (p, va), (_, vb) in zip(la, lb):
                if va != vb:
                    why = explain(va, vb, p)
                    assert why, f'unexplained change {src} {p}: {va!r} -> {vb!r}'
                    for rid in why:
                        key = (f'{short}/{rel_dst}' if not rel_dst.startswith('journal/') else f'{short}/journal/*.jsonl'
                               if 'deleted' not in rel_dst else f'{short}/{os.path.dirname(rel_dst)}/*.jsonl', generic(p), rid)
                        if rel_dst.startswith(GDT_DELETED[1] + '/journal/'):
                            key = (f'{short}/{GDT_DELETED[1]}/journal/*.jsonl', generic(p), rid)
                        log[key] = log.get(key, 0) + 1
        else:
            for rid, n in hits.items():
                key = (f'{short}/{rel_dst}', '(text)', rid)
                log[key] = log.get(key, 0) + n
        for rx in LEFTOVER:
            assert not rx.search(new), f'leftover {rx.pattern} in {dst}'
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        with open(dst, 'wb') as f:
            f.write(new.encode('utf-8'))
        files_done.append((f'{short}/{rel_dst}', len(raw), sum(hits.values())))

desc = {r[0]: r[1] for r in RULES}
with open(LOG, 'w', encoding='utf-8', newline='') as f:
    w = csv.writer(f, lineterminator='\n')
    w.writerow(['file', 'json_path', 'rule', 'what_was_removed', 'replaced_with', 'n_values'])
    REPL = {'audio_endpoint_guid': '{0.0.0.00000000}.{redacted-audio-endpoint-guid}', 'usb_instance_id': 'redacted-usb-instance-id',
            'participant_code': LABEL, 'user_name_in_path': '[redacted]', 'user_home_path': 'C:\\Users\\[redacted]',
            'email': '[redacted-email]'}
    for (fn, p, rid), n in sorted(log.items()):
        w.writerow([fn, p, rid, desc[rid], REPL[rid], n])
tot = {}
for (fn, p, rid), n in log.items():
    tot[rid] = tot.get(rid, 0) + n
print(f'files written: {len(files_done)}  bytes in: {sum(b for _, b, _ in files_done):,}')
print('values replaced per rule:', tot)
print('original participant codes found:', len(ORIGINAL_CODES), '(none of them is left in the output)')

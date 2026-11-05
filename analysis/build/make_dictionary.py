# -*- coding: utf-8 -*-
"""Write data/data_dictionary.csv: every column of every CSV in the package, its meaning, unit and possible values.

    python -I make_dictionary.py <package_root>

Meanings and units are written below by hand; the 'possible_values' column is read from the CSV files themselves
(distinct values when there are few, otherwise the range or a count with examples).
"""
import csv, glob, io, os, re, sys

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
ROOT = sys.argv[1]
TESTS = ['tmtf', 'smrt', 'stripes', 'stm', 'srd', 'gdt', 'smd']

# column -> (meaning KO, meaning EN, unit)
TRIALS = {
    'test': ('검사 이름', 'test name', ''),
    'protocol': ('절차: 과제 · 계단 규칙 · 자극 요약 (앱 기록에서)', 'procedure: task, staircase rule, stimulus summary (from the app record)', ''),
    'condition': ('절차 안의 조건 (변조 주파수 · 밀도 · 소리 종류 · 크기 로빙 등). 없으면 빈칸', 'condition within the procedure (modulation rate, density, sound type, level rove); blank if none', ''),
    'ear': ('검사한 귀', 'test ear', ''),
    'date_kst': ('시행 날짜, 한국 시각(UTC+9)', 'trial date, Korea Standard Time (UTC+9)', 'YYYY-MM-DD'),
    'time_kst': ('시행 시각, 한국 시각, 밀리초까지', 'trial time, KST, to the millisecond', 'HH:MM:SS.mmm'),
    'time_source': ('시각이 무엇을 뜻하는지: trial_start = 시행 시작(소리 예약) · trial_stopped = 답 전에 멈춘 시각 · run_end = 시행 시각 기록이 없어 측정이 끝난 시각 (TMTF 2026-10-11 저녁 첫 21개 측정)',
                    'what the time refers to: trial_start = trial start (sound scheduled); trial_stopped = moment a trial was stopped before a response; run_end = run end time, used where per-trial times were not recorded (first 21 TMTF runs, 2026-10-11 evening)', ''),
    'session_id': ('회기(한 번 앉아서 한 묶음) ID. TMTF 첫 21개 측정은 빈칸', 'session ID (one sitting); blank for the first 21 TMTF runs', ''),
    'run_id': ('측정(회차: 계단 하나 또는 고정 자극 묶음 하나) ID. TMTF 연습 묶음 = <session_id>-practice, 앱이 버린 측정 = <session_id>-discarded-<k>',
               'run ID (one staircase track or one constant-stimuli block). TMTF practice blocks = <session_id>-practice; runs discarded by the app = <session_id>-discarded-<k>', ''),
    'trial_kind': ('시행 종류: main 본 측정 · practice 연습 · example 예시(정답을 보여 줌) · screening 통과 검사', 'kind of trial: main, practice, example (answer shown), screening (pass check)', ''),
    'session_trial_no': ('회기 안 시행 번호 (시각 순, 연습 · 예시 · 멈춘 시행 포함, 1부터)', 'trial number within the session (time order, all kinds, from 1)', 'count'),
    'run_trial_no': ('측정 안 시행 번호 (1부터)', 'trial number within the run (from 1)', 'count'),
    'value': ('표적 구간에 제시한 값 (단위는 unit 열)', 'value presented in the target interval (unit in the unit column)', 'see unit'),
    'unit': ('value 의 단위', 'unit of value', ''),
    'n_intervals': ('한 시행의 구간(소리) 수', 'number of intervals (sounds) per trial', 'count'),
    'target_interval': ('정답 구간 (1부터; STRIPES 는 A/B)', 'correct interval (from 1; STRIPES: A or B)', ''),
    'response_interval': ('참가자가 고른 구간. ‘모르겠음’ 이거나 답 전에 멈추면 빈칸', 'interval chosen by the participant; blank for "don\'t know" or when stopped before a response', ''),
    'scored_interval': ('앱이 채점에 쓴 구간 (= 고른 구간; ‘모르겠음’ 이면 앱이 무작위로 고른 구간)', 'interval used for scoring (= chosen; for "don\'t know" the app picked one at random)', ''),
    'correct': ('정답 1 · 오답 0 (= scored_interval 이 target_interval 과 같음). 답이 없으면 빈칸', 'correct 1 / incorrect 0 (scored_interval == target_interval); blank without a response', '0/1'),
    'reversal': ('계단 반전이 난 시행 1, 아니면 0. 빈칸 = 계단이 아닌 시행 (TMTF 연습 묶음 · 앱이 버린 TMTF 측정 · 예시 · 통과 검사 · 고정 자극 · 답 전에 멈춘 시행). SMRT · STRIPES 연습 측정은 계단이라 값이 있음',
                 'staircase reversal at this trial (1/0). Blank = not part of a staircase track (TMTF practice blocks, the TMTF run discarded by the app, examples, pass checks, constant stimuli, trials stopped before a response). SMRT and STRIPES practice runs are staircases and do have values', '0/1'),
    'reversal_no': ('그 측정 안 반전 번호 (1부터)', 'index of the reversal within the run (from 1)', 'count'),
    'unsure': ('‘모르겠음’ 단추 1 (TMTF · SMRT 에만 있는 단추, 다른 검사는 빈칸)', '"don\'t know" button pressed (1/0); only TMTF and SMRT have it, blank elsewhere', '0/1'),
    'at_limit': ('제시 값이 계단 범위의 끝: easy 쉬운 끝 · hard 어려운 끝 (천장 · 하한 표시)', 'presented value at an end of the staircase range: easy / hard (ceiling / floor marker)', ''),
    'blocked_at_limit': ('이 시행 뒤 계단이 범위 밖으로 가려다 막힘: easy / hard', 'after this trial the staircase asked to go beyond that end: easy / hard', ''),
    'run_status': ('그 측정에 앱이 붙인 결과 상태 (측정의 모든 시행 줄에 같은 값)', 'result status the app gave the run (same on every trial row of the run)', ''),
    'run_flags': ('그 측정에 앱이 붙인 점검 표시 (편향 · 끝 근처 · 우연 등), ; 로 이음', 'check flags the app gave the run (bias, near a limit, chance), joined by ;', ''),
    'excluded': ('1 = 본 분석에서 빼는 시행 (연습 · 예시 · 통과 검사 · 멈춘 측정 · 답 전 멈춤 · 지운 측정)', '1 = excluded from the main analysis (practice, example, pass check, stopped run, stopped trial, deleted run)', '0/1'),
    'exclusion_reason': ('뺀 까닭 (여럿이면 ; 로 이음)', 'reason(s) for exclusion, joined by ;', ''),
}
RUNS = {
    'test': TRIALS['test'],
    'run_id': ('측정(회차) ID — 시행 CSV 의 run_id 와 같음', 'run ID, the same as run_id in the trial CSV', ''),
    'session_id': TRIALS['session_id'],
    'protocol': TRIALS['protocol'],
    'condition': TRIALS['condition'],
    'ear': TRIALS['ear'],
    'run_kind': ('측정 종류: main · practice(연습) · screening(예시 + 통과 검사)', 'kind of run: main, practice, screening (examples + pass check)', ''),
    'date_kst': ('측정 날짜, 한국 시각', 'run date, KST', 'YYYY-MM-DD'),
    'start_time_kst': ('측정 시작 시각 (기록이 없으면 빈칸)', 'run start time (blank if not recorded)', 'HH:MM:SS'),
    'end_time_kst': ('측정 끝 시각', 'run end time', 'HH:MM:SS'),
    'n_trials': ('시행 CSV 에 있는 이 측정의 줄 수 (답 전에 멈춘 시행 포함)', 'rows of this run in the trial CSV (including trials stopped before a response)', 'count'),
    'n_responses': ('답한 시행 수 (correct 가 0 또는 1)', 'trials with a scored response', 'count'),
    'n_correct': ('정답 수', 'correct responses', 'count'),
    'n_unsure': ('‘모르겠음’ 수 (TMTF · SMRT)', '"don\'t know" responses (TMTF, SMRT)', 'count'),
    'n_examples_before': ('측정 전에 들려준 예시 소리 수 (답을 받지 않음, 시행이 아님; 새 틀 앱만 기록)', 'example sounds played before the run (no response, not trials; recorded by the newer apps only)', 'count'),
    'n_reversals': ('반전 수', 'number of reversals', 'count'),
    'reversal_values': ('반전 시행의 제시 값, 순서대로 ; 로 이음', 'presented values at the reversal trials, in order, joined by ;', 'same as threshold_unit'),
    'reversal_trial_nos': ('반전 시행의 측정 안 번호 (run_trial_no), ; 로 이음', 'run_trial_no of each reversal, joined by ;', 'count'),
    'threshold_rule': ('역치를 내는 규칙 (몇 번째 반전부터 어떻게 평균)', 'rule that turns reversals into the threshold', ''),
    'n_reversals_used': ('역치에 쓴 반전 수', 'number of reversals averaged', 'count'),
    'threshold': ('앱이 저장한 역치 (또는 Blankenship 논문 방식 값). 숫자가 아니면 빈칸', 'threshold stored by the app (or the Blankenship paper-method value); blank when there is no numeric threshold', 'see threshold_unit'),
    'threshold_unit': ('threshold 의 단위', 'unit of threshold', ''),
    'value_kind': ('threshold = 70.7 % 등 목표 정답률 역치 · paper_method_value = Blankenship 방식 값(50 % = 우연을 따라감) · none = 숫자 없음',
                   'threshold; paper_method_value (Blankenship 1-up/1-down tracks 50 % = chance); none', ''),
    'no_threshold_reason': ('역치가 없는 이유', 'why there is no numeric threshold', ''),
    'app_status': ('앱이 붙인 결과 상태', 'result status stored by the app', ''),
    'app_flags': ('앱이 붙인 점검 표시, ; 로 이음', 'check flags stored by the app, joined by ;', ''),
    'included': ('1 = 분석에 포함 (본 측정, 끝 규칙까지 감) · 0 = 제외', '1 = included in the analysis (main run that reached its end rule); 0 = excluded', '0/1'),
    'exclusion_reason': ('제외한 까닭', 'reason for exclusion', ''),
    'audio_sample_rate_hz': ('브라우저 오디오 표본률 (앱 기록, 없으면 빈칸)', 'browser audio sample rate recorded by the app (blank if not recorded)', 'Hz'),
    'app_version': ('측정한 앱 판', 'app version that ran the measurement', ''),
    'source': ('이 줄을 만든 원본 기록 위치 (data/raw/<test>/ 안)', 'where in data/raw/<test>/ the run record comes from', ''),
}
UNIT_NOTES = {
    'tmtf': ('TMTF: value = 표적 구간의 진폭 변조 깊이 20·log10(m) dB (0 dB = 100 % 변조 = 가장 쉬움, -40 dB 아래 끝). 표준 구간은 변조 없음.',
             'TMTF: value = AM depth of the target interval, 20·log10(m) dB (0 dB = 100 % = easiest; lower limit -40 dB).'),
    'smrt': ('SMRT: value = 표적의 리플 밀도 RPO (기준 = 20 RPO 두 개; 높을수록 어려움). 공식 SMRT 1.1.3 WAV.',
             'SMRT: value = ripple density of the target in RPO (two 20-RPO references; higher = harder). Official SMRT 1.1.3 WAVs.'),
    'stripes': ('STRIPES: value = 밀도 D (RPO = D/5). 1.1 D = 쉬운 끝 · 20 D = 어려운 끝. target A/B (A-X-B).',
                'STRIPES: value = density D (RPO = D/5); 1.1 D easy end, 20 D hard end; target A or B (A-X-B).'),
    'stm': ('STM: value = 스펙트럼-시간 변조 깊이 20·log10(A) dB (0 dB = 쉬운 끝, -50 dB = 어려운 끝).',
            'STM: value = spectro-temporal modulation depth 20·log10(A) dB (0 dB easy end, -50 dB hard end).'),
    'srd': ('SRD: value = 리플 밀도 RPO (0.125 = 쉬운 끝, 높을수록 어려움). 임상(Drennan 2014) 고정 자극은 반전 · 끝 표시 없음.',
            'SRD: value = ripple density in RPO (0.125 easy end; higher = harder). Clinical constant-stimuli block has no reversals or limit markers.'),
    'gdt': ('GDT: value = 표적 간격 길이 ms (공칭 사다리 값, 길수록 쉬움). 긴 끝 = easy · 짧은 끝 = hard.',
            'GDT: value = nominal gap duration in ms (ladder value; longer = easier). Long end = easy, short end = hard.'),
    'smd': ('SMD: value = 스펙트럼 변조 깊이 dB (봉우리-골, 깊을수록 쉬움; 60 dB = 쉬운 끝). QSMD 는 공식 파일의 깊이.',
            'SMD: value = spectral modulation depth in dB (peak-to-valley; deeper = easier; 60 dB easy end). QSMD: depth of the official file.'),
}
OTHER = [
    ('analysis/pdf_values/<test>.csv', 'key', 'PDF 에 찍힌 값의 이름 (분석 코드가 같은 이름으로 다시 계산)', 'name of a value printed in the PDF (the analysis recomputes the same key)', ''),
    ('analysis/pdf_values/<test>.csv', 'expected', 'PDF 에 찍힌 그대로의 값 (— = PDF 에서 빈칸/없음)', 'the value exactly as printed in the PDF (— = shown as a dash)', 'as printed'),
    ('analysis/pdf_values/<test>.csv', 'where', 'PDF 파일 · 쪽 · 그림 위치', 'PDF file, page and panel', ''),
    ('analysis/output/<test>/numbers.csv', 'key', '분석 코드가 계산한 값의 이름 (check.* = 내부 점검)', 'name of a computed value (check.* = internal checks)', ''),
    ('analysis/output/<test>/numbers.csv', 'value', '계산한 값 (반올림 안 함)', 'computed value, full precision', ''),
    ('analysis/output/<test>/pdf_comparison.csv', 'test', '검사', 'test', ''),
    ('analysis/output/<test>/pdf_comparison.csv', 'key', 'pdf_values 의 key', 'key from pdf_values', ''),
    ('analysis/output/<test>/pdf_comparison.csv', 'pdf', 'PDF 값', 'value printed in the PDF', ''),
    ('analysis/output/<test>/pdf_comparison.csv', 'computed', 'CSV 에서 다시 계산한 값을 PDF 와 같은 자릿수로 쓴 것', 'recomputed value formatted like the PDF value', ''),
    ('analysis/output/<test>/pdf_comparison.csv', 'match', '1 = 글자까지 같음 · 0 = 다름', '1 = identical text, 0 = different', '0/1'),
    ('analysis/output/<test>/pdf_comparison.csv', 'where', 'PDF 위치', 'location in the PDF', ''),
    ('analysis/output/verification_summary.csv', 'test', '검사', 'test', ''),
    ('analysis/output/verification_summary.csv', 'pdf', '대조한 PDF', 'PDF compared', ''),
    ('analysis/output/verification_summary.csv', 'pdf_values', '대조한 값 수', 'number of PDF values compared', 'count'),
    ('analysis/output/verification_summary.csv', 'identical', '같은 값 수', 'identical values', 'count'),
    ('analysis/output/verification_summary.csv', 'different', '다른 값 수', 'different values', 'count'),
    ('analysis/output/verification_summary.csv', 'figure_pages', '다시 그린 그림 쪽 수', 'figure pages redrawn', 'count'),
    ('analysis/output/verification_summary.csv', 'internal_checks', '내부 점검 결과 (예: 다시 낸 역치와 앱 역치가 다른 측정 수)', 'internal checks (e.g. runs whose recomputed threshold differs from the app value)', ''),
    ('analysis/output/verification_summary.csv', 'seconds', '걸린 시간 (실행할 때마다 조금씩 다름)', 'run time (differs a little on every run)', 's'),
    ('data/raw/redaction_log.csv', 'file', '고친 원본 파일 (data/raw 안)', 'raw file changed (inside data/raw)', ''),
    ('data/raw/redaction_log.csv', 'json_path', '바꾼 값의 JSON 위치 ([] = 배열의 모든 원소)', 'JSON path of the replaced value ([] = every array element)', ''),
    ('data/raw/redaction_log.csv', 'rule', '적용한 규칙', 'rule applied', ''),
    ('data/raw/redaction_log.csv', 'what_was_removed', '지운 것', 'what was removed', ''),
    ('data/raw/redaction_log.csv', 'replaced_with', '대신 넣은 글자', 'replacement text', ''),
    ('data/raw/redaction_log.csv', 'n_values', '바꾼 값 수', 'number of values replaced', 'count'),
    ('data/raw/stimulus_file_hashes/<list>.csv', 'file_name', '공식 소리 파일 이름 (배포본 안의 이름 그대로)', 'name of the official sound file, as in the distribution', ''),
    ('data/raw/stimulus_file_hashes/<list>.csv', 'sha256', '그 파일의 SHA-256 (소문자 16진수 64자)', 'SHA-256 of the file (64 lowercase hex digits)', ''),
    ('data/raw/stimulus_file_hashes/<list>.csv', 'source', '받은 곳 · 판 (배포처, 판 번호, commit 또는 zip 해시)', 'where the file comes from (distribution, version, commit or zip hash)', ''),
]


def possible(values, col):
    vals = [v for v in values if v != '']
    blank = len(values) - len(vals)
    if not vals:
        return 'always blank'
    d = sorted(set(vals))
    try:
        nums = [float(v) for v in vals]
        isnum = True
    except ValueError:
        isnum = False
    if col in ('run_id', 'session_id', 'reversal_values', 'reversal_trial_nos', 'time_kst', 'start_time_kst', 'end_time_kst', 'key', 'json_path'):
        s = f'{len(d)} distinct values, e.g. {d[0]}'
    elif isnum and len(d) > 12:
        s = f'{min(nums):g} to {max(nums):g} ({len(d)} distinct)'
    elif len(d) <= 12:
        s = ' | '.join(d)
    else:
        s = f'{len(d)} distinct values, e.g. ' + ' | '.join(d[:3])
    return s + ('; blank allowed' if blank else '')


rows = []
for kind, spec in (('trials', TRIALS), ('runs', RUNS)):
    for t in TESTS:
        path = os.path.join(ROOT, 'data', kind, f'{t}_{kind}.csv')
        data = list(csv.DictReader(open(path, encoding='utf-8')))
        cols = list(data[0].keys())
        assert cols == list(spec.keys()), (path, cols)
        for c in cols:
            ko, en, unit = spec[c]
            if c in ('value',) or (kind == 'runs' and c in ('threshold', 'reversal_values')):
                ko, en = ko + ' — ' + UNIT_NOTES[t][0], en + ' — ' + UNIT_NOTES[t][1]
            rows.append([f'data/{kind}/{t}_{kind}.csv', c, ko, en, unit, possible([r[c] for r in data], c)])
for f, c, ko, en, unit in OTHER:
    sample = sorted(glob.glob(os.path.join(ROOT, f.replace('<test>', '*').replace('<list>', '*'))))
    vals = []
    for p in sample:
        vals += [r[c] for r in csv.DictReader(open(p, encoding='utf-8'))]
    pv = 'positive number of seconds (differs between runs)' if c == 'seconds' else (possible(vals, c) if vals else '')
    rows.append([f, c, ko, en, unit, pv])
# every column of every CSV in the package must be described
covered = {}
for f, c, *_ in rows:
    covered.setdefault(f, set()).add(c)
for p in glob.glob(os.path.join(ROOT, '**', '*.csv'), recursive=True):
    rel = os.path.relpath(p, ROOT).replace(os.sep, '/')
    if rel == 'data/data_dictionary.csv':
        continue
    keys = [k for k in covered if k == rel or re.fullmatch(re.escape(k).replace('<test>', '[a-z]+').replace('<list>', '[^/]+'), rel)]
    head = next(csv.reader(open(p, encoding='utf-8')))
    assert keys, f'not described: {rel}'
    assert set(head) <= set().union(*(covered[k] for k in keys)), f'columns not described: {rel} {set(head)}'
with open(os.path.join(ROOT, 'data', 'data_dictionary.csv'), 'w', encoding='utf-8-sig', newline='') as fh:
    w = csv.writer(fh, lineterminator='\n')
    w.writerow(['file', 'column', 'meaning_ko', 'meaning_en', 'unit', 'possible_values'])
    w.writerows(rows)
print(len(rows), 'rows')

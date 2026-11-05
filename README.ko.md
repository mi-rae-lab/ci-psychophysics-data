# 인공와우 정신물리 검사 7가지 — 공개용 원자료

English version: [README.md](README.md)

- 참가자 1명 (기호 **P01**), 양쪽 인공와우 사용자. 이 검사들을 위해 만든 브라우저 검사 앱으로 스스로 측정함.
- 소리는 스피커를 거치지 않고, 모든 검사에서 컴퓨터의 USB-C 포트 → USB-C 스트리머 케이블(유선) → 외부 음성처리기로 바로 보냄.
  앱 기록의 경로 이름은 앱마다 다름: ‘유선스트리머’(TMTF · SMRT), ‘유선→무선 스트리머’(STM · SRD · GDT · SMD; 경로 종류는 모두
  `wired_streamer`). 이름만 다를 뿐 일곱 검사 모두 같은 유선 스트리머 연결을 썼음(참가자 확인).
  인용한 논문들의 음장(스피커) 측정과 제시 조건이 다르므로 원 논문의 재현이 아님. 음성처리기 설정(코딩 전략 · 자극률 · AGC 등)은
  참가자도 모름.
- 한 사람의 반복 측정이므로 측정 · 시행은 독립된 참가자가 아님. 모집단 추론에 쓰지 않음.

## 폴더

```
README.md                      영어 설명
README.ko.md                   한국어 설명 (이 파일)
data/
  trials/<test>_trials.csv     시행 단위 (한 줄 = 한 시행) — 7개
  runs/<test>_runs.csv         회차(측정) 단위 요약 (한 줄 = 한 측정) — 7개
  raw/<test>/                  앱이 저장한 원래 기록 (개인정보만 지움)
  raw/redaction_log.csv        원래 기록에서 바꾼 값의 위치와 개수
  raw/stimulus_file_hashes/    공식 소리 파일의 SHA-256 목록 (소리 파일 자체는 넣지 않음)
  data_dictionary.csv          모든 CSV 의 열 이름 · 뜻 · 단위 · 가능한 값
analysis/
  reproduce.py                 trials · runs CSV 만으로 PDF 의 역치 · 평균 · SD · 그림을 다시 만들고 PDF 값과 대조
  common.py, tmtf.py … smd.py  검사별 계산 · 그림
  pdf_values/<test>.csv        PDF 에 찍힌 값과 쪽 · 그림 위치 (대조용으로 옮겨 적은 것; PDF 파일 자체는 이 묶음에 없음)
  output/                      위 코드를 실제로 돌린 결과 (대조표 · 다시 그린 그림 · VERIFICATION.md)
  build/                       원래 기록 → CSV 를 만든 스크립트
  requirements.txt
verification/lean4/            검사 앱 로직의 Lean 4 증명 · 빌드 기록 · 공리 검사 · 검증 보고서
SHA256SUMS.txt                 이 묶음 안 모든 파일의 SHA-256
LICENSE                        코드 라이선스 — MIT
LICENSE-DATA.md                데이터 · 문서 라이선스 — CC BY 4.0
```

## 파일과 개수

| 검사 | 시행 줄 | 제외 줄 | 측정 줄 | 분석 포함 측정 | 그중 숫자 값이 있는 측정 | 날짜 (KST) | 귀 L / R (시행 줄) |
|---|---:|---:|---:|---:|---:|---|---|
| TMTF 시간 변조 탐지 | 5,841 | 20 | 157 | 150 | 123 | 10-11 – 11-04 (7일) | 1,050 / 4,791 |
| SMRT 스펙트럼 리플 | 1,171 | 274 | 45 | 33 | 33 | 10-15 – 11-03 (5일) | 376 / 795 |
| STRIPES | 238 | 146 | 12 | 3 | 3 | 10-16 – 11-02 (3일) | 104 / 134 |
| STM 스펙트럼-시간 변조 탐지 | 1,370 | 0 | 27 | 27 | 27 | 10-18 – 10-19 (2일) | 720 / 650 |
| SRD 정적 리플 변별 | 688 | 13 | 18 | 17 | 15 | 10-21 – 11-02 (3일) | 261 / 427 |
| GDT 간격 탐지 | 971 | 105 | 30 | 25 | 18 | 11-01 – 11-03 (3일) | 0 / 971 |
| SMD 스펙트럼 변조 탐지 | 713 | 0 | 13 | 13 | 9 | 11-02 (1일) | 0 / 713 |
| 합계 | **10,992** | **558** | **302** | **268** | **228** | | |

‘숫자 값’ = 역치 또는 Blankenship 논문 방식 값. 숫자가 없는 측정 — TMTF 측정 불가(0 dB 에서 누적 4번 틀림),
SRD 쉬운 끝 막힘(`threshold_near_easy_end`), GDT 짧은 끝 막힘(`threshold_near_floor`), SMD 수렴 안 됨(`threshold_above_window`:
분석 구간 정답률이 목표 70.7 % 보다 낮다고 확인됨, 끝에 닿지 않음), 고정 자극(QSMD · 멈춘 SRD 임상 측정) — 은 `threshold` 가 빈칸이고
`no_threshold_reason` 에 이유가 있음.

## 시행 CSV (`data/trials`)

열 28개, 일곱 파일 모두 같은 순서. 값은 ASCII 문자만(± → `+/-`). 열의 뜻 · 단위 · 가능한 값은 `data/data_dictionary.csv`.
요청한 열과의 대응:

| 요청한 것 | 열 |
|---|---|
| 검사 이름 · 프로토콜/조건 · 귀 | `test` · `protocol`, `condition` · `ear` (L/R) |
| 날짜 · 시각 (KST) | `date_kst`, `time_kst` (밀리초까지), `time_source` |
| 회차 ID · 회차 안 시행 번호 | `run_id` (측정), `session_id` (회기) · `run_trial_no`, `session_trial_no` |
| 제시한 값과 단위 | `value`, `unit` |
| 목표 구간 · 고른 구간 · 정답 여부 | `target_interval` · `response_interval` (+ 앱이 채점한 `scored_interval`) · `correct` |
| 반전 여부 | `reversal`, `reversal_no` |
| ‘확신 없음’ 표시 | `unsure` (‘모르겠음’ 단추, TMTF · SMRT 에만 있음) |
| 편향 · 천장 · 하한 표시 | `at_limit`, `blocked_at_limit` (easy = 쉬운 끝/천장, hard = 어려운 끝/하한), `run_status`, `run_flags` (interval_bias · response_bias · near_ceiling · near_floor · at_chance …) |
| 제외됨 · 제외 이유 | `excluded`, `exclusion_reason` |

## 측정 CSV (`data/runs`)

열 31개, 일곱 파일 모두 같은 순서. 회차 ID · 검사 · 조건 · 귀 · 날짜 · 시행 수(`n_trials`, `n_responses`) · 반전 값들
(`reversal_values`, 순서대로 `;` 로 이음) · 역치(`threshold`, 없으면 빈칸) · 역치가 없는 이유(`no_threshold_reason`) ·
분석 포함/제외(`included`, `exclusion_reason`) 와 함께 역치 규칙(`threshold_rule`), 앱 상태 · 표시, 오디오 표본률, 앱 판,
원래 기록 위치(`source`) 가 있음. 개수 · 날짜 · 반전 값은 시행 CSV 에서, 역치 · 상태 · 표시는 앱이 저장한 값에서 옴.

## 제외 표시

시행은 하나도 지우지 않았고 `excluded = 1` 과 이유로 표시함. 측정 CSV 의 `included = 0` 도 같은 규칙.

| 이유 | 검사 · 시행 줄 수 |
|---|---|
| 연습 | TMTF 연습 시행 15 (0 dB 고정, 계단 아님 — 측정 ID `<session_id>-practice`) · SMRT 연습 측정 12개 274 · STRIPES 연습 측정 2개 62 |
| 예시 — 정답을 보여 줌 | STRIPES 24 |
| 통과 검사 (피드백 있는 짧은 확인, 역치 계단 아님) | STRIPES 37 |
| 끝 규칙 전에 참가자가 멈춘 측정 (역치 없음) | TMTF 5 (255 Hz, 앱이 버린 측정 `<session_id>-discarded-1`) · STRIPES 36 · SRD 13 (임상 72문제 중 12문제에서 멈춤) · GDT 4 |
| 답하기 전에 멈춘 시행 (답 칸 빈칸) | STRIPES 2 · SRD 1 · GDT 2 (위 ‘멈춘 측정’ 줄에 들어 있음) |
| 앱 기록에서 지운 측정 | GDT 2026-11-01 Xie 측정 3개 101시행 (11-03 참가자 요청: “프로그램 오류가 있었어”. 그날 기록 점검에서는 앱 오류를 찾지 못함 — 빼는 것은 참가자 판단. 원래 기록은 `data/raw/gdt/deleted_runs_2026-11-03/`) |

한 줄에 이유가 여럿일 수 있음: STRIPES 는 참가자가 멈춘 통과 검사 측정 안의 예시 6줄 · 통과 검사 7줄이 ‘멈춘 측정 36’ 에도
들어 있어(13줄 겹침) 위 숫자를 더하면 159 지만 제외 줄은 146.

넣지 못한 것: TMTF 10-11 23:12 150 Hz 측정 1개(35시행 뒤 멈춤; 그때 앱 판이 버린 측정의 시행을 저장하지 않아 측정 CSV 에
`n_trials = 0` 인 줄로만 있음) · TMTF 10-24 00:22–00:27 시험 회기 11개(참가자가 “테스트일 뿐 … 시행에 제외해” 라고 한
회기, 측정 · 시행 없음 — `data/raw/tmtf/db.json` 의 sessions 에 excluded 표시로 남음) · 답을 받지 않는 ‘예시 듣기’ 소리.

## 분석 코드 — 실행 방법

Python 3 (3.10.11 에서 확인), 라이브러리는 numpy · matplotlib 만 (`analysis/requirements.txt`).

```
pip install -r analysis/requirements.txt
python analysis/reproduce.py              # 일곱 검사 모두 (약 35초)
python analysis/reproduce.py smrt gdt     # 고른 검사만 (VERIFICATION.md · verification_summary.csv 는 일곱 검사를 다 돌릴 때만 새로 씀)
```

값은 `data/trials/*.csv` 와 `data/runs/*.csv` 만으로 계산함(원래 JSON 은 읽지 않음; `analysis/pdf_values/*.csv` 는 PDF 값과
대조할 때만 읽음). 역치는 앱 값을 옮겨 쓰지 않고 시행 CSV 의
반전 값에서 다시 냄(규칙은 측정 CSV `threshold_rule`). 숫자가 있는지 없는지(측정 불가 · 끝 막힘 등)는 앱이 정한 상태
(`run_status` / `app_status`)를 그대로 씀 — PDF 도 같은 방식. 결과는 `analysis/output/<test>/`:
`numbers.csv`(계산한 값 전부) · `pdf_comparison.csv`(PDF 값과 나란히) · `figures/`(여러 쪽 PDF + 쪽마다 PNG),
그리고 전체 요약 `analysis/output/VERIFICATION.md` · `verification_summary.csv`. 다시 돌려도 결과 파일은 바이트까지 같음
(`verification_summary.csv` 의 걸린 시간 칸만 다름).

## 검사 앱 로직의 형식 검증 (Lean 4)

`verification/lean4/` 에는 일곱 검사 앱마다 계단 규칙 · 측정 판정 · 자극 수식을 Lean 4 로 옮긴 프로젝트와 그 빌드 기록,
공리 검사(`print-axioms.txt`), 검증 보고서가 있음. 일곱 프로젝트 모두 빌드되고, 목록의 어느 정리도 `sorry` 나 Lean 의
표준 공리 세 개(`propext` · `Classical.choice` · `Quot.sound`) 밖의 공리에 기대지 않음. TMTF · SRD · GDT · SMD 는 생성한
입력으로 앱의 JavaScript 와 줄 단위 대조도 함. 앱 자체의 로직만 다루며, 브라우저의 소리 출력 · 스트리머 · 음성처리기 ·
인공와우는 다루지 않음. 자세한 내용은 [verification/lean4/README.md](verification/lean4/README.md).

## 검증 결과 — PDF 와 같은가

2026-11-05 에 이 묶음 그대로 `python analysis/reproduce.py` 를 돌린 결과 (Python 3.10.11 · numpy 2.2.6 · matplotlib 3.10.9).
대조한 PDF 7종(영어판 · 한국어판)은 이 묶음에 들어 있지 않음 — PDF 에 찍힌 값과 그 쪽 · 그림 위치를 `analysis/pdf_values/` 에 옮겨 둠.

| 검사 | 대조한 PDF | PDF 값 | 같음 | 다름 | 다시 그린 쪽 |
|---|---|---:|---:|---:|---:|
| TMTF | TMTF_English.pdf / TMTF_Korean.pdf | 519 | 519 | 0 | 6 |
| SMRT | Figure1_SMRT_detailed_EN.pdf / _KO.pdf | 86 | 86 | 0 | 1 |
| STRIPES | STRIPES_scientific_figures_EN.pdf / _KO.pdf | 45 | 45 | 0 | 3 |
| STM | STM_Scientific_EN.pdf / _KO.pdf | 301 | 301 | 0 | 5 |
| SRD | SRD_scientific_EN.pdf / _KO.pdf | 133 | 133 | 0 | 7 |
| GDT | GDT_scientific_EN.pdf / _KO.pdf | 152 | 152 | 0 | 8 |
| SMD | SMD_scientific_EN.pdf / _KO.pdf | 154 | 154 | 0 | 6 |
| 합계 | | **1,390** | **1,390** | **0** | 36 |

- ‘같음’ = 다시 낸 값을 PDF 에 찍힌 자릿수로 썼을 때 글자까지 같음. 값은 역치 · 평균 · SD · n · 시행 수 · 반전 수 · 반전 값 ·
  정답/시행 · 비율 · 측정 ID · 시각 · 표시(†, IB/NC) 등이며 `analysis/pdf_values/` 에 PDF 글자층에서 옮겨 적음.
  영어판과 한국어판 PDF 의 숫자는 같음(다른 것은 날짜 표기와 문장 속 정수뿐)이라 영어판으로 대조함.
- 각 측정의 다시 낸 역치 = 앱이 저장한 역치: 모든 검사에서 다른 측정 0개 (`internal_checks`).
- 그림은 같은 자료 · 같은 패널을 다시 그린 것이며 모양(색 · 글꼴 · 배치)까지 같지는 않음.

PDF 와 맞추며 알게 된 점 (코드에 반영):
- **TMTF PDF 는 2026-11-03 까지의 기록(측정 142개)으로 만든 것.** 11-04 측정 8개(56–59 Hz)는 CSV 에는 있지만 PDF 에는 없어
  `tmtf.py` 의 `PDF_LAST_DATE` 로 뺌 (`None` 으로 바꾸면 넣음). TMTF 앱은 역치를 0.01 dB 로 반올림해 저장하고 PDF 는 그 값을 평균함.
- **SMRT** 앱은 역치를 0.0001 RPO 로 반올림해 저장하고 PDF 의 SD 는 그 저장값으로 낸 것 (예: 10-22 오른쪽 SD 반올림 전 값이면 0.797, PDF 0.796).
- **SRD** 앱은 반전 값을 1/1000 RPO 정수로 더함 — 그렇게 해야 0.96025 가 0.9603 이 됨 (실수로 더하면 0.9602).
- **SMD** PDF 는 정확히 반인 값을 올림 (2 c/o 평균 (25.70 + 16.95)/2 = 21.325 → 21.33; 파이썬 기본 서식은 21.32). SMD 대조만 그 규칙을 씀.
- 각 PDF 가 다룬 범위: SMRT = 본 측정 33개(연습 제외) · STRIPES = 10-16 의 끝까지 간 본 측정 3개 · STM = 27개 전부 ·
  SRD = 숫자 역치 15개 + 상태만 있는 2개 (멈춘 임상 측정 제외) · GDT = 25개 (지운 3 · 멈춘 2 제외) ·
  SMD = 적응 측정 12개 (같은 밤 QSMD 60문제는 PDF 에 없음 → `numbers.csv` 에만 57/60).

대조하지 않은 것 (자료에서 계산하는 값이 아님): 방법 설명의 설계 상수(소리 길이 · 성분 수 · 주파수 범위 · 시작 값 · 걸음 등 —
`protocol` 열에 있음), 문헌 기준선(STM 의 Won 2015 평균선, SRD 의 Winn & O'Brien 2022 범위), GDT 의 ‘3.5355 ms → 3.5417 ms’
표본 반올림 예시(표본 수는 원래 기록 `gapN` 에만 있음), TMTF 의 ‘코드 기록상 예전 21개는 경사 전 정규화’ 설명(코드 기록에서 온 것),
GDT PDF 가 적은 자기 원본 파일 해시.

## 원래 기록 (`data/raw`)

앱의 `data` 폴더를 2026-11-04 23:33 KST 에 복사한 사본에서 가져옴(앱 기록은 읽기만 함; 2026-11-05 에 앱 기록이 그 사본과
바이트까지 같음을 확인). 앱 폴더 → 이 폴더: 와우TMTF → `tmtf`, 와우SMRT → `smrt`, 와우STRIPES → `stripes`, 와우STM → `stm`,
와우SRD → `srd`, 와우GDT → `gdt`, 와우SMD → `smd`.

- `db.json` = 앱의 기록 (회기 · 측정 · 시행 · 판단 기록 전부). `runs-log.jsonl` = 측정 · 회기가 끝날 때마다 덧붙여 쓰는 기록
  (SMRT 10-20 00:26 회기의 연습 측정 1개는 db.json 측정 목록에는 없고 여기에만 있음). `journal/*.jsonl` = 측정마다 시행을
  하나씩 적은 기록(새 틀 다섯 앱). `gdt/deleted_runs_2026-11-03/` = 지운 GDT 측정 3개의 원래 기록과 설명 (그 안의 README.txt 는 원래
  폴더 설명 그대로라 `db.before.json` · `backup\` · `db.prev.json` 을 적고 있지만, 그 파일들은 이 묶음에 넣지 않음).
- 넣지 않은 것: `backup/`(db.json 의 예전 사본들), `db.prev.json`(바로 앞 판), GDT 지운 기록의 `db.before.json`(지우기 직전
  db.json 전체 사본) — 모두 같은 기록의 다른 판이라 뺌.
- 원래 기록 → CSV: `analysis/build/build_trials.py` · `build_runs.py` 가 이 폴더만으로 `data/trials` · `data/runs` 를 다시 만들며,
  결과는 이 묶음의 CSV 와 바이트까지 같음 (TMTF 10-11 측정 45개는 시행마다 반전이 기록되지 않아, 앱 계단 코드
  `js/track.js` 를 파이썬으로 옮겨 기록된 정오로 다시 돌린 값 — 기록된 제시 값과 반전 값이 모두 맞음).
  `make_dictionary.py` 는 열 설명표를 만듦. `sanitize_raw.py` 는 개인정보를 지운 규칙(아래)이며 원래 앱 폴더가 있어야 돌아감.

## 지운 개인정보

원래 기록의 글자 중 아래 값만 바꿨고, 그 밖의 바이트는 그대로임 (바꾼 뒤 모든 파일을 다시 읽어 값 하나하나를 원래와 대조함).
위치와 개수는 `data/raw/redaction_log.csv`.

| 지운 것 | 어디 | 바꾼 값 수 | 바꾼 글자 |
|---|---|---:|---|
| Windows 오디오 출력 장치 고유 ID (endpoint GUID) | `winStart/winEnd/routeChecks.endpointId`, `pres.win.endpoint`, `presKey`, `presRefKey` (TMTF 를 뺀 6개 앱) | 1,973 | `{0.0.0.00000000}.{redacted-audio-endpoint-guid}` |
| USB 오디오 어댑터의 장치 인스턴스 ID | `hardwareId` 의 마지막 부분 (제품 종류 번호 VID/PID 는 일반 USB 오디오라 남김) | 959 | `redacted-usb-instance-id` |
| 참가자 코드 (앱에 입력한 코드, 한 앱은 이식 기기 이름을 코드로 씀) | `participants[].code`, `participantSnap.code` | 283 | `P01` |
| 컴퓨터 사용자 이름이 든 폴더 경로 | STM 기록의 다시 판정한 이유 글 (`runs[].resultHistory[].reason` · `sessions[].events[].reason` · journal `data.reason`) | 56 | `c-users-[redacted]-…` |

찾아봤지만 기록에 없던 것: 이름 · 이메일 · 컴퓨터 이름 · 사용자 이름이 든 절대 경로(`C:\Users\…`) · 음성처리기 일련번호와
제조사 · 모델 · 맵 · 이식일 칸(앱에 칸은 있으나 모두 빈칸) · 병원 · 임상시험 참여자 번호 · USB 기기 일련번호.
인공와우 기기 이름은 참가자 코드 칸에만 있었고 위에서 `P01` 로 바꿈 — 기록 어디에도 남지 않음.
남긴 것 (사람이나 기기 하나를 가리키지 않음): 앱이 무작위로 만든 ID(참가자 · 회기 · 측정 · 시행), 브라우저 user-agent
(Chrome 판 · Windows), OS · 파이썬 판, 화면 해상도(`env.screen`), ‘스피커’ · ‘USB Audio’ 같은 일반 장치 이름,
USB 오디오 어댑터의 제품 종류 번호(VID/PID, 같은 제품이면 모두 같음), Windows 표준 오디오 효과 GUID(`fxRaw`, 모든 Windows 에서
같은 값), 참가자 정보 칸의 group `CI` · onset `post` · screen `audiogram`(나이 등 나머지는 빈칸), 사용자 이름이 없는 상대 경로
(`Documents/Codex/…/c-users-[redacted]-stm/…`, `Desktop\byrne1994.pdf`), 기록에 적힌 도구 이름(Claude · Codex),
참가자가 직접 쓴 판단 · 정정 · 단서 글(이름 · 장소 · 다른 사람 없음), 날짜 · 시각.

## 공식 소리 파일 (넣지 않음)

| 검사 | 쓴 파일 | 받은 곳 · 판 | 이 묶음에 있는 것 |
|---|---|---|---|
| SMRT | 공식 프로그램의 `Wave` 폴더 WAV 804개 (0.0–20.0 RPO × 0.1, 위상 4개, 44.1 kHz 16비트) | SMRT 1.1.3 (Landsberger & Aronoff, House Ear Institute), https://www.ear-lab.org/smrt.html 무료 Windows 프로그램 (2026-10-15 받음) | `stimulus_file_hashes/smrt_1.1.3_Wave_sha256.csv` |
| STRIPES | webSTRIPES 음원 bank MP3 3,800개 (D 1.1–20.0 × 위/아래 × rove 10, 96 kb/s) + `calibration_sound.wav` · `silence_30s.mp3` | webSTRIPES (Archer-Boyd, Harland, Goehring & Carlyon, MRC CBU · University of Cambridge), https://gitlab.developers.cam.ac.uk/chg/bob/webstripes commit `2743c07f2056a2bb0d137f99a52c4b0c674d39e7` (2023-04-20), MIT 라이선스 | `stimulus_file_hashes/stripes_webstripes_2743c07_audio_sha256.csv` |
| SMD (QSMD) | EasyQSMD 1.0 의 Electric WAV 60개 | EasyQSMD 1.0 (Landsberger 2019), www.ear-lab.org/EasyQSMD 배포 zip (SHA-256 `b469560d…08bd9a`) | `stimulus_file_hashes/qsmd_EasyQSMD_1.0_Electric_sha256.csv` (시행 기록의 파일 해시와 60/60 같음) |

TMTF · STM · SRD · GDT · SMD(적응) 의 소리는 앱이 시행마다 합성했고, 합성에 쓴 값(씨앗 · 위상 등)은 원래 기록에 있음.

## 읽을 때 알아 둘 것

- **시각** = 한국 시각(UTC+9), 시행이 시작된(소리를 예약한) 시각. TMTF 10-11 저녁 첫 측정 21개(20:06–21:18 에 끝남, 앱 2.x 판)는
  시행 시각 · 회기가 기록되지 않던 때라 측정이 끝난 시각을 넣고 `time_source = run_end`. 답 전에 멈춘 시행은 멈춘 시각.
- **귀 고침**: TMTF 11-01 23:27 · 11-02 00:06 회기(측정 5개)와 SMRT 11-03 20:19–20:31 회기 2개(측정 8개)는 오른쪽 귀로
  검사했지만 앱에 왼쪽(L)으로 잘못 입력한 것이라, 참가자 요청으로 앱 기록의 귀를 L → R 로 고침. CSV 는 고친 값(R). 원래 값과 고친 까닭은 원래 기록에 남음(TMTF `earOriginal` · `corrections`, SMRT `fixes`).
- **‘모르겠음’** 은 TMTF · SMRT 에만 있는 단추. 앱은 그 시행을 구간 중 무작위 하나로 채점함(`scored_interval`, `correct`;
  `response_interval` 은 빈칸). 참가자는 2026-11-02 무렵부터 정말 구별할 수 없을 때만 이 단추를 누름.
- **반전 · 끝 표시**는 앱 기록 그대로 (SMRT · TMTF 3.1 판 이후 = 앱이 기록한 반전 위치, 새 틀 다섯 앱 = 시행마다 기록한 반전 ·
  막힘). 예외로 TMTF 10-11 측정 45개는 시행마다 반전이 기록되지 않아 앱 계단 코드를 기록된 정오로 다시 돌린 값이며
  (위 ‘원래 기록 → CSV’), 앱이 직접 내보낸 시행 CSV 의 반전 칸과 같음을 확인함. TMTF 는 0 dB 에서 막힌 요청(더 쉽게 가려다
  못 감)도 방향으로 세어 반전을 정하고, STRIPES · STM · SRD · GDT · SMD 는 막힌 이동을 이동 · 반전으로 세지 않음.
- **제시 설정**(Windows 볼륨 · 출력 장치 · 처리기 프로그램 등)은 CSV 에 없고 원래 기록에 있음. 회기마다 다를 수 있으니 회기 · 날짜를 비교할 때 주의.
- `run_status` · `run_flags` 는 측정 하나 전체에 대한 앱 판정을 그 측정의 모든 시행 줄에 똑같이 적은 것.

## 2026-11-04 시행 묶음과 다른 점

`CI_psychophysics_trials_2026-11-04.zip` 의 시행 CSV 와 비교해 TMTF 의 20줄에만 `run_id` 를 채움(연습 시행 15줄 =
`<session_id>-practice`, 버린 255 Hz 측정 5줄 = `<session_id>-discarded-1`; 예전엔 빈칸). 다른 값 · 다른 여섯 파일은 바이트까지 같음.
참가자 기호는 이 묶음부터 중립 기호 `P01` 을 씀 (11-04 묶음의 README 에 적힌 기호와 다름).

## 라이선스

- 데이터 · 문서 (`data/`, `analysis/pdf_values/`, `analysis/output/`, `README.md` · `README.ko.md`): **CC BY 4.0** — `LICENSE-DATA.md`.
  출처(이 데이터와 저장소 링크)와 라이선스를 밝히고, 바꾼 것이 있으면 바꿨다고 적으면 누구나 쓰고 나누고 고칠 수 있음.
- 코드 (`analysis/*.py`, `analysis/build/*.py`, `verification/lean4/` 안의 Lean · JavaScript · Python · PowerShell 소스): **MIT** — `LICENSE`.
  `verification/lean4/` 의 빌드 기록 · 공리 검사 출력 · 보고서는 CC BY 4.0.
- 공식 소리 파일은 이 묶음에 없고 각 배포처의 조건을 따름 (위 ‘공식 소리 파일’).

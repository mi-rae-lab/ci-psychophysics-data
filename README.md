# Cochlear-implant psychophysics: open data from seven tests

Raw data from seven psychophysical tests (TMTF, SMRT, STRIPES, STM, SRD, GDT, SMD), self-administered by one
bilateral cochlear-implant user between 2026-10-11 and 2026-11-04 (KST).

한국어 설명: [README.ko.md](README.ko.md)

## What this is

- One participant (label **P01**), a bilateral cochlear-implant user, testing themself with browser test apps built
  for these tests.
- Sound did not go through a loudspeaker. In every test it went from the computer's USB-C port over a USB-C streamer
  cable (wired) straight into the external sound processor. The apps store a route name for this connection, and the
  name differs between apps: "유선스트리머" ("wired streamer") in TMTF and SMRT, and "유선→무선 스트리머"
  ("wired→wireless streamer") in STM, SRD, GDT and SMD (route type `wired_streamer` in all of them). Only the names
  differ; the participant confirms that the same wired streamer connection was used in all seven tests.
- Because the sounds were presented this way, and not in a sound field as in the cited papers, these are **not
  replications** of the original studies. The processor settings (coding strategy, stimulation rate, AGC and so on)
  are unknown to the participant.
- These are repeated measurements of one person, so runs and trials are not independent participants. Do not use
  them for population inference.

## Folders

```
README.md                      this file (English)
README.ko.md                   Korean version
data/
  trials/<test>_trials.csv     trial level (one row = one trial), 7 files
  runs/<test>_runs.csv         run level summary (one row = one run), 7 files
  raw/<test>/                  the apps' original records (identifying values removed)
  raw/redaction_log.csv        where values in the original records were replaced, and how many
  raw/stimulus_file_hashes/    SHA-256 lists of the official sound files (the sound files themselves are not included)
  data_dictionary.csv          name, meaning, unit and allowed values of every column in every CSV
analysis/
  reproduce.py                 recomputes thresholds, means, SDs and figures from the trial and run CSVs alone,
                               and compares them with the values printed in the PDF figure sets
  common.py, tmtf.py … smd.py  per-test calculations and figures
  pdf_values/<test>.csv        values printed in the PDFs, with page and panel (transcribed for the comparison;
                               the PDFs themselves are not in this package)
  output/                      results of actually running the code above (comparison tables, redrawn figures,
                               VERIFICATION.md)
  build/                       scripts that built the CSVs from the original records
  requirements.txt
SHA256SUMS.txt                 SHA-256 of every file in this package
LICENSE                        code license: MIT
LICENSE-DATA.md                data and documentation license: CC BY 4.0
```

## Files and counts

| Test | Trial rows | Excluded rows | Run rows | Runs in analysis | ...with a numeric value | Dates (KST) | Ear L / R (trial rows) |
|---|---:|---:|---:|---:|---:|---|---|
| TMTF temporal modulation detection | 5,841 | 20 | 157 | 150 | 123 | 10-11 – 11-04 (7 days) | 1,050 / 4,791 |
| SMRT spectral ripple | 1,171 | 274 | 45 | 33 | 33 | 10-15 – 11-03 (5 days) | 376 / 795 |
| STRIPES | 238 | 146 | 12 | 3 | 3 | 10-16 – 11-02 (3 days) | 104 / 134 |
| STM spectro-temporal modulation detection | 1,370 | 0 | 27 | 27 | 27 | 10-18 – 10-19 (2 days) | 720 / 650 |
| SRD spectral ripple discrimination | 688 | 13 | 18 | 17 | 15 | 10-21 – 11-02 (3 days) | 261 / 427 |
| GDT gap detection | 971 | 105 | 30 | 25 | 18 | 11-01 – 11-03 (3 days) | 0 / 971 |
| SMD spectral modulation detection | 713 | 0 | 13 | 13 | 9 | 11-02 (1 day) | 0 / 713 |
| Total | **10,992** | **558** | **302** | **268** | **228** | | |

"Numeric value" means a threshold or a Blankenship paper-method value. Runs without a number have an empty
`threshold` and the reason in `no_threshold_reason`: TMTF not measurable (four cumulative errors at 0 dB), SRD stuck
at the easy end (`threshold_near_easy_end`), GDT stuck at the short end (`threshold_near_floor`), SMD not converged
(`threshold_above_window`: the proportion correct in the analysis window was confirmed to be below the 70.7% target,
without reaching the end), and fixed-stimulus runs (QSMD, and the stopped SRD clinical run).

The counts in the accompanying write-up (for example 150 TMTF runs and 5,821 TMTF trials) use all records,
including those from 2026-11-04.

## Trial CSVs (`data/trials`)

28 columns, in the same order in all seven files. Values are ASCII only (± is written `+/-`). The meaning, unit and
allowed values of each column are in `data/data_dictionary.csv`.

| What | Columns |
|---|---|
| Test, protocol / condition, ear | `test`, `protocol`, `condition`, `ear` (L/R) |
| Date and time (KST) | `date_kst`, `time_kst` (to the millisecond), `time_source` |
| Run and session IDs, trial numbers | `run_id` (run), `session_id` (session), `run_trial_no`, `session_trial_no` |
| Presented value and unit | `value`, `unit` |
| Target interval, chosen interval, correct | `target_interval`, `response_interval` (plus `scored_interval`, as scored by the app), `correct` |
| Reversals | `reversal`, `reversal_no` |
| "Unsure" mark | `unsure` (the "don't know" button; TMTF and SMRT only) |
| Bias, ceiling and floor marks | `at_limit`, `blocked_at_limit` (easy = easy end / ceiling, hard = hard end / floor), `run_status`, `run_flags` (interval_bias, response_bias, near_ceiling, near_floor, at_chance, ...) |
| Excluded and why | `excluded`, `exclusion_reason` |

## Run CSVs (`data/runs`)

31 columns, in the same order in all seven files. Each row has the run ID, test, condition, ear, date, trial counts
(`n_trials`, `n_responses`), reversal values (`reversal_values`, in order, joined with `;`), the threshold
(`threshold`, empty if there is none), why there is no threshold (`no_threshold_reason`), whether the run is included
(`included`, `exclusion_reason`), the threshold rule (`threshold_rule`), the app's status and flags, the audio sample
rate, the app version and the location in the original records (`source`). Counts, dates and reversal values come
from the trial CSVs; thresholds, status and flags come from the values the apps stored.

## Exclusions

No trial was removed. Excluded trials are marked `excluded = 1` with a reason, and `included = 0` in the run CSVs
follows the same rule.

| Reason | Test: trial rows |
|---|---|
| Practice | TMTF 15 practice trials (fixed at 0 dB, not a staircase; run ID `<session_id>-practice`) · SMRT 12 practice runs, 274 · STRIPES 2 practice runs, 62 |
| Examples (answer shown) | STRIPES 24 |
| Pass checks (short checks with feedback, not threshold staircases) | STRIPES 37 |
| Runs stopped by the participant before the end rule (no threshold) | TMTF 5 (255 Hz, a run the app discarded, `<session_id>-discarded-1`) · STRIPES 36 · SRD 13 (stopped after 12 of the 72 items of the clinical run) · GDT 4 |
| Trials stopped before an answer (empty response) | STRIPES 2 · SRD 1 · GDT 2 (counted in the row above) |
| Runs deleted from the app's records at the participant's request | GDT: three Xie runs from 2026-11-01, 101 trials. On 11-03 the participant asked for them to be deleted, saying "there was a program error". A check of the records that day found no app fault, so excluding them was the participant's own judgment. The original records were kept and are in `data/raw/gdt/deleted_runs_2026-11-03/`. |

A row can have more than one reason. In STRIPES, 6 example rows and 7 pass-check rows lie inside the stopped
pass-check runs and are also counted in "stopped runs: 36" (13 rows overlap), so the numbers above add up to 159 but
146 rows are excluded.

Not in the trial CSVs: one TMTF 150 Hz run on 10-11 at 23:12 (stopped after 35 trials; the app version at the time
did not save the trials of discarded runs, so it appears only as a run row with `n_trials = 0`); 11 TMTF test
sessions on 10-24 between 00:22 and 00:27 (sessions the participant described as "only a test ... exclude from the
trials"; they have no runs or trials and remain as excluded sessions in `data/raw/tmtf/db.json`); and listen-only
example sounds that were never answered.

## Analysis code: how to run

Python 3 (checked with 3.10.11); the only libraries are numpy and matplotlib (`analysis/requirements.txt`).

```
pip install -r analysis/requirements.txt
python analysis/reproduce.py              # all seven tests (about 35 s)
python analysis/reproduce.py smrt gdt     # selected tests only (VERIFICATION.md and verification_summary.csv are rewritten only when all seven run)
```

Values are computed only from `data/trials/*.csv` and `data/runs/*.csv`. The original JSON is not read, and
`analysis/pdf_values/*.csv` is read only for the comparison with the PDFs. Thresholds are not copied from the apps:
they are recomputed from the reversal values in the trial CSVs, using the rule in the run CSV's `threshold_rule`.
Whether a run has a number at all (not measurable, stuck at an end, and so on) follows the status the app assigned
(`run_status` / `app_status`), as the PDFs did. Results go to `analysis/output/<test>/`: `numbers.csv` (every computed
value), `pdf_comparison.csv` (side by side with the PDF values) and `figures/` (a multi-page PDF plus one PNG per
page), with an overall summary in `analysis/output/VERIFICATION.md` and `verification_summary.csv`. Re-running gives
byte-identical result files, except for the run-time column of `verification_summary.csv`.

## Verification: do the numbers match the PDFs?

Result of running `python analysis/reproduce.py` on this package as it is, on 2026-11-05 (Python 3.10.11, numpy
2.2.6, matplotlib 3.10.9). The seven PDF figure sets compared against (English and Korean editions) are not in this
package; the values printed in them, with page and panel, are in `analysis/pdf_values/`.

| Test | PDFs compared | PDF values | Match | Differ | Pages redrawn |
|---|---|---:|---:|---:|---:|
| TMTF | TMTF_English.pdf / TMTF_Korean.pdf | 519 | 519 | 0 | 6 |
| SMRT | Figure1_SMRT_detailed_EN.pdf / _KO.pdf | 86 | 86 | 0 | 1 |
| STRIPES | STRIPES_scientific_figures_EN.pdf / _KO.pdf | 45 | 45 | 0 | 3 |
| STM | STM_Scientific_EN.pdf / _KO.pdf | 301 | 301 | 0 | 5 |
| SRD | SRD_scientific_EN.pdf / _KO.pdf | 133 | 133 | 0 | 7 |
| GDT | GDT_scientific_EN.pdf / _KO.pdf | 152 | 152 | 0 | 8 |
| SMD | SMD_scientific_EN.pdf / _KO.pdf | 154 | 154 | 0 | 6 |
| Total | | **1,390** | **1,390** | **0** | 36 |

- "Match" means the recomputed value, written at the precision printed in the PDF, is exactly the same text. The
  values include thresholds, means, SDs, n, trial counts, reversal counts, reversal values, correct/trials,
  proportions, run IDs, times and marks (†, IB/NC), transcribed from the PDFs' text layer into `analysis/pdf_values/`.
  The numbers in the English and Korean PDFs are the same (only date formats and integers inside sentences differ),
  so the English editions were used.
- For every run, the recomputed threshold equals the threshold the app stored: no run differs in any test
  (`internal_checks`).
- The figures are redrawn from the same data with the same panels; colors, fonts and layout are not identical.

Things found while matching the PDFs (reflected in the code):

- **The TMTF PDF was made from records up to 2026-11-03 (142 runs).** The eight runs from 11-04 (56–59 Hz) are in
  the CSVs but not in that PDF, so `tmtf.py` leaves them out through `PDF_LAST_DATE` (set it to `None` to include
  them). The TMTF app stores thresholds rounded to 0.01 dB, and the PDF averaged those stored values.
- **SMRT**: the app stores thresholds rounded to 0.0001 RPO, and the PDF's SDs were computed from those stored values
  (for example, the 10-22 right-ear SD is 0.797 from unrounded values and 0.796 in the PDF).
- **SRD**: the app adds reversal values as integers in thousandths of an RPO; that is what turns 0.96025 into 0.9603
  (floating-point addition gives 0.9602).
- **SMD**: the PDF rounds exact halves up (2 c/o mean (25.70 + 16.95) / 2 = 21.325 → 21.33; Python's default
  formatting gives 21.32). Only the SMD comparison uses that rule.
- What each PDF covers: SMRT = 33 main runs (practice excluded) · STRIPES = the 3 completed main runs on 10-16 ·
  STM = all 27 · SRD = 15 numeric thresholds plus 2 status-only runs (the stopped clinical run excluded) · GDT = 25
  (the 3 deleted and 2 stopped runs excluded) · SMD = the 12 adaptive runs (the 60 QSMD items from the same night are
  not in the PDF and appear only in `numbers.csv`, 57/60).

Not compared, because they are not values computed from the data: design constants in the method descriptions (sound
durations, numbers of components, frequency ranges, start values, step sizes and so on; these are in the `protocol`
column), literature references (the Won 2015 mean line in STM, the Winn & O'Brien 2022 range in SRD), the GDT example
of sample rounding "3.5355 ms → 3.5417 ms" (sample counts exist only in the original records, `gapN`), the TMTF note
that the earliest 21 runs were normalized before the ramp (it comes from the code history), and the GDT PDF's hashes
of its own source files.

## Original records (`data/raw`)

Taken from a copy of the apps' `data` folders made on 2026-11-04 at 23:33 KST (the app records were only read; on
2026-11-05 the app records were confirmed to be byte-identical to that copy). App folder → this folder: 와우TMTF →
`tmtf`, 와우SMRT → `smrt`, 와우STRIPES → `stripes`, 와우STM → `stm`, 와우SRD → `srd`, 와우GDT → `gdt`, 와우SMD → `smd`.

- `db.json` is the app's record (all sessions, runs, trials and decision records). `runs-log.jsonl` is an
  append-only log written at the end of each run or session (one SMRT practice run from the 10-20 00:26 session is
  only here, not in db.json's run list). `journal/*.jsonl` are per-run, trial-by-trial logs (the five apps built on the
  newer framework). `gdt/deleted_runs_2026-11-03/` holds the original records of the three deleted GDT runs and a note
  about them. That note (README.txt, in Korean) is the original folder note and mentions `db.before.json`, `backup\`
  and `db.prev.json`, which are not included in this package.
- Not included: `backup/` (older copies of db.json), `db.prev.json` (the previous version) and the GDT deletion's
  `db.before.json` (a full copy of db.json just before the deletion), because they are other versions of the same
  records.
- Original records → CSV: `analysis/build/build_trials.py` and `build_runs.py` rebuild `data/trials` and `data/runs`
  from this folder alone, byte-identical to the CSVs in this package. For 45 TMTF runs on 10-11, reversals were not
  recorded per trial, so the app's staircase code (`js/track.js`) was ported to Python and re-run on the recorded
  responses; both the recorded presented values and the reversal values match. `make_dictionary.py` builds the column
  dictionary. `sanitize_raw.py` holds the rules used to remove identifying values (below) and only runs with the
  original app folders.

## Identifying values removed

Only the values below were changed in the original records; every other byte is unchanged (after the change, every
file was read again and every value was compared with the original). Locations and counts are in
`data/raw/redaction_log.csv`.

| What was removed | Where | Values changed | Replaced with |
|---|---|---:|---|
| Windows audio output device ID (endpoint GUID) | `winStart/winEnd/routeChecks.endpointId`, `pres.win.endpoint`, `presKey`, `presRefKey` (six apps, not TMTF) | 1,973 | `{0.0.0.00000000}.{redacted-audio-endpoint-guid}` |
| Device instance ID of the USB audio adapter | last part of `hardwareId` (the VID/PID product IDs are kept; it is a generic USB audio product) | 959 | `redacted-usb-instance-id` |
| Participant code (the code typed into the apps; one app used the implant system's name as the code) | `participants[].code`, `participantSnap.code` | 283 | `P01` |
| Folder path containing the computer's user name | the re-judgment reason texts in the STM records (`runs[].resultHistory[].reason`, `sessions[].events[].reason`, journal `data.reason`) | 56 | `c-users-[redacted]-…` |

Searched for but not present in the records: names, e-mail addresses, computer names, absolute paths with a user
name (`C:\Users\…`), the sound processor's serial number, and the manufacturer, model, map and implant-date fields
(the apps have these fields, but all are empty), hospital, clinical-trial participant number and USB device serial
numbers. The implant system's name appeared only in the participant-code field and was replaced with `P01` above; it
does not remain anywhere in the records.

Kept, because they do not point to a single person or device: random IDs generated by the apps (participant,
session, run, trial), the browser user agent (Chrome version, Windows), OS and Python versions, screen resolution
(`env.screen`), generic device names such as "스피커" (Speakers) and "USB Audio", the USB audio adapter's product IDs
(VID/PID, the same for every unit of that product), the Windows standard audio-effect GUIDs (`fxRaw`, the same on
every Windows installation), the participant fields group `CI`, onset `post` and screen `audiogram` (age and the
other fields are empty), relative paths without a user name (`Documents/Codex/…/c-users-[redacted]-stm/…`,
`Desktop\byrne1994.pdf`), the names of tools written in the records (Claude, Codex), the participant's own notes on
judgments, corrections and cues (no names, places or other people), and dates and times.

## Official sound files (not included)

| Test | Files used | Source and version | In this package |
|---|---|---|---|
| SMRT | 804 WAV files in the official program's `Wave` folder (0.0–20.0 RPO in 0.1 steps, 4 phases, 44.1 kHz, 16-bit) | SMRT 1.1.3 (Landsberger & Aronoff, House Ear Institute), free Windows program from https://www.ear-lab.org/smrt.html (downloaded 2026-10-15) | `stimulus_file_hashes/smrt_1.1.3_Wave_sha256.csv` |
| STRIPES | webSTRIPES audio bank, 3,800 MP3 files (D 1.1–20.0 × up/down × 10 roves, 96 kb/s), plus `calibration_sound.wav` and `silence_30s.mp3` | webSTRIPES (Archer-Boyd, Harland, Goehring & Carlyon, MRC CBU, University of Cambridge), https://gitlab.developers.cam.ac.uk/chg/bob/webstripes commit `2743c07f2056a2bb0d137f99a52c4b0c674d39e7` (2023-04-20), MIT License | `stimulus_file_hashes/stripes_webstripes_2743c07_audio_sha256.csv` |
| SMD (QSMD) | 60 Electric WAV files from EasyQSMD 1.0 | EasyQSMD 1.0 (Landsberger 2019), distribution zip from www.ear-lab.org/EasyQSMD (SHA-256 `b469560d…08bd9a`) | `stimulus_file_hashes/qsmd_EasyQSMD_1.0_Electric_sha256.csv` (60/60 match the file hashes in the trial records) |

The sounds for TMTF, STM, SRD, GDT and SMD (adaptive) were synthesized by the apps for each trial; the values used
for synthesis (seeds, phases and so on) are in the original records.

## Notes for reading the data

- **Times** are Korean time (UTC+9), taken when a trial started (when its sound was scheduled). For the first 21
  TMTF runs on the evening of 10-11 (finished between 20:06 and 21:18, app version 2.x), trial times and sessions
  were not yet recorded, so the run's end time is used, with `time_source = run_end`. For trials stopped before an
  answer, the time of stopping is used.
- **Ear corrections**: the TMTF sessions at 23:27 on 11-01 and 00:06 on 11-02 (5 runs) and two SMRT sessions on 11-03
  between 20:19 and 20:31 (8 runs) were done on the right ear but entered as left (L) in the apps by mistake, so the
  ear in the app records was changed from L to R at the participant's request. The CSVs have the corrected value (R).
  The original value and the reason are kept in the original records (TMTF `earOriginal` and `corrections`, SMRT
  `fixes`).
- **"Unsure"** is a button in TMTF and SMRT only. The app scored such a trial as one interval chosen at random
  (`scored_interval`, `correct`; `response_interval` is empty). From about 2026-11-02 the participant pressed this
  button only when truly unable to tell the sounds apart.
- **Reversal and end marks** are as recorded by the apps (SMRT, and TMTF from version 3.1 on: reversal positions
  recorded by the app; the five apps on the newer framework: reversals and blocked moves recorded per trial). The
  exception is the 45 TMTF runs on 10-11, where reversals were not recorded per trial: these values come from
  re-running the app's staircase code on the recorded responses (see "Original records" above), and they were
  confirmed to match the reversal column of the trial CSV that the app exported itself. TMTF counts a blocked request
  at 0 dB (trying to go easier but unable to) as a direction when deciding reversals; STRIPES, STM, SRD, GDT and SMD
  do not count blocked moves as moves or reversals.
- **Presentation settings** (Windows volume, output device, processor program and so on) are not in the CSVs; they
  are in the original records. They can differ between sessions, so take care when comparing sessions or dates.
- `run_status` and `run_flags` are the app's verdict on the whole run, repeated on every trial row of that run.

## Differences from the 2026-11-04 trial package

Compared with the trial CSVs in `CI_psychophysics_trials_2026-11-04.zip`, only 20 TMTF rows changed: their `run_id`
was filled in (15 practice trials = `<session_id>-practice`, 5 rows of the discarded 255 Hz run =
`<session_id>-discarded-1`; previously empty). Every other value, and the other six files, are byte-identical. From
this package on, the participant label is the neutral `P01` (different from the label in the 11-04 package's
README).

## License

- Data and documentation (`data/`, `analysis/pdf_values/`, `analysis/output/`, `README.md`, `README.ko.md`):
  **CC BY 4.0**, see `LICENSE-DATA.md`. Anyone may use, share and adapt them, as long as they credit the source (this
  dataset and a link to the repository), give the license, and say whether they made changes.
- Code (`analysis/*.py`, `analysis/build/*.py`): **MIT**, see `LICENSE`.
- The official sound files are not in this package and remain under their distributors' terms (see "Official sound
  files" above).

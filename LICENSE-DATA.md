# Data license — CC BY-NC 4.0

Copyright (c) 2026 mi-rae-lab (https://github.com/mi-rae-lab/ci-psychophysics-data)

The data and documentation in this repository are licensed under the
**Creative Commons Attribution-NonCommercial 4.0 International License (CC BY-NC 4.0)**.
They may be used, shared and adapted for **non-commercial purposes only**.
To view a copy of this license, visit https://creativecommons.org/licenses/by-nc/4.0/
(legal code: https://creativecommons.org/licenses/by-nc/4.0/legalcode).

## What this license covers

- `data/` — trial-level and run-level CSV files, the apps' raw records (`data/raw/`), the redaction log,
  the stimulus file hash lists and the data dictionary
- `analysis/pdf_values/` and `analysis/output/` — the values transcribed from the PDF figure sets, the recomputed
  numbers, the comparison tables and the redrawn figures
- `README.md` and `README.ko.md`
- `verification/lean4/` — the build logs, axiom audit outputs and verification reports (the Lean, JavaScript,
  Python and PowerShell source files there are under the PolyForm Noncommercial License 1.0.0)

The Python code (`analysis/*.py`, `analysis/build/*.py`) and the source files under `verification/lean4/` are
licensed separately under the PolyForm Noncommercial License 1.0.0 (see `LICENSE`).

## Attribution

When you use or share these data, credit the dataset, link to this repository, link to the license and say whether
you made changes. For example:

> Cochlear-implant psychophysics open data: seven tests from one bilateral CI user (participant P01), 2026.
> Licensed under CC BY-NC 4.0.

## Not covered

The official sound files used by the tests — SMRT 1.1.3 (ear-lab.org), webSTRIPES (MIT License, MRC CBU,
University of Cambridge) and EasyQSMD 1.0 (ear-lab.org) — are **not included** in this repository and remain under
their own terms. `data/raw/stimulus_file_hashes/` lists only their file names and SHA-256 values.

---

이 저장소의 데이터와 문서는 **CC BY-NC 4.0**(저작자표시-비영리 4.0 국제)으로 공개합니다. **비상업적 목적에 한해**, 출처(이 데이터와
저장소 링크)와 라이선스를 밝히고 바꾼 것이 있으면 바꿨다고 적으면 누구나 쓰고 나누고 고칠 수 있습니다. 상업적으로는 쓸 수 없습니다.
코드는 PolyForm Noncommercial License 1.0.0(`LICENSE`)입니다. 공식 소리 파일(SMRT 1.1.3 · webSTRIPES · EasyQSMD 1.0)은 이 저장소에
없고 각자의 조건을 따릅니다.

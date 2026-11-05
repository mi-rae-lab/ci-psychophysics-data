# Formal verification of the test apps' logic (Lean 4)

For each of the seven test apps, the rules that drive a test were written as a model in Lean 4 and proved as
theorems: the adaptive staircase (step sizes, moves, reversals, stopping and the threshold), how a run is classified
(for example "not measurable" or "stuck at an end"), and the formulas that build the stimuli. Most projects also run
the Lean model and the app's own JavaScript on the same generated inputs and compare the outputs line by line.

ChatGPT Astra 6 Ultra did this verification; Claude Opus 5.5 (max) built the test apps. The files here are as
produced on 2026-11-04 (KST). Each project was delivered as a zip file and is included here unpacked, with its build
log (`lake-build.txt`), its axiom audit (`print-axioms.txt`) and its verification report. The reports are in Korean.

## Results

| Test | Lean project | Lean | Build | Theorems in the axiom audit | Axioms used | Report (Korean) |
|---|---|---|---|---:|---|---|
| TMTF | `tmtf/TMTF-Lean` (Lean root: `tools/lean`) | 4.24.0 | passed | 123 (22 use none) | `propext`, `Classical.choice`, `Quot.sound` | `tmtf/report.ko.md` |
| SMRT | `smrt/wowSMRT-Lean4` | 4.24.0 | passed | 168 (28 use none) | same three | `smrt/report.ko.html` |
| STRIPES | `stripes/stripes-lean4` | 4.24.0 | passed | 95 (23 use none) | same three | `stripes/report.ko.md` |
| STM | `stm/stm-lean4` | 4.19.0 | passed | 168 (27 use none) | same three | `stm/report.ko.html` |
| SRD | `srd/WowSRD-Lean` (Lean root: `tools/lean`) | 4.24.0 | passed | 124 (10 use none) | same three | `srd/report.ko.md` |
| GDT | `gdt/WowGDT-Lean4` | 4.24.0 | passed | 231 (60 use none) | same three | `gdt/report.ko.html` |
| SMD | `smd/SMD-Lean` (Lean root: `tools/lean`) | 4.24.0 | passed | 157 (19 use none) | same three | `smd/report.ko.md`, `smd/theorem-map.ko.md` |

- "Theorems in the axiom audit" counts the theorems listed in each `print-axioms.txt`; the number in brackets is how
  many of them depend on no axioms at all.
- No listed theorem depends on `sorryAx` (an unfinished proof) or on any axiom beyond Lean's three standard ones
  (`propext`, `Classical.choice`, `Quot.sound`). The GDT audit (`gdt/environment-audit.txt`) also walks every
  constant in the environment: 1,554 constants, 734 theorems and 0 axiom declarations.
- `lake build` exits with code 0 even when a proof contains `sorry`, so it is the axiom audit, not the build alone,
  that shows the proofs are complete.
- `stm/stm-lean4/audit-controls/` holds deliberate negative controls (one file with `sorry`, one with a foreign
  axiom and one with `native_decide`). They exist to show that the audit catches these cases and are not part of
  the proofs.
- The builds and audits were run on Windows (`x86_64-w64-windows-gnu`). The projects use only Lean's core library;
  they do not need Mathlib.

## Cross-checks against the apps' JavaScript

TMTF, SRD, GDT and SMD run the app's JavaScript and the Lean model on generated inputs and compare every output line:

- GDT (`gdt/js-lean-comparison.txt`): 18,476 input lines (seed 20261101), 236,198 output lines from each side, no
  differences.
- SRD (`srd/WowSRD-Lean/verification/cross-check.txt`) and SMD (`smd/SMD-Lean/evidence/js-cross-check.txt`): no
  differences in any compared category.
- TMTF (`tmtf/TMTF-Lean/verification/cross-check.txt`): passed; floating-point values agree within the stated
  tolerances (largest relative difference 8.55e-16 against a tolerance of 1e-9, and 8.42e-7 against 2e-5 for gain).

SMRT, STM and STRIPES describe in their reports how the model was tied to the app code. The reports also note where
the Lean model and the app behave differently at the edges; for example, in STRIPES the Lean model returns the
finished state unchanged if input arrives after a run has ended, whereas the app raises an error.

## What this does and does not show

- It shows that the rules written in the Lean models have the proved properties, and that on the tested inputs the
  apps' JavaScript gives the same outputs as the Lean models.
- It does not prove that the JavaScript is correct for every possible input: the cross-checks cover finite sets of
  inputs.
- It says nothing about the browser's audio output beyond the app code, the streamer cable, the sound processor or
  the implant. Those are black boxes.
- It does not show that the tests measure what they are meant to measure.

## How to reproduce

1. Install elan, the Lean version manager (https://github.com/leanprover/elan). Each project's `lean-toolchain`
   file selects its Lean version.
2. Go to the project's Lean root (for TMTF, SRD and SMD that is `tools/lean` inside the project) and run
   `lake build`.
3. Run the axiom audit with `lake env lean <file>`, where the file is `PrintAxioms.lean`, `MyAudit.lean` or
   `Audit.lean`, depending on the project. STRIPES includes `stripes-lean4/verify.ps1`, which runs the build and the
   audit together. Each report has a section on how to reproduce it ("재현 방법").

## License

The Lean, JavaScript, Python and PowerShell sources here are under the MIT License (`../../LICENSE`). The build logs,
audit outputs and reports are under CC BY 4.0 (`../../LICENSE-DATA.md`).

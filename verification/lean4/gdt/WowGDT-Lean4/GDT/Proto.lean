import GDT.Stair
import GDT.Target

/-!
# 세 절차 — 앱 `js/protocol.js` `PROTOCOLS` (zeng · xie · blank) 의 계단 · 분석 · 반복 값 (Claude, 2026-11-01)

| | zeng (권장, Wei 2007 · Zeng 1999) | xie (Xie 2022) | blank (Blankenship 2022) |
|---|---|---|---|
| 구간 q · 우연 | 3 · 1/3 | 2 · 1/2 | 2 · 1/2 |
| 사다리 · 시작 | geo20 (k = i − 12) · i 12 (20 ms) | xie · i 14 (20 ms) | blank · i 9 (20 ms) |
| 규칙 · step | 2-down 1-up · 굵게 2칸 → 4번째 반전부터 1칸 | 2-down 1-up · 1칸 | 1-up 1-down · 1칸 |
| 반전 · 남김 | 12 · 8 (기하 평균) | 10 · 6 (산술) | 5 · 3 (산술) |
| 목표 · 관문 | 1/√2 · 우연 관문 | 1/√2 · 우연 관문 | 1/2 (= 우연) · 관문 없음 |
| 값 · 반복 | 역치 · 2 track (+3번째: |k̄₁ − k̄₂| > 1) | 역치 · 3 track | 논문 방식 값 · 2 track |
공통: 끝에서 막힌 이동 5번이면 멈춤 · 유효 200 · 기술적 실패 10 · 분석 구간 막힘 허용 0.

증명한 것: `cfg_ok` (세 설정 모두 js `Stair.init` 점검을 지남 · fine ≤ coarse) · 칸 끝 `ceilI` 19 · 36 · 29 · 시작 값 20 ms ·
`ends_209` (응답 209개면 세 절차 모두 끝남) · `zeng_thr` · `xie_thr` · `blank_thr` (처음부터 돌린 track 의 역치 개수와 합의 범위:
zeng −96 ≤ Σk ≤ 56 (8개, 0.3125 … 226.27 ms) · xie 6 … 600 (6개, 1 … 100 ms) · blank 6 … 360 (3개, 2 … 120 ms)) ·
`xie_blank_no_clamp` (xie · blank 는 끝으로 잘리는 이동 없음) · `zeng_clamp_example` (zeng 은 굵은 step 2칸이 위 끝 19 에서 잘릴 수 있음: 18 → 19) ·
`zeng_conv` · `xie_conv` · `blank_conv` (목표 > 우연: zeng · xie 참, blank 거짓)
-/

namespace GDT

/-- 절차 — 계단 설정 + 분석 · 반복 값 (js `P.task.intervals` · `targetPOf(P)` · `P.analysis.chance_gate` · `value_kind` · `P.repeat`) -/
structure Proto where
  name : String
  cfg : Cfg
  q : Nat
  target : TargetP
  gate : Bool
  /-- value_kind = 'paper_value' (논문 방식 값, 역치 아님) -/
  paper : Bool
  /-- repeat.tracks_per_condition -/
  need : Nat
  /-- repeat.third_if_k_diff_gt (없으면 none) -/
  third : Option Nat
  /-- analysis.boundary_blocks_allowed_in_window -/
  blocksMax : Nat

def zengCfg : Cfg :=
  { ladder := geo20, startI := 12, nHarder := 2, coarseI := 2, fineI := 1, switchFrom := 4, totalRev := 12, retained := 8,
    boundaryStop := 5, maxValid := 200, maxTech := 10 }
def xieCfg : Cfg :=
  { ladder := xieL, startI := 14, nHarder := 2, coarseI := 1, fineI := 1, switchFrom := 0, totalRev := 10, retained := 6,
    boundaryStop := 5, maxValid := 200, maxTech := 10 }
def blankCfg : Cfg :=
  { ladder := blankL, startI := 9, nHarder := 1, coarseI := 1, fineI := 1, switchFrom := 0, totalRev := 5, retained := 3,
    boundaryStop := 5, maxValid := 200, maxTech := 10 }

def zeng : Proto :=
  { name := "zeng", cfg := zengCfg, q := 3, target := .sqrtHalf, gate := true, paper := false, need := 2, third := some 1, blocksMax := 0 }
def xie : Proto :=
  { name := "xie", cfg := xieCfg, q := 2, target := .sqrtHalf, gate := true, paper := false, need := 3, third := none, blocksMax := 0 }
def blank : Proto :=
  { name := "blank", cfg := blankCfg, q := 2, target := .half, gate := false, paper := true, need := 2, third := none, blocksMax := 0 }

def protoOf : String → Option Proto
  | "zeng" => some zeng
  | "xie" => some xie
  | "blank" => some blank
  | _ => none

theorem zeng_ok : zengCfg.ok := by unfold Cfg.ok; decide
theorem xie_ok : xieCfg.ok := by unfold Cfg.ok; decide
theorem blank_ok : blankCfg.ok := by unfold Cfg.ok; decide

theorem cfg_ok : zengCfg.ok ∧ xieCfg.ok ∧ blankCfg.ok := ⟨zeng_ok, xie_ok, blank_ok⟩

theorem ceilI_values : zengCfg.ceilI = 19 ∧ xieCfg.ceilI = 36 ∧ blankCfg.ceilI = 29 := by decide

/-- 세 절차 모두 20 ms 에서 시작 (zeng: k = 0 → 20·2⁰ ms) -/
theorem start_values : valueOf zengCfg.ladder zengCfg.startI = 0 ∧ valueOf xieCfg.ladder xieCfg.startI = 20 ∧
    valueOf blankCfg.ladder blankCfg.startI = 20 := by decide

/-- 응답 209개면 (유효 200 + 기술적 실패 10 − 1) 세 절차 모두 반드시 끝남 -/
theorem ends_209 (os : List Outcome) (h : 209 ≤ os.length) :
    (run zengCfg (init zengCfg) os).1.status ≠ .running ∧ (run xieCfg (init xieCfg) os).1.status ≠ .running ∧
    (run blankCfg (init blankCfg) os).1.status ≠ .running :=
  ⟨run_ends zengCfg zeng_ok os (by simp [zengCfg]; omega), run_ends xieCfg xie_ok os (by simp [xieCfg]; omega),
   run_ends blankCfg blank_ok os (by simp [blankCfg]; omega)⟩

/-- zeng: 역치는 반전 8개의 k 합 Σk, −96 ≤ Σk ≤ 56 → 20·2^(Σk/16) ms ∈ [0.3125, 226.27] (사다리 끝 그대로) -/
theorem zeng_thr (os : List Outcome) {sum : Int} {cnt : Nat}
    (h : threshold zengCfg (run zengCfg (init zengCfg) os).1 = some (sum, cnt)) : cnt = 8 ∧ -96 ≤ sum ∧ sum ≤ 56 := by
  obtain ⟨h1, h2, h3⟩ := run_threshold_bounds zengCfg zeng_ok geo20_ok os h
  have e : vlo zengCfg.ladder = -12 ∧ vhi zengCfg.ladder = 7 := geo20_ends
  rw [e.1] at h2; rw [e.2] at h3
  simp only [zengCfg] at h1
  subst h1
  exact ⟨rfl, by omega, by omega⟩

/-- xie: 역치는 반전 6개 간격(ms) 합, 6 ≤ 합 ≤ 600 → 평균 1 … 100 ms -/
theorem xie_thr (os : List Outcome) {sum : Int} {cnt : Nat}
    (h : threshold xieCfg (run xieCfg (init xieCfg) os).1 = some (sum, cnt)) : cnt = 6 ∧ 6 ≤ sum ∧ sum ≤ 600 := by
  obtain ⟨h1, h2, h3⟩ := run_threshold_bounds xieCfg xie_ok xieL_ok os h
  have e : vlo xieCfg.ladder = 1 ∧ vhi xieCfg.ladder = 100 := xieL_ends
  rw [e.1] at h2; rw [e.2] at h3
  simp only [xieCfg] at h1
  subst h1
  exact ⟨rfl, by omega, by omega⟩

/-- blank: 논문 방식 값은 반전 3개 간격(ms) 합, 6 ≤ 합 ≤ 360 → 평균 2 … 120 ms -/
theorem blank_thr (os : List Outcome) {sum : Int} {cnt : Nat}
    (h : threshold blankCfg (run blankCfg (init blankCfg) os).1 = some (sum, cnt)) : cnt = 3 ∧ 6 ≤ sum ∧ sum ≤ 360 := by
  obtain ⟨h1, h2, h3⟩ := run_threshold_bounds blankCfg blank_ok blankL_ok os h
  have e : vlo blankCfg.ladder = 2 ∧ vhi blankCfg.ladder = 120 := blankL_ends
  rw [e.1] at h2; rw [e.2] at h3
  simp only [blankCfg] at h1
  subst h1
  exact ⟨rfl, by omega, by omega⟩

/-- xie · blank (step 1칸): 끝으로 잘리는 이동이 없음 -/
theorem xie_blank_no_clamp (os : List Outcome) :
    (∀ t ∈ (run xieCfg (init xieCfg) os).2, t.clamped = false) ∧ (∀ t ∈ (run blankCfg (init blankCfg) os).2, t.clamped = false) :=
  ⟨unit_no_clamp_run xieCfg xie_ok rfl rfl os, unit_no_clamp_run blankCfg blank_ok rfl rfl os⟩

/-- zeng: 굵은 step(2칸) 이 위 끝에서 잘릴 수 있음 — 틀림 4번: 12 → 14 → 16 → 18 → 19 (요청 20, 끝 19 로 자름) -/
theorem zeng_clamp_example :
    ((run zengCfg (init zengCfg) [.wrong, .wrong, .wrong, .wrong]).2.map (fun t => (t.i, t.nextI, t.clamped))) =
      [(12, 14, false), (14, 16, false), (16, 18, false), (18, 19, true)] := by decide

/-- 목표 > 우연 (수렴 점검을 함): zeng · xie 참, blank 거짓 (js `convOk`) -/
theorem zeng_conv : convOk zeng.target zeng.q = true := by decide +kernel
theorem xie_conv : convOk xie.target xie.q = true := by decide +kernel
theorem blank_conv : convOk blank.target blank.q = false := by decide +kernel

end GDT

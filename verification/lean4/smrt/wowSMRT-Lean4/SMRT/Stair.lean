import SMRT.Round

/-!
# 계단 — 앱 `js/track.js` `SmrtTrack` 의 모형과 성질 (Claude, 2026-10-22)

공식 SMRT 1.1.3 기본값 (SMRT.exe 폼 데이터): Up 1 · Down 1 · Step Size 2칸 (0.2 RPO) · Reversals 10 · Reversals to Average 6,
시작 0.5 RPO (칸 5), 기준 20 RPO (칸 200), 바닥 0.1 RPO (칸 1, 논문 본문), 표적이 기준에 닿으면 멈춤(천장), 시행 상한 250 (이 앱).
칸 idx = RPO × 10 (정수 — 공식 WAV 파일 이름과 1:1).

js 와 같은 순서 · 같은 값으로 상태를 바꿈 (`respond` = js `respond(correct)`, `move` = js `move(d)`):
  끝났으면 아무것도 안 함 → 바닥이면 floorHits + 1 → 시행 기록 → 맞힘: wRun 0 · cRun + 1, cRun ≥ nDown 이면 cRun 0 · move(+1)
  / 틀림: cRun 0 · wRun + 1, wRun ≥ nUp 이면 wRun 0 · move(−1) → (천장으로 끝났으면 그대로) → 반전 ≥ 10 이면 끝 → 시행 ≥ 250 이면 끝 · 미완.
  move(d): 앞 방향이 있고 d 가 다르면 반전(값 = 이동 전 칸, 시행 번호 = 시행 수 − 1) → 방향 = d →
           d > 0 이고 칸 + 2 ≥ 200 이면 끝 · 천장(칸 그대로) → 아니면 칸 = max(1, 칸 + d·2).
  js 의 `idx − step` 은 음수가 될 수 있으나 max(1, ·) 를 거치면 자연수 뺄셈(0 에서 멈춤)과 같은 값 (바닥 ≥ 0).

증명한 것 (공식 설정 `smrtCfg`, 처음부터 돌린 모든 응답 순서):
* `good_run` 칸은 늘 홀수 1 … 199, 반전 값도 모두 홀수 1 … 199, 진행 중이면 시행 < 250 · 반전 < 10, 맞힌 수 ≤ 시행 수
* `respond_correct` 맞히면 칸 + 2 (0.2 RPO 촘촘하게) — 단 칸 199 (19.9 RPO) 에서 맞히면 천장으로 끝 (칸 그대로)
* `respond_wrong` 틀리면 칸 = max(1, 칸 − 2) — 바닥 0.1 RPO 에서 또 틀리면 제자리
* `respond_revs` 반전은 하나씩만, 값은 이동 전 칸 · `respond_rev_iff` 반전 ⇔ 앞 방향이 있고 이번 방향(맞힘 +1 · 틀림 −1)과 다름
* `run_ends` 응답이 250 개 이상이면 반드시 끝남
* `run_thr_bounds` 역치 = 마지막 6 반전 합 S / 60 RPO, 6 ≤ S ≤ 1194 (0.1 … 19.9 RPO), S 짝수
* `thr4_no_tie` 저장 값 thr = S/60 의 소수 넷째 자리 반올림은 늘 한 가지 (정확히 .5 인 경우 없음)
-/

namespace SMRT

structure Cfg where
  startIdx : Nat
  refIdx : Nat
  stepIdx : Nat
  minIdx : Nat
  nDown : Nat
  nUp : Nat
  totalRev : Nat
  avgLast : Nat
  maxTrials : Nat
deriving Repr

/-- 공식 SMRT 1.1.3 설정 (js `PROTO`) -/
def smrtCfg : Cfg :=
  { startIdx := 5, refIdx := 200, stepIdx := 2, minIdx := 1, nDown := 1, nUp := 1, totalRev := 10, avgLast := 6, maxTrials := 250 }

structure St where
  idx : Nat
  cRun : Nat
  wRun : Nat
  dir : Int
  revs : List Nat
  revAt : List Nat
  nTrials : Nat
  nCorrect : Nat
  floorHits : Nat
  done : Bool
  ceiling : Bool
  incomplete : Bool
deriving Repr, Inhabited

def init (c : Cfg) : St :=
  { idx := c.startIdx, cRun := 0, wRun := 0, dir := 0, revs := [], revAt := [], nTrials := 0, nCorrect := 0, floorHits := 0,
    done := false, ceiling := false, incomplete := false }

/-- 반전인가: 앞 방향이 있고 (≠ 0) 이번 방향이 다름 -/
def isRev (s : St) (d : Int) : Bool := s.dir != 0 && d != s.dir

/-- js `move(d)` — 시행을 기록한 뒤 부름 (revAt = 시행 수 − 1) -/
def move (c : Cfg) (s : St) (d : Int) : St :=
  let s1 : St := if isRev s d then { s with revs := s.revs ++ [s.idx], revAt := s.revAt ++ [s.nTrials - 1] } else s
  let s2 : St := { s1 with dir := d }
  if 0 < d ∧ c.refIdx ≤ s.idx + c.stepIdx then { s2 with done := true, ceiling := true }
  else if 0 < d then { s2 with idx := max c.minIdx (s.idx + c.stepIdx) }
  else { s2 with idx := max c.minIdx (s.idx - c.stepIdx) }

/-- 시행 기록까지 (js: 바닥 floorHits, trials.push) -/
def record (c : Cfg) (s : St) (correct : Bool) : St :=
  { s with floorHits := if s.idx ≤ c.minIdx then s.floorHits + 1 else s.floorHits,
           nTrials := s.nTrials + 1,
           nCorrect := if correct then s.nCorrect + 1 else s.nCorrect }

/-- 정오에 따른 연속 수 · 이동 (js respond 의 가운데) -/
def react (c : Cfg) (s0 : St) (correct : Bool) : St :=
  if correct then
    if c.nDown ≤ s0.cRun + 1 then move c { s0 with wRun := 0, cRun := 0 } 1
    else { s0 with wRun := 0, cRun := s0.cRun + 1 }
  else
    if c.nUp ≤ s0.wRun + 1 then move c { s0 with cRun := 0, wRun := 0 } (-1)
    else { s0 with cRun := 0, wRun := s0.wRun + 1 }

/-- 끝 판정 (js: 천장이면 그대로, 반전 수 먼저, 그다음 시행 상한) -/
def finish (c : Cfg) (s1 : St) : St :=
  if s1.done then s1
  else if c.totalRev ≤ s1.revs.length then { s1 with done := true }
  else if c.maxTrials ≤ s1.nTrials then { s1 with done := true, incomplete := true }
  else s1

/-- js `respond(correct)` -/
def respond (c : Cfg) (s : St) (correct : Bool) : St :=
  if s.done then s else finish c (react c (record c s correct) correct)

/-- 응답 순서대로 — 끝난 뒤의 응답은 받지 않음. 시행마다 제시한 칸을 함께 돌려줌 -/
def run (c : Cfg) : St → List Bool → St × List Nat
  | s, [] => (s, [])
  | s, b :: bs =>
    if s.done then (s, [])
    else
      let r := run c (respond c s b) bs
      (r.1, s.idx :: r.2)

/-! ## 결과 (js `result()`) -/

/-- 역치에 쓰는 반전 = 마지막 avgLast 개 (js `reversals.slice(-avgLast)`) -/
def usedRevs (c : Cfg) (s : St) : List Nat := s.revs.drop (s.revs.length - c.avgLast)

/-- 역치 (합, 개수): 천장이면 없음, 반전이 모자라면 없음 — thr = 합 / (10 · 개수) RPO -/
def thrSum (c : Cfg) (s : St) : Option (Nat × Nat) :=
  if s.ceiling then none
  else if (usedRevs c s).length < c.avgLast then none
  else some ((usedRevs c s).sum, (usedRevs c s).length)

/-- 결과의 incomplete: 천장 → false, 반전 모자람 → true, 아니면 상태 값 -/
def resIncomplete (c : Cfg) (s : St) : Bool :=
  if s.ceiling then false else if (usedRevs c s).length < c.avgLast then true else s.incomplete

/-- 저장 값 thr 의 4자리 정수 (thr·10⁴): 합·1000/개수 에 가장 가까운 정수 -/
def thr4 (sum cnt : Nat) : Nat := roundDiv (sum * 1000) cnt

/-- 저장 값 sd 의 4자리 정수: √(10⁶·(c·Q − S²) / (c·max(1, c−1))) 에 가장 가까운 정수 (js 는 max(1, c−1) 로 나눔) -/
def sd4 (l : List Nat) : Nat :=
  sqrtRound (1000000 * (l.length * (l.map (fun x => x * x)).sum - l.sum * l.sum)) (l.length * max 1 (l.length - 1))

/-- sd4 가 반올림 경계에 정확히 걸리는지 -/
def sd4Tie (l : List Nat) : Bool :=
  sqTie (1000000 * (l.length * (l.map (fun x => x * x)).sum - l.sum * l.sum)) (l.length * max 1 (l.length - 1))

/-! ## 기본 성질 (모든 설정) -/

theorem respond_done (c : Cfg) (s : St) (b : Bool) (h : s.done = true) : respond c s b = s := by
  simp [respond, h]

theorem move_revs (c : Cfg) (s : St) (d : Int) :
    (move c s d).revs = (if isRev s d then s.revs ++ [s.idx] else s.revs) := by
  unfold move
  by_cases h : isRev s d <;> simp only [h, ↓reduceIte] <;> split <;> (try split) <;> rfl

theorem move_nTrials (c : Cfg) (s : St) (d : Int) : (move c s d).nTrials = s.nTrials := by
  unfold move
  by_cases h : isRev s d <;> simp only [h, ↓reduceIte] <;> split <;> (try split) <;> rfl

theorem move_nCorrect (c : Cfg) (s : St) (d : Int) : (move c s d).nCorrect = s.nCorrect := by
  unfold move
  by_cases h : isRev s d <;> simp only [h, ↓reduceIte] <;> split <;> (try split) <;> rfl

theorem move_dir (c : Cfg) (s : St) (d : Int) : (move c s d).dir = d := by
  unfold move
  by_cases h : isRev s d <;> simp only [h, ↓reduceIte] <;> split <;> (try split) <;> rfl

theorem move_done (c : Cfg) (s : St) (d : Int) :
    (move c s d).done = (if 0 < d ∧ c.refIdx ≤ s.idx + c.stepIdx then true else s.done) := by
  unfold move
  by_cases h : isRev s d <;> simp only [h, ↓reduceIte] <;> split <;> (try split) <;> simp_all

theorem move_ceiling (c : Cfg) (s : St) (d : Int) :
    (move c s d).ceiling = (if 0 < d ∧ c.refIdx ≤ s.idx + c.stepIdx then true else s.ceiling) := by
  unfold move
  by_cases h : isRev s d <;> simp only [h, ↓reduceIte] <;> split <;> (try split) <;> simp_all

theorem move_idx (c : Cfg) (s : St) (d : Int) :
    (move c s d).idx = (if 0 < d ∧ c.refIdx ≤ s.idx + c.stepIdx then s.idx
      else if 0 < d then max c.minIdx (s.idx + c.stepIdx) else max c.minIdx (s.idx - c.stepIdx)) := by
  unfold move
  by_cases h : isRev s d <;> simp only [h, ↓reduceIte] <;> split <;> (try split) <;> simp_all

theorem move_incomplete (c : Cfg) (s : St) (d : Int) : (move c s d).incomplete = s.incomplete := by
  unfold move
  by_cases h : isRev s d <;> simp only [h, ↓reduceIte] <;> split <;> (try split) <;> rfl

theorem finish_fields (c : Cfg) (s1 : St) :
    (finish c s1).idx = s1.idx ∧ (finish c s1).revs = s1.revs ∧ (finish c s1).nTrials = s1.nTrials ∧
    (finish c s1).nCorrect = s1.nCorrect ∧ (finish c s1).ceiling = s1.ceiling ∧ (finish c s1).dir = s1.dir := by
  unfold finish; split <;> (try split) <;> (try split) <;> simp

theorem finish_done (c : Cfg) (s1 : St) :
    (finish c s1).done = (s1.done || decide (c.totalRev ≤ s1.revs.length) || decide (c.maxTrials ≤ s1.nTrials)) := by
  unfold finish
  by_cases h1 : s1.done = true
  · simp [h1]
  · have hf : s1.done = false := by simpa using h1
    simp only [h1, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
    by_cases h2 : c.totalRev ≤ s1.revs.length
    · simp [h2]
    · by_cases h3 : c.maxTrials ≤ s1.nTrials
      · simp [h2, h3]
      · simp [h2, h3, hf]

/-- 끝나지 않은 상태에서 한 시행: 시행 수 + 1 -/
theorem respond_nTrials (c : Cfg) (s : St) (b : Bool) (h : s.done = false) : (respond c s b).nTrials = s.nTrials + 1 := by
  simp only [respond, h, Bool.false_eq_true, ↓reduceIte]
  rw [(finish_fields c _).2.2.1]
  unfold react record
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split <;> simp [move_nTrials]

/-- 반전은 하나씩만, 값은 이동 전 칸 -/
theorem respond_revs (c : Cfg) (s : St) (b : Bool) :
    (respond c s b).revs = s.revs ∨ (respond c s b).revs = s.revs ++ [s.idx] := by
  by_cases h : s.done = true
  · left; rw [respond_done c s b h]
  · have hf : s.done = false := by simpa using h
    simp only [respond, hf, Bool.false_eq_true, ↓reduceIte]
    rw [(finish_fields c _).2.1]
    unfold react record
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split <;> simp only [move_revs] <;>
      (try split) <;> simp

/-! ## 공식 설정 (smrtCfg) 에서 -/

/-- 공식 설정에서는 응답마다 반드시 이동을 시도함 (Up 1 · Down 1): 방향 = 맞힘 +1 · 틀림 −1 -/
def dirOf (b : Bool) : Int := if b then 1 else -1

theorem react_smrt (s0 : St) (b : Bool) :
    react smrtCfg s0 b = move smrtCfg { s0 with wRun := 0, cRun := 0 } (dirOf b) := by
  unfold react dirOf
  cases b <;> simp [smrtCfg]

/-- 맞히면: 칸 + 2 (천장 아님), 또는 칸 199 에서 천장으로 끝 (칸 그대로) -/
theorem respond_correct (s : St) (h : s.done = false) (hodd : s.idx % 2 = 1) (hle : s.idx ≤ 199) :
    ((respond smrtCfg s true).idx = s.idx + 2 ∧ (respond smrtCfg s true).ceiling = s.ceiling ∧ s.idx ≤ 197) ∨
    (s.idx = 199 ∧ (respond smrtCfg s true).idx = 199 ∧ (respond smrtCfg s true).ceiling = true ∧
      (respond smrtCfg s true).done = true) := by
  have e_idx : (respond smrtCfg s true).idx = (if 200 ≤ s.idx + 2 then s.idx else max 1 (s.idx + 2)) := by
    simp only [respond, h, Bool.false_eq_true, ↓reduceIte]
    rw [react_smrt, (finish_fields smrtCfg _).1, move_idx]
    simp [dirOf, smrtCfg, record]
  have e_ceil : (respond smrtCfg s true).ceiling = (if 200 ≤ s.idx + 2 then true else s.ceiling) := by
    simp only [respond, h, Bool.false_eq_true, ↓reduceIte]
    rw [react_smrt, (finish_fields smrtCfg _).2.2.2.2.1, move_ceiling]
    simp [dirOf, smrtCfg, record]
  have e_done : 200 ≤ s.idx + 2 → (respond smrtCfg s true).done = true := by
    intro hc
    simp only [respond, h, Bool.false_eq_true, ↓reduceIte]
    rw [react_smrt, finish_done, move_done]
    simp [dirOf, smrtCfg, record, hc]
  by_cases h199 : s.idx = 199
  · right
    have hc : 200 ≤ s.idx + 2 := by omega
    refine ⟨h199, ?_, ?_, e_done hc⟩
    · rw [e_idx, if_pos hc, h199]
    · rw [e_ceil, if_pos hc]
  · left
    have h197 : s.idx ≤ 197 := by omega
    have hc : ¬ (200 ≤ s.idx + 2) := by omega
    refine ⟨?_, ?_, h197⟩
    · rw [e_idx, if_neg hc]; omega
    · rw [e_ceil, if_neg hc]

/-- 틀리면: 칸 = max(1, 칸 − 2) (바닥에서 또 틀리면 제자리), 천장 상태는 그대로 -/
theorem respond_wrong (s : St) (h : s.done = false) :
    (respond smrtCfg s false).idx = max 1 (s.idx - 2) ∧ (respond smrtCfg s false).ceiling = s.ceiling := by
  simp only [respond, h, Bool.false_eq_true, ↓reduceIte]
  rw [react_smrt]
  have hfi := finish_fields smrtCfg (move smrtCfg { record smrtCfg s false with wRun := 0, cRun := 0 } (dirOf false))
  rw [hfi.1, hfi.2.2.2.2.1, move_idx, move_ceiling]
  simp [dirOf, smrtCfg, record]

/-- 반전 ⇔ 앞 방향이 있고 이번 방향(맞힘 +1 · 틀림 −1)과 다름 -/
theorem respond_rev_iff (s : St) (b : Bool) (h : s.done = false) :
    (respond smrtCfg s b).revs = s.revs ++ [s.idx] ↔ (s.dir ≠ 0 ∧ dirOf b ≠ s.dir) := by
  simp only [respond, h, Bool.false_eq_true, ↓reduceIte]
  rw [react_smrt, (finish_fields smrtCfg _).2.1, move_revs]
  simp only [isRev, record, bne_iff_ne, ne_eq, Bool.and_eq_true]
  by_cases hc : ¬ s.dir = 0 ∧ ¬ dirOf b = s.dir
  · rw [if_pos hc]; exact ⟨fun _ => hc, fun _ => rfl⟩
  · rw [if_neg hc]
    constructor
    · intro hh
      have := congrArg List.length hh
      simp at this
    · intro hh; exact absurd hh hc

/-! ### 불변식: 칸 · 반전 값은 홀수 1 … 199, 진행 중이면 시행 < 250 · 반전 < 10 -/

def Good (s : St) : Prop :=
  s.idx % 2 = 1 ∧ 1 ≤ s.idx ∧ s.idx ≤ 199 ∧
  (∀ r ∈ s.revs, r % 2 = 1 ∧ 1 ≤ r ∧ r ≤ 199) ∧
  (s.done = false → s.nTrials < 250 ∧ s.revs.length < 10) ∧
  s.nCorrect ≤ s.nTrials

theorem init_good : Good (init smrtCfg) := by
  simp [Good, init, smrtCfg]

theorem respond_nCorrect_le (s : St) (b : Bool) (h : s.done = false) (hc : s.nCorrect ≤ s.nTrials) :
    (respond smrtCfg s b).nCorrect ≤ (respond smrtCfg s b).nTrials := by
  simp only [respond, h, Bool.false_eq_true, ↓reduceIte]
  rw [react_smrt, (finish_fields smrtCfg _).2.2.2.1, (finish_fields smrtCfg _).2.2.1, move_nCorrect, move_nTrials]
  simp only [record]
  cases b <;> simp <;> omega

theorem respond_good (s : St) (b : Bool) (hs : Good s) : Good (respond smrtCfg s b) := by
  by_cases hd : s.done = true
  · rw [respond_done smrtCfg s b hd]; exact hs
  have hf : s.done = false := by simpa using hd
  obtain ⟨hodd, h1, h199, hrev, hrun, hc⟩ := hs
  have hidx : (respond smrtCfg s b).idx % 2 = 1 ∧ 1 ≤ (respond smrtCfg s b).idx ∧ (respond smrtCfg s b).idx ≤ 199 := by
    cases b
    · rw [(respond_wrong s hf).1]
      by_cases hk : s.idx ≤ 2
      · have : s.idx = 1 := by omega
        subst_vars; simp [this]
      · have : max 1 (s.idx - 2) = s.idx - 2 := by omega
        rw [this]; omega
    · rcases respond_correct s hf hodd h199 with ⟨he, _, h197⟩ | ⟨_, he, _, _⟩
      · rw [he]; omega
      · rw [he]; omega
  have hrv : ∀ r ∈ (respond smrtCfg s b).revs, r % 2 = 1 ∧ 1 ≤ r ∧ r ≤ 199 := by
    rcases respond_revs smrtCfg s b with he | he
    · rw [he]; exact hrev
    · rw [he]; intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hrev r hr
      · simp at hr; subst hr; exact ⟨hodd, h1, h199⟩
  have hrn : (respond smrtCfg s b).done = false → (respond smrtCfg s b).nTrials < 250 ∧ (respond smrtCfg s b).revs.length < 10 := by
    intro hd'
    have hd2 := hd'
    simp only [respond, hf, Bool.false_eq_true, ↓reduceIte] at hd2
    rw [finish_done] at hd2
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le] at hd2
    obtain ⟨⟨_, hr⟩, ht⟩ := hd2
    simp only [respond, hf, Bool.false_eq_true, ↓reduceIte]
    rw [(finish_fields smrtCfg _).2.2.1, (finish_fields smrtCfg _).2.1]
    simp only [smrtCfg] at hr ht
    exact ⟨ht, hr⟩
  exact ⟨hidx.1, hidx.2.1, hidx.2.2, hrv, hrn, respond_nCorrect_le s b hf hc⟩

theorem run_good : ∀ (bs : List Bool) (s : St), Good s → Good (run smrtCfg s bs).1
  | [], s, hs => by simpa [run] using hs
  | b :: bs, s, hs => by
    simp only [run]
    split
    · exact hs
    · exact run_good bs (respond smrtCfg s b) (respond_good s b hs)

/-- 처음부터 돌린 계단: 칸 · 반전 값은 늘 홀수 1 … 199 (0.1 … 19.9 RPO, 기준 20 RPO 에 닿지 않음) -/
theorem good_run (bs : List Bool) : Good (run smrtCfg (init smrtCfg) bs).1 :=
  run_good bs _ init_good

/-! ### 끝남 -/

theorem run_ends_aux : ∀ (bs : List Bool) (s : St), Good s → bs.length + s.nTrials ≥ 250 →
    (run smrtCfg s bs).1.done = true
  | [], s, hs, hl => by
    simp only [run]
    cases hd : s.done with
    | true => rfl
    | false =>
      have := (hs.2.2.2.2.1 hd).1
      simp at hl; omega
  | b :: bs, s, hs, hl => by
    simp only [run]
    split
    · assumption
    · rename_i hd
      apply run_ends_aux bs (respond smrtCfg s b) (respond_good s b hs)
      rw [respond_nTrials smrtCfg s b (by simpa using hd)]
      simp at hl; omega

/-- 응답이 250 개 이상이면 반드시 끝남 -/
theorem run_ends (bs : List Bool) (h : bs.length ≥ 250) : (run smrtCfg (init smrtCfg) bs).1.done = true :=
  run_ends_aux bs _ init_good (by simp [init, smrtCfg]; omega)

/-! ### 역치 범위 -/

theorem sum_odd_bounds : ∀ (l : List Nat), (∀ r ∈ l, r % 2 = 1 ∧ 1 ≤ r ∧ r ≤ 199) →
    l.length ≤ l.sum ∧ l.sum ≤ 199 * l.length ∧ l.sum % 2 = l.length % 2
  | [], _ => by simp
  | r :: l, h => by
    have h1 := h r (by simp)
    have h2 := sum_odd_bounds l (fun x hx => h x (by simp [hx]))
    simp only [List.sum_cons, List.length_cons]
    refine ⟨by omega, by omega, by omega⟩

/-- 역치 = 합 S / 60 RPO (마지막 6 반전), 6 ≤ S ≤ 1194 (0.1 … 19.9 RPO), S 짝수 -/
theorem run_thr_bounds (bs : List Bool) {S cnt : Nat}
    (h : thrSum smrtCfg (run smrtCfg (init smrtCfg) bs).1 = some (S, cnt)) :
    cnt = 6 ∧ 6 ≤ S ∧ S ≤ 1194 ∧ S % 2 = 0 := by
  have hg := good_run bs
  unfold thrSum at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i _ hlen
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hS, hc⟩ := h
      have hl : (usedRevs smrtCfg (run smrtCfg (init smrtCfg) bs).1).length = 6 := by
        unfold usedRevs at hlen ⊢
        simp [smrtCfg] at hlen ⊢; omega
      have hb := sum_odd_bounds (usedRevs smrtCfg (run smrtCfg (init smrtCfg) bs).1)
        (fun r hr => hg.2.2.2.1 r (List.mem_of_mem_drop hr))
      rw [hl] at hb
      subst hS; subst hc
      exact ⟨hl, hb.1, hb.2.1, by omega⟩

/-- 저장 값 thr = S/60 의 넷째 자리 반올림이 갈리는 경우는 없음: S·10⁴/60 은 정확히 ‘정수 + 1/2’ 이 될 수 없음 -/
theorem thr4_no_tie (S j : Nat) : 2 * (S * 1000) ≠ (2 * j + 1) * 6 := by
  intro h
  have h1 : (2 * (S * 1000)) % 4 = 0 := by omega
  have h2 : ((2 * j + 1) * 6) % 4 = 2 := by omega
  omega

/-- 저장 값 sd (반전 6개) 의 넷째 자리 반올림도 갈리는 경우가 없음:
    √(10⁶·X/30) 가 정확히 ‘정수 + 1/2’ 이려면 (2k+1)²·30 = 4·10⁶·X 여야 하는데 왼쪽은 4 로 나눈 나머지가 2 -/
theorem sd4_no_tie (X k : Nat) : (2 * k + 1) ^ 2 * 30 ≠ 4 * (1000000 * X) := by
  intro h
  have hm : (2 * k + 1) % 4 = 1 ∨ (2 * k + 1) % 4 = 3 := by omega
  have hsq : (2 * k + 1) ^ 2 % 4 = 1 := by
    rw [Nat.pow_mod]; rcases hm with h | h <;> rw [h]
  have h2 : ((2 * k + 1) ^ 2 * 30) % 4 = 2 := by rw [Nat.mul_mod, hsq]
  have h1 : (4 * (1000000 * X)) % 4 = 0 := by omega
  omega

end SMRT

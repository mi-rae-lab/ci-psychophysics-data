import SMD.Arith

/-!
# 계단 — 앱 `js/staircase.js` `Stair.step` · `Stair.threshold` 의 모형과 성질 (Claude, 2026-10-31)

Won 2015 SMD: 2-down 1-up, 20 dB 시작, 처음 4번 반전까지 2 dB → 4번째 반전을 떠나는 이동부터 0.5 dB, 반전 14번, 마지막 10번 평균.
깊이 h = 2·D (0.5 dB 칸, 정수) · 0 … 120 (0 … 60 dB) · 시작 40 · step 4 (2 dB) / 1 (0.5 dB).
방향 dir: −1 = 어렵게(얕게, h 줄임) · +1 = 쉽게(깊게, h 늘림) · 0 = 머묾. `lastDir` 의 0 은 js 의 null (아직 실제 이동 없음).
js 와 같은 순서 · 같은 값으로 상태를 바꿈 — 칸별 함수로 펼쳐 씀:
요청 방향 `reqDir` → 막힘 `isBlocked` → 반전 `isRev` → step `reqStepOf` (반전 수 + 이번 반전 < 4 이면 굵게) → 원하는 깊이 `want` → 끝으로 자름 `clampH` → 끝 판정 `endCheck`.

증명한 것 (모든 상태 · 모든 응답):
* `step_h_le` 깊이는 늘 0 … 120 · `step_h_near` 한 번에 많아야 4 칸
* `step_wrong` · `step_second_correct` · `step_first_correct` · `step_invalid` 응답마다의 움직임
* `step_revs` 반전은 실제 이동에서 방향이 바뀔 때만 하나 늘고 그 값은 이동 전 깊이 · `step_blocked_no_rev` 막힌 이동은 반전 아님
* `step_size_rule` 실제 이동의 step 은 (지금까지 반전 수 + 이번 반전) < 4 이면 4, 아니면 1 — ‘4번째 반전을 떠나는 이동부터 0.5 dB’
* `run_no_clamp` 처음부터 돌린 계단은 끝으로 잘리는 이동이 없음 (굵은 step 동안 깊이는 늘 4 의 배수 · 끝 0 · 120 도 4 의 배수)
* `run_ends` 응답이 210개 이상이면 반드시 끝남 (유효 200 + 기술적 실패 10 상한)
* `run_threshold_bounds` 역치(마지막 10 반전의 h 합 / 20)는 0 … 60 dB
-/

namespace SMD

inductive StStatus
  | running | reversalTarget | trialCap | techFail
deriving DecidableEq, Repr, Inhabited

inductive Move
  | stay | move | blocked | invalid
deriving DecidableEq, Repr, Inhabited

inductive Outcome
  | correct | wrong | invalid
deriving DecidableEq, Repr, Inhabited

/-- 설정 — js `Stair.cfgFrom(PROTOCOLS.won2015)` -/
structure Cfg where
  startH : Nat
  ceilH : Nat
  floorH : Nat
  nHarder : Nat
  coarseH : Nat
  fineH : Nat
  switchFrom : Nat
  totalRev : Nat
  retained : Nat
  maxValid : Nat
  maxTech : Nat
deriving Repr

def wonCfg : Cfg :=
  { startH := 40, ceilH := 120, floorH := 0, nHarder := 2, coarseH := 4, fineH := 1, switchFrom := 4, totalRev := 14, retained := 10, maxValid := 200, maxTech := 10 }

/-- 반전 기록: 이동 전 깊이 · 유효 시행 번호 · 끝 표시 (0 없음, 1 위 끝 ceiling, 2 바닥 floor) · 이동 방향 -/
structure Rev where
  h : Nat
  validNo : Nat
  atBound : Nat
  dirAfter : Int
deriving DecidableEq, Repr, Inhabited

structure St where
  h : Nat
  streak : Nat
  lastDir : Int
  revs : List Rev
  attempts : Nat
  valid : Nat
  tech : Nat
  moves : Nat
  status : StStatus
deriving Repr, Inhabited

/-- 시행 기록 (js `tr` 의 판정 · 대조에 쓰는 칸) -/
structure Tr where
  h : Nat
  isValid : Bool
  correct : Bool
  validNo : Nat
  move : Move
  blockedAt : Nat
  reversal : Bool
  reqDir : Int
  reqStep : Nat
  effStep : Nat
  clamped : Bool
  postStreak : Nat
deriving Repr, Inhabited

def init (c : Cfg) : St := { h := c.startH, streak := 0, lastDir := 0, revs := [], attempts := 0, valid := 0, tech := 0, moves := 0, status := .running }

/-! ## 한 시행 — 칸별 함수 -/

/-- 요청 방향: 맞히면 연속 정답 + 1 이 nHarder 에 닿을 때 −1 (어렵게), 아니면 0 · 틀리면 +1 (쉽게) -/
def reqDir (c : Cfg) (s : St) (correct : Bool) : Int :=
  if correct then (if s.streak + 1 ≥ c.nHarder then -1 else 0) else 1

/-- 새 연속 정답 (이동에 쓴 정답 쌍은 다시 쓰지 않음) -/
def newStreak (c : Cfg) (s : St) (correct : Bool) : Nat :=
  if correct then (if s.streak + 1 ≥ c.nHarder then 0 else s.streak + 1) else 0

/-- 끝에 막힌 이동: 위 끝에서 더 깊게(+1) · 바닥에서 더 얕게(−1) -/
def isBlocked (c : Cfg) (s : St) (dir : Int) : Bool :=
  (decide (dir > 0) && decide (s.h ≥ c.ceilH)) || (decide (dir < 0) && decide (s.h ≤ c.floorH))

/-- 실제 이동 -/
def moved (c : Cfg) (s : St) (dir : Int) : Bool := decide (dir ≠ 0) && !isBlocked c s dir

/-- 반전: 실제 이동이고, 앞의 실제 이동이 있었고, 방향이 바뀜 -/
def isRev (c : Cfg) (s : St) (dir : Int) : Bool := moved c s dir && decide (s.lastDir ≠ 0) && decide (dir ≠ s.lastDir)

/-- js `stepFor(cfg, revCount)`: 반전 수(이번 이동이 반전이면 그것까지) < switchFrom 이면 굵게 -/
def stepFor (c : Cfg) (n : Nat) : Nat := if n < c.switchFrom then c.coarseH else c.fineH

/-- js `tr.requestedStepH` — 방향이 0 이 아니면 (막혀도) stepFor(반전 수 + 이번 반전) -/
def reqStepOf (c : Cfg) (s : St) (dir : Int) : Nat :=
  if dir = 0 then 0 else stepFor c (s.revs.length + (if isRev c s dir then 1 else 0))

/-- 원하는 깊이 (정수) -/
def want (c : Cfg) (s : St) (dir : Int) : Int := (s.h : Int) + dir * (reqStepOf c s dir : Int)

/-- js `Math.min(ceilH, Math.max(floorH, want))` -/
def clampH (c : Cfg) (v : Int) : Nat := min c.ceilH (max c.floorH v.toNat)

def newH (c : Cfg) (s : St) (dir : Int) : Nat := if moved c s dir then clampH c (want c s dir) else s.h

def atB (c : Cfg) (h : Nat) : Nat := if h = c.ceilH then 1 else if h = c.floorH then 2 else 0

def newRevs (c : Cfg) (s : St) (dir : Int) (validNo : Nat) : List Rev :=
  if isRev c s dir then s.revs ++ [{ h := s.h, validNo := validNo, atBound := atB c s.h, dirAfter := dir }] else s.revs

/-- 유효 시행 뒤 끝 판정 (js: 반전 수 먼저, 그다음 유효 시행 상한) -/
def endCheck (c : Cfg) (revs : List Rev) (valid : Nat) : StStatus :=
  if revs.length ≥ c.totalRev then .reversalTarget
  else if valid ≥ c.maxValid then .trialCap
  else .running

def moveOf (c : Cfg) (s : St) (dir : Int) : Move :=
  if dir = 0 then .stay else if isBlocked c s dir then .blocked else .move

def stepValid (c : Cfg) (s : St) (correct : Bool) : St × Tr :=
  let dir := reqDir c s correct
  let valid := s.valid + 1
  let revs := newRevs c s dir valid
  let h' := newH c s dir
  ({ h := h', streak := newStreak c s correct, lastDir := if moved c s dir then dir else s.lastDir, revs := revs,
     attempts := s.attempts + 1, valid := valid, tech := s.tech, moves := if moved c s dir then s.moves + 1 else s.moves,
     status := endCheck c revs valid },
   { h := s.h, isValid := true, correct := correct, validNo := valid, move := moveOf c s dir,
     blockedAt := if moveOf c s dir = .blocked then (if dir > 0 then 1 else 2) else 0, reversal := isRev c s dir,
     reqDir := dir, reqStep := reqStepOf c s dir,
     effStep := if moved c s dir then (if h' ≥ s.h then h' - s.h else s.h - h') else 0,
     clamped := moved c s dir && decide ((h' : Int) ≠ want c s dir), postStreak := newStreak c s correct })

def stepInvalid (c : Cfg) (s : St) : St × Tr :=
  ({ s with attempts := s.attempts + 1, tech := s.tech + 1, status := if s.tech + 1 ≥ c.maxTech then .techFail else s.status },
   { h := s.h, isValid := false, correct := false, validNo := 0, move := .invalid, blockedAt := 0, reversal := false,
     reqDir := 0, reqStep := 0, effStep := 0, clamped := false, postStreak := s.streak })

/-- 한 시행 (js `Stair.step`, 진행 중일 때) -/
def step (c : Cfg) (s : St) : Outcome → St × Tr
  | .correct => stepValid c s true
  | .wrong => stepValid c s false
  | .invalid => stepInvalid c s

/-- 응답 순서대로 (끝나면 멈춤 — 끝난 계단에는 시행을 내지 않음) -/
def run (c : Cfg) : St → List Outcome → St × List Tr
  | s, [] => (s, [])
  | s, o :: os =>
    if s.status = .running then
      let r := step c s o
      let rest := run c r.1 os
      (rest.1, r.2 :: rest.2)
    else (s, [])

/-- 역치: 반전이 14번 이상이면 마지막 10번의 h 합과 개수 (thr dB = 합 / (2 · 개수)) -/
def threshold (c : Cfg) (s : St) : Option (Nat × Nat) :=
  if s.revs.length < c.totalRev then none
  else
    let kept := s.revs.drop (s.revs.length - c.retained)
    some ((kept.map (·.h)).sum, kept.length)

/-! ## 칸별 보조정리 -/

section props
variable (c : Cfg)

theorem reqDir_cases (s : St) (b : Bool) : reqDir c s b = 1 ∨ reqDir c s b = 0 ∨ reqDir c s b = -1 := by
  unfold reqDir; split <;> (try split) <;> simp

/-- 실제 이동이면 원하는 깊이는 끝 안쪽으로 향함 — 위 끝을 넘지 않게 자르고, 바닥 아래로는 toNat 와 max 가 자름 -/
theorem newH_le (s : St) (dir : Int) (h : s.h ≤ c.ceilH) : newH c s dir ≤ c.ceilH := by
  unfold newH clampH
  split
  · exact Nat.min_le_left _ _
  · exact h

theorem step_h_le (s : St) (o : Outcome) (h : s.h ≤ c.ceilH) : (step c s o).1.h ≤ c.ceilH := by
  cases o
  · exact newH_le c s _ h
  · exact newH_le c s _ h
  · simpa [step, stepInvalid] using h

theorem stepFor_le (n : Nat) (hc : c.fineH ≤ c.coarseH) : stepFor c n ≤ c.coarseH := by
  unfold stepFor; split <;> omega

theorem reqStepOf_le (s : St) (dir : Int) (hc : c.fineH ≤ c.coarseH) : reqStepOf c s dir ≤ c.coarseH := by
  unfold reqStepOf; split
  · exact Nat.zero_le _
  · exact stepFor_le c _ hc

/-- 한 번에 많아야 굵은 step 만큼 (|dir| ≤ 1 · 끝으로 자르면 더 적게) -/
theorem newH_near (s : St) (dir : Int) (hd : dir = 1 ∨ dir = 0 ∨ dir = -1) (hc : c.fineH ≤ c.coarseH) (hf : c.floorH ≤ s.h) (hs : s.h ≤ c.ceilH) :
    newH c s dir ≤ s.h + c.coarseH ∧ s.h ≤ newH c s dir + c.coarseH := by
  have hq := reqStepOf_le c s dir hc
  unfold newH clampH want
  split
  · rcases hd with hd | hd | hd <;> subst hd
    · simp only [Int.one_mul]
      constructor <;> omega
    · simp
      constructor <;> omega
    · constructor <;> omega
  · omega

theorem step_h_near (s : St) (o : Outcome) (hc : c.fineH ≤ c.coarseH) (hf : c.floorH ≤ s.h) (hs : s.h ≤ c.ceilH) :
    (step c s o).1.h ≤ s.h + c.coarseH ∧ s.h ≤ (step c s o).1.h + c.coarseH := by
  cases o
  · exact newH_near c s _ (reqDir_cases c s true) hc hf hs
  · exact newH_near c s _ (reqDir_cases c s false) hc hf hs
  · simp [step, stepInvalid]

/-- 틀리면 쉽게(+1): 위 끝이면 막힘 · 아니면 이동, 연속 정답 0 -/
theorem step_wrong (s : St) :
    (step c s .wrong).1.streak = 0 ∧ (step c s .wrong).2.reqDir = 1 ∧
    (step c s .wrong).2.move = (if s.h ≥ c.ceilH then .blocked else .move) := by
  simp only [step, stepValid, reqDir, newStreak, moveOf, isBlocked]
  by_cases hk : s.h ≥ c.ceilH <;> simp [hk]

/-- 두 번째 연속 정답이면 어렵게(−1): 바닥이면 막힘 · 아니면 이동, 연속 정답은 0 으로 -/
theorem step_second_correct (s : St) (hn : c.nHarder = 2) (hs : s.streak = 1) :
    (step c s .correct).1.streak = 0 ∧ (step c s .correct).2.reqDir = -1 ∧
    (step c s .correct).2.move = (if s.h ≤ c.floorH then .blocked else .move) := by
  simp only [step, stepValid, reqDir, newStreak, moveOf, isBlocked, hn, hs]
  by_cases hk : s.h ≤ c.floorH <;> simp [hk]

/-- 첫 정답(연속 정답 0)은 머묾, 연속 정답 1 -/
theorem step_first_correct (s : St) (hn : c.nHarder = 2) (hs : s.streak = 0) :
    (step c s .correct).1.h = s.h ∧ (step c s .correct).1.streak = 1 ∧ (step c s .correct).2.move = .stay := by
  simp [step, stepValid, newH, moved, isBlocked, reqDir, newStreak, moveOf, hn, hs]

/-- 기술적 실패는 깊이 · 연속 정답 · 방향 · 반전 · 유효 시행 수를 바꾸지 않음 -/
theorem step_invalid (s : St) :
    (step c s .invalid).1.h = s.h ∧ (step c s .invalid).1.streak = s.streak ∧ (step c s .invalid).1.lastDir = s.lastDir ∧
    (step c s .invalid).1.revs = s.revs ∧ (step c s .invalid).1.valid = s.valid ∧ (step c s .invalid).1.tech = s.tech + 1 := by
  simp [step, stepInvalid]

theorem isRev_moved (s : St) (dir : Int) (h : isRev c s dir = true) : moved c s dir = true := by
  simp only [isRev, Bool.and_eq_true] at h
  exact h.1.1

theorem moveOf_of_moved (s : St) (dir : Int) (h : moved c s dir = true) : moveOf c s dir = .move := by
  simp only [moved, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  simp [moveOf, h.1, h.2]

theorem stepValid_revs (s : St) (b : Bool) :
    (stepValid c s b).1.revs = s.revs ∨
    (∃ r : Rev, (stepValid c s b).1.revs = s.revs ++ [r] ∧ r.h = s.h ∧ (stepValid c s b).2.move = .move ∧ (stepValid c s b).2.reversal = true) := by
  by_cases hr : isRev c s (reqDir c s b) = true
  · right
    refine ⟨{ h := s.h, validNo := s.valid + 1, atBound := atB c s.h, dirAfter := reqDir c s b }, by simp [stepValid, newRevs, hr], rfl, ?_, by simpa [stepValid] using hr⟩
    simpa [stepValid] using moveOf_of_moved c s _ (isRev_moved c s _ hr)
  · left
    simp [stepValid, newRevs, hr]

/-- 반전: 실제 이동에서 방향이 바뀔 때만 하나 늘고, 그 값은 이동 전 깊이 (그 시행에서 제시한 깊이) -/
theorem step_revs (s : St) (o : Outcome) :
    (step c s o).1.revs = s.revs ∨
    (∃ r : Rev, (step c s o).1.revs = s.revs ++ [r] ∧ r.h = s.h ∧ (step c s o).2.move = .move ∧ (step c s o).2.reversal = true) := by
  cases o
  · exact stepValid_revs c s true
  · exact stepValid_revs c s false
  · left; simp [step, stepInvalid]

/-- 막힌 이동은 반전이 아님 (반전 목록 그대로) -/
theorem step_blocked_no_rev (s : St) (o : Outcome) (h : (step c s o).2.move = .blocked) : (step c s o).1.revs = s.revs := by
  rcases step_revs c s o with h1 | ⟨_, _, _, hm, _⟩
  · exact h1
  · rw [hm] at h; cases h

/-- step 규칙: 실제 이동의 요청 step = (지금까지 반전 수 + 이번이 반전이면 1) < switchFrom 이면 굵게, 아니면 잘게 -/
theorem step_size_rule (s : St) (b : Bool) (hm : (stepValid c s b).2.move = .move) :
    (stepValid c s b).2.reqStep = (if (stepValid c s b).1.revs.length < c.switchFrom then c.coarseH else c.fineH) := by
  have hd : reqDir c s b ≠ 0 := by
    intro h0; simp [stepValid, moveOf, h0] at hm
  simp only [stepValid, reqStepOf, hd, ↓reduceIte, stepFor, newRevs]
  by_cases hr : isRev c s (reqDir c s b) = true <;> simp [hr]

end props

/-! ### 끝으로 잘리는 이동 없음 (처음부터 돌린 Won 계단)
굵은 step(4) 동안 깊이는 늘 4 의 배수이고 끝 0 · 120 도 4 의 배수라, 막히지 않은 이동은 끝 안에 정확히 떨어짐. 잔 step(1)은 막히지 않으면 늘 안쪽. -/

/-- 불변식: 깊이 0 … 120, 그리고 (반전이 4번 미만이면 깊이는 4 의 배수) -/
def NoClampInv (s : St) : Prop := s.h ≤ 120 ∧ (s.revs.length < 4 → s.h % 4 = 0)

theorem init_noClamp : NoClampInv (init wonCfg) := by simp [NoClampInv, init, wonCfg]

@[simp] theorem wonCfg_ceilH : wonCfg.ceilH = 120 := rfl
@[simp] theorem wonCfg_floorH : wonCfg.floorH = 0 := rfl
@[simp] theorem wonCfg_coarseH : wonCfg.coarseH = 4 := rfl
@[simp] theorem wonCfg_fineH : wonCfg.fineH = 1 := rfl
@[simp] theorem wonCfg_switchFrom : wonCfg.switchFrom = 4 := rfl

/-- 1 · −1 방향의 막힘 (Won 설정) -/
theorem isBlocked_up (s : St) : isBlocked wonCfg s 1 = decide (120 ≤ s.h) := by simp [isBlocked, wonCfg]
theorem isBlocked_down (s : St) : isBlocked wonCfg s (-1) = decide (s.h ≤ 0) := by simp [isBlocked, wonCfg]

/-- 핵심: 방향 하나에 대해 — 새 깊이 ≤ 120 · (새 반전 수 < 4 → 새 깊이는 4 의 배수) · 실제 이동이면 새 깊이 = 원하는 깊이 (자르지 않음) -/
theorem noClamp_core (s : St) (dir : Int) (v : Nat) (hd : dir = 1 ∨ dir = 0 ∨ dir = -1) (hle : s.h ≤ 120)
    (hm4 : s.revs.length < 4 → s.h % 4 = 0) :
    newH wonCfg s dir ≤ 120 ∧ ((newRevs wonCfg s dir v).length < 4 → newH wonCfg s dir % 4 = 0) ∧
    (moved wonCfg s dir = true → ((newH wonCfg s dir : Nat) : Int) = want wonCfg s dir) := by
  have hrevs : (newRevs wonCfg s dir v).length = s.revs.length + (if isRev wonCfg s dir then 1 else 0) := by
    unfold newRevs; split <;> simp_all
  rw [hrevs]
  have hrm : isRev wonCfg s dir = true → moved wonCfg s dir = true := isRev_moved wonCfg s dir
  unfold newH want reqStepOf
  cases hm : moved wonCfg s dir
  · -- 실제 이동이 아님: 깊이 · 반전 그대로
    have hr : isRev wonCfg s dir = false := by cases h : isRev wonCfg s dir <;> simp_all
    simp only [hr, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    exact ⟨hle, hm4, fun h => absurd h (by simp)⟩
  · have hd0 : dir ≠ 0 := by intro h0; simp [moved, h0] at hm
    have hnb : isBlocked wonCfg s dir = false := by
      cases hb : isBlocked wonCfg s dir
      · rfl
      · simp [moved, hb] at hm
    simp only [↓reduceIte, hd0, stepFor, clampH, wonCfg_ceilH, wonCfg_floorH, wonCfg_coarseH, wonCfg_fineH, wonCfg_switchFrom, true_implies]
    rcases hd with hd | hd | hd
    · subst hd
      rw [isBlocked_up] at hnb
      have hc : s.h < 120 := by have := hnb; simp at this; omega
      have hrv : isRev wonCfg s 1 = (decide (s.lastDir ≠ 0) && decide (1 ≠ s.lastDir)) := by simp [isRev, hm]
      simp only [hrv]
      by_cases hl : s.lastDir = 0 <;> by_cases h1 : s.lastDir = 1 <;> simp [hl, h1] <;> (repeat' split) <;> omega
    · exact absurd hd hd0
    · subst hd
      rw [isBlocked_down] at hnb
      have hc : 0 < s.h := by have := hnb; simp at this; omega
      have hrv : isRev wonCfg s (-1) = (decide (s.lastDir ≠ 0) && decide (-1 ≠ s.lastDir)) := by simp [isRev, hm]
      simp only [hrv]
      by_cases hl : s.lastDir = 0 <;> by_cases h1 : s.lastDir = -1 <;> simp [hl, h1] <;> (repeat' split) <;> omega

/-- 한 유효 시행: 불변식을 지키고 · 잘리지 않고 · 실제 이동의 step = 요청 step -/
theorem stepValid_noClamp (s : St) (b : Bool) (hi : NoClampInv s) :
    NoClampInv (stepValid wonCfg s b).1 ∧ (stepValid wonCfg s b).2.clamped = false ∧
    ((stepValid wonCfg s b).2.move = .move → (stepValid wonCfg s b).2.effStep = (stepValid wonCfg s b).2.reqStep) := by
  obtain ⟨hle, hm4⟩ := hi
  have core := noClamp_core s (reqDir wonCfg s b) (s.valid + 1) (reqDir_cases wonCfg s b) hle hm4
  obtain ⟨c1, c2, c3⟩ := core
  refine ⟨⟨c1, c2⟩, ?_, ?_⟩
  · show (moved wonCfg s (reqDir wonCfg s b) && decide (((newH wonCfg s (reqDir wonCfg s b) : Nat) : Int) ≠ want wonCfg s (reqDir wonCfg s b))) = false
    cases hm : moved wonCfg s (reqDir wonCfg s b)
    · rfl
    · simp [c3 hm]
  · intro hmove
    have hm : moved wonCfg s (reqDir wonCfg s b) = true := by
      have hd0 : reqDir wonCfg s b ≠ 0 := by intro h0; simp [stepValid, moveOf, h0] at hmove
      have hnb : isBlocked wonCfg s (reqDir wonCfg s b) = false := by
        cases hb : isBlocked wonCfg s (reqDir wonCfg s b)
        · rfl
        · simp [stepValid, moveOf, hd0, hb] at hmove
      simp [moved, hd0, hnb]
    have e := c3 hm
    show (if moved wonCfg s (reqDir wonCfg s b) = true then
        (if newH wonCfg s (reqDir wonCfg s b) ≥ s.h then newH wonCfg s (reqDir wonCfg s b) - s.h else s.h - newH wonCfg s (reqDir wonCfg s b)) else 0)
      = reqStepOf wonCfg s (reqDir wonCfg s b)
    rw [if_pos hm]
    unfold want at e
    rcases reqDir_cases wonCfg s b with hd | hd | hd
    · rw [hd] at e ⊢; split <;> omega
    · rw [hd] at hm; simp [moved] at hm
    · rw [hd] at e ⊢; split <;> omega

theorem step_noClamp (s : St) (o : Outcome) (hi : NoClampInv s) :
    NoClampInv (step wonCfg s o).1 ∧ (step wonCfg s o).2.clamped = false ∧
    ((step wonCfg s o).2.move = .move → (step wonCfg s o).2.effStep = (step wonCfg s o).2.reqStep) := by
  cases o
  · exact stepValid_noClamp s true hi
  · exact stepValid_noClamp s false hi
  · refine ⟨by simpa [step, stepInvalid, NoClampInv] using hi, rfl, fun h => ?_⟩
    simp [step, stepInvalid] at h

theorem run_noClamp_aux : ∀ (os : List Outcome) (s : St), NoClampInv s →
    ∀ t ∈ (run wonCfg s os).2, t.clamped = false ∧ (t.move = .move → t.effStep = t.reqStep)
  | [], s, _ => by simp [run]
  | o :: os, s, hi => by
    simp only [run]
    split
    · intro t ht
      simp only [List.mem_cons] at ht
      rcases ht with ht | ht
      · subst ht; exact (step_noClamp s o hi).2
      · exact run_noClamp_aux os _ (step_noClamp s o hi).1 t ht
    · simp

/-- 처음부터 돌린 계단: 끝으로 잘리는 이동이 없고, 실제 이동의 step 은 요청한 step 그대로 (2 dB 또는 0.5 dB) -/
theorem run_no_clamp (os : List Outcome) :
    ∀ t ∈ (run wonCfg (init wonCfg) os).2, t.clamped = false ∧ (t.move = .move → t.effStep = t.reqStep) :=
  run_noClamp_aux os _ init_noClamp

/-! ### 끝남 -/

/-- 진행 중 상태의 불변식: 시도 = 유효 + 기술적 실패, 진행 중이면 유효 < 200 · 기술적 실패 < 10 -/
def Inv (c : Cfg) (s : St) : Prop :=
  s.attempts = s.valid + s.tech ∧ (s.status = .running → s.valid < c.maxValid ∧ s.tech < c.maxTech)

theorem init_inv (c : Cfg) (h1 : 0 < c.maxValid) (h2 : 0 < c.maxTech) : Inv c (init c) := by
  simp [Inv, init, h1, h2]

theorem endCheck_running {c : Cfg} {revs : List Rev} {v : Nat} (h : endCheck c revs v = .running) : v < c.maxValid := by
  unfold endCheck at h
  split at h
  · cases h
  · split at h
    · cases h
    · omega

theorem step_attempts (c : Cfg) (s : St) (o : Outcome) : (step c s o).1.attempts = s.attempts + 1 := by
  cases o <;> simp [step, stepValid, stepInvalid]

theorem step_inv (c : Cfg) (s : St) (o : Outcome) (hs : Inv c s) (hr : s.status = .running) : Inv c (step c s o).1 := by
  obtain ⟨ha, hb⟩ := hs
  have hb' := hb hr
  cases o
  · refine ⟨by simp [step, stepValid]; omega, fun h => ⟨endCheck_running (by simpa [step, stepValid] using h), by simpa [step, stepValid] using hb'.2⟩⟩
  · refine ⟨by simp [step, stepValid]; omega, fun h => ⟨endCheck_running (by simpa [step, stepValid] using h), by simpa [step, stepValid] using hb'.2⟩⟩
  · refine ⟨by simp [step, stepInvalid]; omega, fun h => ?_⟩
    simp only [step, stepInvalid] at h ⊢
    by_cases ht : s.tech + 1 ≥ c.maxTech
    · simp [ht] at h
    · exact ⟨hb'.1, by omega⟩

theorem run_ends_aux (c : Cfg) : ∀ (os : List Outcome) (s : St), Inv c s →
    os.length + s.attempts ≥ c.maxValid + c.maxTech → (run c s os).1.status ≠ .running
  | [], s, hs, hl => by
    simp only [run]
    intro hr
    have h1 := hs.2 hr
    have h2 := hs.1
    simp at hl
    omega
  | o :: os, s, hs, hl => by
    simp only [run]
    split
    · rename_i hr
      apply run_ends_aux c os (step c s o).1 (step_inv c s o hs hr)
      rw [step_attempts]
      simp at hl
      omega
    · assumption

/-- Won 설정에서 응답이 210개 이상이면 반드시 끝남 (유효 200 + 기술적 실패 10) -/
theorem run_ends (os : List Outcome) (h : os.length ≥ 210) : (run wonCfg (init wonCfg) os).1.status ≠ .running :=
  run_ends_aux wonCfg os (init wonCfg) (init_inv wonCfg (by decide) (by decide)) (by simp [init, wonCfg]; omega)

/-! ### 역치 범위 -/

theorem sum_bounds : ∀ (l : List Rev), (∀ r ∈ l, r.h ≤ 120) → (l.map (·.h)).sum ≤ 120 * l.length
  | [], _ => by simp
  | r :: l, h => by
    have h1 := h r (by simp)
    have h2 := sum_bounds l (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- 반전 값이 모두 120 이하면 역치 = 합 / (2 · 10) 은 0 … 60 dB (합 ≤ 1200, 개수 10) -/
theorem threshold_bounds (s : St) (hk : ∀ r ∈ s.revs, r.h ≤ 120) {sum cnt : Nat} (h : threshold wonCfg s = some (sum, cnt)) :
    cnt = 10 ∧ sum ≤ 120 * 10 := by
  unfold threshold at h
  split at h
  · cases h
  · rename_i hlen
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hl : (s.revs.drop (s.revs.length - wonCfg.retained)).length = 10 := by
      simp [wonCfg] at hlen ⊢; omega
    have hb := sum_bounds (s.revs.drop (s.revs.length - wonCfg.retained)) (fun r hr => hk r (List.mem_of_mem_drop hr))
    rw [hl] at hb
    subst h1; subst h2
    exact ⟨hl, hb⟩

/-- 반전 값(이동 전 깊이)은 늘 0 … 120 — 한 시행 -/
theorem step_revs_le (s : St) (o : Outcome) (hk : s.h ≤ 120) (hr : ∀ r ∈ s.revs, r.h ≤ 120) :
    ∀ r ∈ (step wonCfg s o).1.revs, r.h ≤ 120 := by
  rcases step_revs wonCfg s o with h | ⟨r0, h, hk0, _, _⟩
  · rw [h]; exact hr
  · rw [h]; intro r hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hr r hm
    · simp at hm; subst hm; omega

/-- 응답 순서 전체: 깊이와 반전 값이 늘 0 … 120 -/
theorem run_bounds : ∀ (os : List Outcome) (s : St), s.h ≤ 120 → (∀ r ∈ s.revs, r.h ≤ 120) →
    (run wonCfg s os).1.h ≤ 120 ∧ ∀ r ∈ (run wonCfg s os).1.revs, r.h ≤ 120
  | [], s, hk, hr => by simp only [run]; exact ⟨hk, hr⟩
  | o :: os, s, hk, hr => by
    simp only [run]
    split
    · exact run_bounds os (step wonCfg s o).1 (step_h_le wonCfg s o (by simpa [wonCfg] using hk)) (step_revs_le s o hk hr)
    · exact ⟨hk, hr⟩

/-- 처음부터 돌린 track 의 역치는 0 … 60 dB (마지막 10 반전의 h 합 ≤ 1200, 역치 = 합 / 20) -/
theorem run_threshold_bounds (os : List Outcome) {sum cnt : Nat}
    (h : threshold wonCfg (run wonCfg (init wonCfg) os).1 = some (sum, cnt)) : cnt = 10 ∧ sum ≤ 1200 :=
  threshold_bounds _ (run_bounds os (init wonCfg) (by decide) (by simp [init])).2 h

end SMD

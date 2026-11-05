import GDT.Ladder

/-!
# 계단 — 앱 `js/staircase.js` `Stair.step` · `Stair.threshold` 의 모형과 성질 (Claude, 2026-11-01)

n-down 1-up 계단 (js `Stair.init` 이 1번 틀리면 쉬워지는 규칙만 받음), 상태는 사다리 칸 i (0 … M−1, 짧은 끝 floorI = 0 · 긴 끝 ceilI = M−1).
방향 dir: −1 = 어렵게(짧은 간격, i 줄임) · +1 = 쉽게(긴 간격, i 늘림) · 0 = 머묾. `lastDir` 의 0 은 js 의 null (아직 실제 이동 없음).
js 와 같은 순서 · 같은 값으로 상태를 바꿈 — 칸별 함수로 펼쳐 씀:
요청 방향 `reqDir` → 막힘 `isBlocked` (긴 끝에서 +1 · 짧은 끝에서 −1) → 반전 `isRev` → step `reqStepOf` (반전 수 + 이번 반전 < switchFrom 이면 굵게) →
원하는 칸 `want` → 끝으로 자름 `clampI` (js `Math.min(ceilI, Math.max(floorI, want))`) → 막힌 수 `newBF` · `newBC` (측정 전체에서 셈) →
끝 판정 `endCheck` (js 순서: 반전 수 → 짧은 끝 막힘 수 → 긴 끝 막힘 수 → 유효 시행 상한).

증명한 것 (모든 설정 · 모든 상태 · 모든 응답 — 세 절차 값은 Proto.lean):
* `step_i_le` · `run_bounds` 칸은 늘 0 … M−1 · `step_i_near` 한 번에 많아야 굵은 step 만큼 · `moved_changes_i` 실제 이동이면 칸이 바뀜
  (js 의 ‘실제 이동인데 칸이 그대로’ 예외에 닿지 않음)
* `step_blocked` 막힌 이동은 이동도 반전도 아님 (칸 · 반전 · 방향 · 이동 수 그대로) · 긴 끝이면 blockedCeil + 1, 짧은 끝이면 blockedFloor + 1
* `step_not_blocked` 막히지 않은 시행은 막힌 수를 바꾸지 않음 · `wrong_at_ceiling` 긴 끝에서 틀리면 늘 긴 끝 막힘 ·
  `correct_at_floor` 짧은 끝에서 맞히면 칸 그대로 (머묾 또는 막힘)
* `unit_no_clamp_run` step 이 1칸인 절차(xie · blank)는 끝으로 잘리는 이동이 없음 (zeng 의 잘림 예는 Proto.lean)
* `step_floor_block` · `step_ceil_block` 진행 중 계단에서 막힌 수가 boundaryStop 에 닿는 그 시행에 floor_stop · ceiling_stop
* `step_invalid` 기술적 실패는 시도 · 기술적 실패 수(와 상한이면 상태)만 바꿈
* `step_revs` 반전은 실제 이동에서 방향이 바뀔 때만 하나 늘고 그 값은 이동 전 칸 (그 시행에서 제시한 칸)
* `step_size_rule` 실제 이동의 step = (지금까지 반전 수 + 이번 반전) < switchFrom 이면 굵게, 아니면 잘게
* `run_inv` 처음부터 돌린 계단의 끝 상태: 반전 목표면 반전 수 = totalRev · floor_stop 이면 blockedFloor = boundaryStop ·
  ceiling_stop 이면 blockedCeil = boundaryStop · 시행 상한이면 유효 = maxValid · 기술적 실패면 실패 = maxTech
* `run_ends` 응답이 maxValid + maxTech − 1 개 이상이면 반드시 끝남
* `threshold_spec` · `threshold_bounds` 역치 = 마지막 retained 개 반전의 valueOf 합 (geo: k = i − 12, list: 정수 ms) · 그 평균은 [첫 값, 끝 값] 안
-/

namespace GDT

inductive StStatus
  | running | reversalTarget | floorStop | ceilingStop | trialCap | techFail
deriving DecidableEq, Repr, Inhabited

inductive Move
  | stay | move | blocked | invalid
deriving DecidableEq, Repr, Inhabited

inductive Outcome
  | correct | wrong | invalid
deriving DecidableEq, Repr, Inhabited

/-- 설정 — js `Stair.cfgFrom(P)` (floorI = 0, ceilI = 사다리 길이 − 1, nEasier = 1) -/
structure Cfg where
  ladder : Ladder
  startI : Nat
  nHarder : Nat
  coarseI : Nat
  fineI : Nat
  switchFrom : Nat
  totalRev : Nat
  retained : Nat
  boundaryStop : Nat
  maxValid : Nat
  maxTech : Nat
deriving Repr

def Cfg.ceilI (c : Cfg) : Nat := c.ladder.vals.length - 1

/-- js `Stair.init` 의 점검 (그 밖 fine ≤ coarse · 상한 > 0 — 세 절차 모두 참, Proto.lean) -/
def Cfg.ok (c : Cfg) : Prop :=
  0 < c.ladder.len ∧ c.startI ≤ c.ceilI ∧ 0 < c.coarseI ∧ 0 < c.fineI ∧ c.fineI ≤ c.coarseI ∧
  0 < c.retained ∧ c.retained ≤ c.totalRev ∧ 0 < c.boundaryStop ∧ 0 < c.maxValid ∧ 0 < c.maxTech ∧
  (c.nHarder = 1 ∨ c.nHarder = 2 ∨ c.nHarder = 3)

/-- 반전 기록: 이동 전 칸 · 유효 시행 번호 · 시도 번호 · 끝 표시 (0 없음, 1 긴 끝 ceiling, 2 짧은 끝 floor) · 이동 방향 -/
structure Rev where
  i : Nat
  validNo : Nat
  attemptNo : Nat
  atBound : Nat
  dirAfter : Int
deriving DecidableEq, Repr, Inhabited

structure St where
  i : Nat
  streak : Nat
  lastDir : Int
  revs : List Rev
  attempts : Nat
  valid : Nat
  tech : Nat
  moves : Nat
  blockedFloor : Nat
  blockedCeil : Nat
  status : StStatus
deriving Repr, Inhabited

/-- 시행 기록 (js `tr` 의 판정 · 대조에 쓰는 칸) -/
structure Tr where
  i : Nat
  isValid : Bool
  correct : Bool
  validNo : Nat
  attemptNo : Nat
  move : Move
  blockedAt : Nat
  reversal : Bool
  reqDir : Int
  reqStep : Nat
  effStep : Nat
  clamped : Bool
  postStreak : Nat
  nextI : Nat
  statusAfter : StStatus
deriving Repr, Inhabited

def init (c : Cfg) : St :=
  { i := c.startI, streak := 0, lastDir := 0, revs := [], attempts := 0, valid := 0, tech := 0, moves := 0,
    blockedFloor := 0, blockedCeil := 0, status := .running }

/-! ## 한 시행 — 칸별 함수 -/

/-- 요청 방향: 맞히면 연속 정답 + 1 이 nHarder 에 닿을 때 −1 (어렵게), 아니면 0 · 틀리면 +1 (쉽게) -/
def reqDir (c : Cfg) (s : St) (correct : Bool) : Int :=
  if correct then (if s.streak + 1 ≥ c.nHarder then -1 else 0) else 1

/-- 새 연속 정답 (이동에 쓴 정답들은 다시 쓰지 않음 — 막혀도 0 으로) -/
def newStreak (c : Cfg) (s : St) (correct : Bool) : Nat :=
  if correct then (if s.streak + 1 ≥ c.nHarder then 0 else s.streak + 1) else 0

/-- 끝에 막힌 이동: 긴 끝에서 더 길게(+1) · 짧은 끝에서 더 짧게(−1) -/
def isBlocked (c : Cfg) (s : St) (dir : Int) : Bool :=
  (decide (dir > 0) && decide (s.i ≥ c.ceilI)) || (decide (dir < 0) && decide (s.i ≤ 0))

/-- 실제 이동 -/
def moved (c : Cfg) (s : St) (dir : Int) : Bool := decide (dir ≠ 0) && !isBlocked c s dir

/-- 반전: 실제 이동이고, 앞의 실제 이동이 있었고, 방향이 바뀜 -/
def isRev (c : Cfg) (s : St) (dir : Int) : Bool := moved c s dir && decide (s.lastDir ≠ 0) && decide (dir ≠ s.lastDir)

/-- js `stepFor(cfg, revCount)`: 반전 수(이번 이동이 반전이면 그것까지) < switchFrom 이면 굵게 -/
def stepFor (c : Cfg) (n : Nat) : Nat := if n < c.switchFrom then c.coarseI else c.fineI

/-- js `tr.requestedStepI` — 방향이 0 이 아니면 (막혀도) stepFor(반전 수 + 이번 반전) -/
def reqStepOf (c : Cfg) (s : St) (dir : Int) : Nat :=
  if dir = 0 then 0 else stepFor c (s.revs.length + (if isRev c s dir then 1 else 0))

/-- 원하는 칸 (정수) -/
def want (c : Cfg) (s : St) (dir : Int) : Int := (s.i : Int) + dir * (reqStepOf c s dir : Int)

/-- js `Math.min(ceilI, Math.max(floorI, want))` (floorI = 0) -/
def clampI (c : Cfg) (v : Int) : Nat := min c.ceilI v.toNat

def newI (c : Cfg) (s : St) (dir : Int) : Nat := if moved c s dir then clampI c (want c s dir) else s.i

/-- js: `state.i === cfg.ceilI ? 'ceiling' : state.i === cfg.floorI ? 'floor' : null` -/
def atB (c : Cfg) (i : Nat) : Nat := if i = c.ceilI then 1 else if i = 0 then 2 else 0

def newRevs (c : Cfg) (s : St) (dir : Int) (validNo attemptNo : Nat) : List Rev :=
  if isRev c s dir then s.revs ++ [{ i := s.i, validNo := validNo, attemptNo := attemptNo, atBound := atB c s.i, dirAfter := dir }]
  else s.revs

/-- js `if (dir > 0) next.blockedCeil++; else next.blockedFloor++;` (막힌 이동일 때) -/
def newBF (c : Cfg) (s : St) (dir : Int) : Nat := if isBlocked c s dir && decide (dir < 0) then s.blockedFloor + 1 else s.blockedFloor
def newBC (c : Cfg) (s : St) (dir : Int) : Nat := if isBlocked c s dir && decide (dir > 0) then s.blockedCeil + 1 else s.blockedCeil

/-- 유효 시행 뒤 끝 판정 (js 순서: 반전 수 → 짧은 끝 막힘 → 긴 끝 막힘 → 유효 시행 상한) -/
def endCheck (c : Cfg) (revs : List Rev) (bf bc valid : Nat) : StStatus :=
  if revs.length ≥ c.totalRev then .reversalTarget
  else if bf ≥ c.boundaryStop then .floorStop
  else if bc ≥ c.boundaryStop then .ceilingStop
  else if valid ≥ c.maxValid then .trialCap
  else .running

def moveOf (c : Cfg) (s : St) (dir : Int) : Move :=
  if dir = 0 then .stay else if isBlocked c s dir then .blocked else .move

def blockedAtOf (c : Cfg) (s : St) (dir : Int) : Nat :=
  if moveOf c s dir = .blocked then (if dir > 0 then 1 else 2) else 0

def effStepOf (c : Cfg) (s : St) (dir : Int) : Nat :=
  if moved c s dir then (if newI c s dir ≥ s.i then newI c s dir - s.i else s.i - newI c s dir) else 0

def stepValid (c : Cfg) (s : St) (correct : Bool) : St × Tr :=
  let dir := reqDir c s correct
  let st' := endCheck c (newRevs c s dir (s.valid + 1) (s.attempts + 1)) (newBF c s dir) (newBC c s dir) (s.valid + 1)
  ({ i := newI c s dir, streak := newStreak c s correct, lastDir := if moved c s dir then dir else s.lastDir,
     revs := newRevs c s dir (s.valid + 1) (s.attempts + 1), attempts := s.attempts + 1, valid := s.valid + 1, tech := s.tech,
     moves := if moved c s dir then s.moves + 1 else s.moves, blockedFloor := newBF c s dir, blockedCeil := newBC c s dir,
     status := st' },
   { i := s.i, isValid := true, correct := correct, validNo := s.valid + 1, attemptNo := s.attempts + 1, move := moveOf c s dir,
     blockedAt := blockedAtOf c s dir, reversal := isRev c s dir, reqDir := dir, reqStep := reqStepOf c s dir,
     effStep := effStepOf c s dir, clamped := moved c s dir && decide ((newI c s dir : Int) ≠ want c s dir),
     postStreak := newStreak c s correct, nextI := newI c s dir, statusAfter := st' })

def techStatus (c : Cfg) (s : St) : StStatus := if s.tech + 1 ≥ c.maxTech then .techFail else s.status

def stepInvalid (c : Cfg) (s : St) : St × Tr :=
  ({ s with attempts := s.attempts + 1, tech := s.tech + 1, status := techStatus c s },
   { i := s.i, isValid := false, correct := false, validNo := 0, attemptNo := s.attempts + 1, move := .invalid, blockedAt := 0,
     reversal := false, reqDir := 0, reqStep := 0, effStep := 0, clamped := false, postStreak := s.streak, nextI := s.i,
     statusAfter := techStatus c s })

/-- 한 시행 (js `Stair.step`, 진행 중일 때) -/
def step (c : Cfg) (s : St) : Outcome → St × Tr
  | .correct => stepValid c s true
  | .wrong => stepValid c s false
  | .invalid => stepInvalid c s

/-- 응답 순서대로 (끝나면 멈춤 — js 는 끝난 계단에 시행을 내면 예외) -/
def run (c : Cfg) : St → List Outcome → St × List Tr
  | s, [] => (s, [])
  | s, o :: os =>
    if s.status = .running then
      let r := step c s o
      let rest := run c r.1 os
      (rest.1, r.2 :: rest.2)
    else (s, [])

/-- 역치 (js `Stair.threshold`): 반전이 totalRev 번 이상이면 마지막 retained 개의 valueOf 합과 개수
  (geo: thr = base·2^(합/(2·개수)) ms · list: thr = 합/개수 ms) -/
def threshold (c : Cfg) (s : St) : Option (Int × Nat) :=
  if s.revs.length < c.totalRev then none
  else
    let kept := s.revs.drop (s.revs.length - c.retained)
    some ((kept.map (fun r => valueOf c.ladder r.i)).sum, kept.length)

/-! ## 칸 하나씩 꺼내 보는 등식 (정의 그대로) -/

section fields
variable (c : Cfg) (s : St) (b : Bool)
@[simp] theorem sv_i : (stepValid c s b).1.i = newI c s (reqDir c s b) := rfl
@[simp] theorem sv_streak : (stepValid c s b).1.streak = newStreak c s b := rfl
@[simp] theorem sv_lastDir : (stepValid c s b).1.lastDir = if moved c s (reqDir c s b) then reqDir c s b else s.lastDir := rfl
@[simp] theorem sv_revs : (stepValid c s b).1.revs = newRevs c s (reqDir c s b) (s.valid + 1) (s.attempts + 1) := rfl
@[simp] theorem sv_attempts : (stepValid c s b).1.attempts = s.attempts + 1 := rfl
@[simp] theorem sv_valid : (stepValid c s b).1.valid = s.valid + 1 := rfl
@[simp] theorem sv_tech : (stepValid c s b).1.tech = s.tech := rfl
@[simp] theorem sv_moves : (stepValid c s b).1.moves = if moved c s (reqDir c s b) then s.moves + 1 else s.moves := rfl
@[simp] theorem sv_bf : (stepValid c s b).1.blockedFloor = newBF c s (reqDir c s b) := rfl
@[simp] theorem sv_bc : (stepValid c s b).1.blockedCeil = newBC c s (reqDir c s b) := rfl
@[simp] theorem sv_status : (stepValid c s b).1.status =
    endCheck c (newRevs c s (reqDir c s b) (s.valid + 1) (s.attempts + 1)) (newBF c s (reqDir c s b)) (newBC c s (reqDir c s b)) (s.valid + 1) := rfl
@[simp] theorem sv_tr_i : (stepValid c s b).2.i = s.i := rfl
@[simp] theorem sv_tr_isValid : (stepValid c s b).2.isValid = true := rfl
@[simp] theorem sv_tr_move : (stepValid c s b).2.move = moveOf c s (reqDir c s b) := rfl
@[simp] theorem sv_tr_blockedAt : (stepValid c s b).2.blockedAt = blockedAtOf c s (reqDir c s b) := rfl
@[simp] theorem sv_tr_reversal : (stepValid c s b).2.reversal = isRev c s (reqDir c s b) := rfl
@[simp] theorem sv_tr_reqDir : (stepValid c s b).2.reqDir = reqDir c s b := rfl
@[simp] theorem sv_tr_reqStep : (stepValid c s b).2.reqStep = reqStepOf c s (reqDir c s b) := rfl
@[simp] theorem sv_tr_effStep : (stepValid c s b).2.effStep = effStepOf c s (reqDir c s b) := rfl
@[simp] theorem sv_tr_nextI : (stepValid c s b).2.nextI = newI c s (reqDir c s b) := rfl
@[simp] theorem sv_tr_validNo : (stepValid c s b).2.validNo = s.valid + 1 := rfl
end fields

/-! ## 칸별 보조정리 -/

section props
variable (c : Cfg)

theorem reqDir_cases (s : St) (b : Bool) : reqDir c s b = 1 ∨ reqDir c s b = 0 ∨ reqDir c s b = -1 := by
  unfold reqDir; split <;> (try split) <;> simp

theorem newI_le (s : St) (dir : Int) (h : s.i ≤ c.ceilI) : newI c s dir ≤ c.ceilI := by
  unfold newI clampI
  split
  · exact Nat.min_le_left _ _
  · exact h

/-- 칸은 늘 0 … ceilI (= M − 1) -/
theorem step_i_le (s : St) (o : Outcome) (h : s.i ≤ c.ceilI) : (step c s o).1.i ≤ c.ceilI := by
  cases o
  · exact newI_le c s _ h
  · exact newI_le c s _ h
  · simpa [step, stepInvalid] using h

theorem stepFor_le (n : Nat) (hc : c.fineI ≤ c.coarseI) : stepFor c n ≤ c.coarseI := by
  unfold stepFor; split <;> omega

theorem stepFor_pos (n : Nat) (h1 : 0 < c.coarseI) (h2 : 0 < c.fineI) : 0 < stepFor c n := by
  unfold stepFor; split <;> omega

theorem reqStepOf_le (s : St) (dir : Int) (hc : c.fineI ≤ c.coarseI) : reqStepOf c s dir ≤ c.coarseI := by
  unfold reqStepOf; split
  · exact Nat.zero_le _
  · exact stepFor_le c _ hc

theorem reqStepOf_pos (s : St) (dir : Int) (hd : dir ≠ 0) (h1 : 0 < c.coarseI) (h2 : 0 < c.fineI) : 0 < reqStepOf c s dir := by
  unfold reqStepOf; rw [if_neg hd]; exact stepFor_pos c _ h1 h2

theorem moved_iff (s : St) (dir : Int) : moved c s dir = true ↔ dir ≠ 0 ∧ isBlocked c s dir = false := by
  simp [moved]

/-- 한 번에 많아야 굵은 step 만큼 (|dir| ≤ 1 · 끝으로 자르면 더 적게) -/
theorem newI_near (s : St) (dir : Int) (hd : dir = 1 ∨ dir = 0 ∨ dir = -1) (hc : c.fineI ≤ c.coarseI) (hs : s.i ≤ c.ceilI) :
    newI c s dir ≤ s.i + c.coarseI ∧ s.i ≤ newI c s dir + c.coarseI := by
  have hq := reqStepOf_le c s dir hc
  unfold newI clampI want
  split
  · rcases hd with hd | hd | hd <;> subst hd
    · simp only [Int.one_mul]
      constructor <;> omega
    · simp
      constructor <;> omega
    · constructor <;> omega
  · omega

theorem step_i_near (s : St) (o : Outcome) (hc : c.fineI ≤ c.coarseI) (hs : s.i ≤ c.ceilI) :
    (step c s o).1.i ≤ s.i + c.coarseI ∧ s.i ≤ (step c s o).1.i + c.coarseI := by
  cases o
  · exact newI_near c s _ (reqDir_cases c s true) hc hs
  · exact newI_near c s _ (reqDir_cases c s false) hc hs
  · simp [step, stepInvalid]

/-- 실제 이동이면 칸이 바뀜 (js 의 ‘실제 이동인데 칸이 그대로’ 예외는 닿지 않음) · 바뀐 크기 1 … 굵은 step -/
theorem moved_changes_i (s : St) (dir : Int) (hd : dir = 1 ∨ dir = 0 ∨ dir = -1) (h1 : 0 < c.coarseI) (h2 : 0 < c.fineI)
    (hm : moved c s dir = true) : newI c s dir ≠ s.i := by
  have hm' := (moved_iff c s dir).mp hm
  have hp := reqStepOf_pos c s dir hm'.1 h1 h2
  have hb := hm'.2
  unfold newI clampI want
  rw [if_pos hm]
  rcases hd with hd | hd | hd
  · subst hd
    have : s.i < c.ceilI := by
      unfold isBlocked at hb; simp at hb; omega
    simp only [Int.one_mul]
    omega
  · exact absurd hd hm'.1
  · subst hd
    have : 0 < s.i := by
      unfold isBlocked at hb; simp at hb; omega
    omega

/-- 틀리면 쉽게(+1): 긴 끝이면 막힘 · 아니면 이동, 연속 정답 0 -/
theorem step_wrong (s : St) :
    (step c s .wrong).1.streak = 0 ∧ (step c s .wrong).2.reqDir = 1 ∧
    (step c s .wrong).2.move = (if s.i ≥ c.ceilI then .blocked else .move) := by
  simp only [step, sv_streak, sv_tr_reqDir, sv_tr_move, reqDir, newStreak, moveOf, isBlocked]
  by_cases hk : s.i ≥ c.ceilI <;> simp [hk]

/-- 연속 정답이 nHarder 에 닿으면 어렵게(−1): 짧은 끝이면 막힘 · 아니면 이동, 연속 정답은 0 으로 -/
theorem step_harder (s : St) (hs : s.streak + 1 ≥ c.nHarder) :
    (step c s .correct).1.streak = 0 ∧ (step c s .correct).2.reqDir = -1 ∧
    (step c s .correct).2.move = (if s.i ≤ 0 then .blocked else .move) := by
  simp only [step, sv_streak, sv_tr_reqDir, sv_tr_move, reqDir, newStreak, moveOf, isBlocked, hs]
  by_cases hk : s.i ≤ 0 <;> simp [hk]

/-- 아직 닿지 않은 정답은 머묾 (칸 그대로), 연속 정답 + 1 -/
theorem step_stay (s : St) (hs : ¬ s.streak + 1 ≥ c.nHarder) :
    (step c s .correct).1.i = s.i ∧ (step c s .correct).1.streak = s.streak + 1 ∧ (step c s .correct).2.move = .stay := by
  simp [step, newI, moved, isBlocked, reqDir, newStreak, moveOf, hs]

/-- 기술적 실패는 칸 · 연속 정답 · 방향 · 반전 · 유효 시행 · 이동 · 막힌 수를 바꾸지 않음 (시도 + 1, 기술적 실패 + 1 · 상한이면 상태만) -/
theorem step_invalid (s : St) :
    (step c s .invalid).1.i = s.i ∧ (step c s .invalid).1.streak = s.streak ∧ (step c s .invalid).1.lastDir = s.lastDir ∧
    (step c s .invalid).1.revs = s.revs ∧ (step c s .invalid).1.valid = s.valid ∧ (step c s .invalid).1.moves = s.moves ∧
    (step c s .invalid).1.blockedFloor = s.blockedFloor ∧ (step c s .invalid).1.blockedCeil = s.blockedCeil ∧
    (step c s .invalid).1.attempts = s.attempts + 1 ∧ (step c s .invalid).1.tech = s.tech + 1 ∧
    (step c s .invalid).1.status = (if s.tech + 1 ≥ c.maxTech then .techFail else s.status) := by
  simp [step, stepInvalid, techStatus]

theorem isRev_moved (s : St) (dir : Int) (h : isRev c s dir = true) : moved c s dir = true := by
  simp only [isRev, Bool.and_eq_true] at h
  exact h.1.1

theorem moveOf_of_moved (s : St) (dir : Int) (h : moved c s dir = true) : moveOf c s dir = .move := by
  simp only [moved, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  simp [moveOf, h.1, h.2]

theorem newRevs_len (s : St) (dir : Int) (v a : Nat) :
    (newRevs c s dir v a).length = s.revs.length + (if isRev c s dir then 1 else 0) := by
  unfold newRevs; split <;> simp_all

theorem stepValid_revs (s : St) (b : Bool) :
    (stepValid c s b).1.revs = s.revs ∨
    (∃ r : Rev, (stepValid c s b).1.revs = s.revs ++ [r] ∧ r.i = s.i ∧ (stepValid c s b).2.move = .move ∧ (stepValid c s b).2.reversal = true) := by
  by_cases hr : isRev c s (reqDir c s b) = true
  · right
    refine ⟨{ i := s.i, validNo := s.valid + 1, attemptNo := s.attempts + 1, atBound := atB c s.i, dirAfter := reqDir c s b },
      by simp [newRevs, hr], rfl, ?_, by simpa using hr⟩
    simpa using moveOf_of_moved c s _ (isRev_moved c s _ hr)
  · left
    simp [newRevs, hr]

/-- 반전: 실제 이동에서 방향이 바뀔 때만 하나 늘고, 그 값은 이동 전 칸 (그 시행에서 제시한 칸) -/
theorem step_revs (s : St) (o : Outcome) :
    (step c s o).1.revs = s.revs ∨
    (∃ r : Rev, (step c s o).1.revs = s.revs ++ [r] ∧ r.i = s.i ∧ (step c s o).2.move = .move ∧ (step c s o).2.reversal = true) := by
  cases o
  · exact stepValid_revs c s true
  · exact stepValid_revs c s false
  · left; simp [step, stepInvalid]

/-- step 규칙: 실제 이동의 요청 step = (지금까지 반전 수 + 이번이 반전이면 1) < switchFrom 이면 굵게, 아니면 잘게 -/
theorem step_size_rule (s : St) (b : Bool) (hm : (stepValid c s b).2.move = .move) :
    (stepValid c s b).2.reqStep = (if (stepValid c s b).1.revs.length < c.switchFrom then c.coarseI else c.fineI) := by
  have hd : reqDir c s b ≠ 0 := by
    intro h0; simp [moveOf, h0] at hm
  simp only [sv_tr_reqStep, sv_revs, reqStepOf, hd, ↓reduceIte, stepFor, newRevs_len]

/-- 막힌 이동: 이동도 반전도 아님 (칸 · 반전 · 방향 · 이동 수 그대로) · 긴 끝(blockedAt 1)이면 blockedCeil + 1, 짧은 끝(2)이면 blockedFloor + 1 -/
theorem step_blocked (s : St) (o : Outcome) (h : (step c s o).2.move = .blocked) :
    (step c s o).1.i = s.i ∧ (step c s o).1.revs = s.revs ∧ (step c s o).1.lastDir = s.lastDir ∧
    (step c s o).1.moves = s.moves ∧ (step c s o).2.reversal = false ∧ (step c s o).2.effStep = 0 ∧
    (((step c s o).2.blockedAt = 1 ∧ (step c s o).2.reqDir = 1 ∧ c.ceilI ≤ s.i ∧
        (step c s o).1.blockedCeil = s.blockedCeil + 1 ∧ (step c s o).1.blockedFloor = s.blockedFloor) ∨
     ((step c s o).2.blockedAt = 2 ∧ (step c s o).2.reqDir = -1 ∧ s.i = 0 ∧
        (step c s o).1.blockedFloor = s.blockedFloor + 1 ∧ (step c s o).1.blockedCeil = s.blockedCeil)) := by
  cases o with
  | invalid => simp [step, stepInvalid] at h
  | correct =>
    simp only [step] at h ⊢
    rcases reqDir_cases c s true with hd | hd | hd <;>
      simp_all [newI, moved, isBlocked, moveOf, newRevs, isRev, effStepOf, blockedAtOf, newBF, newBC] <;> omega
  | wrong =>
    simp only [step] at h ⊢
    rcases reqDir_cases c s false with hd | hd | hd <;>
      simp_all [newI, moved, isBlocked, moveOf, newRevs, isRev, effStepOf, blockedAtOf, newBF, newBC] <;> omega

/-- 긴 끝에서 틀리면 늘 긴 끝 막힘 (그래서 분석 구간의 긴 끝 틀림 수 = 긴 끝 막힘 수 ≤ boundaryStop − 1) -/
theorem wrong_at_ceiling (s : St) (h : s.i = c.ceilI) :
    (step c s .wrong).2.move = .blocked ∧ (step c s .wrong).2.blockedAt = 1 ∧ (step c s .wrong).1.i = s.i := by
  simp [step, moveOf, blockedAtOf, isBlocked, reqDir, newI, moved, h]

/-- 짧은 끝에서 맞히면 머묾이거나 짧은 끝 막힘 — 칸은 그대로 (짧은 끝을 떠나는 것은 틀린 시행뿐) -/
theorem correct_at_floor (s : St) (h : s.i = 0) :
    (step c s .correct).2.move ≠ .move ∧ (step c s .correct).1.i = 0 := by
  simp only [step, sv_tr_move, sv_i]
  unfold moveOf newI moved isBlocked reqDir
  by_cases hs : s.streak + 1 ≥ c.nHarder <;> simp [hs, h]

/-- 막히지 않은 시행은 막힌 수를 바꾸지 않음 -/
theorem step_not_blocked (s : St) (o : Outcome) (h : (step c s o).2.move ≠ .blocked) :
    (step c s o).1.blockedFloor = s.blockedFloor ∧ (step c s o).1.blockedCeil = s.blockedCeil := by
  cases o with
  | invalid => simp [step, stepInvalid]
  | correct =>
    simp only [step, sv_tr_move, sv_bf, sv_bc] at h ⊢
    unfold newBF newBC
    unfold moveOf at h
    by_cases hb : isBlocked c s (reqDir c s true) = true
    · rcases reqDir_cases c s true with hd | hd | hd <;> simp_all
    · simp_all
  | wrong =>
    simp only [step, sv_tr_move, sv_bf, sv_bc] at h ⊢
    unfold newBF newBC
    unfold moveOf at h
    by_cases hb : isBlocked c s (reqDir c s false) = true
    · rcases reqDir_cases c s false with hd | hd | hd <;> simp_all
    · simp_all

theorem newBF_le (s : St) (dir : Int) : newBF c s dir ≤ s.blockedFloor + 1 ∧ s.blockedFloor ≤ newBF c s dir := by
  unfold newBF; split <;> omega

theorem newBC_le (s : St) (dir : Int) : newBC c s dir ≤ s.blockedCeil + 1 ∧ s.blockedCeil ≤ newBC c s dir := by
  unfold newBC; split <;> omega

/-- 한 시행에서 두 끝의 막힌 수가 함께 늘지는 않음 -/
theorem newBF_newBC (s : St) (dir : Int) : newBF c s dir + newBC c s dir ≤ s.blockedFloor + s.blockedCeil + 1 := by
  unfold newBF newBC
  by_cases h1 : (isBlocked c s dir && decide (dir < 0)) = true <;>
  by_cases h2 : (isBlocked c s dir && decide (dir > 0)) = true <;>
  simp only [h1, h2, ↓reduceIte, Bool.false_eq_true] <;> (try simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2) <;> omega

end props

@[simp] theorem sv_tr_clamped (c : Cfg) (s : St) (b : Bool) : (stepValid c s b).2.clamped =
    (moved c s (reqDir c s b) && decide ((newI c s (reqDir c s b) : Int) ≠ want c s (reqDir c s b))) := rfl

/-- 굵은 · 잔 step 이 모두 1 칸이면 (xie · blank) 끝으로 잘리는 이동이 없음 — 막히지 않은 이동은 늘 끝 안에 떨어짐 -/
theorem unit_no_clamp (c : Cfg) (h1 : c.coarseI = 1) (h2 : c.fineI = 1) (s : St) (o : Outcome) (hs : s.i ≤ c.ceilI) :
    (step c s o).2.clamped = false := by
  have hsf : ∀ n, stepFor c n = 1 := by intro n; unfold stepFor; split <;> omega
  have key : ∀ b : Bool, (stepValid c s b).2.clamped = false := by
    intro b
    rw [sv_tr_clamped]
    cases hm : moved c s (reqDir c s b)
    · rfl
    · have hm' := (moved_iff c s _).mp hm
      have hstep : reqStepOf c s (reqDir c s b) = 1 := by
        unfold reqStepOf; rw [if_neg hm'.1]; exact hsf _
      simp only [Bool.true_and, decide_eq_false_iff_not, Classical.not_not]
      unfold newI clampI want
      rw [if_pos hm, hstep]
      have hb := hm'.2
      rcases reqDir_cases c s b with hd | hd | hd
      · rw [hd] at hb ⊢
        have : s.i < c.ceilI := by unfold isBlocked at hb; simp at hb; omega
        omega
      · exact absurd hd hm'.1
      · rw [hd] at hb ⊢
        have : 0 < s.i := by unfold isBlocked at hb; simp at hb; omega
        omega
  cases o
  · exact key true
  · exact key false
  · rfl

/-! ## 끝 판정의 경우 -/

theorem endCheck_cases (c : Cfg) (revs : List Rev) (bf bc v : Nat) :
    (endCheck c revs bf bc v = .reversalTarget ∧ c.totalRev ≤ revs.length) ∨
    (endCheck c revs bf bc v = .floorStop ∧ revs.length < c.totalRev ∧ c.boundaryStop ≤ bf) ∨
    (endCheck c revs bf bc v = .ceilingStop ∧ revs.length < c.totalRev ∧ bf < c.boundaryStop ∧ c.boundaryStop ≤ bc) ∨
    (endCheck c revs bf bc v = .trialCap ∧ revs.length < c.totalRev ∧ bf < c.boundaryStop ∧ bc < c.boundaryStop ∧ c.maxValid ≤ v) ∨
    (endCheck c revs bf bc v = .running ∧ revs.length < c.totalRev ∧ bf < c.boundaryStop ∧ bc < c.boundaryStop ∧ v < c.maxValid) := by
  unfold endCheck
  by_cases h1 : revs.length ≥ c.totalRev
  · left; simp [h1]
  · by_cases h2 : bf ≥ c.boundaryStop
    · right; left; simp [h1, h2]; omega
    · by_cases h3 : bc ≥ c.boundaryStop
      · right; right; left; simp [h1, h2, h3]; omega
      · by_cases h4 : v ≥ c.maxValid
        · right; right; right; left; simp [h1, h2, h3, h4]; omega
        · right; right; right; right; simp [h1, h2, h3, h4]; omega

/-! ## 불변식 — 처음부터 돌린 계단의 모든 상태 -/

/-- 칸 범위 · 시도 = 유효 + 실패 · 진행 중이면 모든 상한 아래 · 끝난 상태는 그 끝에 정확히 닿음 · 반전 값도 칸 범위 안 -/
def RInv (c : Cfg) (s : St) : Prop :=
  s.i ≤ c.ceilI ∧ s.attempts = s.valid + s.tech ∧
  (s.status = .running → s.valid < c.maxValid ∧ s.tech < c.maxTech ∧ s.revs.length < c.totalRev ∧
     s.blockedFloor < c.boundaryStop ∧ s.blockedCeil < c.boundaryStop) ∧
  (s.status = .reversalTarget → s.revs.length = c.totalRev) ∧
  (s.status = .floorStop → s.blockedFloor = c.boundaryStop ∧ s.blockedCeil < c.boundaryStop ∧ s.revs.length < c.totalRev) ∧
  (s.status = .ceilingStop → s.blockedCeil = c.boundaryStop ∧ s.blockedFloor < c.boundaryStop ∧ s.revs.length < c.totalRev) ∧
  (s.status = .trialCap → s.valid = c.maxValid ∧ s.revs.length < c.totalRev ∧ s.blockedFloor < c.boundaryStop ∧ s.blockedCeil < c.boundaryStop) ∧
  (s.status = .techFail → s.tech = c.maxTech) ∧
  (∀ r ∈ s.revs, r.i ≤ c.ceilI)

theorem init_rinv (c : Cfg) (h : c.ok) : RInv c (init c) := by
  obtain ⟨_, h1, _, _, _, h2, h3, h4, h5, h6, _⟩ := h
  refine ⟨h1, rfl, fun _ => ⟨h5, h6, by simp [init]; omega, h4, h4⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [init]

theorem stepValid_rinv (c : Cfg) (s : St) (b : Bool) (hi : RInv c s) (hr : s.status = .running) :
    RInv c (stepValid c s b).1 := by
  obtain ⟨hI, hA, hR, _, _, _, _, _, hRev⟩ := hi
  obtain ⟨hv, ht, hrv, hbf, hbc⟩ := hR hr
  have hlen := newRevs_len c s (reqDir c s b) (s.valid + 1) (s.attempts + 1)
  have hF := newBF_le c s (reqDir c s b)
  have hC := newBC_le c s (reqDir c s b)
  have hFC := newBF_newBC c s (reqDir c s b)
  have hrl : (newRevs c s (reqDir c s b) (s.valid + 1) (s.attempts + 1)).length ≤ s.revs.length + 1 := by
    rw [hlen]; split <;> omega
  have hrevs : ∀ r ∈ newRevs c s (reqDir c s b) (s.valid + 1) (s.attempts + 1), r.i ≤ c.ceilI := by
    intro r hm
    unfold newRevs at hm
    split at hm
    · rcases List.mem_append.mp hm with hm | hm
      · exact hRev r hm
      · simp at hm; subst hm; exact hI
    · exact hRev r hm
  refine ⟨newI_le c s _ hI, by simp; omega, ?_, ?_, ?_, ?_, ?_, ?_, by simpa using hrevs⟩
  all_goals
    simp only [sv_status, sv_valid, sv_tech, sv_revs, sv_bf, sv_bc]
    rcases endCheck_cases c (newRevs c s (reqDir c s b) (s.valid + 1) (s.attempts + 1)) (newBF c s (reqDir c s b))
      (newBC c s (reqDir c s b)) (s.valid + 1) with ⟨he, h1⟩ | ⟨he, h1, h2⟩ | ⟨he, h1, h2, h3⟩ | ⟨he, h1, h2, h3, h4⟩ | ⟨he, h1, h2, h3, h4⟩ <;>
      rw [he] <;> simp <;> omega

theorem stepInvalid_rinv (c : Cfg) (s : St) (hi : RInv c s) (hr : s.status = .running) :
    RInv c (stepInvalid c s).1 := by
  obtain ⟨hI, hA, hR, _, _, _, _, _, hRev⟩ := hi
  obtain ⟨hv, ht, hrv, hbf, hbc⟩ := hR hr
  unfold stepInvalid techStatus
  by_cases hc : s.tech + 1 ≥ c.maxTech
  · simp only [hc, ↓reduceIte]
    refine ⟨hI, by simp; omega, ?_, ?_, ?_, ?_, ?_, ?_, hRev⟩ <;> simp <;> omega
  · simp only [hc, ↓reduceIte, hr]
    refine ⟨hI, by simp; omega, ?_, ?_, ?_, ?_, ?_, ?_, hRev⟩ <;> simp <;> omega

theorem step_rinv (c : Cfg) (s : St) (o : Outcome) (hi : RInv c s) (hr : s.status = .running) : RInv c (step c s o).1 := by
  cases o
  · exact stepValid_rinv c s true hi hr
  · exact stepValid_rinv c s false hi hr
  · exact stepInvalid_rinv c s hi hr

/-- 진행 중 계단에서 짧은 끝에 막힌 시행: blockedFloor + 1 이 boundaryStop 에 닿는 바로 그 시행에 floor_stop -/
theorem step_floor_block (c : Cfg) (s : St) (o : Outcome) (hi : RInv c s) (hr : s.status = .running)
    (hm : (step c s o).2.move = .blocked) (hb : (step c s o).2.blockedAt = 2) :
    (step c s o).1.blockedFloor = s.blockedFloor + 1 ∧
    ((step c s o).1.status = .floorStop ↔ s.blockedFloor + 1 = c.boundaryStop) := by
  obtain ⟨hI, _, hR, _⟩ := hi
  obtain ⟨hv, ht, hrv, hbf, hbc⟩ := hR hr
  obtain ⟨_, hrevs, _, _, _, _, hside⟩ := step_blocked c s o hm
  have hbf' : (step c s o).1.blockedFloor = s.blockedFloor + 1 ∧ (step c s o).1.blockedCeil = s.blockedCeil := by
    rcases hside with ⟨h1, _⟩ | ⟨_, _, _, h4, h5⟩
    · rw [hb] at h1; cases h1
    · exact ⟨h4, h5⟩
  refine ⟨hbf'.1, ?_⟩
  cases o with
  | invalid => simp [step, stepInvalid] at hm
  | correct | wrong =>
    simp only [step] at hrevs hbf' ⊢
    rw [sv_status, ← sv_revs, ← sv_bf, ← sv_bc, hrevs, hbf'.1, hbf'.2]
    unfold endCheck
    simp only [Nat.not_le.mpr hrv, ↓reduceIte]
    by_cases h : s.blockedFloor + 1 ≥ c.boundaryStop
    · simp [h]; omega
    · simp only [h, ↓reduceIte, Nat.not_le.mpr hbc]
      constructor
      · intro h2; split at h2 <;> cases h2
      · intro h2; omega

/-- 진행 중 계단에서 긴 끝에 막힌 시행: blockedCeil + 1 이 boundaryStop 에 닿는 바로 그 시행에 ceiling_stop -/
theorem step_ceil_block (c : Cfg) (s : St) (o : Outcome) (hi : RInv c s) (hr : s.status = .running)
    (hm : (step c s o).2.move = .blocked) (hb : (step c s o).2.blockedAt = 1) :
    (step c s o).1.blockedCeil = s.blockedCeil + 1 ∧
    ((step c s o).1.status = .ceilingStop ↔ s.blockedCeil + 1 = c.boundaryStop) := by
  obtain ⟨hI, _, hR, _⟩ := hi
  obtain ⟨hv, ht, hrv, hbf, hbc⟩ := hR hr
  obtain ⟨_, hrevs, _, _, _, _, hside⟩ := step_blocked c s o hm
  have hbc' : (step c s o).1.blockedCeil = s.blockedCeil + 1 ∧ (step c s o).1.blockedFloor = s.blockedFloor := by
    rcases hside with ⟨_, _, _, h4, h5⟩ | ⟨h1, _⟩
    · exact ⟨h4, h5⟩
    · rw [hb] at h1; cases h1
  refine ⟨hbc'.1, ?_⟩
  cases o with
  | invalid => simp [step, stepInvalid] at hm
  | correct | wrong =>
    simp only [step] at hrevs hbc' ⊢
    rw [sv_status, ← sv_revs, ← sv_bf, ← sv_bc, hrevs, hbc'.1, hbc'.2]
    unfold endCheck
    simp only [Nat.not_le.mpr hrv, ↓reduceIte, Nat.not_le.mpr hbf]
    by_cases h : s.blockedCeil + 1 ≥ c.boundaryStop
    · simp [h]; omega
    · simp only [h, ↓reduceIte]
      constructor
      · intro h2; split at h2 <;> cases h2
      · intro h2; omega

/-! ## 응답 순서 전체 -/

/-- 불변식을 지키는 상태에서 돌리면: 끝 상태도 불변식 · 모든 시행 기록의 제시 칸 · 다음 칸이 0 … ceilI -/
theorem run_inv (c : Cfg) : ∀ (os : List Outcome) (s : St), RInv c s →
    RInv c (run c s os).1 ∧ ∀ t ∈ (run c s os).2, t.i ≤ c.ceilI ∧ t.nextI ≤ c.ceilI
  | [], s, hi => by simp [run, hi]
  | o :: os, s, hi => by
    simp only [run]
    split
    · rename_i hr
      have hi' := step_rinv c s o hi hr
      obtain ⟨ih1, ih2⟩ := run_inv c os (step c s o).1 hi'
      refine ⟨ih1, ?_⟩
      intro t ht
      simp only [List.mem_cons] at ht
      rcases ht with ht | ht
      · subst ht
        refine ⟨?_, ?_⟩
        · cases o <;> simp [step, stepInvalid] <;> exact hi.1
        · have := hi'.1
          cases o <;> simp_all [step, stepInvalid]
      · exact ih2 t ht
    · simp [hi]

/-- 진행 중인 불변식 상태의 모든 시행에서 참인 성질은 처음부터 돌린 계단의 모든 시행 기록에서 참 -/
theorem run_forall (c : Cfg) (Q : Tr → Prop) (hQ : ∀ s o, RInv c s → s.status = .running → Q (step c s o).2) :
    ∀ (os : List Outcome) (s : St), RInv c s → ∀ t ∈ (run c s os).2, Q t
  | [], s, _ => by simp [run]
  | o :: os, s, hi => by
    simp only [run]
    split
    · rename_i hr
      intro t ht
      simp only [List.mem_cons] at ht
      rcases ht with ht | ht
      · subst ht; exact hQ s o hi hr
      · exact run_forall c Q hQ os _ (step_rinv c s o hi hr) t ht
    · simp

/-- step 1칸 절차의 처음부터 돌린 계단: 끝으로 잘린 이동이 하나도 없음 -/
theorem unit_no_clamp_run (c : Cfg) (hc : c.ok) (h1 : c.coarseI = 1) (h2 : c.fineI = 1) (os : List Outcome) :
    ∀ t ∈ (run c (init c) os).2, t.clamped = false :=
  run_forall c (fun t => t.clamped = false) (fun s o hi _ => unit_no_clamp c h1 h2 s o hi.1) os (init c) (init_rinv c hc)

/-- 처음부터 돌린 계단 (설정이 js init 점검을 지날 때): 끝 상태의 모양 -/
theorem run_end_state (c : Cfg) (hc : c.ok) (os : List Outcome) : RInv c (run c (init c) os).1 :=
  (run_inv c os (init c) (init_rinv c hc)).1

/-- 끝남: 불변식을 지키고 (남은 응답 + 시도 + 1) ≥ maxValid + maxTech 이면 끝난 상태로 멈춤 -/
theorem run_ends_aux (c : Cfg) : ∀ (os : List Outcome) (s : St), RInv c s →
    c.maxValid + c.maxTech ≤ os.length + s.attempts + 1 → (run c s os).1.status ≠ .running
  | [], s, hi, hl => by
    simp only [run]
    intro hr
    obtain ⟨_, hA, hR, _⟩ := hi
    have := hR hr
    simp at hl
    omega
  | o :: os, s, hi, hl => by
    simp only [run]
    split
    · rename_i hr
      apply run_ends_aux c os (step c s o).1 (step_rinv c s o hi hr)
      have : (step c s o).1.attempts = s.attempts + 1 := by cases o <;> simp [step, stepInvalid]
      rw [this]
      simp at hl
      omega
    · assumption

/-- 응답이 maxValid + maxTech − 1 개 이상이면 반드시 끝남 (세 절차: 200 + 10 − 1 = 209) -/
theorem run_ends (c : Cfg) (hc : c.ok) (os : List Outcome) (h : c.maxValid + c.maxTech ≤ os.length + 1) :
    (run c (init c) os).1.status ≠ .running :=
  run_ends_aux c os (init c) (init_rinv c hc) (by simp [init]; omega)

/-! ## 역치 -/

/-- 역치가 있으면: 개수 = retained · 합 = 마지막 retained 개 반전의 valueOf 합 · 반전 수 ≥ totalRev -/
theorem threshold_spec (c : Cfg) (s : St) (hc : c.retained ≤ c.totalRev) {sum : Int} {cnt : Nat}
    (h : threshold c s = some (sum, cnt)) :
    cnt = c.retained ∧ c.totalRev ≤ s.revs.length ∧
    sum = ((s.revs.drop (s.revs.length - c.retained)).map (fun r => valueOf c.ladder r.i)).sum := by
  unfold threshold at h
  split at h
  · cases h
  · rename_i hlen
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, by omega, h1.symm⟩
    rw [← h2, List.length_drop]
    omega

theorem sum_bounds_int (f : Rev → Int) (lo hi : Int) : ∀ (l : List Rev), (∀ r ∈ l, lo ≤ f r ∧ f r ≤ hi) →
    lo * (l.length : Int) ≤ (l.map f).sum ∧ (l.map f).sum ≤ hi * (l.length : Int)
  | [], _ => by simp
  | r :: l, h => by
    have h1 := h r (by simp)
    have h2 := sum_bounds_int f lo hi l (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have e1 : lo * ((l.length + 1 : Nat) : Int) = lo * (l.length : Int) + lo := by
      rw [Int.natCast_add, Int.mul_add]; simp
    have e2 : hi * ((l.length + 1 : Nat) : Int) = hi * (l.length : Int) + hi := by
      rw [Int.natCast_add, Int.mul_add]; simp
    rw [e1, e2]
    omega

/-- 반전 칸이 모두 0 … ceilI 이면: 첫 값 · 개수 ≤ 합 ≤ 끝 값 · 개수 (평균이 사다리 값 범위 안) -/
theorem threshold_bounds (c : Cfg) (s : St) (hL : LadderOK c.ladder) (hk : ∀ r ∈ s.revs, r.i ≤ c.ceilI)
    {sum : Int} {cnt : Nat} (h : threshold c s = some (sum, cnt)) :
    vlo c.ladder * (cnt : Int) ≤ sum ∧ sum ≤ vhi c.ladder * (cnt : Int) := by
  unfold threshold at h
  split at h
  · cases h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    apply sum_bounds_int
    intro r hr
    have hri := hk r (List.mem_of_mem_drop hr)
    have hlen := hL.1
    apply hL.2
    unfold Cfg.ceilI at hri
    unfold Ladder.len at hlen ⊢
    omega

/-- 처음부터 돌린 계단의 역치: 개수 = retained, 평균(합/개수)은 사다리 값 범위 [첫 값, 끝 값] 안 -/
theorem run_threshold_bounds (c : Cfg) (hc : c.ok) (hL : LadderOK c.ladder) (os : List Outcome) {sum : Int} {cnt : Nat}
    (h : threshold c (run c (init c) os).1 = some (sum, cnt)) :
    cnt = c.retained ∧ vlo c.ladder * (cnt : Int) ≤ sum ∧ sum ≤ vhi c.ladder * (cnt : Int) := by
  have hi := run_end_state c hc os
  have hb := threshold_bounds c _ hL hi.2.2.2.2.2.2.2.2 h
  exact ⟨(threshold_spec c _ hc.2.2.2.2.2.2.1 h).1, hb⟩

end GDT

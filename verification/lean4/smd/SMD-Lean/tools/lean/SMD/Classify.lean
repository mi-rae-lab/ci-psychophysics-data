import SMD.Exact
import SMD.Target
import SMD.Stair

/-!
# 적응 track 분류 — 앱 `js/analysis.js` `classifyAdaptive` 의 판정 경로 (Claude, 2026-10-31)

js 와 같은 순서:
1. 계단 상태로 첫 상태: 기술적 실패 · 시행 상한 · (반전 14번 + 역치 있음) → 범위 안 완료 · 그 밖 자료 부족 (멈춤 `participant_aborted` 은 화면 입력이라 모형 밖)
2. 분석 구간 W: 완료면 남기지 않은 마지막 반전(4번째)의 다음 유효 시행부터 끝까지, 시행 상한이면 마지막 20 유효 시행
3. W 안: 위 끝(120 = 60 dB)에 막힌 이동 수 · 바닥(0)에 막힌 이동 수 · 위 끝 정답 · 더 얕은 깊이(h < 120) 정답 · W 전체 정답 · W 앞 위 끝 막힘
4. 0 dB 검정: track 의 h = 0 유효 시행 **전부**로 ‘정답률 > 1/3’ 정확 이항 p < 1/20 (막힘과 상관없이)
5. 완료 · 시행 상한이면: 0 dB 경보 → 신뢰성 부족 · 두 끝 다 막힘 → 신뢰성 부족 · 위 끝 막힘 → (Fisher: 위 끝 정답률 < 더 얕은 깊이, p < .05) 신뢰성 부족 /
   (위 끝 정답률 < 70.7 % 확인) > 60 dB / 그 밖 쉬운 끝에 막힘 · 바닥 막힘 → 바닥에 막힘 · (완료이고) W 정답률 < 70.7 % 확인 → 계단이 아직 올라가는 중
6. 표시: 위 끝 근처 · 바닥 근처 (완료이고 W 에서 끝 깊이를 썼지만 막히지 않음) · 앞부분 위 끝 막힘 3번 이상 · 0 dB 경보 · track 전체가 우연(1/3)보다 낫다는 증거 없음
js 는 70.7 % 검정을 부동소수(`Stats.le`)로 셈 — 여기서는 `belowSig` (ℤ[√2] 정확 판정). 둘이 다르면 CrossCheck 가 잡음.
자리 검정(순열, 부동소수 통계량)과 제시 설정 표시는 이 모형 밖.

증명한 것: `numeric_iff` (숫자 역치 ⇔ 첫 상태 완료 ∧ 0 dB 경보 없음 ∧ W 에 막힌 이동 없음 ∧ W 정답률 < 70.7 % 가 확인되지 않음) ·
`zero_alarm_unreliable` · `both_ends_unreliable` · `above_iff` (‘> 60 dB’ 의 조건) · `numeric_thr_bounds` (숫자 역치는 0 … 60 dB) ·
`refineCore_cases` (판정 조건 7개의 128가지 경우를 모두 따짐)
-/

namespace SMD

inductive AStatus
  | completeInRange | trialCap | techFail | insufficient | unreliable | aboveRange | nearCeiling | nearFloor | aboveWindow
deriving DecidableEq, Repr, Inhabited

inductive AReason
  | none | zeroAbove | bothEnds | ceilWorse | ceilBelow | ceilBlocked | floorBlocked | windowBelow
deriving DecidableEq, Repr, Inhabited

/-- W 안의 셈 (js `bound`) -/
structure Bound where
  nWin : Nat
  kWin : Nat
  ceilBlocksWin : Nat
  floorBlocksWin : Nat
  ceilBlocksBefore : Nat
  touchedCeil : Bool
  touchedFloor : Bool
  nC : Nat
  kC : Nat
  nL : Nat
  kL : Nat
deriving Repr, Inhabited

structure AResult where
  status : AStatus
  reason : AReason
  nearCeil : Bool
  nearFloor : Bool
  earlyCeil : Bool
  zeroAlarm : Bool
  notAboveChance : Bool
  thr : Option (Nat × Nat)   -- 숫자 역치일 때만 (h 합, 개수 — dB = 합 / (2 · 개수))
  bound : Option Bound
  sigCeilWorse : Bool
  ceilBelow : Bool
  winBelow : Bool
  nZero : Nat
  kZero : Nat
deriving Repr, Inhabited

/-- 막힌 이동의 끝: 1 위 끝(ceiling) · 2 바닥(floor) -/
def isBlockAt (t : Tr) (side : Nat) : Bool := t.move == .blocked && t.blockedAt == side

def firstStatus (c : Cfg) (s : St) : AStatus :=
  if s.status = .techFail then .techFail
  else if s.status = .trialCap then .trialCap
  else if s.status = .reversalTarget ∧ (threshold c s).isSome then .completeInRange
  else .insufficient

/-- 분석 구간 W (js) -/
def window (c : Cfg) (s : St) (valid : List Tr) (st0 : AStatus) : Option (List Tr) :=
  if st0 = .completeInRange then
    let nDrop := s.revs.length - c.retained
    if nDrop > 0 then
      let lastDrop := s.revs.getD (nDrop - 1) default
      some (valid.filter (fun t => t.validNo > lastDrop.validNo))
    else some valid
  else if st0 = .trialCap then some (valid.drop (valid.length - 20))
  else none

def boundOf (c : Cfg) (valid W : List Tr) : Bound :=
  let firstW := match W.head? with | some t => t.validNo | none => 1000000
  let atC := W.filter (fun t => t.h == c.ceilH)
  let lower := W.filter (fun t => decide (t.h < c.ceilH))
  { nWin := W.length, kWin := (W.filter (·.correct)).length,
    ceilBlocksWin := (W.filter (isBlockAt · 1)).length,
    floorBlocksWin := (W.filter (isBlockAt · 2)).length,
    ceilBlocksBefore := (valid.filter (fun t => isBlockAt t 1 && decide (t.validNo < firstW))).length,
    touchedCeil := W.any (fun t => t.h == c.ceilH),
    touchedFloor := W.any (fun t => t.h == c.floorH),
    nC := atC.length, kC := (atC.filter (·.correct)).length,
    nL := lower.length, kL := (lower.filter (·.correct)).length }

/-- js: `(atC.length && lower.length) ? fisherGreater(kl, lower.length − kl, kc, atC.length − kc) : null` 의 lt05 -/
def sigCeilWorseOf (b : Bound) : Bool := decide (b.nC > 0) && decide (b.nL > 0) && fgSig b.kL (b.nL - b.kL) b.kC (b.nC - b.kC)

/-- 위 끝 정답률 < 70.7 % 확인 (정확): nC > 0 이고 P(X ≤ kC | nC, 1/√2) < 1/20 -/
def ceilBelowOf (b : Bound) : Bool := decide (b.nC > 0) && belowSig b.nC b.kC

/-- W 정답률 < 70.7 % 확인 (정확): 수렴 점검 -/
def winBelowOf (b : Bound) : Bool := decide (b.nWin > 0) && belowSig b.nWin b.kWin

/-- 0 dB 검정: h = 0 유효 시행 전부의 정답률 > 1/3 (정확 이항 p < 1/20) -/
def zeroAlarmOf (valid : List Tr) : Bool :=
  let z := valid.filter (fun t => t.h == 0)
  decide (z.length > 0) && geThirdSig z.length (z.filter (·.correct)).length

/-- 판정의 핵심 — 조건 7개 (js 의 if 순서 그대로): 첫 상태가 완료 · 시행 상한인가(active) · 0 dB 경보 · 위 끝 막힘 · 바닥 막힘 ·
  Fisher 신뢰성 부족 · 위 끝 정답률 < 70.7 % 확인 · W 정답률 < 70.7 % 확인 (W 판정은 첫 상태가 완료일 때만) -/
def refineCore (st0 : AStatus) (active zero limC limF sigC cBel wBel : Bool) : AStatus × AReason :=
  if active then
    if zero then (.unreliable, .zeroAbove)
    else if limC && limF then (.unreliable, .bothEnds)
    else if limC then
      if sigC then (.unreliable, .ceilWorse)
      else if cBel then (.aboveRange, .ceilBelow)
      else (.nearCeiling, .ceilBlocked)
    else if limF then (.nearFloor, .floorBlocked)
    else if st0 = .completeInRange && wBel then (.aboveWindow, .windowBelow)
    else (st0, .none)
  else (st0, .none)

/-- 마지막 상태 (blocksMax = 0: 막힌 이동이 하나라도 있으면 막힘) -/
def refine (st0 : AStatus) (zero : Bool) (b : Bound) : AStatus × AReason :=
  refineCore st0 (st0 == .completeInRange || st0 == .trialCap) zero (decide (b.ceilBlocksWin > 0)) (decide (b.floorBlocksWin > 0))
    (sigCeilWorseOf b) (ceilBelowOf b) (winBelowOf b)

/-- 분류 (js `classifyAdaptive` 의 판정 부분) -/
def classify (c : Cfg) (s : St) (trs : List Tr) : AResult :=
  let valid := trs.filter (·.isValid)
  let st0 := firstStatus c s
  let W := window c s valid st0
  let b := W.map (boundOf c valid)
  let zero := zeroAlarmOf valid
  let (st, rs) := match b with
    | some b => refine st0 zero b
    | none => (st0, .none)
  let n := valid.length
  let k := (valid.filter (·.correct)).length
  let z := valid.filter (fun t => t.h == 0)
  { status := st, reason := rs,
    nearCeil := (match b with | some b => b.ceilBlocksWin == 0 && b.touchedCeil | none => false) && st == .completeInRange,
    nearFloor := (match b with | some b => b.floorBlocksWin == 0 && b.touchedFloor | none => false) && st == .completeInRange,
    earlyCeil := (match b with | some b => decide (b.ceilBlocksBefore ≥ 3) | none => false),
    zeroAlarm := zero,
    notAboveChance := decide (n > 0) && !geThirdSig n k,
    thr := if st = .completeInRange then threshold c s else none,
    bound := b,
    sigCeilWorse := (match b with | some b => sigCeilWorseOf b | none => false),
    ceilBelow := (match b with | some b => ceilBelowOf b | none => false),
    winBelow := (match b with | some b => winBelowOf b | none => false),
    nZero := z.length, kZero := (z.filter (·.correct)).length }

/-! ## 성질 -/

theorem firstStatus_cases (c : Cfg) (s : St) :
    firstStatus c s = .techFail ∨ firstStatus c s = .trialCap ∨ firstStatus c s = .completeInRange ∨ firstStatus c s = .insufficient := by
  unfold firstStatus; split <;> (try split) <;> (try split) <;> simp

theorem window_some {c : Cfg} {s : St} {v W : List Tr} {st0 : AStatus} (h : window c s v st0 = some W) :
    st0 = .completeInRange ∨ st0 = .trialCap := by
  unfold window at h
  by_cases h1 : st0 = .completeInRange
  · left; exact h1
  · by_cases h2 : st0 = .trialCap
    · right; exact h2
    · simp [h1, h2] at h

/-- 판정 핵심의 모든 경우 (첫 상태 st0 가 판정이 만드는 상태가 아닐 때): 숫자 · ‘> 60 dB’ · 신뢰성 부족의 조건 -/
theorem refineCore_cases (st0 : AStatus) (a z e f sg cb wb : Bool)
    (hst : st0 ≠ .unreliable ∧ st0 ≠ .aboveRange ∧ st0 ≠ .nearCeiling ∧ st0 ≠ .nearFloor ∧ st0 ≠ .aboveWindow) :
    ((refineCore st0 a z e f sg cb wb).1 = .completeInRange ↔
      (st0 = .completeInRange ∧ (a = false ∨ (z = false ∧ e = false ∧ f = false ∧ wb = false)))) ∧
    ((refineCore st0 a z e f sg cb wb).1 = .aboveRange ↔ (a = true ∧ z = false ∧ e = true ∧ f = false ∧ sg = false ∧ cb = true)) ∧
    (a = true → z = true → refineCore st0 a z e f sg cb wb = (.unreliable, .zeroAbove)) ∧
    (a = true → z = false → e = true → f = true → refineCore st0 a z e f sg cb wb = (.unreliable, .bothEnds)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hst
  cases a <;> cases z <;> cases e <;> cases f <;> cases sg <;> cases cb <;> cases wb <;>
    by_cases hc : st0 = .completeInRange <;> simp_all [refineCore]

/-- 첫 상태는 판정이 만드는 상태가 아님 -/
theorem firstStatus_not_refined (c : Cfg) (s : St) :
    firstStatus c s ≠ .unreliable ∧ firstStatus c s ≠ .aboveRange ∧ firstStatus c s ≠ .nearCeiling ∧
    firstStatus c s ≠ .nearFloor ∧ firstStatus c s ≠ .aboveWindow := by
  rcases firstStatus_cases c s with h | h | h | h <;> rw [h] <;> decide

/-- 숫자 역치(범위 안 완료) ⇔ 첫 상태가 완료 ∧ 0 dB 경보 없음 ∧ W 에 위 끝 · 바닥 막힘 없음 ∧ W 정답률 < 70.7 % 가 확인되지 않음 (W 가 있을 때) -/
theorem numeric_iff (c : Cfg) (s : St) (zero : Bool) (b : Bound) :
    (refine (firstStatus c s) zero b).1 = .completeInRange ↔
      (firstStatus c s = .completeInRange ∧ zero = false ∧ b.ceilBlocksWin = 0 ∧ b.floorBlocksWin = 0 ∧ winBelowOf b = false) := by
  unfold refine
  rw [(refineCore_cases _ _ _ _ _ _ _ _ (firstStatus_not_refined c s)).1]
  constructor
  · rintro ⟨h0, h1 | h1⟩
    · rw [h0] at h1; simp at h1
    · simp only [decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero] at h1
      exact ⟨h0, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩
    refine ⟨h0, Or.inr ⟨h1, by simp [h2], by simp [h3], h4⟩⟩

/-- 0 dB 경보는 첫 상태가 완료 · 시행 상한이면 늘 신뢰성 부족 -/
theorem zero_alarm_unreliable {st0 : AStatus} (b : Bound) (h0 : st0 = .completeInRange ∨ st0 = .trialCap) :
    refine st0 true b = (.unreliable, .zeroAbove) := by
  rcases h0 with h0 | h0 <;> subst h0 <;> simp [refine, refineCore]

/-- 0 dB 경보 없이 두 끝 다 막히면 신뢰성 부족 -/
theorem both_ends_unreliable {st0 : AStatus} {b : Bound} (h0 : st0 = .completeInRange ∨ st0 = .trialCap)
    (hE : b.ceilBlocksWin > 0) (hF : b.floorBlocksWin > 0) : refine st0 false b = (.unreliable, .bothEnds) := by
  rcases h0 with h0 | h0 <;> subst h0 <;> simp [refine, refineCore, hE, hF]

/-- ‘> 60 dB’ ⇔ (첫 상태가 완료 · 시행 상한) ∧ 0 dB 경보 없음 ∧ 위 끝만 막힘 ∧ Fisher 신뢰성 부족 아님 ∧ 정확 1/√2 검정이 위 끝 정답률 < 70.7 % 를 확인 -/
theorem above_iff (c : Cfg) (s : St) (zero : Bool) (b : Bound) :
    (refine (firstStatus c s) zero b).1 = .aboveRange ↔
      ((firstStatus c s == .completeInRange || firstStatus c s == .trialCap) = true ∧ zero = false ∧ b.ceilBlocksWin > 0 ∧ b.floorBlocksWin = 0 ∧
        sigCeilWorseOf b = false ∧ ceilBelowOf b = true) := by
  unfold refine
  rw [(refineCore_cases _ _ _ _ _ _ _ _ (firstStatus_not_refined c s)).2.1]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero]

/-- 결과의 숫자 역치는 계단의 역치 그대로 -/
theorem classify_thr {c : Cfg} {s : St} {trs : List Tr} {x : Nat × Nat} (h : (classify c s trs).thr = some x) : threshold c s = some x := by
  unfold classify at h
  simp only [] at h
  split at h <;> split at h <;> first | exact h | cases h

/-- 숫자 역치는 처음부터 돌린 track 에서 0 … 60 dB (마지막 10 반전의 h 합 ≤ 1200, dB = 합 / 20) -/
theorem numeric_thr_bounds (os : List Outcome) {sum cnt : Nat}
    (h : (classify wonCfg (run wonCfg (init wonCfg) os).1 (run wonCfg (init wonCfg) os).2).thr = some (sum, cnt)) :
    cnt = 10 ∧ sum ≤ 1200 :=
  run_threshold_bounds os (classify_thr h)

end SMD

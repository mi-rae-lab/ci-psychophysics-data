import SRD.Exact
import SRD.Target
import SRD.Stair

/-!
# 적응 track 분류 — 앱 `js/analysis.js` `classifyAdaptive` 의 판정 경로 (Claude, 2026-10-21)

js 와 같은 순서:
1. 계단 상태로 첫 상태: 기술적 실패 · 시행 상한 · (반전 13번 + 역치 있음) → 범위 안 완료 · 그 밖 자료 부족
2. 분석 구간 W: 완료면 남기지 않은 마지막 반전(5번째)의 다음 유효 시행부터 끝까지, 시행 상한이면 마지막 20 유효 시행
3. W 안: 쉬운 끝(칸 0)에 막힌 이동 수 · 어려운 끝(칸 13)에 막힌 이동 수 · 칸 0 과 더 촘촘한 칸의 정답 · 칸 13 의 정답
4. 완료 · 시행 상한이면: 두 끝 다 막힘 → 신뢰성 부족 · 쉬운 끝 막힘 → (Fisher: 칸 0 정답률 < 촘촘한 칸, p < .05) 신뢰성 부족 /
   (칸 0 정답률 < 70.7 % 확인) < 0.125 범위 밖 / 그 밖 쉬운 끝 막힘 · 어려운 끝 막힘 → (칸 13 정답률 > 70.7 % 확인) > 11.314 범위 밖 / 그 밖 어려운 끝 막힘
5. 표시: 쉬운 끝 근처 · 어려운 끝 근처 (완료이고 W 에서 끝 칸을 썼지만 막히지 않음) · 앞부분 쉬운 끝 막힘 3번 이상 · track 전체가 우연(1/3)보다 낫다는 증거 없음
js 는 4 의 70.7 % 검정을 부동소수로 셈 — 여기서는 `belowSig` · `aboveSig` (ℤ[√2] 정확 판정). 둘이 다르면 CrossCheck 가 잡음.
자리 검정(순열, 부동소수 통계량)과 제시 설정 표시는 이 모형 밖.

증명한 것: `numeric_no_blocks` (숫자 역치는 W 에 막힌 이동이 없을 때만) · `below_iff` · `above_iff` (범위 밖 판정의 조건) ·
`both_ends_unreliable` · `numeric_thr_bounds` (숫자 역치는 0.125 … 11.314 rpo)
-/

namespace SRD

inductive AStatus
  | completeInRange | trialCap | techFail | insufficient | unreliable | belowRange | nearEasy | aboveRange | nearHard
deriving DecidableEq, Repr, Inhabited

inductive AReason
  | none | bothEnds | easyWorse | easyBelow | easyBlocked | hardAbove | hardBlocked
deriving DecidableEq, Repr, Inhabited

/-- W 안의 셈 (js `bound`) -/
structure Bound where
  nWin : Nat
  easyBlocksWin : Nat
  hardBlocksWin : Nat
  easyBlocksBefore : Nat
  touchedEasy : Bool
  touchedHard : Bool
  n0 : Nat
  k0 : Nat
  nHarder : Nat
  kHarder : Nat
  nH : Nat
  kH : Nat
deriving Repr, Inhabited

structure AResult where
  status : AStatus
  reason : AReason
  nearEasy : Bool
  nearHard : Bool
  earlyEasy : Bool
  notAboveChance : Bool
  thr : Option (Nat × Nat)   -- 숫자 역치일 때만 (milli 합, 개수)
  bound : Option Bound
  sigEasyWorse : Bool
  below : Bool
  above : Bool
deriving Repr, Inhabited

def isBlockAt (t : Tr) (side : Nat) : Bool := t.move == .blocked && t.blockedAt == side

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
  let at0 := W.filter (fun t => t.k == c.minK)
  let atH := W.filter (fun t => t.k == c.maxK)
  let harder := W.filter (fun t => t.k > c.minK)
  { nWin := W.length,
    easyBlocksWin := (W.filter (isBlockAt · 1)).length,
    hardBlocksWin := (W.filter (isBlockAt · 2)).length,
    easyBlocksBefore := (valid.filter (fun t => isBlockAt t 1 && decide (t.validNo < firstW))).length,
    touchedEasy := W.any (fun t => t.k == c.minK),
    touchedHard := W.any (fun t => t.k == c.maxK),
    n0 := at0.length, k0 := (at0.filter (·.correct)).length,
    nHarder := harder.length, kHarder := (harder.filter (·.correct)).length,
    nH := atH.length, kH := (atH.filter (·.correct)).length }

/-- js: `(at0.length && harder.length) ? fisherGreater(kh, harder.length − kh, k0, at0.length − k0) : null` 의 lt05 -/
def sigEasyWorseOf (b : Bound) : Bool :=
  b.n0 > 0 && b.nHarder > 0 && fgSig b.kHarder (b.nHarder - b.kHarder) b.k0 (b.n0 - b.k0)

/-- 0.125 정답률 < 70.7 % 확인 (정확): n0 > 0 이고 P(X ≤ k0 | n0, 1/√2) < 1/20 -/
def belowOf (b : Bound) : Bool := b.n0 > 0 && belowSig b.n0 b.k0
/-- 11.314 정답률 > 70.7 % 확인 (정확): nH > 0 이고 P(X ≥ kH | nH, 1/√2) < 1/20 -/
def aboveOf (b : Bound) : Bool := b.nH > 0 && aboveSig b.nH b.kH

def firstStatus (c : Cfg) (s : St) : AStatus :=
  if s.status = .techFail then .techFail
  else if s.status = .trialCap then .trialCap
  else if s.status = .reversalTarget ∧ (threshold c s).isSome then .completeInRange
  else .insufficient

/-- 끝 막힘에 따른 마지막 상태의 핵심 — 조건 6개: 첫 상태가 완료·시행 상한인가 · 쉬운 끝 막힘 · 어려운 끝 막힘 ·
  Fisher 신뢰성 부족 · 0.125 정답률 < 70.7 % 확인 · 11.314 정답률 > 70.7 % 확인 (js 의 if 순서 그대로) -/
def refineCore (st0 : AStatus) (active limE limH sigE bel abv : Bool) : AStatus × AReason :=
  if active then
    if limE && limH then (.unreliable, .bothEnds)
    else if limE then
      if sigE then (.unreliable, .easyWorse)
      else if bel then (.belowRange, .easyBelow)
      else (.nearEasy, .easyBlocked)
    else if limH then
      if abv then (.aboveRange, .hardAbove)
      else (.nearHard, .hardBlocked)
    else (st0, .none)
  else (st0, .none)

/-- 끝 막힘에 따른 마지막 상태 (blocksMax = 0) -/
def refine (st0 : AStatus) (b : Bound) : AStatus × AReason :=
  refineCore st0 (st0 == .completeInRange || st0 == .trialCap) (decide (b.easyBlocksWin > 0)) (decide (b.hardBlocksWin > 0))
    (sigEasyWorseOf b) (belowOf b) (aboveOf b)

/-- 분류 (js `classifyAdaptive` 의 판정 부분) -/
def classify (c : Cfg) (s : St) (trs : List Tr) : AResult :=
  let valid := trs.filter (·.isValid)
  let st0 := firstStatus c s
  let W := window c s valid st0
  let b := W.map (boundOf c valid)
  let (st, rs) := match b with
    | some b => refine st0 b
    | none => (st0, .none)
  let n := valid.length
  let k := (valid.filter (·.correct)).length
  { status := st, reason := rs,
    nearEasy := (match b with | some b => b.easyBlocksWin == 0 && b.touchedEasy | none => false) && st == .completeInRange,
    nearHard := (match b with | some b => b.hardBlocksWin == 0 && b.touchedHard | none => false) && st == .completeInRange,
    earlyEasy := (match b with | some b => b.easyBlocksBefore ≥ 3 | none => false),
    notAboveChance := n > 0 && !geThirdSig n k,
    thr := if st = .completeInRange then threshold c s else none,
    bound := b,
    sigEasyWorse := (match b with | some b => sigEasyWorseOf b | none => false),
    below := (match b with | some b => belowOf b | none => false),
    above := (match b with | some b => aboveOf b | none => false) }

/-! ## 성질 -/

/-- 첫 상태는 이 넷 가운데 하나 -/
theorem firstStatus_cases (c : Cfg) (s : St) :
    firstStatus c s = .techFail ∨ firstStatus c s = .trialCap ∨ firstStatus c s = .completeInRange ∨ firstStatus c s = .insufficient := by
  unfold firstStatus; split <;> (try split) <;> (try split) <;> simp

/-- 창이 있으면 첫 상태는 완료 또는 시행 상한 -/
theorem window_some {c : Cfg} {s : St} {v W : List Tr} {st0 : AStatus} (h : window c s v st0 = some W) :
    st0 = .completeInRange ∨ st0 = .trialCap := by
  unfold window at h
  by_cases h1 : st0 = .completeInRange
  · left; exact h1
  · by_cases h2 : st0 = .trialCap
    · right; exact h2
    · simp [h1, h2] at h

/-- 핵심 판정의 성질 — 조건 6개의 64가지 경우를 모두 따짐 (첫 상태 st0 는 범위 밖 · 신뢰성 부족 · 끝 막힘이 아님) -/
theorem refineCore_props (st0 : AStatus) (a e h sg bl ab : Bool)
    (hst : st0 ≠ .belowRange ∧ st0 ≠ .aboveRange ∧ st0 ≠ .unreliable ∧ st0 ≠ .nearEasy ∧ st0 ≠ .nearHard) :
    ((refineCore st0 a e h sg bl ab).1 = .belowRange ↔ (a = true ∧ e = true ∧ h = false ∧ sg = false ∧ bl = true)) ∧
    ((refineCore st0 a e h sg bl ab).1 = .aboveRange ↔ (a = true ∧ e = false ∧ h = true ∧ ab = true)) ∧
    (a = true → e = true → h = true → refineCore st0 a e h sg bl ab = (.unreliable, .bothEnds)) ∧
    ((refineCore st0 a e h sg bl ab).1 = st0 → (a = false ∨ (e = false ∧ h = false))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hst
  cases a <;> cases e <;> cases h <;> cases sg <;> cases bl <;> cases ab <;> simp_all [refineCore] <;>
    (try (intro hh; subst hh; simp_all))

/-- 핵심 판정이 ‘범위 안 완료’ 를 내면: 첫 상태가 완료였고, 판정이 꺼져 있었거나 두 끝 다 막히지 않음 -/
theorem refineCore_complete (st0 : AStatus) (a e h sg bl ab : Bool) (hc : (refineCore st0 a e h sg bl ab).1 = .completeInRange) :
    st0 = .completeInRange ∧ (a = false ∨ (e = false ∧ h = false)) := by
  cases a <;> cases e <;> cases h <;> cases sg <;> cases bl <;> cases ab <;> simp_all [refineCore]

/-- 숫자 역치(범위 안 완료)는 분석 구간에 끝에 막힌 이동이 하나도 없을 때만 -/
theorem numeric_no_blocks (c : Cfg) (s : St) (trs : List Tr) (h : (classify c s trs).status = .completeInRange) :
    ∀ b, (classify c s trs).bound = some b → b.easyBlocksWin = 0 ∧ b.hardBlocksWin = 0 := by
  intro b hb
  unfold classify at h hb
  simp only [] at h hb
  cases hW : window c s (trs.filter (·.isValid)) (firstStatus c s) with
  | none => simp [hW] at hb
  | some W =>
    simp only [hW, Option.map_some, Option.some.injEq] at hb h
    subst hb
    have hact := window_some hW
    unfold refine at h
    have hc := refineCore_complete _ _ _ _ _ _ _ h
    have ha : (firstStatus c s == .completeInRange || firstStatus c s == .trialCap) = true := by
      rcases hact with h' | h' <;> rw [h'] <;> decide
    rw [ha] at hc
    rcases hc.2 with h1 | ⟨hE, hH⟩
    · cases h1
    · simp only [decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero] at hE hH
      exact ⟨hE, hH⟩

/-- 두 끝 다 막히면 신뢰성 부족 (첫 상태가 완료 · 시행 상한일 때) -/
theorem both_ends_unreliable {st0 : AStatus} {b : Bound} (h0 : st0 = .completeInRange ∨ st0 = .trialCap)
    (hE : b.easyBlocksWin > 0) (hH : b.hardBlocksWin > 0) : refine st0 b = (.unreliable, .bothEnds) := by
  rcases h0 with h0 | h0 <;> subst h0 <;> simp [refine, refineCore, hE, hH]

/-- ‘< 0.125 rpo’ ⇔ (첫 상태가 완료 · 시행 상한) ∧ 쉬운 끝만 막힘 ∧ Fisher 신뢰성 부족 아님 ∧ 정확 1/√2 검정이 확인 -/
theorem below_iff (c : Cfg) (s : St) (b : Bound) :
    (refine (firstStatus c s) b).1 = .belowRange ↔
      ((firstStatus c s == .completeInRange || firstStatus c s == .trialCap) = true ∧ b.easyBlocksWin > 0 ∧ b.hardBlocksWin = 0 ∧
        sigEasyWorseOf b = false ∧ belowOf b = true) := by
  have hst : firstStatus c s ≠ .belowRange ∧ firstStatus c s ≠ .aboveRange ∧ firstStatus c s ≠ .unreliable ∧
      firstStatus c s ≠ .nearEasy ∧ firstStatus c s ≠ .nearHard := by
    rcases firstStatus_cases c s with h | h | h | h <;> rw [h] <;> decide
  unfold refine
  rw [(refineCore_props _ _ _ _ _ _ _ hst).1]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero]

/-- ‘> 11.314 rpo’ ⇔ (첫 상태가 완료 · 시행 상한) ∧ 어려운 끝만 막힘 ∧ 정확 1/√2 검정이 확인 -/
theorem above_iff (c : Cfg) (s : St) (b : Bound) :
    (refine (firstStatus c s) b).1 = .aboveRange ↔
      ((firstStatus c s == .completeInRange || firstStatus c s == .trialCap) = true ∧ b.easyBlocksWin = 0 ∧ b.hardBlocksWin > 0 ∧
        aboveOf b = true) := by
  have hst : firstStatus c s ≠ .belowRange ∧ firstStatus c s ≠ .aboveRange ∧ firstStatus c s ≠ .unreliable ∧
      firstStatus c s ≠ .nearEasy ∧ firstStatus c s ≠ .nearHard := by
    rcases firstStatus_cases c s with h | h | h | h <;> rw [h] <;> decide
  unfold refine
  rw [(refineCore_props _ _ _ _ _ _ _ hst).2.1]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero]

/-- 결과의 숫자 역치는 계단의 역치 그대로 -/
theorem classify_thr {c : Cfg} {s : St} {trs : List Tr} {x : Nat × Nat} (h : (classify c s trs).thr = some x) : threshold c s = some x := by
  unfold classify at h
  simp only [] at h
  split at h <;> split at h <;> first | exact h | cases h

/-- 숫자 역치는 처음부터 돌린 track 에서 0.125 … 11.314 rpo (milli 합 / 8000) -/
theorem numeric_thr_bounds (os : List Outcome) {sum cnt : Nat}
    (h : (classify wonCfg (run wonCfg (init wonCfg) os).1 (run wonCfg (init wonCfg) os).2).thr = some (sum, cnt)) :
    cnt = 8 ∧ 125 * 8 ≤ sum ∧ sum ≤ 11314 * 8 :=
  run_threshold_bounds os (classify_thr h)

end SRD

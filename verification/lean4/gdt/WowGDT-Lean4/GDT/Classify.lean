import GDT.Exact
import GDT.Target
import GDT.Proto

/-!
# 적응 track 분류 — 앱 `js/analysis.js` `classifyAdaptive` 의 판정 경로 (Claude, 2026-11-01)

js 와 같은 순서:
1. 계단 상태로 첫 상태: 기술적 실패 · floor_stop → 짧은 끝에 막힘(이유 floor_stop) · ceiling_stop → 긴 끝에 막힘(이유 ceiling_stop) ·
   시행 상한 · (반전 목표 + 역치 있음) → 범위 안 완료 · 그 밖 자료 부족 (멈춤 `participant_aborted` 은 화면 입력이라 모형 밖)
2. 분석 구간 W: 완료면 남기지 않은 마지막 반전의 다음 유효 시행부터 끝까지, 시행 상한이면 마지막 20 유효 시행 (그 밖은 없음)
3. W 안의 셈 (`Bound`): 긴 끝 · 짧은 끝에 막힌 이동 수 · 긴 끝 · 더 짧은 간격 · 짧은 끝 시행과 정답 · W 전체 정답 · W 앞 막힘
4. 완료 · 시행 상한이면 (`refineCore`): 두 끝 다 막힘 → 신뢰성 부족 · 긴 끝 막힘 → (Fisher 긴 끝 < 더 짧은 간격) 신뢰성 부족 /
   (긴 끝 정답률 < 목표 확인) 범위 밖(더 김) / 그 밖 긴 끝에 막힘 · 짧은 끝 막힘 → (짧은 끝 정답률 > 목표 확인) 범위 밖(더 짧음) / 짧은 끝에 막힘 ·
   (완료 ∧ 목표 > 우연 ∧ W 정답률 < 목표 확인) → 계단이 아직 올라가는 중
5. 우연 관문 (`gateCore`, 절차가 chance_gate 일 때): 아직 완료이고 시행 전체 정답률 > 1/q 가 확인되지 않으면 → 우연보다 높다는 증거 없음
6. 표시: 긴 끝 근처 · 짧은 끝 근처 (관문 앞 상태가 완료이고 W 가 끝 칸에 닿았지만 막히지 않음) · 앞부분 긴 끝 막힘 3번 이상 ·
   규칙이 우연을 쫓음(목표 ≤ 우연) · track 전체가 우연보다 높다는 증거 없음
js 는 목표 검정을 부동소수(`Stats.le/ge`)로 셈 — 여기서는 정확 판정 (1/√2: ℤ[√2], 1/2: 유리수). 둘이 다르면 CrossCheck 가 잡음.
자리 순열 검정 · 제시 설정 표시는 이 모형 밖.

증명한 것: `decision_complete_iff` (판정 핵심 + 관문의 모든 경우: 완료로 남음 ⇔ 첫 상태 완료 ∧ (비활성 ∨ 두 끝 막힘 없음 ∧ ¬(목표 > 우연 ∧ W 아래 확인)) ∧ (관문 없음 ∨ 우연 이상 확인)) ·
`classify_numeric_iff` (숫자 역치 ⇔ 첫 상태 완료 ∧ W 에 막힌 이동 0 ∧ ¬(convOk ∧ W 정답률 < 목표 확인) ∧ (¬관문 ∨ 우연 이상 확인)) ·
`core_above_iff` · `core_below_iff` · `core_unreliable_iff` · `core_window_iff` (범위 밖 · 신뢰성 부족 · 올라가는 중의 조건) ·
`classify_floor_stop` · `classify_ceiling_stop` · `classify_tech_fail` · `aboveWindow_needs_conv` · `notAboveChance_needs_gate` ·
`blank_never_window_or_gate` (blank 은 ‘올라가는 중’ · ‘우연 관문’ 이 나오지 않음) · `classify_thr` · `zeng_numeric_thr` · `xie_numeric_thr` · `blank_numeric_thr`
-/

namespace GDT

inductive AStatus
  | completeInRange | trialCap | techFail | insufficient | nearFloor | nearCeiling
  | unreliable | aboveRange | belowRange | aboveWindow | notAboveChance
deriving DecidableEq, Repr, Inhabited

inductive AReason
  | none | floorStop | ceilingStop | bothEnds | ceilWorse | ceilBelow | ceilBlocked | floorAbove | floorBlocked | windowBelow | notAboveChance
deriving DecidableEq, Repr, Inhabited

/-- W 안의 셈 (js `bound`) -/
structure Bound where
  nWin : Nat
  kWin : Nat
  ceilBlocksWin : Nat
  floorBlocksWin : Nat
  ceilBlocksBefore : Nat
  floorBlocksBefore : Nat
  touchedCeil : Bool
  touchedFloor : Bool
  nC : Nat
  kC : Nat
  nL : Nat
  kL : Nat
  nF : Nat
  kF : Nat
  firstValidNo : Option Nat
deriving Repr, Inhabited

/-- 막힌 이동의 끝: 1 긴 끝(ceiling) · 2 짧은 끝(floor) -/
def isBlockAt (t : Tr) (side : Nat) : Bool := t.move == .blocked && t.blockedAt == side

def firstStatus (c : Cfg) (s : St) : AStatus :=
  match s.status with
  | .techFail => .techFail
  | .floorStop => .nearFloor
  | .ceilingStop => .nearCeiling
  | .trialCap => .trialCap
  | .reversalTarget => if (threshold c s).isSome then .completeInRange else .insufficient
  | .running => .insufficient

/-- js `let reason = floor_stop · ceiling_stop · null` -/
def firstReason (s : St) : AReason :=
  match s.status with
  | .floorStop => .floorStop
  | .ceilingStop => .ceilingStop
  | _ => .none

/-- 분석 구간 W (js) -/
def window (c : Cfg) (s : St) (valid : List Tr) (st0 : AStatus) : Option (List Tr) :=
  if st0 = .completeInRange then
    if s.revs.length - c.retained > 0 then
      some (valid.filter (fun t => t.validNo > (s.revs.getD (s.revs.length - c.retained - 1) default).validNo))
    else some valid
  else if st0 = .trialCap then some (valid.drop (valid.length - 20))
  else none

def boundOf (c : Cfg) (valid W : List Tr) : Bound :=
  let firstW := match W.head? with | some t => t.validNo | none => 1000000000
  { nWin := W.length, kWin := (W.filter (·.correct)).length,
    ceilBlocksWin := (W.filter (isBlockAt · 1)).length,
    floorBlocksWin := (W.filter (isBlockAt · 2)).length,
    ceilBlocksBefore := (valid.filter (fun t => isBlockAt t 1 && decide (t.validNo < firstW))).length,
    floorBlocksBefore := (valid.filter (fun t => isBlockAt t 2 && decide (t.validNo < firstW))).length,
    touchedCeil := W.any (fun t => t.i == c.ceilI),
    touchedFloor := W.any (fun t => t.i == 0),
    nC := (W.filter (fun t => t.i == c.ceilI)).length,
    kC := (W.filter (fun t => t.i == c.ceilI && t.correct)).length,
    nL := (W.filter (fun t => decide (t.i < c.ceilI))).length,
    kL := (W.filter (fun t => decide (t.i < c.ceilI) && t.correct)).length,
    nF := (W.filter (fun t => t.i == 0)).length,
    kF := (W.filter (fun t => t.i == 0 && t.correct)).length,
    firstValidNo := W.head?.map (·.validNo) }

/-- js: `(atC.length && lower.length) ? fisherGreater(kl, lower.length − kl, kc, atC.length − kc) : null` 의 lt05 -/
def sigCeilWorseOf (b : Bound) : Bool := decide (b.nC > 0) && decide (b.nL > 0) && fgSig b.kL (b.nL - b.kL) b.kC (b.nC - b.kC)

/-- 긴 끝 정답률 < 목표 확인 (정확): nC > 0 이고 P(X ≤ kC | nC, tp) < 1/20 -/
def ceilBelowOf (tg : TargetP) (b : Bound) : Bool := decide (b.nC > 0) && leSigT tg b.nC b.kC

/-- 짧은 끝 정답률 > 목표 확인 (정확): nF > 0 이고 P(X ≥ kF | nF, tp) < 1/20 -/
def floorAboveOf (tg : TargetP) (b : Bound) : Bool := decide (b.nF > 0) && geSigT tg b.nF b.kF

/-- W 정답률 < 목표 확인 (정확): 수렴 점검 -/
def winBelowOf (tg : TargetP) (b : Bound) : Bool := decide (b.nWin > 0) && leSigT tg b.nWin b.kWin

/-- 시행 전체 정답률 > 우연 1/q 확인 (js `n && lt05(binomGe(k, n, q))`) -/
def aboveChanceOf (q n k : Nat) : Bool := decide (n > 0) && geSig q n k

/-- 판정의 핵심 (js 의 if 순서 그대로) — active: 첫 상태가 완료 · 시행 상한 -/
def refineCore (st0 : AStatus) (rs0 : AReason) (active limC limF sigC cBel fAbv wBel conv : Bool) : AStatus × AReason :=
  if active then
    if limC && limF then (.unreliable, .bothEnds)
    else if limC then
      if sigC then (.unreliable, .ceilWorse)
      else if cBel then (.aboveRange, .ceilBelow)
      else (.nearCeiling, .ceilBlocked)
    else if limF then
      if fAbv then (.belowRange, .floorAbove)
      else (.nearFloor, .floorBlocked)
    else if st0 == .completeInRange && conv && wBel then (.aboveWindow, .windowBelow)
    else (st0, rs0)
  else (st0, rs0)

/-- 우연 관문 (js: 완료인데 관문 절차이고 우연 이상이 확인되지 않으면) -/
def gateCore (st : AStatus) (rs : AReason) (gate above : Bool) : AStatus × AReason :=
  if st == .completeInRange && gate && !above then (.notAboveChance, .notAboveChance) else (st, rs)

/-! ## 분류 — 칸별 함수 -/

def validOf (trs : List Tr) : List Tr := trs.filter (·.isValid)

def isActive (st0 : AStatus) : Bool := st0 == .completeInRange || st0 == .trialCap

def boundOpt (P : Proto) (s : St) (trs : List Tr) : Option Bound :=
  (window P.cfg s (validOf trs) (firstStatus P.cfg s)).map (boundOf P.cfg (validOf trs))

def limCOf (P : Proto) (b : Bound) : Bool := decide (b.ceilBlocksWin > P.blocksMax)
def limFOf (P : Proto) (b : Bound) : Bool := decide (b.floorBlocksWin > P.blocksMax)

def refineOf (P : Proto) (s : St) : Option Bound → AStatus × AReason
  | some b => refineCore (firstStatus P.cfg s) (firstReason s) (isActive (firstStatus P.cfg s)) (limCOf P b) (limFOf P b)
      (sigCeilWorseOf b) (ceilBelowOf P.target b) (floorAboveOf P.target b) (winBelowOf P.target b) (convOk P.target P.q)
  | none => (firstStatus P.cfg s, firstReason s)

def aboveOf (P : Proto) (trs : List Tr) : Bool :=
  aboveChanceOf P.q (validOf trs).length ((validOf trs).filter (·.correct)).length

/-- 마지막 상태 · 이유 -/
def statusOf (P : Proto) (s : St) (trs : List Tr) : AStatus × AReason :=
  gateCore (refineOf P s (boundOpt P s trs)).1 (refineOf P s (boundOpt P s trs)).2 P.gate (aboveOf P trs)

structure AResult where
  status : AStatus
  reason : AReason
  nearCeil : Bool
  nearFloor : Bool
  earlyCeil : Bool
  ruleChance : Bool
  notAboveChance : Bool
  /-- 숫자 역치일 때만 (valueOf 합, 개수) -/
  thr : Option (Int × Nat)
  /-- 계단의 역치 R (상태와 상관없이) -/
  thrRaw : Option (Int × Nat)
  bound : Option Bound
  sigCeilWorse : Bool
  ceilBelow : Bool
  floorAbove : Bool
  winBelow : Bool
  /-- 우연 검정 p 의 분자 · 분모 (js `pVsChanceExact`) -/
  pAll : Option (Nat × Nat)
  nValid : Nat
  nCorrect : Nat
  nAttempts : Nat
  nTech : Nat
  nBlocked : Nat
  maxI : Option Nat
  minI : Option Nat
deriving Repr, Inhabited

/-- 분류 (js `classifyAdaptive` 의 판정 · 대조 부분) -/
def classify (P : Proto) (s : St) (trs : List Tr) : AResult :=
  let valid := validOf trs
  let bo := boundOpt P s trs
  let pre := (refineOf P s bo).1
  let fin := statusOf P s trs
  let n := valid.length
  let k := (valid.filter (·.correct)).length
  { status := fin.1, reason := fin.2,
    nearCeil := (match bo with | some b => !limCOf P b && b.touchedCeil | none => false) && pre == .completeInRange,
    nearFloor := (match bo with | some b => !limFOf P b && b.touchedFloor | none => false) && pre == .completeInRange,
    earlyCeil := (match bo with | some b => decide (b.ceilBlocksBefore ≥ 3) | none => false),
    ruleChance := !convOk P.target P.q,
    notAboveChance := decide (n > 0) && !geSig P.q n k,
    thr := if fin.1 = .completeInRange then threshold P.cfg s else none,
    thrRaw := threshold P.cfg s,
    bound := bo,
    sigCeilWorse := (match bo with | some b => sigCeilWorseOf b | none => false),
    ceilBelow := (match bo with | some b => ceilBelowOf P.target b | none => false),
    floorAbove := (match bo with | some b => floorAboveOf P.target b | none => false),
    winBelow := (match bo with | some b => winBelowOf P.target b | none => false),
    pAll := if n > 0 then some (geNum P.q n k, geDen P.q n) else none,
    nValid := n, nCorrect := k, nAttempts := s.attempts, nTech := s.tech,
    nBlocked := (valid.filter (·.move == .blocked)).length,
    maxI := (valid.map (·.i)).max?, minI := (valid.map (·.i)).min? }

/-! ## 판정 핵심의 모든 경우 -/

/-- 완료로 남음 ⇔ 첫 상태 완료 ∧ (비활성 ∨ (긴 끝 · 짧은 끝 막힘 없음 ∧ ¬(목표 > 우연 ∧ W 아래 확인))) ∧ (관문 없음 ∨ 우연 이상 확인) -/
theorem decision_complete_iff (st0 : AStatus) (rs0 : AReason) (a lc lf sc cb fa wb cv g ab : Bool) :
    (gateCore (refineCore st0 rs0 a lc lf sc cb fa wb cv).1 (refineCore st0 rs0 a lc lf sc cb fa wb cv).2 g ab).1 = .completeInRange ↔
      st0 = .completeInRange ∧ (a = false ∨ (lc = false ∧ lf = false ∧ (cv && wb) = false)) ∧ (g = false ∨ ab = true) := by
  by_cases h : st0 = .completeInRange
  · subst h
    cases a <;> cases lc <;> cases lf <;> cases sc <;> cases cb <;> cases fa <;> cases wb <;> cases cv <;> cases g <;> cases ab <;>
      simp [refineCore, gateCore]
  · constructor
    · intro hc
      exfalso
      unfold gateCore refineCore at hc
      cases a <;> cases lc <;> cases lf <;> cases sc <;> cases cb <;> cases fa <;> cases g <;> cases ab <;>
        simp_all
    · intro hc; exact absurd hc.1 h

/-- 범위 밖(더 김) ⇔ 활성 ∧ 긴 끝만 막힘 ∧ Fisher 신뢰성 부족 아님 ∧ 긴 끝 정답률 < 목표 확인 (첫 상태가 범위 밖 · 관문 상태가 아닐 때) -/
theorem core_above_iff (st0 : AStatus) (rs0 : AReason) (a lc lf sc cb fa wb cv : Bool) (h0 : st0 ≠ .aboveRange) :
    (refineCore st0 rs0 a lc lf sc cb fa wb cv).1 = .aboveRange ↔ (a = true ∧ lc = true ∧ lf = false ∧ sc = false ∧ cb = true) := by
  unfold refineCore
  cases a <;> cases lc <;> cases lf <;> cases sc <;> cases cb <;> cases fa <;> cases wb <;> cases cv <;>
    by_cases hc : st0 = .completeInRange <;> simp_all

/-- 범위 밖(더 짧음) ⇔ 활성 ∧ 짧은 끝만 막힘 ∧ 짧은 끝 정답률 > 목표 확인 -/
theorem core_below_iff (st0 : AStatus) (rs0 : AReason) (a lc lf sc cb fa wb cv : Bool) (h0 : st0 ≠ .belowRange) :
    (refineCore st0 rs0 a lc lf sc cb fa wb cv).1 = .belowRange ↔ (a = true ∧ lc = false ∧ lf = true ∧ fa = true) := by
  unfold refineCore
  cases a <;> cases lc <;> cases lf <;> cases sc <;> cases cb <;> cases fa <;> cases wb <;> cases cv <;>
    by_cases hc : st0 = .completeInRange <;> simp_all

/-- 신뢰성 부족 ⇔ 활성 ∧ (두 끝 다 막힘 ∨ 긴 끝 막힘이고 Fisher: 긴 끝 정답률 < 더 짧은 간격) -/
theorem core_unreliable_iff (st0 : AStatus) (rs0 : AReason) (a lc lf sc cb fa wb cv : Bool) (h0 : st0 ≠ .unreliable) :
    (refineCore st0 rs0 a lc lf sc cb fa wb cv).1 = .unreliable ↔ (a = true ∧ lc = true ∧ (lf = true ∨ sc = true)) := by
  unfold refineCore
  cases a <;> cases lc <;> cases lf <;> cases sc <;> cases cb <;> cases fa <;> cases wb <;> cases cv <;>
    by_cases hc : st0 = .completeInRange <;> simp_all

/-- 계단이 아직 올라가는 중 ⇔ 활성 ∧ 막힘 없음 ∧ 첫 상태 완료 ∧ 목표 > 우연 ∧ W 정답률 < 목표 확인 -/
theorem core_window_iff (st0 : AStatus) (rs0 : AReason) (a lc lf sc cb fa wb cv : Bool) (h0 : st0 ≠ .aboveWindow) :
    (refineCore st0 rs0 a lc lf sc cb fa wb cv).1 = .aboveWindow ↔
      (a = true ∧ lc = false ∧ lf = false ∧ st0 = .completeInRange ∧ cv = true ∧ wb = true) := by
  unfold refineCore
  cases a <;> cases lc <;> cases lf <;> cases sc <;> cases cb <;> cases fa <;> cases wb <;> cases cv <;>
    by_cases hc : st0 = .completeInRange <;> simp_all

/-! ## 분류 수준의 성질 -/

theorem window_of_complete {c : Cfg} {s : St} {v : List Tr} (h : firstStatus c s = .completeInRange) :
    ∃ W, window c s v (firstStatus c s) = some W := by
  unfold window; rw [h]; simp only [↓reduceIte]; split <;> exact ⟨_, rfl⟩

theorem boundOpt_of_complete {P : Proto} {s : St} {trs : List Tr} (h : firstStatus P.cfg s = .completeInRange) :
    ∃ b, boundOpt P s trs = some b := by
  obtain ⟨W, hW⟩ := window_of_complete (v := validOf trs) h
  exact ⟨_, by unfold boundOpt; rw [hW]; rfl⟩

/-- 숫자 역치 (범위 안 완료로 남음) ⇔ 첫 상태 완료 ∧ W 에 긴 끝 · 짧은 끝 막힌 이동이 없음 (허용 0) ∧
  ¬(목표 > 우연 ∧ W 정답률 < 목표 확인) ∧ (관문 없음 ∨ 시행 전체 정답률 > 우연 확인) -/
theorem classify_numeric_iff (P : Proto) (s : St) (trs : List Tr) (hbm : P.blocksMax = 0) :
    (statusOf P s trs).1 = .completeInRange ↔
      firstStatus P.cfg s = .completeInRange ∧
      ∃ b, boundOpt P s trs = some b ∧ b.ceilBlocksWin = 0 ∧ b.floorBlocksWin = 0 ∧
        (convOk P.target P.q && winBelowOf P.target b) = false ∧ (P.gate = false ∨ aboveOf P trs = true) := by
  unfold statusOf
  cases hb : boundOpt P s trs with
  | none =>
    simp only [refineOf]
    constructor
    · intro hc
      have h0 : firstStatus P.cfg s = .completeInRange := by
        unfold gateCore at hc; split at hc <;> simp_all
      obtain ⟨b, hb'⟩ := boundOpt_of_complete (trs := trs) h0
      rw [hb] at hb'; cases hb'
    · rintro ⟨_, b, hb', _⟩; cases hb'
  | some b =>
    simp only [refineOf]
    rw [decision_complete_iff]
    constructor
    · rintro ⟨h0, h1, h2⟩
      refine ⟨h0, b, rfl, ?_⟩
      rcases h1 with h1 | ⟨h1, h1', h1''⟩
      · simp [isActive, h0] at h1
      · simp only [limCOf, limFOf, hbm, decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero] at h1 h1'
        exact ⟨h1, h1', h1'', h2⟩
    · rintro ⟨h0, b', hb', h1, h2, h3, h4⟩
      cases hb'
      refine ⟨h0, Or.inr ⟨?_, ?_, h3⟩, h4⟩ <;> simp [limCOf, limFOf, hbm, h1, h2]

theorem classify_status (P : Proto) (s : St) (trs : List Tr) : (classify P s trs).status = (statusOf P s trs).1 := rfl
theorem classify_reason (P : Proto) (s : St) (trs : List Tr) : (classify P s trs).reason = (statusOf P s trs).2 := rfl

theorem window_none_of_stop {c : Cfg} {s : St} {v : List Tr}
    (h : firstStatus c s ≠ .completeInRange ∧ firstStatus c s ≠ .trialCap) : window c s v (firstStatus c s) = none := by
  unfold window; simp [h.1, h.2]

/-- floor_stop 으로 멈춘 track → 짧은 끝에 막힘, 이유 floor_stop (분석 구간 판정 · 관문 없이) -/
theorem classify_floor_stop (P : Proto) (s : St) (trs : List Tr) (h : s.status = .floorStop) :
    statusOf P s trs = (.nearFloor, .floorStop) := by
  have h0 : firstStatus P.cfg s = .nearFloor := by simp [firstStatus, h]
  have hb : boundOpt P s trs = none := by
    unfold boundOpt; rw [window_none_of_stop (by rw [h0]; decide)]; rfl
  unfold statusOf; rw [hb]; simp [refineOf, gateCore, h0, firstReason, h]

/-- ceiling_stop 으로 멈춘 track → 긴 끝에 막힘, 이유 ceiling_stop -/
theorem classify_ceiling_stop (P : Proto) (s : St) (trs : List Tr) (h : s.status = .ceilingStop) :
    statusOf P s trs = (.nearCeiling, .ceilingStop) := by
  have h0 : firstStatus P.cfg s = .nearCeiling := by simp [firstStatus, h]
  have hb : boundOpt P s trs = none := by
    unfold boundOpt; rw [window_none_of_stop (by rw [h0]; decide)]; rfl
  unfold statusOf; rw [hb]; simp [refineOf, gateCore, h0, firstReason, h]

/-- 기술적 실패로 끝난 track → 기술적 실패 (이유 없음) -/
theorem classify_tech_fail (P : Proto) (s : St) (trs : List Tr) (h : s.status = .techFail) :
    statusOf P s trs = (.techFail, .none) := by
  have h0 : firstStatus P.cfg s = .techFail := by simp [firstStatus, h]
  have hb : boundOpt P s trs = none := by
    unfold boundOpt; rw [window_none_of_stop (by rw [h0]; decide)]; rfl
  unfold statusOf; rw [hb]; simp [refineOf, gateCore, h0, firstReason, h]

theorem firstStatus_not_window (c : Cfg) (s : St) : firstStatus c s ≠ .aboveWindow ∧ firstStatus c s ≠ .notAboveChance := by
  unfold firstStatus
  cases s.status <;> simp
  split <;> simp

/-- ‘계단이 아직 올라가는 중’ 은 목표 > 우연인 절차에서만 -/
theorem aboveWindow_needs_conv (P : Proto) (s : St) (trs : List Tr) (h : (statusOf P s trs).1 = .aboveWindow) :
    convOk P.target P.q = true := by
  have hf := firstStatus_not_window P.cfg s
  unfold statusOf gateCore at h
  have h' : (refineOf P s (boundOpt P s trs)).1 = .aboveWindow := by split at h <;> simp_all
  cases hb : boundOpt P s trs with
  | none => rw [hb] at h'; simp [refineOf] at h'; exact absurd h' hf.1
  | some b =>
    rw [hb] at h'
    simp only [refineOf] at h'
    exact ((core_window_iff _ _ _ _ _ _ _ _ _ _ hf.1).mp h').2.2.2.2.1

/-- ‘우연보다 높다는 증거 없음’ 은 관문 절차에서만, 그리고 그때 우연 이상이 확인되지 않음 -/
theorem notAboveChance_needs_gate (P : Proto) (s : St) (trs : List Tr) (h : (statusOf P s trs).1 = .notAboveChance) :
    P.gate = true ∧ aboveOf P trs = false := by
  have hf := firstStatus_not_window P.cfg s
  have hr : (refineOf P s (boundOpt P s trs)).1 ≠ .notAboveChance := by
    cases hb : boundOpt P s trs with
    | none => simp [refineOf]; exact hf.2
    | some b =>
      simp only [refineOf, refineCore]
      repeat' split
      all_goals simp_all
  unfold statusOf gateCore at h
  split at h
  · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc; exact ⟨hc.1.2, hc.2⟩
  · exact absurd h hr

/-- blank (목표 1/2 = 우연, 관문 없음): ‘올라가는 중’ · ‘우연보다 높다는 증거 없음’ 이 나오지 않음 -/
theorem blank_never_window_or_gate (s : St) (trs : List Tr) :
    (statusOf blank s trs).1 ≠ .aboveWindow ∧ (statusOf blank s trs).1 ≠ .notAboveChance := by
  constructor
  · intro h; have := aboveWindow_needs_conv blank s trs h; rw [blank_conv] at this; cases this
  · intro h; have := (notAboveChance_needs_gate blank s trs h).1; simp [blank] at this

/-! ## 숫자 역치 = 계단의 역치 -/

theorem classify_thr {P : Proto} {s : St} {trs : List Tr} {x : Int × Nat} (h : (classify P s trs).thr = some x) :
    threshold P.cfg s = some x ∧ (classify P s trs).status = .completeInRange := by
  unfold classify at h
  simp only [] at h
  split at h
  · rename_i hc; exact ⟨h, hc⟩
  · cases h

/-- zeng: 숫자 역치는 처음부터 돌린 track 의 반전 8개 k 합, −96 ≤ Σk ≤ 56 (0.3125 … 226.27 ms) -/
theorem zeng_numeric_thr (os : List Outcome) {sum : Int} {cnt : Nat}
    (h : (classify zeng (run zengCfg (init zengCfg) os).1 (run zengCfg (init zengCfg) os).2).thr = some (sum, cnt)) :
    cnt = 8 ∧ -96 ≤ sum ∧ sum ≤ 56 :=
  zeng_thr os (classify_thr h).1

theorem xie_numeric_thr (os : List Outcome) {sum : Int} {cnt : Nat}
    (h : (classify xie (run xieCfg (init xieCfg) os).1 (run xieCfg (init xieCfg) os).2).thr = some (sum, cnt)) :
    cnt = 6 ∧ 6 ≤ sum ∧ sum ≤ 600 :=
  xie_thr os (classify_thr h).1

theorem blank_numeric_thr (os : List Outcome) {sum : Int} {cnt : Nat}
    (h : (classify blank (run blankCfg (init blankCfg) os).1 (run blankCfg (init blankCfg) os).2).thr = some (sum, cnt)) :
    cnt = 3 ∧ 6 ≤ sum ∧ sum ≤ 360 :=
  blank_thr os (classify_thr h).1

end GDT

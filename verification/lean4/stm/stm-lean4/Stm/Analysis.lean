import Std

/-!
Executable abstraction of `js/analysis.js`, pinned to the inspected source.

Scope and correspondence obligations:
* `classifyCode` begins AFTER construction of the valid-trial analysis window,
  floor predicate, threshold, block count, and the two statistical test results.
  `zeroWorse` and `belowTarget` mean the corresponding p-value exists and is
  strictly below 0.05. This file does NOT prove floating-point probabilities,
  Fisher/binomial tests, window extraction, or JavaScript/Lean equivalence.
* Threshold inputs are exact tenths of a dB. For the default ten retained
  integer-dB reversals, their integer sum is exactly this representation.
  Means are stored as numerator/denominator pairs, without rounded division.
* `condSummary` starts from already filtered and chronologically sorted test
  outcomes. `none` outcomes are removed here. Sorting, raw-record parsing and
  condition/presentation-key construction remain correspondence obligations.
  The model retains state, final value, required count, used tracks, and the
  near-boundary flag; UI notes, provisional display means, IDs and `rule`
  metadata are not represented.
* `groupSummary` accepts the six condition slots in canonical condition order.
  A missing condition is `none`.
-/

namespace Stm.Analysis

inductive Status where
  | insufficient | aborted | technical | cap | complete | below | unreliable
  | above | nearCeiling | protocolDeviation | running | legacyBoundaryAffected
  deriving Repr, DecidableEq, BEq

def Status.code : Status → Nat
  | .insufficient => 0 | .aborted => 1 | .technical => 2 | .cap => 3
  | .complete => 4 | .below => 5 | .unreliable => 6 | .above => 7
  | .nearCeiling => 8 | .protocolDeviation => 9 | .running => 10
  | .legacyBoundaryAffected => 11

def Status.ofCode : Nat → Status
  | 1 => .aborted | 2 => .technical | 3 => .cap | 4 => .complete
  | 5 => .below | 6 => .unreliable | 7 => .above | 8 => .nearCeiling
  | 9 => .protocolDeviation | 10 => .running | 11 => .legacyBoundaryAffected
  | _ => .insufficient

inductive StairStatus where
  | other | technical | cap | reversalTarget
  deriving Repr, DecidableEq, BEq

def StairStatus.ofCode : Nat → StairStatus
  | 1 => .technical | 2 => .cap | 3 => .reversalTarget | _ => .other

structure ClassifyInput where
  aborted : Bool
  hasState : Bool
  stairStatus : StairStatus
  rawTenths : Option Int
  windowFloor : Bool
  blocked : Nat
  ceilingAllowance : Nat
  zeroN : Nat
  zeroWorse : Bool
  belowTarget : Bool
  deriving Repr

def baseStatus (i : ClassifyInput) : Status :=
  if i.aborted then .aborted
  else if !i.hasState then .insufficient
  else match i.stairStatus with
    | .technical => .technical
    | .cap => .cap
    | .reversalTarget => if i.rawTenths.isSome then .complete else .insufficient
    | .other => .insufficient

def censorStatus (zeroWorse belowTarget hasZero : Bool) : Status :=
  if zeroWorse then .unreliable
  else if hasZero && belowTarget then .above
  else .nearCeiling

def refineStatus (base : Status) (floor limited zeroWorse belowTarget hasZero : Bool) : Status :=
  match base with
  | .complete =>
      if floor then .below
      else if limited then censorStatus zeroWorse belowTarget hasZero
      else .complete
  | .cap =>
      if limited then censorStatus zeroWorse belowTarget hasZero else .cap
  | x => x

def classifyStatus (i : ClassifyInput) : Status :=
  refineStatus (baseStatus i) i.windowFloor (decide (i.ceilingAllowance < i.blocked))
    i.zeroWorse i.belowTarget (decide (0 < i.zeroN))

structure Classification where
  status : Status
  thresholdTenths : Option Int
  rawTenths : Option Int
  deriving Repr

def classify (i : ClassifyInput) : Classification :=
  let status := classifyStatus i
  { status, thresholdTenths := if status = .complete then i.rawTenths else none,
    rawTenths := i.rawTenths }

def classifyCode (aborted hasState : Bool) (stateCode : Nat)
    (hasThreshold windowFloor : Bool) (blocked ceilingAllowance zeroN : Nat)
    (zeroWorse belowTarget : Bool) : Nat :=
  (classifyStatus {
    aborted, hasState, stairStatus := StairStatus.ofCode stateCode,
    rawTenths := if hasThreshold then some 0 else none,
    windowFloor, blocked, ceilingAllowance, zeroN, zeroWorse, belowTarget }).code

theorem censor_ne_complete (w b z : Bool) : censorStatus w b z ≠ .complete := by
  cases w <;> cases b <;> cases z <;> decide

theorem refine_complete_iff (s : Status) (f l w b z : Bool) :
    refineStatus s f l w b z = .complete ↔ s = .complete ∧ f = false ∧ l = false := by
  cases s <;> cases f <;> cases l <;>
    simp [refineStatus, censor_ne_complete]

theorem completed_floor_priority (l w b z : Bool) :
    refineStatus .complete true l w b z = .below := by
  rfl

theorem cap_floor_is_not_below (f w b z : Bool) :
    refineStatus .cap f false w b z = .cap := by
  rfl

theorem reliability_priority (b z : Bool) :
    censorStatus true b z = .unreliable := by
  rfl

theorem above_requires_zero_observations (b : Bool) :
    censorStatus false b false = .nearCeiling := by
  cases b <;> rfl

theorem limited_complete_unreliable (b z : Bool) :
    refineStatus .complete false true true b z = .unreliable := by
  rfl

theorem cap_can_be_censored (f b z : Bool) :
    refineStatus .cap f true true b z = .unreliable := by
  rfl

theorem terminal_failure_immune (f l w b z : Bool) :
    refineStatus .technical f l w b z = .technical ∧
    refineStatus .aborted f l w b z = .aborted ∧
    refineStatus .insufficient f l w b z = .insufficient := by
  exact ⟨rfl, rfl, rfl⟩

theorem complete_guard (i : ClassifyInput) (h : classifyStatus i = .complete) :
    baseStatus i = .complete ∧ i.windowFloor = false ∧ i.blocked ≤ i.ceilingAllowance := by
  have hi := (refine_complete_iff _ _ _ _ _ _).mp h
  exact ⟨hi.1, hi.2.1, by simpa using hi.2.2⟩

theorem base_complete_iff (i : ClassifyInput) :
    baseStatus i = .complete ↔
      i.aborted = false ∧ i.hasState = true ∧ i.stairStatus = .reversalTarget ∧
      i.rawTenths.isSome = true := by
  cases i with
  | mk a s status raw floor blocked allowance n worse below =>
      cases a <;> cases s <;> cases status <;> cases raw <;> simp [baseStatus]

theorem complete_full_guard (i : ClassifyInput) :
    classifyStatus i = .complete ↔
      i.aborted = false ∧ i.hasState = true ∧ i.stairStatus = .reversalTarget ∧
      i.rawTenths.isSome = true ∧ i.windowFloor = false ∧
      i.blocked ≤ i.ceilingAllowance := by
  simp only [classifyStatus, refine_complete_iff, base_complete_iff]
  simp only [decide_eq_false_iff_not, Nat.not_lt]
  exact ⟨fun ⟨⟨a, b, c, d⟩, e, f⟩ => ⟨a, b, c, d, e, f⟩,
    fun ⟨a, b, c, d, e, f⟩ => ⟨⟨a, b, c, d⟩, e, f⟩⟩

theorem aborted_priority (i : ClassifyInput) (h : i.aborted = true) :
    classifyStatus i = .aborted := by
  simp [classifyStatus, baseStatus, refineStatus, h]

theorem numeric_only_complete (i : ClassifyInput) (v : Int)
    (h : (classify i).thresholdTenths = some v) :
    (classify i).status = .complete := by
  by_cases hs : classifyStatus i = .complete
  · exact hs
  · simp [classify, hs] at h

theorem numeric_has_guards (i : ClassifyInput) (v : Int)
    (h : (classify i).thresholdTenths = some v) :
    baseStatus i = .complete ∧ i.windowFloor = false ∧ i.blocked ≤ i.ceilingAllowance := by
  exact complete_guard i (numeric_only_complete i v h)

theorem complete_has_numeric (i : ClassifyInput) (h : classifyStatus i = .complete) :
    (classify i).thresholdTenths.isSome = true := by
  have hr := ((base_complete_iff i).mp (complete_guard i h).1).2.2.2
  simp [classify, h, hr]

theorem classification_numeric_iff (i : ClassifyInput) :
    (classify i).thresholdTenths.isSome = true ↔ classifyStatus i = .complete := by
  constructor
  · intro hn
    by_cases hc : classifyStatus i = .complete
    · exact hc
    · simp [classify, hc] at hn
  · exact complete_has_numeric i

theorem strict_ceiling_limit (i : ClassifyInput) (hb : baseStatus i = .complete)
    (hf : i.windowFloor = false) (hcount : i.blocked = i.ceilingAllowance) :
    classifyStatus i = .complete := by
  simp [classifyStatus, hb, hf, hcount, refineStatus]

def applyAudit (auditOK : Bool) (r : Classification) : Classification :=
  if auditOK then r else { r with status := .protocolDeviation, thresholdTenths := none }

theorem failed_audit_erases_numeric (r : Classification) :
    (applyAudit false r).status = .protocolDeviation ∧
    (applyAudit false r).thresholdTenths = none ∧
    (applyAudit false r).rawTenths = r.rawTenths := by
  exact ⟨rfl, rfl, rfl⟩

inductive Kind where
  | none | num | above | ceil | below
  deriving Repr, DecidableEq, BEq

instance : LawfulBEq Kind where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | contradiction
  rfl {a} := by cases a <;> decide

def Kind.ofCode : Nat → Kind
  | 1 => .num | 2 => .above | 3 => .ceil | 4 => .below | _ => .none

def Kind.code : Kind → Nat
  | .none => 0 | .num => 1 | .above => 2 | .ceil => 3 | .below => 4

structure Track where
  kind : Kind
  tenths : Int := 0
  near : Bool := false
  deriving Repr, DecidableEq

structure ResultView where
  status : Status
  thresholdTenths : Option Int
  near : Bool := false
  changedFlag : Bool := false
  deriving Repr

structure RunView where
  adaptive : Bool
  practice : Bool := false
  result : Option ResultView
  changedDuring : Bool := false
  deriving Repr

def outcome (r : RunView) : Track :=
  if !r.adaptive then ⟨.none, 0, false⟩
  else match r.result with
    | none => ⟨.none, 0, false⟩
    | some x =>
        if x.changedFlag || r.changedDuring then ⟨.none, 0, false⟩
        else match x.status, x.thresholdTenths with
          | .complete, some t => ⟨.num, t, x.near⟩
          | .above, _ => ⟨.above, 0, false⟩
          | .nearCeiling, _ => ⟨.ceil, 0, false⟩
          | .below, _ => ⟨.below, 0, false⟩
          | _, _ => ⟨.none, 0, false⟩

def isIncluded (r : RunView) : Bool := !r.practice && (outcome r).kind == .num

def inMainGroup (changedDuring : Bool) (referenceKey : Option String) (key : String) : Bool :=
  !changedDuring && match referenceKey with
    | none => true
    | some reference => key == reference

def outcomeCode (adaptive practice hasResult : Bool) (statusCode : Nat)
    (hasThreshold changedFlag changedDuring near : Bool) (tenths : Int) : Nat × Bool :=
  let r : RunView := {
    adaptive, practice, changedDuring,
    result := if hasResult then some {
      status := Status.ofCode statusCode,
      thresholdTenths := if hasThreshold then some tenths else none,
      changedFlag, near } else none }
  ((outcome r).kind.code, isIncluded r)

theorem changed_during_excluded (r : RunView) (h : r.changedDuring = true) :
    (outcome r).kind = .none := by
  cases hr : r.result <;> simp [outcome, hr, h]

theorem changed_flag_excluded (r : RunView) (x : ResultView)
    (hr : r.result = some x) (hc : x.changedFlag = true) :
    (outcome r).kind = .none := by
  simp [outcome, hr, hc]

theorem practice_excluded (r : RunView) (h : r.practice = true) :
    isIncluded r = false := by
  simp [isIncluded, h]

theorem changed_not_in_main (referenceKey : Option String) (key : String) :
    inMainGroup true referenceKey key = false := by
  simp [inMainGroup]

theorem changed_not_included (r : RunView) (h : r.changedDuring = true) :
    isIncluded r = false := by
  simp [isIncluded, changed_during_excluded r h, show (Kind.none == Kind.num) = false from rfl]

/- Exact value represents `numerator / denominator` dB, not an integer quotient. -/
structure ExactMean where
  numerator : Int
  denominator : Nat
  deriving Repr, DecidableEq

def meanOf (ts : List Track) : ExactMean :=
  { numerator := (ts.map (·.tenths)).sum, denominator := 10 * ts.length }

theorem meanOf_positive_denominator (ts : List Track) (h : ts ≠ []) :
    0 < (meanOf ts).denominator := by
  cases ts with
  | nil => contradiction
  | cons a rest => simp [meanOf]

inductive SummaryState where
  | provisional | final | above | ceil | below | mixed
  deriving Repr, DecidableEq, BEq

def SummaryState.code : SummaryState → Nat
  | .provisional => 0 | .final => 1 | .above => 2 | .ceil => 3 | .below => 4 | .mixed => 5

structure Summary where
  state : SummaryState := .provisional
  value : Option ExactMean := none
  needMore : Nat := 0
  used : List Track := []
  boundary : Bool := false
  deriving Repr

def isUp (t : Track) : Bool := t.kind == .above || t.kind == .ceil

def settle (ts : List Track) : Summary :=
  let common : Summary := { used := ts, boundary := ts.any (·.near) }
  if !ts.isEmpty && ts.all (fun t => t.kind == .num) then
    { common with state := .final, value := some (meanOf ts) }
  else if ts.all isUp then
    { common with state := if !ts.isEmpty && ts.all (fun t => t.kind == .above)
                           then .above else .ceil }
  else if !ts.isEmpty && ts.all (fun t => t.kind == .below) then
    { common with state := .below }
  else { common with state := .mixed }

def absDiffTenths (a b : Track) : Nat := (a.tenths - b.tenths).natAbs

def sameCensor (a b : Track) : Bool := a.kind == b.kind || (isUp a && isUp b)

def needThird (a b : Track) : Bool :=
  if a.kind == .num && b.kind == .num then decide (30 < absDiffTenths a b)
  else !sameCensor a b

def selectedCount (sixRule : Bool) (ts : List Track) : Nat :=
  if sixRule then 6
  else match ts with
    | a :: b :: _ => if needThird a b then 3 else 2
    | _ => 2

def condSummary (sixRule : Bool) (orderedOutcomes : List Track) : Summary :=
  let det := orderedOutcomes.filter (fun t => t.kind != .none)
  let need := selectedCount sixRule det
  if det.length < need then { needMore := need - det.length }
  else settle (det.take need)

def summaryCode (sixRule : Bool) (tracks : List (Nat × Int)) : Nat × Nat × Int × Nat :=
  let ts := tracks.map (fun p => ({ kind := Kind.ofCode p.1, tenths := p.2 } : Track))
  let s := condSummary sixRule ts
  (s.state.code, s.needMore, (s.value.map (·.numerator)).getD 0, s.used.length)

theorem selected_six (ts : List Track) : selectedCount true ts = 6 := by
  rfl

theorem selected_won_two_or_three (ts : List Track) :
    selectedCount false ts = 2 ∨ selectedCount false ts = 3 := by
  cases ts with
  | nil => exact Or.inl rfl
  | cons a xs =>
      cases xs with
      | nil => exact Or.inl rfl
      | cons b rest =>
          cases h : needThird a b <;> simp [selectedCount, h]

theorem exactly_three_db_no_third (a b : Track)
    (ha : a.kind = .num) (hb : b.kind = .num) (hd : absDiffTenths a b = 30) :
    needThird a b = false := by
  simp [needThird, ha, hb, hd, show (Kind.num == Kind.num) = true from rfl]

theorem over_three_db_needs_third (a b : Track)
    (ha : a.kind = .num) (hb : b.kind = .num) (hd : 30 < absDiffTenths a b) :
    needThird a b = true := by
  simp [needThird, ha, hb, hd, show (Kind.num == Kind.num) = true from rfl]

theorem exactly_three_db_uses_two (a b : Track) (rest : List Track)
    (ha : a.kind = .num) (hb : b.kind = .num) (hd : absDiffTenths a b = 30) :
    selectedCount false (a :: b :: rest) = 2 := by
  simp [selectedCount, exactly_three_db_no_third a b ha hb hd]

theorem over_three_db_uses_three (a b : Track) (rest : List Track)
    (ha : a.kind = .num) (hb : b.kind = .num) (hd : 30 < absDiffTenths a b) :
    selectedCount false (a :: b :: rest) = 3 := by
  simp [selectedCount, over_three_db_needs_third a b ha hb hd]

theorem numeric_censored_pair_needs_third (a b : Track)
    (ha : a.kind = .num) (hb : b.kind ≠ .num) :
    needThird a b = true := by
  cases hbk : b.kind <;> simp_all [needThird, sameCensor, isUp]

theorem above_ceil_pair_needs_no_third (a b : Track)
    (ha : a.kind = .above) (hb : b.kind = .ceil) :
    needThird a b = false := by
  simp [needThird, sameCensor, isUp, ha, hb]

theorem settle_numeric_iff (ts : List Track) :
    (settle ts).value.isSome = true ↔
      !ts.isEmpty && ts.all (fun t => t.kind == .num) = true := by
  simp only [settle]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  all_goals cases ts <;> simp_all

theorem settle_final_iff (ts : List Track) :
    (settle ts).state = .final ↔
      !ts.isEmpty && ts.all (fun t => t.kind == .num) = true := by
  simp only [settle]
  split <;> simp_all
  split
  · split <;> simp_all
    all_goals cases ts <;> simp_all
  · split <;> simp_all
    all_goals cases ts <;> simp_all

theorem settle_used (ts : List Track) : (settle ts).used = ts := by
  simp only [settle]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

theorem settle_nonfinal_has_no_mean (ts : List Track) (h : (settle ts).state ≠ .final) :
    (settle ts).value = none := by
  simp only [settle] at h ⊢
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

theorem settle_no_numeric_if_nonnum (ts : List Track)
    (h : ts.all (fun t => t.kind == .num) = false) :
    (settle ts).value = none := by
  simp only [settle, h, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  split <;> simp_all
  split <;> simp_all

theorem settle_with_nonnum_has_no_mean (ts : List Track) (x : Track)
    (hx : x ∈ ts) (hk : x.kind ≠ .num) :
    (settle ts).value = none := by
  apply settle_no_numeric_if_nonnum
  cases hb : ts.all (fun t => t.kind == .num) with
  | false => rfl
  | true =>
      have hxnum := (List.all_eq_true.mp hb) x hx
      cases hkind : x.kind <;> simp_all

theorem mixed_has_no_mean (ts : List Track) (h : (settle ts).state = .mixed) :
    (settle ts).value = none := by
  simp only [settle] at h ⊢
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

theorem condition_nonfinal_has_no_mean (sixRule : Bool) (ts : List Track)
    (h : (condSummary sixRule ts).state ≠ .final) :
    (condSummary sixRule ts).value = none := by
  simp only [condSummary] at h ⊢
  split
  · rfl
  · rename_i hc
    apply settle_nonfinal_has_no_mean
    simpa only [hc, ↓reduceIte] using h

theorem condition_mixed_has_no_mean (sixRule : Bool) (ts : List Track)
    (h : (condSummary sixRule ts).state = .mixed) :
    (condSummary sixRule ts).value = none := by
  apply condition_nonfinal_has_no_mean
  simp [h]

theorem settle_numeric_positive_denominator (ts : List Track) (v : ExactMean)
    (h : (settle ts).value = some v) : 0 < v.denominator := by
  simp only [settle] at h
  split at h
  · rename_i hc
    have hm : meanOf ts = v := Option.some.inj h
    rw [← hm]
    apply meanOf_positive_denominator
    intro he
    simp [he] at hc
  · split at h <;> simp_all
    split at h <;> simp_all

theorem condition_numeric_positive_denominator (sixRule : Bool) (ts : List Track) (v : ExactMean)
    (h : (condSummary sixRule ts).value = some v) : 0 < v.denominator := by
  simp only [condSummary] at h
  split at h
  · contradiction
  · exact settle_numeric_positive_denominator _ v h

theorem six_pending_below_six (ts : List Track)
    (h : (ts.filter (fun t => t.kind != .none)).length < 6) :
    (condSummary true ts).state = .provisional ∧
    (condSummary true ts).value = none ∧
    (condSummary true ts).needMore = 6 - (ts.filter (fun t => t.kind != .none)).length := by
  simp [condSummary, selectedCount, h]

theorem six_settles_exactly_first_six (ts : List Track)
    (h : 6 ≤ (ts.filter (fun t => t.kind != .none)).length) :
    condSummary true ts = settle ((ts.filter (fun t => t.kind != .none)).take 6) := by
  simp [condSummary, selectedCount, Nat.not_lt.mpr h]

theorem six_final_uses_six (ts : List Track)
    (h : (condSummary true ts).state = .final) :
    (condSummary true ts).used.length = 6 := by
  by_cases hn : (ts.filter (fun t => t.kind != .none)).length < 6
  · have hp := (six_pending_below_six ts hn).1
    simp [hp] at h
  · have hn' : 6 ≤ (ts.filter (fun t => t.kind != .none)).length := Nat.le_of_not_lt hn
    rw [six_settles_exactly_first_six ts hn', settle_used, List.length_take]
    exact Nat.min_eq_left hn'

def finalValue (s : Option Summary) : Option ExactMean :=
  s.bind (fun x => if x.state = .final then x.value else none)

/- Combining exact rational pairs with no floating-point or integer division. -/
def addExact (a b : ExactMean) : ExactMean :=
  { numerator := a.numerator * b.denominator + b.numerator * a.denominator,
    denominator := a.denominator * b.denominator }

def meanExact (vs : List ExactMean) : ExactMean :=
  let sum := vs.foldl addExact { numerator := 0, denominator := 1 }
  { numerator := sum.numerator, denominator := sum.denominator * vs.length }

structure GroupSummary where
  nFinal : Nat
  all6Final : Bool
  meanSTM : Option ExactMean
  deriving Repr

def groupSummary (slots : List (Option Summary)) : GroupSummary :=
  let finals := slots.filterMap finalValue
  let all6 := decide (finals.length = 6)
  { nFinal := finals.length, all6Final := all6,
    meanSTM := if all6 then some (meanExact finals) else none }

theorem group_numeric_iff_six (slots : List (Option Summary)) :
    (groupSummary slots).meanSTM.isSome = true ↔ (groupSummary slots).nFinal = 6 := by
  simp [groupSummary]

theorem group_non_six_has_no_mean (slots : List (Option Summary))
    (h : (groupSummary slots).nFinal ≠ 6) :
    (groupSummary slots).meanSTM = none := by
  simp [groupSummary] at h ⊢
  exact h

theorem nonfinal_slot_contributes_no_value (s : Summary) (h : s.state ≠ .final) :
    finalValue (some s) = none := by
  simp [finalValue, h]

theorem six_mean_requires_every_slot (slots : List (Option Summary))
    (hlen : slots.length = 6) (hmean : (groupSummary slots).meanSTM.isSome = true) :
    ∀ s ∈ slots, (finalValue s).isSome = true := by
  have hf : (slots.filterMap finalValue).length = 6 := (group_numeric_iff_six slots).mp hmean
  have hnot : ¬ ∃ s ∈ slots, finalValue s = none := by
    intro ⟨s, hs, hv⟩
    have hlt := (List.length_filterMap_lt_length_iff_exists (f := finalValue) (xs := slots)).mpr
      ⟨s, hs, hv⟩
    rw [hf, hlen] at hlt
    exact Nat.lt_irrefl 6 hlt
  intro s hs
  cases hv : finalValue s with
  | none => exact False.elim (hnot ⟨s, hs, hv⟩)
  | some v => rfl

theorem six_mean_requires_final_states (slots : List (Option Summary))
    (hlen : slots.length = 6) (hmean : (groupSummary slots).meanSTM.isSome = true) :
    ∀ s ∈ slots, ∃ cs, s = some cs ∧ cs.state = .final ∧ cs.value.isSome = true := by
  intro s hs
  have hf := six_mean_requires_every_slot slots hlen hmean s hs
  cases s with
  | none => simp [finalValue] at hf
  | some cs =>
      by_cases hcs : cs.state = .final
      · exact ⟨cs, rfl, hcs, by simpa [finalValue, hcs] using hf⟩
      · simp [finalValue, hcs] at hf

theorem missing_slot_forbids_group_mean (slots : List (Option Summary))
    (hlen : slots.length = 6) (hmissing : none ∈ slots) :
    (groupSummary slots).meanSTM = none := by
  cases hv : (groupSummary slots).meanSTM with
  | none => rfl
  | some v =>
      have hs : (groupSummary slots).meanSTM.isSome = true := by simp [hv]
      have hslot := six_mean_requires_every_slot slots hlen hs none hmissing
      simp [finalValue] at hslot

/- Regression witnesses are kernel-checked computations, not exhaustive claims. -/
example : classifyCode false true 3 true false 0 0 0 false false = 4 := by decide
example : classifyCode false true 3 true true 1 0 5 true true = 5 := by decide
example : classifyCode false true 2 false true 0 0 0 false false = 3 := by decide
example : classifyCode false true 2 false true 1 0 5 true true = 6 := by decide
example : summaryCode false [(1, -100), (1, -130)] = (1, 0, -230, 2) := by decide
example : summaryCode false [(1, -100), (1, -131)] = (0, 1, 0, 0) := by decide
example : summaryCode false [(1, -100), (2, 0), (1, -120)] = (5, 0, 0, 3) := by decide
example : summaryCode false [(2, 0), (3, 0)] = (3, 0, 0, 2) := by decide
example : summaryCode true [(1, -100), (1, -120), (1, -130)] = (0, 3, 0, 0) := by decide

end Stm.Analysis

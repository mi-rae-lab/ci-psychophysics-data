import Std

/-!
Executable specification of js/staircase.js for the repository's default
protocol. This models typed, finite integer inputs. JavaScript coercions,
JSON cloning, host exceptions and floating point division are outside it.
The source application is not imported or modified.
-/
namespace Stm.Staircase

inductive Dir where
  | harder | easier
  deriving DecidableEq, Repr, BEq

def Dir.sign : Dir → Int
  | .harder => -1
  | .easier => 1

inductive Status where
  | running | technicalFailure | reversalTargetReached
  | trialCapBeforeReversalTarget
  deriving DecidableEq, Repr, BEq

inductive Bound where
  | ceiling | floor
  deriving DecidableEq, Repr, BEq

inductive Move where
  | invalidNoChange | stay | blockedZeroMove | move
  deriving DecidableEq, Repr, BEq

structure Reversal where
  db : Int
  validNo : Nat
  attemptNo : Nat
  trialId : String
  dirAfter : Dir
  atBound : Option Bound
  deriving DecidableEq, Repr, BEq

structure State where
  levelDb : Int := 0
  correctStreak : Nat := 0
  lastDir : Option Dir := none
  reversals : List Reversal := []
  attemptCount : Nat := 0
  validCount : Nat := 0
  technicalCount : Nat := 0
  moves : Nat := 0
  processed : List String := []
  status : Status := .running
  deriving DecidableEq, Repr, BEq

def init : State := {}

structure Outcome where
  trialId : String
  presentedDb : Int
  valid : Bool
  correct : Bool
  deriving DecidableEq, Repr, BEq

/- The textual invalid reason is not used in numerical state transitions. -/
structure Transition where
  trialId : String
  attemptNo : Nat
  validNo : Option Nat
  presentedDb : Int
  valid : Bool
  correct : Option Bool
  preStreak : Nat
  postStreak : Nat
  requestedDir : Int := 0
  requestedStepDb : Int := 0
  effectiveStepDb : Nat := 0
  move : Move
  clamped : Bool := false
  reversal : Bool := false
  reversalNo : Option Nat := none
  reversalAtBound : Option Bound := none
  blockedAt : Option Bound := none
  nextDb : Int
  nextPresented : Bool
  statusAfter : Status
  deriving DecidableEq, Repr, BEq

def atBound (db : Int) : Option Bound :=
  if db = 0 then some .ceiling else if db = -50 then some .floor else none

def blocked (db : Int) : Dir → Bool
  | .harder => decide (db ≤ -50)
  | .easier => decide (0 ≤ db)

def isReversal (s : State) (dir : Dir) : Bool :=
  !blocked s.levelDb dir &&
    decide (s.lastDir ≠ none) && decide (s.lastDir ≠ some dir)

def requestedStep (nextReversalCount : Nat) : Int :=
  if nextReversalCount < 4 then 4 else 2

def clamp (want : Int) : Int := min 0 (max (-50) want)

def validStatus (reversals valid : Nat) : Status :=
  if 14 ≤ reversals then .reversalTargetReached
  else if 200 ≤ valid then .trialCapBeforeReversalTarget else .running

/- The reset happens even when the subsequent directional move is blocked. -/
def request (streak : Nat) (correct : Bool) : Option Dir × Nat :=
  if correct then
    if 2 ≤ streak + 1 then (some .harder, 0) else (none, streak + 1)
  else (some .easier, 0)

structure Shift where
  state : State
  requestedStepDb : Int := 0
  effectiveStepDb : Nat := 0
  move : Move
  clamped : Bool := false
  reversal : Bool := false
  reversalNo : Option Nat := none
  reversalAtBound : Option Bound := none
  blockedAt : Option Bound := none
  deriving DecidableEq, Repr, BEq

/- s here already has incremented attempt/valid counts and appended trialId. -/
def shift (s : State) (trialId : String) (dir : Dir) : Shift :=
  let rev := isReversal s dir
  let nextCount := s.reversals.length + if rev then 1 else 0
  let stepDb := requestedStep nextCount
  if blocked s.levelDb dir then
    { state := s, requestedStepDb := stepDb, move := .blockedZeroMove,
      blockedAt := some (if dir = .easier then .ceiling else .floor) }
  else
    let want := s.levelDb + dir.sign * stepDb
    let got := clamp want
    let bound := atBound s.levelDb
    let nextReversals := if rev then s.reversals ++
      [{ db := s.levelDb, validNo := s.validCount, attemptNo := s.attemptCount,
         trialId := trialId, dirAfter := dir, atBound := bound }] else s.reversals
    { state := { s with levelDb := got, lastDir := some dir,
                        reversals := nextReversals, moves := s.moves + 1 },
      requestedStepDb := stepDb, effectiveStepDb := (got - s.levelDb).natAbs,
      move := .move, clamped := decide (got ≠ want), reversal := rev,
      reversalNo := if rev then some nextReversals.length else none,
      reversalAtBound := if rev then bound else none }

def motion (s : State) (id : String) (dir : Option Dir) : Shift :=
  match dir with
  | none => { state := s, move := .stay }
  | some d => shift s id d

def advance (s : State) (o : Outcome) : State × Transition :=
  let counted : State := { s with attemptCount := s.attemptCount + 1, processed := s.processed ++ [o.trialId] }
  if !o.valid then
    let next : State := { counted with technicalCount := s.technicalCount + 1, status := if 10 ≤ s.technicalCount + 1 then .technicalFailure else s.status }
    (next, {
      trialId := o.trialId, attemptNo := next.attemptCount,
      validNo := none, presentedDb := s.levelDb, valid := false, correct := none,
      preStreak := s.correctStreak, postStreak := s.correctStreak,
      move := .invalidNoChange, nextDb := next.levelDb,
      nextPresented := decide (next.status = .running), statusAfter := next.status })
  else
    let req := request s.correctStreak o.correct
    let counted : State := { counted with validCount := s.validCount + 1, correctStreak := req.2 }
    let sh := motion counted o.trialId req.1
    let next : State := { sh.state with status := validStatus sh.state.reversals.length sh.state.validCount }
    (next, {
      trialId := o.trialId, attemptNo := next.attemptCount,
      validNo := some next.validCount, presentedDb := s.levelDb, valid := true,
      correct := some o.correct, preStreak := s.correctStreak,
      postStreak := next.correctStreak,
      requestedDir := match req.1 with | none => 0 | some dir => dir.sign,
      requestedStepDb := sh.requestedStepDb, effectiveStepDb := sh.effectiveStepDb,
      move := sh.move, clamped := sh.clamped, reversal := sh.reversal,
      reversalNo := sh.reversalNo, reversalAtBound := sh.reversalAtBound,
      blockedAt := sh.blockedAt, nextDb := next.levelDb,
      nextPresented := decide (next.status = .running), statusAfter := next.status })

inductive Error where
  | alreadyEnded | depthMismatch
  deriving DecidableEq, Repr, BEq

inductive StepResult where
  | duplicate (state : State)
  | rejected (error : Error)
  | advanced (state : State) (transition : Transition)
  deriving DecidableEq, Repr, BEq

/- Guard priority is part of the executable specification. -/
def step (s : State) (o : Outcome) : StepResult :=
  if o.trialId ∈ s.processed then .duplicate s
  else if s.status ≠ .running then .rejected .alreadyEnded
  else if o.presentedDb ≠ s.levelDb then .rejected .depthMismatch
  else let (next, tr) := advance s o; .advanced next tr

def Bounded (s : State) : Prop := -50 ≤ s.levelDb ∧ s.levelDb ≤ 0
def CountConsistent (s : State) : Prop :=
  s.attemptCount = s.validCount + s.technicalCount ∧
  s.processed.length = s.attemptCount

theorem init_bounded : Bounded init := by simp [Bounded, init]
theorem init_count_consistent : CountConsistent init := by simp [CountConsistent, init]

theorem clamp_bounded (x : Int) : -50 ≤ clamp x ∧ clamp x ≤ 0 := by
  unfold clamp
  omega

theorem requestedStep_positive (r : Nat) : 0 < requestedStep r := by
  unfold requestedStep
  split <;> omega

theorem fourth_reversal_uses_fine : requestedStep 4 = 2 := by decide
theorem before_fourth_uses_coarse (r : Nat) (h : r < 4) :
    requestedStep r = 4 := by simp [requestedStep, h]
theorem fourth_and_later_use_fine (r : Nat) (h : 4 ≤ r) :
    requestedStep r = 2 := by simp [requestedStep, Nat.not_lt.mpr h]

theorem target_has_priority (r v : Nat) (h : 14 ≤ r) :
    validStatus r v = .reversalTargetReached := by simp [validStatus, h]

theorem cap_only_before_target (r v : Nat) (hr : r < 14) (hv : 200 ≤ v) :
    validStatus r v = .trialCapBeforeReversalTarget := by
  simp [validStatus, Nat.not_le.mpr hr, hv]

theorem duplicate_has_priority (s : State) (o : Outcome)
    (h : o.trialId ∈ s.processed) : step s o = .duplicate s := by
  simp [step, h]

theorem ended_before_depth_check (s : State) (o : Outcome)
    (hid : o.trialId ∉ s.processed) (hend : s.status ≠ .running) :
    step s o = .rejected .alreadyEnded := by simp [step, hid, hend]

theorem wrong_depth_rejected (s : State) (o : Outcome)
    (hid : o.trialId ∉ s.processed) (hrun : s.status = .running)
    (hdepth : o.presentedDb ≠ s.levelDb) :
    step s o = .rejected .depthMismatch := by simp [step, hid, hrun, hdepth]

theorem invalid_preserves_adaptive_state (s : State) (o : Outcome)
    (h : o.valid = false) :
    (advance s o).1.levelDb = s.levelDb ∧
    (advance s o).1.correctStreak = s.correctStreak ∧
    (advance s o).1.reversals = s.reversals ∧
    (advance s o).1.lastDir = s.lastDir ∧
    (advance s o).1.moves = s.moves ∧
    (advance s o).1.validCount = s.validCount := by simp [advance, h]

theorem invalid_tenth_terminates (s : State) (o : Outcome)
    (h : o.valid = false) (ht : 10 ≤ s.technicalCount + 1) :
    (advance s o).1.status = .technicalFailure := by simp [advance, h, ht]

theorem blocked_is_not_reversal (s : State) (dir : Dir)
    (h : blocked s.levelDb dir = true) : isReversal s dir = false := by
  simp [isReversal, h]

theorem blocked_preserves_movement_state (s : State) (id : String) (dir : Dir)
    (h : blocked s.levelDb dir = true) :
    (shift s id dir).state = s ∧ (shift s id dir).reversal = false ∧
    (shift s id dir).effectiveStepDb = 0 := by simp [shift, h]

theorem first_correct_stays : request 0 true = (none, 1) := by decide
theorem second_correct_harder : request 1 true = (some .harder, 0) := by decide
theorem incorrect_resets_and_eases (streak : Nat) :
    request streak false = (some .easier, 0) := by simp [request]

theorem shift_bounded (s : State) (id : String) (dir : Dir) (h : Bounded s) :
    Bounded (shift s id dir).state := by
  unfold shift
  split
  · exact h
  · exact clamp_bounded _

theorem shift_counts (s : State) (id : String) (dir : Dir) :
    (shift s id dir).state.attemptCount = s.attemptCount ∧
    (shift s id dir).state.validCount = s.validCount ∧
    (shift s id dir).state.technicalCount = s.technicalCount ∧
    (shift s id dir).state.processed = s.processed := by
  unfold shift
  split <;> simp

theorem shift_streak (s : State) (id : String) (dir : Dir) :
    (shift s id dir).state.correctStreak = s.correctStreak := by
  unfold shift
  split <;> rfl

theorem request_streak_lt_two (streak : Nat) (correct : Bool) :
    (request streak correct).2 < 2 := by
  unfold request
  split
  · split <;> simp_all <;> omega
  · simp

@[simp] theorem shift_attemptCount (s : State) (id : String) (dir : Dir) :
    (shift s id dir).state.attemptCount = s.attemptCount := (shift_counts s id dir).1
@[simp] theorem shift_validCount (s : State) (id : String) (dir : Dir) :
    (shift s id dir).state.validCount = s.validCount := (shift_counts s id dir).2.1
@[simp] theorem shift_technicalCount (s : State) (id : String) (dir : Dir) :
    (shift s id dir).state.technicalCount = s.technicalCount := (shift_counts s id dir).2.2.1
@[simp] theorem shift_processed (s : State) (id : String) (dir : Dir) :
    (shift s id dir).state.processed = s.processed := (shift_counts s id dir).2.2.2

@[simp] theorem motion_attemptCount (s : State) (id : String) (dir : Option Dir) :
    (motion s id dir).state.attemptCount = s.attemptCount := by cases dir <;> simp [motion]
@[simp] theorem motion_validCount (s : State) (id : String) (dir : Option Dir) :
    (motion s id dir).state.validCount = s.validCount := by cases dir <;> simp [motion]
@[simp] theorem motion_technicalCount (s : State) (id : String) (dir : Option Dir) :
    (motion s id dir).state.technicalCount = s.technicalCount := by cases dir <;> simp [motion]
@[simp] theorem motion_processed (s : State) (id : String) (dir : Option Dir) :
    (motion s id dir).state.processed = s.processed := by cases dir <;> simp [motion]
@[simp] theorem motion_streak (s : State) (id : String) (dir : Option Dir) :
    (motion s id dir).state.correctStreak = s.correctStreak := by
  cases dir <;> simp [motion, shift_streak]

theorem motion_bounded (s : State) (id : String) (dir : Option Dir)
    (h : Bounded s) : Bounded (motion s id dir).state := by
  cases dir with
  | none => exact h
  | some d => exact shift_bounded s id d h

theorem advance_counts (s : State) (o : Outcome) :
    (advance s o).1.attemptCount = s.attemptCount + 1 ∧
    (advance s o).1.validCount = s.validCount + (if o.valid then 1 else 0) ∧
    (advance s o).1.technicalCount = s.technicalCount + (if o.valid then 0 else 1) ∧
    (advance s o).1.processed = s.processed ++ [o.trialId] := by
  cases h : o.valid <;> simp [advance, h]

theorem advance_count_consistent (s : State) (o : Outcome)
    (h : CountConsistent s) : CountConsistent (advance s o).1 := by
  rcases advance_counts s o with ⟨ha, hv, ht, hp⟩
  rcases h with ⟨hc, hl⟩
  unfold CountConsistent
  rw [ha, hv, ht, hp, List.length_append, hl]
  cases o.valid <;> simp_all <;> omega

theorem advance_valid_streak_lt_two (s : State) (o : Outcome)
    (h : o.valid = true) : (advance s o).1.correctStreak < 2 := by
  simp only [advance, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    motion_streak]
  exact request_streak_lt_two s.correctStreak o.correct

theorem advance_bounded (s : State) (o : Outcome) (h : Bounded s) :
    Bounded (advance s o).1 := by
  cases hv : o.valid with
  | false => simpa [advance, hv, Bounded] using h
  | true =>
    let counted : State := { s with attemptCount := s.attemptCount + 1, processed := s.processed ++ [o.trialId], validCount := s.validCount + 1, correctStreak := (request s.correctStreak o.correct).2 }
    have hm := motion_bounded counted o.trialId (request s.correctStreak o.correct).1 h
    simpa [advance, hv, counted, Bounded] using hm

theorem accepted_preserves_bounds (s n : State) (o : Outcome) (tr : Transition)
    (h : Bounded s) (hs : step s o = .advanced n tr) : Bounded n := by
  unfold step at hs
  split at hs
  · contradiction
  · split at hs
    · contradiction
    · split at hs
      · contradiction
      · have hn : (advance s o).1 = n := by cases he : advance s o; simp_all
        rw [← hn]
        exact advance_bounded s o h

theorem accepted_preserves_counts (s n : State) (o : Outcome) (tr : Transition)
    (h : CountConsistent s) (hs : step s o = .advanced n tr) : CountConsistent n := by
  unfold step at hs
  split at hs
  · contradiction
  · split at hs
    · contradiction
    · split at hs
      · contradiction
      · have hn : (advance s o).1 = n := by cases he : advance s o; simp_all
        rw [← hn]
        exact advance_count_consistent s o h

theorem nonblocked_shift_changes_depth (s : State) (id : String) (dir : Dir)
    (h : Bounded s) (hb : blocked s.levelDb dir = false) :
    (shift s id dir).state.levelDb ≠ s.levelDb := by
  simp only [shift, hb, Bool.false_eq_true, ↓reduceIte]
  have hp := requestedStep_positive
    (s.reversals.length + if isReversal s dir then 1 else 0)
  cases dir <;> simp only [Dir.sign, Int.neg_one_mul, Int.one_mul]
  all_goals simp only [blocked, decide_eq_false_iff_not] at hb
  all_goals unfold Bounded at h
  all_goals unfold clamp
  all_goals omega

def EvenDepth (s : State) : Prop := s.levelDb % 2 = 0

theorem init_even_depth : EvenDepth init := by simp [EvenDepth, init]

theorem clamp_even (x : Int) (h : x % 2 = 0) : clamp x % 2 = 0 := by
  unfold clamp
  omega

theorem requestedStep_even (r : Nat) : requestedStep r % 2 = 0 := by
  unfold requestedStep
  split <;> decide

theorem shift_even_depth (s : State) (id : String) (dir : Dir)
    (h : EvenDepth s) : EvenDepth (shift s id dir).state := by
  unfold shift
  split
  · exact h
  · unfold EvenDepth at *
    dsimp
    apply clamp_even
    have hp := requestedStep_even
      (s.reversals.length + if isReversal s dir then 1 else 0)
    cases dir <;> simp only [Dir.sign, Int.neg_one_mul, Int.one_mul] at *
    all_goals omega

theorem motion_even_depth (s : State) (id : String) (dir : Option Dir)
    (h : EvenDepth s) : EvenDepth (motion s id dir).state := by
  cases dir with
  | none => exact h
  | some d => exact shift_even_depth s id d h

theorem advance_even_depth (s : State) (o : Outcome) (h : EvenDepth s) :
    EvenDepth (advance s o).1 := by
  cases hv : o.valid with
  | false => simpa [advance, hv, EvenDepth] using h
  | true =>
    let counted : State := { s with attemptCount := s.attemptCount + 1, processed := s.processed ++ [o.trialId], validCount := s.validCount + 1, correctStreak := (request s.correctStreak o.correct).2 }
    have hm := motion_even_depth counted o.trialId (request s.correctStreak o.correct).1 h
    simpa [advance, hv, counted, EvenDepth] using hm

theorem accepted_is_advance (s n : State) (o : Outcome) (tr : Transition)
    (hs : step s o = .advanced n tr) : (advance s o).1 = n := by
  unfold step at hs
  split at hs
  · contradiction
  · split at hs
    · contradiction
    · split at hs
      · contradiction
      · cases he : advance s o; simp_all

theorem accepted_requires_running (s n : State) (o : Outcome) (tr : Transition)
    (hs : step s o = .advanced n tr) : s.status = .running := by
  unfold step at hs
  split at hs
  · contradiction
  · split at hs
    · contradiction
    · simp_all

theorem shift_reversal_count (s : State) (id : String) (dir : Dir) :
    s.reversals.length ≤ (shift s id dir).state.reversals.length ∧
    (shift s id dir).state.reversals.length ≤ s.reversals.length + 1 := by
  unfold shift
  split
  · simp
  · dsimp
    split <;> simp

theorem actual_reversal_records_presented_depth
    (s : State) (id : String) (dir : Dir)
    (hb : blocked s.levelDb dir = false) (hr : isReversal s dir = true) :
    (shift s id dir).state.reversals = s.reversals ++
      [{ db := s.levelDb, validNo := s.validCount, attemptNo := s.attemptCount,
         trialId := id, dirAfter := dir, atBound := atBound s.levelDb }] := by
  simp [shift, hb, hr]

def RunningCaps (s : State) : Prop := s.status = .running →
  s.validCount < 200 ∧ s.technicalCount < 10 ∧ s.reversals.length < 14

theorem init_running_caps : RunningCaps init := by simp [RunningCaps, init]

theorem validStatus_running_iff (r v : Nat) :
    validStatus r v = .running ↔ r < 14 ∧ v < 200 := by
  unfold validStatus
  split
  · simp_all; omega
  · split <;> simp_all <;> omega

theorem advance_running_caps (s : State) (o : Outcome)
    (hrun : s.status = .running) (hc : RunningCaps s) :
    RunningCaps (advance s o).1 := by
  have hs := hc hrun
  cases hv : o.valid with
  | false =>
    simp only [RunningCaps, advance, hv, Bool.not_false, ↓reduceIte]
    intro hnew
    split at hnew
    · contradiction
    · exact ⟨hs.1, by omega, hs.2.2⟩
  | true =>
    simp only [RunningCaps, advance, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    intro hnew
    have hcnew := (validStatus_running_iff _ _).mp hnew
    simp only [motion_validCount] at hcnew ⊢
    simp only [motion_technicalCount]
    exact ⟨hcnew.2, hs.2.1, hcnew.1⟩

/- Reachability includes only fresh, depth-matching accepted trials. Duplicate
   calls and rejected calls do not add an accepted transition. -/
inductive Reachable : State → Prop where
  | initial : Reachable init
  | accepted {s n : State} {o : Outcome} {tr : Transition} :
      Reachable s → step s o = .advanced n tr → Reachable n

theorem reachable_invariants (s : State) (h : Reachable s) :
    Bounded s ∧ EvenDepth s ∧ CountConsistent s ∧ RunningCaps s := by
  induction h with
  | initial => exact ⟨init_bounded, init_even_depth, init_count_consistent, init_running_caps⟩
  | @accepted old next o tr _ hs ih =>
    have hn := accepted_is_advance old next o tr hs
    have hr := accepted_requires_running old next o tr hs
    rw [← hn]
    exact ⟨advance_bounded old o ih.1, advance_even_depth old o ih.2.1,
      advance_count_consistent old o ih.2.2.1, advance_running_caps old o hr ih.2.2.2⟩

theorem reachable_running_attempt_bound (s : State) (h : Reachable s)
    (hr : s.status = .running) : s.attemptCount ≤ 208 := by
  rcases reachable_invariants s h with ⟨_, _, hc, hcap⟩
  rcases hc with ⟨hcount, _⟩
  have hcaps := hcap hr
  omega

theorem accepted_attempt_at_most_209 (s n : State) (o : Outcome) (tr : Transition)
    (hr : Reachable s) (hs : step s o = .advanced n tr) : n.attemptCount ≤ 209 := by
  have hbound := reachable_running_attempt_bound s hr (accepted_requires_running s n o tr hs)
  have hn := accepted_is_advance s n o tr hs
  have ha := (advance_counts s o).1
  rw [hn] at ha
  omega

theorem attempt_209_is_terminal (s : State) (h : Reachable s)
    (ha : 209 ≤ s.attemptCount) : s.status ≠ .running := by
  intro hr
  have hb := reachable_running_attempt_bound s h hr
  omega

theorem fourth_actual_reversal_uses_fine (s : State) (id : String) (dir : Dir)
    (hr : isReversal s dir = true) (hlen : s.reversals.length = 3) :
    (shift s id dir).requestedStepDb = 2 := by
  simp [shift, hr, hlen, requestedStep]
  split <;> rfl

def ReversalSafe (r : Reversal) : Prop :=
  (-50 ≤ r.db ∧ r.db ≤ 0) ∧ r.db % 2 = 0 ∧ r.atBound = atBound r.db

def ReversalsSafe (s : State) : Prop := ∀ r ∈ s.reversals, ReversalSafe r

theorem init_reversals_safe : ReversalsSafe init := by simp [ReversalsSafe, init]

theorem shift_reversals_safe (s : State) (id : String) (dir : Dir)
    (hb : Bounded s) (he : EvenDepth s) (hr : ReversalsSafe s) :
    ReversalsSafe (shift s id dir).state := by
  unfold shift
  split
  · exact hr
  · unfold ReversalsSafe
    dsimp
    split
    · intro r hm
      simp only [List.mem_append, List.mem_singleton] at hm
      rcases hm with hprev | hnew
      · exact hr r hprev
      · subst r
        exact ⟨hb, he, rfl⟩
    · exact hr

theorem motion_reversals_safe (s : State) (id : String) (dir : Option Dir)
    (hb : Bounded s) (he : EvenDepth s) (hr : ReversalsSafe s) :
    ReversalsSafe (motion s id dir).state := by
  cases dir with
  | none => exact hr
  | some d => exact shift_reversals_safe s id d hb he hr

theorem advance_reversals_safe (s : State) (o : Outcome)
    (hb : Bounded s) (he : EvenDepth s) (hr : ReversalsSafe s) :
    ReversalsSafe (advance s o).1 := by
  cases hv : o.valid with
  | false => simpa [advance, hv, ReversalsSafe] using hr
  | true =>
    let counted : State := { s with attemptCount := s.attemptCount + 1, processed := s.processed ++ [o.trialId], validCount := s.validCount + 1, correctStreak := (request s.correctStreak o.correct).2 }
    have hm := motion_reversals_safe counted o.trialId
      (request s.correctStreak o.correct).1 hb he hr
    simpa [advance, hv, counted, ReversalsSafe] using hm

theorem reachable_reversals_safe (s : State) (h : Reachable s) : ReversalsSafe s := by
  induction h with
  | initial => exact init_reversals_safe
  | @accepted old next o tr hr hs ih =>
    rw [← accepted_is_advance old next o tr hs]
    have hi := reachable_invariants old hr
    exact advance_reversals_safe old o hi.1 hi.2.1 ih

theorem accepted_id_fresh (s n : State) (o : Outcome) (tr : Transition)
    (hs : step s o = .advanced n tr) : o.trialId ∉ s.processed := by
  unfold step at hs
  split at hs
  · contradiction
  · assumption

theorem reachable_processed_nodup (s : State) (h : Reachable s) :
    s.processed.Nodup := by
  induction h with
  | initial => simp [init]
  | @accepted old next o tr _ hs ih =>
    have hf := accepted_id_fresh old next o tr hs
    rw [← accepted_is_advance old next o tr hs, (advance_counts old o).2.2.2]
    change List.Pairwise (fun a b : String => a ≠ b) (old.processed ++ [o.trialId])
    rw [List.pairwise_append]
    refine ⟨ih, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    intro he
    subst a
    exact hf ha

theorem reachable_streak_lt_two (s : State) (h : Reachable s) : s.correctStreak < 2 := by
  induction h with
  | initial => simp [init]
  | @accepted old next o tr _ hs ih =>
    rw [← accepted_is_advance old next o tr hs]
    cases hv : o.valid with
    | false => simpa [advance, hv] using ih
    | true => exact advance_valid_streak_lt_two old o hv

theorem reachable_attempt_at_most_209 (s : State) (h : Reachable s) :
    s.attemptCount ≤ 209 := by
  cases h with
  | initial => simp [init]
  | @accepted old next o tr hr hs => exact accepted_attempt_at_most_209 old s o tr hr hs

theorem motion_reversal_count (s : State) (id : String) (dir : Option Dir) :
    s.reversals.length ≤ (motion s id dir).state.reversals.length ∧
    (motion s id dir).state.reversals.length ≤ s.reversals.length + 1 := by
  cases dir with
  | none => simp [motion]
  | some d => exact shift_reversal_count s id d

theorem advance_reversal_count (s : State) (o : Outcome) :
    s.reversals.length ≤ (advance s o).1.reversals.length ∧
    (advance s o).1.reversals.length ≤ s.reversals.length + 1 := by
  cases hv : o.valid with
  | false => simp [advance, hv]
  | true =>
    let counted : State := { s with attemptCount := s.attemptCount + 1, processed := s.processed ++ [o.trialId], validCount := s.validCount + 1, correctStreak := (request s.correctStreak o.correct).2 }
    have hm := motion_reversal_count counted o.trialId (request s.correctStreak o.correct).1
    simpa [advance, hv, counted] using hm

theorem reachable_counter_limits (s : State) (h : Reachable s) :
    s.validCount ≤ 200 ∧ s.technicalCount ≤ 10 ∧ s.reversals.length ≤ 14 := by
  cases h with
  | initial => simp [init]
  | @accepted old next o tr hr hs =>
    have hi := (reachable_invariants old hr).2.2.2
      (accepted_requires_running old s o tr hs)
    have hn := accepted_is_advance old s o tr hs
    rcases advance_counts old o with ⟨_, hv, ht, _⟩
    have hrev := advance_reversal_count old o
    rw [hn] at hv ht hrev
    cases hvv : o.valid <;> simp_all <;> omega

end Stm.Staircase

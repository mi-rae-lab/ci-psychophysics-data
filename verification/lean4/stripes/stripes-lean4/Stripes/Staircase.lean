import Std

/-!
# A finite STRIPES staircase specification

This module formalizes the proposed staircase in the supplied README, §§12–13.
One tick is 0.1 density D; admissible densities are 11 through 200 ticks.
The model has no audio, browser timing, persistence, participant, or clinical
assumptions. A response is assumed to concern the density stored in the state;
checking that the played file actually has that density is outside this model.

Completed states absorb later inputs. This is a total mathematical interface:
the JavaScript implementation can instead reject a fresh input after completion.
Consequently these theorems are not a proof of equivalence to that implementation.

All executable fixtures use the kernel-checked `decide` tactic, not `native_decide`.
-/

namespace Stripes.Staircase

/-- A density represented exactly in units of 0.1 D, with its bounds certified. -/
abbrev Tick := { n : Nat // 11 ≤ n ∧ n ≤ 200 }

/-- Saturation to the available stimulus-bank range. -/
def clamp (n : Nat) : Tick :=
  ⟨max 11 (min 200 n), by omega⟩

inductive Direction where
  | harder
  | easier
  deriving DecidableEq, Repr

inductive Response where
  | correct
  | incorrect
  | invalid
  deriving DecidableEq, Repr

inductive Status where
  | running
  | reversalTargetReached
  | trialCapBeforeReversalTarget
  | technicalFailure
  deriving DecidableEq, Repr

structure State where
  density : Tick := ⟨11, by decide⟩
  correctStreak : Nat := 0
  lastDirection : Option Direction := none
  reversalTicks : List Nat := []
  attempts : Nat := 0
  validTrials : Nat := 0
  technicalFailures : Nat := 0
  moves : Nat := 0
  processed : List Nat := []
  status : Status := .running
  deriving DecidableEq, Repr

def initial : State := {}

/-- An outward request at a boundary does not constitute a movement. -/
def blocked (s : State) (d : Direction) : Bool :=
  match d with
  | .harder => decide (200 ≤ s.density.val)
  | .easier => decide (s.density.val ≤ 11)

/-- The first movement, whose predecessor is `none`, cannot be a reversal. -/
def isReversal (s : State) (d : Direction) : Bool :=
  match s.lastDirection with
  | none => false
  | some previous => decide (previous ≠ d)

/--
Apply a requested movement. Store the pre-movement presented density on reversal.
The movement leaving genuine reversal number four already uses the fine step.
-/
def applyMove (s : State) (d : Direction) : State :=
  if blocked s d then s
  else
    let reversals :=
      if isReversal s d then s.reversalTicks ++ [s.density.val]
      else s.reversalTicks
    let stepSize := if reversals.length < 4 then 5 else 2
    let requested :=
      match d with
      | .harder => s.density.val + stepSize
      | .easier => s.density.val - stepSize
    { s with
      density := clamp requested
      lastDirection := some d
      reversalTicks := reversals
      moves := s.moves + 1 }

/-- Reversal completion takes precedence if the 200th valid trial also completes. -/
def finishValid (s : State) : State :=
  { s with status :=
      if 8 ≤ s.reversalTicks.length then .reversalTargetReached
      else if 200 ≤ s.validTrials then .trialCapBeforeReversalTarget
      else .running }

/-- Process one fresh input on a running track. Use `step` for the guarded API. -/
def applyResponse (s : State) (trialId : Nat) (response : Response) : State :=
  let attempted := { s with
    attempts := s.attempts + 1
    processed := s.processed ++ [trialId] }
  match response with
  | .invalid =>
      { attempted with
        technicalFailures := s.technicalFailures + 1
        status := if 10 ≤ s.technicalFailures + 1 then .technicalFailure else .running }
  | .correct =>
      let count := s.correctStreak + 1
      let scored := { attempted with
        validTrials := s.validTrials + 1
        correctStreak := if 2 ≤ count then 0 else count }
      finishValid (if 2 ≤ count then applyMove scored .harder else scored)
  | .incorrect =>
      let scored := { attempted with validTrials := s.validTrials + 1, correctStreak := 0 }
      finishValid (applyMove scored .easier)

/-- Duplicate IDs and inputs to a completed state do not change the state. -/
def step (s : State) (trialId : Nat) (response : Response) : State :=
  if trialId ∈ s.processed then s
  else if s.status = .running then applyResponse s trialId response
  else s

/-- Run a list with fresh successive IDs when starting from `initial`. -/
def runResponses (responses : List Response) (nextId : Nat := 0)
    (state : State := initial) : State :=
  match responses with
  | [] => state
  | response :: rest =>
      runResponses rest (nextId + 1) (step state nextId response)

/-- Exact arithmetic output: numerator/denominator in D, with no rounding. -/
structure ExactThreshold where
  numerator : Nat
  denominator : Nat
  deriving DecidableEq, Repr

/-- The final four reversal densities in chronological order. -/
def retained (s : State) : List Nat :=
  (s.reversalTicks.reverse.take 4).reverse

/--
An ordinary threshold is only produced at genuine-reversal completion.
The denominator converts the retained tick sum into density D.
-/
def threshold (s : State) : Option ExactThreshold :=
  if s.status = .reversalTargetReached ∧ 8 ≤ s.reversalTicks.length then
    some { numerator := (retained s).sum, denominator := 10 * (retained s).length }
  else none

/-! ## General, universally quantified properties -/

theorem step_bounds (s : State) (trialId : Nat) (response : Response) :
    11 ≤ (step s trialId response).density.val ∧
      (step s trialId response).density.val ≤ 200 :=
  (step s trialId response).density.property

theorem duplicate_ignored (s : State) (trialId : Nat) (response : Response)
    (h : trialId ∈ s.processed) :
    step s trialId response = s := by
  simp [step, h]

theorem terminal_absorbing (s : State) (trialId : Nat) (response : Response)
    (h : s.status ≠ .running) :
    step s trialId response = s := by
  simp [step, h]

/-- Invalid input may change bookkeeping and termination, but not this core. -/
def adaptiveCore (s : State) :=
  (s.density.val, s.correctStreak, s.lastDirection, s.reversalTicks, s.moves, s.validTrials)

theorem invalid_preserves_adaptive_core (s : State) (trialId : Nat) :
    adaptiveCore (step s trialId .invalid) = adaptiveCore s := by
  by_cases hd : trialId ∈ s.processed
  · simp [step, hd]
  · by_cases hr : s.status = .running
    · simp [step, hd, hr, applyResponse, adaptiveCore]
    · simp [step, hd, hr]

theorem fresh_invalid_increments_technical_count (s : State) (trialId : Nat)
    (hd : trialId ∉ s.processed) (hr : s.status = .running) :
    (step s trialId .invalid).technicalFailures = s.technicalFailures + 1 := by
  simp [step, hd, hr, applyResponse]

theorem blocked_request_is_no_move (s : State) (d : Direction)
    (h : blocked s d = true) :
    applyMove s d = s := by
  simp [applyMove, h]

theorem first_move_not_reversal (s : State) (d : Direction)
    (h : s.lastDirection = none) :
    (applyMove s d).reversalTicks = s.reversalTicks := by
  cases hb : blocked s d <;> simp [applyMove, hb, isReversal, h]

theorem incomplete_has_no_threshold (s : State)
    (h : s.status ≠ .reversalTargetReached) :
    threshold s = none := by
  simp [threshold, h]

/-! ## Exact README §13 regression fixtures -/

def mainResponses : List Response :=
  [.correct, .correct, .correct, .correct, .incorrect,
   .correct, .correct, .incorrect, .correct, .correct,
   .incorrect, .correct, .correct, .incorrect, .correct, .correct]

def mainFixture : State := runResponses mainResponses

theorem fixture_reversals :
    mainFixture.reversalTicks = [21, 16, 21, 16, 18, 16, 18, 16] := by
  decide

theorem fixture_retained : retained mainFixture = [18, 16, 18, 16] := by
  decide

theorem fixture_exact_threshold :
    threshold mainFixture = some { numerator := 68, denominator := 40 } := by
  decide

/-- The computed threshold is 17/10 by exact cross multiplication. -/
theorem fixture_threshold_is_seventeen_tenths :
    ∃ t, threshold mainFixture = some t ∧
      t.numerator * 10 = 17 * t.denominator ∧ 0 < t.denominator := by
  refine ⟨⟨68, 40⟩, ?_⟩
  decide

theorem fixture_stops_at_sixteen :
    mainFixture.status = .reversalTargetReached ∧ mainFixture.validTrials = 16 ∧
      mainFixture.density.val = 18 := by
  decide

/-- The value 18 is the next planned density, not a seventeenth presented trial. -/
theorem fixture_later_input_ignored (trialId : Nat) (response : Response) :
    step mainFixture trialId response = mainFixture := by
  apply terminal_absorbing
  decide

theorem fixture_lower_boundary_WWCC :
    let s := runResponses [.incorrect, .incorrect, .correct, .correct]
    s.reversalTicks = [] ∧ s.density.val = 16 ∧ s.moves = 1 := by
  decide

theorem fixture_invalid_keeps_correct_streak :
    let s := runResponses [.correct, .invalid, .correct]
    s.validTrials = 2 ∧ s.attempts = 3 ∧ s.density.val = 16 ∧ s.moves = 1 := by
  decide

theorem fixture_ten_invalids :
    let s := runResponses (List.replicate 10 .invalid)
    s.status = .technicalFailure ∧ s.attempts = 10 ∧ s.density.val = 11 := by
  decide

set_option maxRecDepth 4096 in
theorem fixture_all_incorrect_trial_cap :
    let s := runResponses (List.replicate 200 .incorrect)
    s.status = .trialCapBeforeReversalTarget ∧ s.validTrials = 200 ∧
      s.reversalTicks = [] ∧ threshold s = none := by
  decide

end Stripes.Staircase

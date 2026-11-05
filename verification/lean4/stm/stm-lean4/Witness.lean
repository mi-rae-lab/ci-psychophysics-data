import Stm.Threshold

/- Independent nonvacuity witnesses; the original specification is unchanged. -/
namespace Reaudit
open Stm.Staircase Stm.Threshold

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def tick (s : State) (id : Nat) (correct : Bool) : State :=
  match step s { trialId := toString id, presentedDb := s.levelDb,
                 valid := true, correct := correct } with
  | .advanced n _ => n
  | _ => s

theorem tick_reachable (s : State) (id : Nat) (b : Bool) (hr : Reachable s) :
    Reachable (tick s id b) := by
  unfold tick
  split
  · exact Reachable.accepted hr (by assumption)
  · exact hr

def run (s : State) (id : Nat) : List Bool → State
  | [] => s
  | b :: bs => run (tick s id b) (id + 1) bs

theorem run_reachable (s : State) (id : Nat) (bs : List Bool) (hr : Reachable s) :
    Reachable (run s id bs) := by
  induction bs generalizing s id with
  | nil => exact hr
  | cons b bs ih => exact ih _ _ (tick_reachable s id b hr)

def answers : List Bool :=
  [true,true,false,true,true,false,true,true,false,true,true,false,
   true,true,false,true,true,false,true,true,false,true,true]

def witness : State := run init 0 answers

theorem witness_reachable : Reachable witness :=
  run_reachable init 0 answers Reachable.initial

theorem witness_fourteen_reversals : witness.reversals.length = 14 := by decide
theorem witness_twenty_three_attempts : witness.attemptCount = 23 := by decide
theorem witness_target_status : witness.status = .reversalTargetReached := by decide

theorem reachable_threshold_nonempty :
    ∃ s : State, Reachable s ∧ ∃ m, threshold s = some m := by
  refine ⟨witness, witness_reachable, Stm.Arithmetic.threshold10 (retained witness), ?_⟩
  apply threshold_present_at_target
  rw [witness_fourteen_reversals]
  decide

#print axioms witness_reachable
#print axioms witness_fourteen_reversals
#print axioms witness_twenty_three_attempts
#print axioms witness_target_status
#print axioms reachable_threshold_nonempty
end Reaudit

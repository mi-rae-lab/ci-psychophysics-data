import Std

/-!
STRIPES methodology: algebraic balance, averaging, and exact finite counterexamples.

The abstract-field theorems are algebraic statements, not stochastic convergence
theorems. Interpreting p as a probability additionally requires 0 <= p <= 1 and
the stated stationary, independent-response model. No real-valued square root is
constructed: the formal target equation is p*p = 1/2.

The finite examples use uniform lists of independent draws. Repeated entries in
[4,4,4,8] represent distinct equally likely latent outcomes, hence P(4)=3/4.
These are counterexamples to universal claims, not fitted STRIPES participant data.
-/

namespace Stripes.Statistics
open Lean.Grind

section Balance
variable {K : Type} [CommRing K]

/-- Under local iid responses, the next movement block is W, CW, or CC. -/
theorem movement_block_mass (p : K) :
    (1 - p) + p * (1 - p) + p * p = 1 := by grind

/-- Expected signed movement at movement epochs, away from clipping. -/
theorem movement_drift (p harder easier : K) :
    harder * p * p - easier * ((1-p) + p*(1-p)) =
      (harder + easier) * p * p - easier := by grind

end Balance

section FieldBalance
variable {K : Type} [Field K] [IsCharP K 0]

/-- Balance is conditional on the block-probability model, not a finite-run claim. -/
theorem equal_step_balance (p s : K) (hs : s ≠ 0) :
    s*p*p - s*(1-p*p) = 0 ↔ p*p = 1/2 := by grind

theorem unequal_step_balance (p h e : K) (hne : h+e ≠ 0) :
    h*p*p - e*(1-p*p) = 0 ↔ p*p = e/(h+e) := by grind

/-- Separates forced-choice guessing and lapse from raw correct-response probability. -/
theorem guessing_lapse_identity (p lapse sensitivity : K)
    (h : p = 1/2 + (1/2-lapse)*sensitivity)
    (hne : 1/2-lapse ≠ 0) :
    sensitivity = (p-1/2)/(1/2-lapse) := by grind

/-- Algebra only: the covariance numerator must be justified by a data model. -/
theorem equicorrelated_moment_identity (n variance covariance : K) (hn : n ≠ 0) :
    (n*variance + n*(n-1)*covariance)/(n*n) =
      covariance + (variance-covariance)/n := by grind

/-- Three-run mean square exposes cross-products; they cannot be silently dropped. -/
theorem three_error_square (x y z : K) :
    ((x+y+z)/3)^2 = (x*x+y*y+z*z+2*x*y+2*x*z+2*y*z)/9 := by grind

/-- Last four reversal errors are not automatically independent observations. -/
theorem four_error_square (w x y z : K) :
    ((w+x+y+z)/4)^2 =
      (w*w+x*x+y*y+z*z+2*w*x+2*w*y+2*w*z+2*x*y+2*x*z+2*y*z)/16 := by grind

end FieldBalance

section FiniteBias
variable {K : Type} [CommRing K]
attribute [local instance] Semiring.natCast

def sumValues : List K → K
  | [] => 0
  | x :: xs => x + sumValues xs

/-- Exact finite-sum bias expansion; no independence assumption is needed here. -/
theorem shifted_square_sum (xs : List K) (bias : K) :
    sumValues (xs.map (fun e => (bias+e)*(bias+e))) =
      (NatCast.natCast xs.length : K)*bias*bias + 2*bias*sumValues xs +
        sumValues (xs.map (fun e => e*e)) := by
  induction xs with
  | nil => simp [sumValues, Semiring.natCast_zero]; grind
  | cons x xs ih =>
    simp only [List.map_cons, sumValues, List.length_cons, Semiring.natCast_add,
      Semiring.natCast_one]
    grind

theorem zero_mean_noise_keeps_bias_square (xs : List K) (bias : K)
    (hz : sumValues xs = 0) :
    sumValues (xs.map (fun e => (bias+e)*(bias+e))) =
      (NatCast.natCast xs.length : K)*bias*bias + sumValues (xs.map (fun e => e*e)) := by
  have h := shifted_square_sum xs bias
  grind

end FiniteBias

/- Exact finite models: a list is a uniform multiset of latent elementary outcomes. -/
def average (xs : List Rat) : Rat := xs.foldl (· + ·) 0 / (xs.length : Rat)

def triples (xs : List Rat) : List (Rat × Rat × Rat) :=
  xs.flatMap fun x => xs.flatMap fun y => xs.map fun z => (x, y, z)

def fixedTwo (t : Rat × Rat × Rat) : Rat := (t.1 + t.2.1)/2
def fixedThree (t : Rat × Rat × Rat) : Rat := (t.1 + t.2.1 + t.2.2)/3

/-- Strictly more than 1 D selects all three runs; otherwise use the first two. -/
def conditionalMean (t : Rat × Rat × Rat) : Rat :=
  if t.1-t.2.1 > 1 ∨ t.2.1-t.1 > 1 then fixedThree t else fixedTwo t

/-- The selected mean is the first-pair mean plus a conditional adjustment. -/
theorem conditional_mean_adjustment (t : Rat × Rat × Rat) :
    conditionalMean t = fixedTwo t +
      (if t.1-t.2.1 > 1 ∨ t.2.1-t.1 > 1 then (t.2.2-fixedTwo t)/3 else 0) := by
  unfold conditionalMean fixedTwo fixedThree
  split <;> grind

def meanSquaredError (xs : List Rat) (truth : Rat) : Rat :=
  average (xs.map (fun x => (x-truth)^2))

theorem asymmetric_single_mean : average [4,4,4,8] = 5 := by
  simp [average, List.foldl]
  grind

/-- iid unbiased input measurements need not give an unbiased selected mean. -/
theorem asymmetric_selected_mean :
    average ((triples [4,4,4,8]).map conditionalMean) = 39/8 := by
  simp [average, triples, conditionalMean, fixedTwo, fixedThree, List.foldl]
  grind

theorem asymmetric_selected_bias :
    average ((triples [4,4,4,8]).map conditionalMean) - 5 = -(1/8 : Rat) := by
  rw [asymmetric_selected_mean]
  grind

theorem symmetric_selected_unbiased :
    average ((triples [4,6]).map conditionalMean) = 5 := by
  simp [average, triples, conditionalMean, fixedTwo, fixedThree, List.foldl]
  grind

theorem symmetric_selected_mse :
    meanSquaredError ((triples [4,6]).map conditionalMean) 5 = 5/9 := by
  simp [meanSquaredError, average, triples, conditionalMean, fixedTwo, fixedThree,
    List.foldl]
  grind

theorem symmetric_fixed_two_mse :
    meanSquaredError ((triples [4,6]).map fixedTwo) 5 = 1/2 := by
  simp [meanSquaredError, average, triples, fixedTwo, List.foldl]
  grind

theorem symmetric_fixed_three_mse :
    meanSquaredError ((triples [4,6]).map fixedThree) 5 = 1/3 := by
  simp [meanSquaredError, average, triples, fixedThree, List.foldl]
  grind

/-- A counterexample to 'adding a third only on disagreement always improves MSE'. -/
theorem conditional_repeat_can_increase_mse :
    meanSquaredError ((triples [4,6]).map conditionalMean) 5 >
      meanSquaredError ((triples [4,6]).map fixedTwo) 5 := by
  rw [symmetric_selected_mse, symmetric_fixed_two_mse]
  grind

end Stripes.Statistics

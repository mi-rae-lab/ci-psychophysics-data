import Std

/-!
# Finite experimental-design facts for STRIPES

This file is an independent mathematical model.  It does not change the
application.  All probabilities below are ratios of finite cardinalities.
Interpreting those ratios as response probabilities requires fair guessing and,
where stated, independence.  These assumptions are not verified about a person
or an audio device by any theorem in this file.

The model of the repetition policy assumes two completed main measurements and
a third completed main measurement when requested.  Aborts, failed measurements,
replacement runs, and persistent storage belong to other models.

Only `Std` is imported.  Closed computations use kernel-checked `decide`.
-/

namespace Stripes.Design

/-! ## Two alternatives: uniform independent target and response -/

/-- `false` and `true` name the two alternatives A and B. -/
def choiceOutcomes : List (Bool × Bool) :=
  [(false, false), (false, true), (true, false), (true, true)]

def choiceCorrect (outcome : Bool × Bool) : Bool :=
  outcome.1 == outcome.2

theorem choice_outcomes_four : choiceOutcomes.length = 4 := by decide

theorem choice_correct_two :
    (choiceOutcomes.filter choiceCorrect).length = 2 := by decide

/-- The chance ratio 2/4 equals 1/2, expressed without division or rounding. -/
theorem chance_is_one_half :
    (choiceOutcomes.filter choiceCorrect).length * 2 =
      choiceOutcomes.length := by decide

/-! ## Training gate: at least four successes among five -/

/-- Every Boolean word of length `n`, with every word listed exactly once by
construction.  For the five-trial gate the complete list is computed below. -/
def booleanWords : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (booleanWords n).flatMap fun w => [false :: w, true :: w]

def gatePasses (word : List Bool) : Bool :=
  decide (4 ≤ word.count true)

def gateOutcomeCount : Nat := (booleanWords 5).length
def gatePassCount : Nat := ((booleanWords 5).filter gatePasses).length
def gateFailCount : Nat :=
  ((booleanWords 5).filter fun w => !gatePasses w).length

theorem gate_words_have_length_five :
    (booleanWords 5).all (fun w => decide (w.length = 5)) = true := by decide

theorem gate_words_have_no_duplicates : (booleanWords 5).Nodup := by decide

theorem gate_outcomes_32 : gateOutcomeCount = 32 := by decide
theorem gate_passes_6 : gatePassCount = 6 := by decide
theorem gate_fails_26 : gateFailCount = 26 := by decide

/-- Five words have exactly four successes. -/
theorem exactly_four_successes_5 :
    ((booleanWords 5).filter fun w => decide (w.count true = 4)).length = 5 := by
  decide

/-- One word has five successes. -/
theorem exactly_five_successes_1 :
    ((booleanWords 5).filter fun w => decide (w.count true = 5)).length = 1 := by
  decide

theorem gate_success_partition : gatePassCount = 5 + 1 := by decide

/-- Under five independent fair guesses the pass ratio is 6/32 = 3/16. -/
theorem gate_chance_three_sixteenths :
    gatePassCount * 16 = 3 * gateOutcomeCount := by decide

/-- Ordered samples with replacement from an arbitrary finite alphabet. -/
def wordsFrom (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap fun a => (wordsFrom alphabet n).map (a :: ·)

/-- The product-space count is proved symbolically; no million-row enumeration
is required for four blocks. -/
theorem wordsFrom_length (alphabet : List α) (n : Nat) :
    (wordsFrom alphabet n).length = alphabet.length ^ n := by
  induction n with
  | zero => simp [wordsFrom]
  | succ n ih =>
    simp [wordsFrom, List.length_flatMap, List.map_const', ih,
      Nat.pow_succ, Nat.mul_comm]

/-- Counterfactual four-block product space.  An actual session may stop at
the first passing block; the event "a pass occurs by block four" is the same
event in this pre-sampled space, assuming independent fair guesses. -/
def fourBlockOutcomeCount : Nat := gateOutcomeCount ^ 4
def fourBlockAllFailCount : Nat := gateFailCount ^ 4
def fourBlockAnyPassCount : Nat :=
  fourBlockOutcomeCount - fourBlockAllFailCount

theorem four_blocks_product_space_count :
    (wordsFrom (booleanWords 5) 4).length = fourBlockOutcomeCount := by
  simp [wordsFrom_length, fourBlockOutcomeCount, gateOutcomeCount]

theorem four_blocks_all_fail_space_count :
    (wordsFrom ((booleanWords 5).filter fun w => !gatePasses w) 4).length =
      fourBlockAllFailCount := by
  simp [wordsFrom_length, fourBlockAllFailCount, gateFailCount]

theorem four_blocks_outcomes : fourBlockOutcomeCount = 1048576 := by decide
theorem four_blocks_all_fail : fourBlockAllFailCount = 456976 := by decide
theorem four_blocks_any_pass : fourBlockAnyPassCount = 591600 := by decide

/-- The exact chance ratio is 36975/65536 (about 56.4194 percent), not 3/16. -/
theorem four_blocks_reduced_ratio :
    fourBlockAnyPassCount * 65536 = 36975 * fourBlockOutcomeCount := by decide

theorem fair_guesser_can_pass_gate : 0 < gatePassCount := by decide
theorem fair_guesser_can_pass_by_block_four : 0 < fourBlockAnyPassCount := by decide

/-! ## Conditional third measurement, exact ticks, and practice exclusion -/

/-- One density unit D is ten ticks. -/
def ticksPerD : Nat := 10

/-- Absolute difference, using truncated natural subtraction. -/
def tickGap (a b : Nat) : Nat := (a - b) + (b - a)

def mainRunCount (first second : Nat) : Nat :=
  if ticksPerD < tickGap first second then 3 else 2

def selectedMainRuns (first second third : Nat) : List Nat :=
  if ticksPerD < tickGap first second then [first, second, third]
  else [first, second]

theorem main_run_count_is_two_or_three (first second : Nat) :
    mainRunCount first second = 2 ∨ mainRunCount first second = 3 := by
  unfold mainRunCount
  split <;> simp

theorem main_run_count_bounds (first second : Nat) :
    2 ≤ mainRunCount first second ∧ mainRunCount first second ≤ 3 := by
  unfold mainRunCount
  split <;> omega

theorem selected_run_count (first second third : Nat) :
    (selectedMainRuns first second third).length = mainRunCount first second := by
  unfold selectedMainRuns mainRunCount
  split <;> simp

theorem gap_exactly_one_D_requests_no_third (first second : Nat)
    (h : tickGap first second = 10) : mainRunCount first second = 2 := by
  simp [mainRunCount, ticksPerD, h]

theorem gap_above_one_D_requests_third (first second : Nat)
    (h : 10 < tickGap first second) : mainRunCount first second = 3 := by
  simp [mainRunCount, ticksPerD, h]

theorem concrete_boundary : mainRunCount 30 40 = 2 := by decide
theorem concrete_above_boundary : mainRunCount 30 41 = 3 := by decide

/-- An exact, not necessarily reduced, fraction.  This avoids all floating-point
rounding.  `meanOfMainRuns []` has denominator zero; the selected-run policy below
has two or three entries and therefore excludes that case. -/
structure ExactRatio where
  numerator : Nat
  denominator : Nat
  deriving DecidableEq, Repr

def meanOfMainRuns (_practice : List Nat) (main : List Nat) : ExactRatio :=
  ⟨main.sum, main.length⟩

def plannedMean (practice : List Nat) (first second third : Nat) : ExactRatio :=
  meanOfMainRuns practice (selectedMainRuns first second third)

theorem practice_is_excluded (p₁ p₂ main : List Nat) :
    meanOfMainRuns p₁ main = meanOfMainRuns p₂ main := by rfl

theorem planned_mean_denominator_positive
    (practice : List Nat) (first second third : Nat) :
    0 < (plannedMean practice first second third).denominator := by
  change 0 < (selectedMainRuns first second third).length
  rw [selected_run_count]
  have h := main_run_count_bounds first second
  omega

theorem two_main_measurements_exact_mean
    (practice : List Nat) (first second third : Nat)
    (h : ¬10 < tickGap first second) :
    plannedMean practice first second third = ⟨first + second, 2⟩ := by
  simp [plannedMean, meanOfMainRuns, selectedMainRuns, ticksPerD, h, List.sum_cons]

theorem three_main_measurements_exact_mean
    (practice : List Nat) (first second third : Nat)
    (h : 10 < tickGap first second) :
    plannedMean practice first second third = ⟨first + second + third, 3⟩ := by
  simp [plannedMean, meanOfMainRuns, selectedMainRuns, ticksPerD, h,
    List.sum_cons, Nat.add_assoc]

/-! ## Fractional run thresholds: the representation used by the application

A run threshold is the sum of four retained reversal ticks divided by 40 in D
units.  It can therefore be a fractional tick.  The preceding integer-tick
model is a special case; this section keeps each run's integer *sum* and compares
the sums against 40, preserving those fractional thresholds exactly.

These are mathematical rational comparisons, not a proof that JavaScript
floating-point arithmetic performs every comparison identically.
-/

def retainedSumScale : Nat := 4 * ticksPerD

def mainRunCountFromSums (firstSum secondSum : Nat) : Nat :=
  if retainedSumScale < tickGap firstSum secondSum then 3 else 2

def selectedMainSums (firstSum secondSum thirdSum : Nat) : List Nat :=
  if retainedSumScale < tickGap firstSum secondSum then
    [firstSum, secondSum, thirdSum]
  else [firstSum, secondSum]

/-- Mean in D, using a denominator of 80 for two runs or 120 for three runs. -/
def plannedDensityMean (_practiceSums : List Nat)
    (firstSum secondSum thirdSum : Nat) : ExactRatio :=
  let chosen := selectedMainSums firstSum secondSum thirdSum
  ⟨chosen.sum, retainedSumScale * chosen.length⟩

theorem retained_sum_scale_forty : retainedSumScale = 40 := by decide

theorem fractional_run_count_bounds (firstSum secondSum : Nat) :
    2 ≤ mainRunCountFromSums firstSum secondSum ∧
      mainRunCountFromSums firstSum secondSum ≤ 3 := by
  unfold mainRunCountFromSums
  split <;> omega

theorem fractional_gap_exactly_one_D_requests_no_third
    (firstSum secondSum : Nat) (h : tickGap firstSum secondSum = 40) :
    mainRunCountFromSums firstSum secondSum = 2 := by
  simp [mainRunCountFromSums, retainedSumScale, ticksPerD, h]

theorem fractional_gap_above_one_D_requests_third
    (firstSum secondSum : Nat) (h : 40 < tickGap firstSum secondSum) :
    mainRunCountFromSums firstSum secondSum = 3 := by
  simp [mainRunCountFromSums, retainedSumScale, ticksPerD, h]

theorem fractional_two_run_mean (practice : List Nat)
    (firstSum secondSum thirdSum : Nat) (h : ¬40 < tickGap firstSum secondSum) :
    plannedDensityMean practice firstSum secondSum thirdSum =
      ⟨firstSum + secondSum, 80⟩ := by
  simp [plannedDensityMean, selectedMainSums, retainedSumScale, ticksPerD, h,
    List.sum_cons]

theorem fractional_three_run_mean (practice : List Nat)
    (firstSum secondSum thirdSum : Nat) (h : 40 < tickGap firstSum secondSum) :
    plannedDensityMean practice firstSum secondSum thirdSum =
      ⟨firstSum + secondSum + thirdSum, 120⟩ := by
  simp [plannedDensityMean, selectedMainSums, retainedSumScale, ticksPerD, h,
    List.sum_cons, Nat.add_assoc]

theorem fractional_practice_is_excluded
    (p₁ p₂ : List Nat) (firstSum secondSum thirdSum : Nat) :
    plannedDensityMean p₁ firstSum secondSum thirdSum =
      plannedDensityMean p₂ firstSum secondSum thirdSum := by rfl

/-! ## Agreement does not bound bias without an accuracy assumption

Here `truth` is an arbitrary reference value, not an experimentally established
threshold.  Two reports may agree exactly at `truth + bias` for any natural
`bias`.  The repetition rule then requests only two runs; their exact mean still
differs from the reference by that bias.  Thus consistency alone imposes no
accuracy bound in this model.
-/

theorem equal_measurements_request_two (value : Nat) :
    mainRunCount value value = 2 := by
  simp [mainRunCount, tickGap, ticksPerD]

theorem equal_measurements_mean (practice : List Nat) (value third : Nat) :
    plannedMean practice value value third = ⟨value + value, 2⟩ := by
  simp [plannedMean, meanOfMainRuns, selectedMainRuns, tickGap, ticksPerD,
    List.sum_cons]

theorem arbitrarily_biased_consistent_measurements
    (practice : List Nat) (truth bias third : Nat) :
    mainRunCount (truth + bias) (truth + bias) = 2 ∧
    (plannedMean practice (truth + bias) (truth + bias) third).denominator = 2 ∧
    (plannedMean practice (truth + bias) (truth + bias) third).numerator =
      2 * (truth + bias) ∧
    (plannedMean practice (truth + bias) (truth + bias) third).numerator -
      2 * truth = 2 * bias := by
  constructor
  · exact equal_measurements_request_two _
  simp only [equal_measurements_mean]
  constructor
  · trivial
  constructor
  · change (truth + bias) + (truth + bias) = 2 * (truth + bias)
    omega
  · change (truth + bias) + (truth + bias) - 2 * truth = 2 * bias
    omega

/-!
Neither the eight-reversal stopping criterion nor passage through the training
gate is asserted to establish clinical validity, individual ability, unbiased
threshold estimation, or repeatability in a population.  The finite counting
results above demonstrate why a passing gate alone is not a guarantee against
fair guessing.  A theorem about clinical reliability would require an explicit
validated observation model and empirical premises, which are absent here.
-/

end Stripes.Design

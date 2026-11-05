import Std

/-!
# A finite, rational Chebyshev/Markov risk bound

This independent mathematical model does not edit or execute the application.
An atom is an outcome with a rational probability weight and a rational error
relative to a specified target.  The model permits arbitrary dependence,
asymmetry, and bias: its second moment is the mean squared error about that
target, not necessarily a variance.

The weighted inequality is proved below by a pointwise bound and list induction.
The probability-space structure additionally requires nonnegative weights and
total mass one.  No distributional assumptions about real participants, run
independence, or a variance value are inferred from these formal proofs.

The fixed-sample-size corollary takes a separately justified second-moment bound
as an explicit premise.  It does not establish that bound from independence or
prove that data-dependent stopping satisfies a fixed-sample-size formula.

All theorems use only Std and are checked by Lean's kernel.
-/

namespace Stripes.FiniteRisk

open Lean.Grind

structure Atom where
  weight : Rat
  error : Rat
  deriving Repr

def mass : List Atom → Rat
  | [] => 0
  | a :: atoms => a.weight + mass atoms

/-- The second moment of the error about the specified target. -/
def secondMoment : List Atom → Rat
  | [] => 0
  | a :: atoms => a.weight * (a.error * a.error) + secondMoment atoms

/-- The mass of outcomes whose squared error is at least `q`. -/
def tailMass (q : Rat) : List Atom → Rat
  | [] => 0
  | a :: atoms => (if q ≤ a.error * a.error then a.weight else 0) + tailMass q atoms

/-- The mass of outcomes whose squared error is strictly below `q`. -/
def insideMass (q : Rat) : List Atom → Rat
  | [] => 0
  | a :: atoms => (if a.error * a.error < q then a.weight else 0) + insideMass q atoms

def NonnegativeWeights (atoms : List Atom) : Prop :=
  ∀ a ∈ atoms, 0 ≤ a.weight

/-- List positions are elementary outcomes.  Equal atom values may occur at
distinct positions; their masses add, so duplicate values do not invalidate
the finite probability interpretation. -/
structure FiniteErrorLaw where
  atoms : List Atom
  weights_nonnegative : NonnegativeWeights atoms
  total_mass_one : mass atoms = 1

theorem square_nonnegative (x : Rat) : 0 ≤ x * x := by
  by_cases hx : 0 ≤ x
  · exact Rat.mul_nonneg hx hx
  · have hn : 0 ≤ -x := by grind
    have hh := Rat.mul_nonneg hn hn
    grind

theorem square_le_square_of_nonnegative (a b : Rat)
    (ha : 0 ≤ a) (hab : a ≤ b) : a * a ≤ b * b := by
  have hb : 0 ≤ b := Rat.le_trans ha hab
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hab ha)
    (Rat.mul_le_mul_of_nonneg_left hab hb)

/-- This proves the event interpretation; it is not merely a name assigned to
a squared-error comparison.  The right side means `|x| >= epsilon`. -/
theorem squared_error_event_iff (x epsilon : Rat) (he : 0 < epsilon) :
    epsilon * epsilon ≤ x * x ↔ x ≤ -epsilon ∨ epsilon ≤ x := by
  constructor
  · intro hsq
    by_cases hlo : x ≤ -epsilon
    · exact Or.inl hlo
    · by_cases hhi : epsilon ≤ x
      · exact Or.inr hhi
      · have hleft : 0 < epsilon - x := by grind
        have hright : 0 < epsilon + x := by grind
        have hp := Rat.mul_pos hleft hright
        grind
  · intro h
    cases h with
    | inl hlo =>
      have hle : epsilon ≤ -x := by grind
      have hs := square_le_square_of_nonnegative epsilon (-x) (Rat.le_of_lt he) hle
      grind
    | inr hhi =>
      exact square_le_square_of_nonnegative epsilon x (Rat.le_of_lt he) hhi

theorem secondMoment_nonnegative (atoms : List Atom)
    (hw : NonnegativeWeights atoms) : 0 ≤ secondMoment atoms := by
  induction atoms with
  | nil => exact Rat.le_refl
  | cons a atoms ih =>
    have ha : 0 ≤ a.weight := hw a (by simp)
    have ht : NonnegativeWeights atoms := by
      intro b hb
      exact hw b (by simp [hb])
    have hterm := Rat.mul_nonneg ha (square_nonnegative a.error)
    have hrest := ih ht
    exact Rat.add_nonneg hterm hrest

/-- The pointwise Markov bound for the nonnegative variable `error²`. -/
theorem atom_tail_bound (a : Atom) (q : Rat) (hw : 0 ≤ a.weight) :
    q * (if q ≤ a.error * a.error then a.weight else 0) ≤
      a.weight * (a.error * a.error) := by
  by_cases hq : q ≤ a.error * a.error
  · simp only [if_pos hq]
    have h := Rat.mul_le_mul_of_nonneg_left hq hw
    simpa only [Rat.mul_comm q a.weight] using h
  · simp only [if_neg hq, Rat.mul_zero]
    exact Rat.mul_nonneg hw (square_nonnegative a.error)

/-- The finite weighted inequality, without assuming total mass one. -/
theorem cutoff_mul_tail_le_secondMoment (atoms : List Atom) (q : Rat)
    (hw : NonnegativeWeights atoms) :
    q * tailMass q atoms ≤ secondMoment atoms := by
  induction atoms with
  | nil => simp [tailMass, secondMoment]; exact Rat.le_refl
  | cons a atoms ih =>
    have ha : 0 ≤ a.weight := hw a (by simp)
    have ht : NonnegativeWeights atoms := by
      intro b hb
      exact hw b (by simp [hb])
    have hhead := atom_tail_bound a q ha
    have htail := ih ht
    simp only [tailMass, secondMoment, Rat.mul_add]
    grind

theorem tailMass_nonnegative (atoms : List Atom) (q : Rat)
    (hw : NonnegativeWeights atoms) : 0 ≤ tailMass q atoms := by
  induction atoms with
  | nil => exact Rat.le_refl
  | cons a atoms ih =>
    have ha : 0 ≤ a.weight := hw a (by simp)
    have ht : NonnegativeWeights atoms := by
      intro b hb
      exact hw b (by simp [hb])
    have hrest := ih ht
    simp only [tailMass]
    split
    · exact Rat.add_nonneg ha hrest
    · simpa only [Rat.zero_add] using hrest

theorem tailMass_le_mass (atoms : List Atom) (q : Rat)
    (hw : NonnegativeWeights atoms) : tailMass q atoms ≤ mass atoms := by
  induction atoms with
  | nil => exact Rat.le_refl
  | cons a atoms ih =>
    have ha : 0 ≤ a.weight := hw a (by simp)
    have ht : NonnegativeWeights atoms := by
      intro b hb
      exact hw b (by simp [hb])
    have hrest := ih ht
    simp only [tailMass, mass]
    split <;> grind

/-- This checks the probability interpretation, rather than only naming an
arbitrary weighted sum a probability. -/
theorem tail_probability_bounds (law : FiniteErrorLaw) (q : Rat) :
    0 ≤ tailMass q law.atoms ∧ tailMass q law.atoms ≤ 1 := by
  constructor
  · exact tailMass_nonnegative law.atoms q law.weights_nonnegative
  · have h := tailMass_le_mass law.atoms q law.weights_nonnegative
    simpa only [law.total_mass_one] using h

theorem inside_plus_tail_eq_mass (atoms : List Atom) (q : Rat) :
    insideMass q atoms + tailMass q atoms = mass atoms := by
  induction atoms with
  | nil => simp [insideMass, tailMass, mass]; grind
  | cons a atoms ih =>
    simp only [insideMass, tailMass, mass]
    by_cases hq : q ≤ a.error * a.error
    · have hnot : ¬a.error * a.error < q := by grind
      simp only [if_pos hq, if_neg hnot]
      grind
    · have hlt : a.error * a.error < q := Rat.not_le.mp hq
      simp only [if_neg hq, if_pos hlt]
      grind

theorem coverage_from_tail_bound (law : FiniteErrorLaw) (q alpha : Rat)
    (htail : tailMass q law.atoms ≤ alpha) :
    1 - alpha ≤ insideMass q law.atoms := by
  have hp := inside_plus_tail_eq_mass law.atoms q
  have hm := law.total_mass_one
  grind

/-- Markov's inequality for squared error on a finite rational probability law.
It becomes the usual Chebyshev inequality when the target is the mean. -/
theorem finite_second_moment_risk_bound (law : FiniteErrorLaw) (q : Rat)
    (hq : 0 < q) :
    tailMass q law.atoms ≤ secondMoment law.atoms / q := by
  have h := cutoff_mul_tail_le_secondMoment law.atoms q law.weights_nonnegative
  apply Rat.le_of_mul_le_mul_right (c := q) (hc := hq)
  rw [Rat.div_mul_cancel (Rat.ne_of_gt hq)]
  simpa only [Rat.mul_comm q (tailMass q law.atoms)] using h

/-- With a positive error tolerance, the bad event is `epsilon² ≤ error²`,
equivalently being outside the open interval `(-epsilon, epsilon)`.
`alpha` is the failure probability; the confidence level is `1 - alpha`. -/
theorem finite_tolerance_risk_bound (law : FiniteErrorLaw) (epsilon alpha : Rat)
    (he : 0 < epsilon)
    (hm : secondMoment law.atoms ≤ alpha * (epsilon * epsilon)) :
    tailMass (epsilon * epsilon) law.atoms ≤ alpha := by
  have he2 : 0 < epsilon * epsilon := Rat.mul_pos he he
  have h := cutoff_mul_tail_le_secondMoment law.atoms (epsilon * epsilon)
    law.weights_nonnegative
  have hh := Rat.le_trans h hm
  apply Rat.le_of_mul_le_mul_right (c := epsilon * epsilon) (hc := he2)
  simpa only [Rat.mul_comm (epsilon * epsilon)
    (tailMass (epsilon * epsilon) law.atoms)] using hh

/-- Fixed-n corollary.  `n` is a positive rational representation of the
preassigned sample count.  The premise `secondMoment <= V/n` must be proved
or independently justified for the error of that sample mean.  For unbiased,
pairwise uncorrelated measurements of variance at most V it is the familiar
bound; that probabilistic derivation is NOT an assumption-free result here.

The sample-size condition is written without division as `V <= n*alpha*eps²`.
For positive `alpha` and `epsilon`, it is equivalent to
`n >= V/(alpha*eps²)`.  Merely substituting a sample variance for V does not
establish either premise. -/
theorem fixed_sample_count_risk_bound (law : FiniteErrorLaw)
    (n V epsilon alpha : Rat)
    (hn : 0 < n) (he : 0 < epsilon)
    (hm : secondMoment law.atoms ≤ V / n)
    (hbudget : V ≤ n * (alpha * (epsilon * epsilon))) :
    tailMass (epsilon * epsilon) law.atoms ≤ alpha := by
  apply finite_tolerance_risk_bound law epsilon alpha he
  have hdiv : V / n ≤ alpha * (epsilon * epsilon) := by
    apply Rat.le_of_mul_le_mul_right (c := n) (hc := hn)
    rw [Rat.div_mul_cancel (Rat.ne_of_gt hn)]
    simpa only [Rat.mul_comm n (alpha * (epsilon * epsilon))] using hbudget
  exact Rat.le_trans hm hdiv

/-- The usual division-form sample-size condition is equivalent to the
multiplication-form budget when the failure probability and tolerance are
positive. -/
theorem sample_count_condition_iff (n V epsilon alpha : Rat)
    (ha : 0 < alpha) (he : 0 < epsilon) :
    V / (alpha * (epsilon * epsilon)) ≤ n ↔
      V ≤ n * (alpha * (epsilon * epsilon)) := by
  have hd : 0 < alpha * (epsilon * epsilon) := Rat.mul_pos ha (Rat.mul_pos he he)
  constructor
  · intro h
    have hm := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hd)
    rw [Rat.div_mul_cancel (Rat.ne_of_gt hd)] at hm
    exact hm
  · intro h
    apply Rat.le_of_mul_le_mul_right (c := alpha * (epsilon * epsilon)) (hc := hd)
    rw [Rat.div_mul_cancel (Rat.ne_of_gt hd)]
    exact h

/-- A positive natural sample count, the conventional sufficient n-bound, and
both the failure-probability and confidence conclusions.  The error law and
the MSE premise remain explicit.  `alpha` denotes failure probability, not
confidence; in an application one chooses `0 < alpha < 1`. -/
theorem fixed_n_risk_and_coverage_from_second_moment (law : FiniteErrorLaw)
    (n : Nat) (V epsilon alpha : Rat)
    (hn : 0 < n) (ha : 0 < alpha) (he : 0 < epsilon)
    (hm : secondMoment law.atoms ≤ V / (n : Rat))
    (hcount : V / (alpha * (epsilon * epsilon)) ≤ (n : Rat)) :
    tailMass (epsilon * epsilon) law.atoms ≤ alpha ∧
      1 - alpha ≤ insideMass (epsilon * epsilon) law.atoms := by
  have hnq : 0 < (n : Rat) := Rat.natCast_pos.mpr hn
  have hbudget := (sample_count_condition_iff (n : Rat) V epsilon alpha ha he).mp hcount
  have hrisk := fixed_sample_count_risk_bound law (n : Rat) V epsilon alpha hnq he hm hbudget
  exact ⟨hrisk, coverage_from_tail_bound law (epsilon * epsilon) alpha hrisk⟩

end Stripes.FiniteRisk

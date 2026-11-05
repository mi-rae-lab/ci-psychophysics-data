import Std

/-!
Exact arithmetic consequences of the default protocol. No assertion here
identifies a JavaScript Number operation with exact arithmetic. In particular,
the integer 3 dB decision is deliberately separated from binary64 subtraction.
-/
namespace Stm.Arithmetic

def sumDb : List Int → Int
  | [] => 0
  | x :: xs => x + sumDb xs

def BoundedLevels (xs : List Int) : Prop :=
  ∀ x ∈ xs, -50 ≤ x ∧ x ≤ 0

theorem sum_upper (xs : List Int) (h : BoundedLevels xs) : sumDb xs ≤ 0 := by
  induction xs with
  | nil => simp [sumDb]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : BoundedLevels xs := by
      intro y hy
      exact h y (by simp [hy])
    have hi := ih ht
    simp only [sumDb]
    omega

theorem sum_lower (xs : List Int) (h : BoundedLevels xs) :
    (-50 : Int) * (xs.length : Int) ≤ sumDb xs := by
  induction xs with
  | nil => simp [sumDb]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : BoundedLevels xs := by
      intro y hy
      exact h y (by simp [hy])
    have hi := ih ht
    simp only [sumDb, List.length_cons]
    omega

theorem ten_reversal_numerator_bounds (xs : List Int)
    (h : BoundedLevels xs) (len : xs.length = 10) :
    -500 ≤ sumDb xs ∧ sumDb xs ≤ 0 := by
  have hl := sum_lower xs h
  have hu := sum_upper xs h
  simp only [len] at hl
  omega

def EvenLevels (xs : List Int) : Prop := ∀ x ∈ xs, x % 2 = 0

theorem sum_even (xs : List Int) (h : EvenLevels xs) : sumDb xs % 2 = 0 := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : EvenLevels xs := by
      intro y hy
      exact h y (by simp [hy])
    have hi := ih ht
    simp only [sumDb]
    omega

/- An exact threshold is numerator/denominator, not a rounded Float. -/
structure ExactMean where
  numerator : Int
  denominator : Nat
  positive : 0 < denominator

def threshold10 (xs : List Int) : ExactMean :=
  ⟨sumDb xs, 10, by decide⟩

theorem threshold_denominator (xs : List Int) :
    (threshold10 xs).denominator = 10 := rfl

def needsThird (sum1 sum2 : Int) : Bool := decide (30 < (sum1 - sum2).natAbs)

theorem exact_three_no_third (a b : Int) (h : (a-b).natAbs = 30) :
    needsThird a b = false := by simp [needsThird, h]

theorem above_three_needs_third (a b : Int) (h : 30 < (a-b).natAbs) :
    needsThird a b = true := by simp [needsThird, h]

theorem below_three_no_third (a b : Int) (h : (a-b).natAbs ≤ 30) :
    needsThird a b = false := by simp [needsThird]; omega

theorem exact_counterexample_pair : needsThird (-68) (-98) = false := by decide

/- Actual binary64 encodings are independently inspected in the JS witness.
   These theorems concern their exact rational values, not an IEEE semantics
   implementation or the compiler's floating point arithmetic. -/
def binary64CommonDenominator : Int := 1125899906842624
def encodedNeg68Numerator : Int := -7656119366529843
def encodedNeg98Numerator : Int := -2758454771764429 * 4

theorem encoded_pair_delta :
    encodedNeg68Numerator - encodedNeg98Numerator =
      3 * binary64CommonDenominator + 1 := by decide

theorem encoded_pair_strictly_above_three :
    3 * binary64CommonDenominator <
      encodedNeg68Numerator - encodedNeg98Numerator := by decide

theorem encoding_denominator_positive : 0 < binary64CommonDenominator := by decide

/- Exact digital timing; these are sample counts, not physical output latency. -/
def sampleRate : Nat := 44100
def rampSamples : Nat := 882
def leadSamples : Nat := 22050
def intervalSamples : Nat := 44100
def isiSamples : Nat := 22050
def firstOn : Nat := leadSamples
def firstOff : Nat := firstOn + intervalSamples
def secondOn : Nat := firstOff + isiSamples
def secondOff : Nat := secondOn + intervalSamples

theorem ramp_exact_twenty_ms : rampSamples * 1000 = sampleRate * 20 := by decide
theorem isi_exact_half_second : isiSamples * 2 = sampleRate := by decide
theorem first_interval_exact : firstOff - firstOn = sampleRate := by decide
theorem second_interval_exact : secondOff - secondOn = sampleRate := by decide
theorem total_exact_three_seconds : secondOff = 3 * sampleRate := by decide
theorem intervals_disjoint : firstOff < secondOn := by decide
theorem sample_indices :
    firstOn = 22050 ∧ firstOff = 66150 ∧ secondOn = 88200 ∧ secondOff = 132300 := by decide

/- The envelope sample clock is the rational pair 44100/44. -/
theorem envelope_rate_not_1000 : (44100 : Nat) ≠ 1000 * 44 := by decide
theorem envelope_clock_exact (n : Nat) : n * 44 * 44100 = 44100 * (44 * n) := by
  omega

/- Abstract finite sums for the C/P/Q linear recombination, over integers.
This proves distributivity only, not trigonometry, FFTs, or Float error bounds. -/
theorem scalar_sum (a : Int) (xs : List Int) :
    sumDb (xs.map (fun x => a * x)) = a * sumDb xs := by
  induction xs with
  | nil => simp [sumDb]
  | cons x xs ih => simp [sumDb, ih, Int.mul_add]

theorem pair_sum (xs : List (Int × Int)) :
    sumDb (xs.map (fun x => x.1 + x.2)) =
      sumDb (xs.map Prod.fst) + sumDb (xs.map Prod.snd) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, sumDb]; rw [ih]; omega

theorem modulation_recombination (a s c p q carrier : Int) :
    carrier + a * (s * p + c * q) = carrier + a * s * p + a * c * q := by
  simp only [Int.mul_add, Int.mul_assoc]
  omega

end Stm.Arithmetic

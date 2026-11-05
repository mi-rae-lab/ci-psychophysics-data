import Stm.Staircase
import Stm.Arithmetic

/-!
Connection from reachable default staircase states to an exact rational
threshold. Numerator/denominator pairs denote exact fractions; this module
does not identify them with JavaScript's rounded Number division. The
source's Number.isFinite check is not modeled as a primitive. Instead, the
proof supplies finite integer numerator bounds and a positive denominator.
-/
namespace Stm.Threshold

open Stm.Staircase Stm.Arithmetic

def retained (s : State) : List Int :=
  (s.reversals.drop (s.reversals.length - 10)).map Reversal.db

def threshold (s : State) : Option ExactMean :=
  if s.reversals.length < 14 then none else some (threshold10 (retained s))

theorem threshold_absent_before_target (s : State) (h : s.reversals.length < 14) :
    threshold s = none := by simp [threshold, h]

theorem threshold_present_at_target (s : State) (h : 14 ≤ s.reversals.length) :
    threshold s = some (threshold10 (retained s)) := by
  simp [threshold, Nat.not_lt.mpr h]

theorem retained_count (s : State) (h : 10 ≤ s.reversals.length) :
    (retained s).length = 10 := by
  simp only [retained, List.length_map, List.length_drop]
  omega

theorem reachable_target_exactly_fourteen (s : State) (hr : Reachable s)
    (ht : 14 ≤ s.reversals.length) : s.reversals.length = 14 := by
  have hl := (reachable_counter_limits s hr).2.2
  omega

theorem reachable_retains_reversals_five_through_fourteen
    (s : State) (hr : Reachable s) (ht : 14 ≤ s.reversals.length) :
    retained s = (s.reversals.drop 4).map Reversal.db := by
  simp [retained, reachable_target_exactly_fourteen s hr ht]

theorem reachable_retained_bounded (s : State) (hr : Reachable s) :
    BoundedLevels (retained s) := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨r, hm, he⟩
  have hs := reachable_reversals_safe s hr r (List.mem_of_mem_drop hm)
  rw [← he]
  exact hs.1

theorem reachable_retained_even (s : State) (hr : Reachable s) :
    EvenLevels (retained s) := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨r, hm, he⟩
  have hs := reachable_reversals_safe s hr r (List.mem_of_mem_drop hm)
  rw [← he]
  exact hs.2.1

theorem reachable_threshold_numerator_bounds (s : State) (hr : Reachable s)
    (ht : 14 ≤ s.reversals.length) :
    -500 ≤ sumDb (retained s) ∧ sumDb (retained s) ≤ 0 := by
  apply ten_reversal_numerator_bounds
  · exact reachable_retained_bounded s hr
  · apply retained_count; omega

theorem reachable_threshold_numerator_even (s : State) (hr : Reachable s) :
    sumDb (retained s) % 2 = 0 :=
  sum_even (retained s) (reachable_retained_even s hr)

theorem reachable_threshold_numerator_is_twice_integer (s : State)
    (hr : Reachable s) : ∃ k : Int, sumDb (retained s) = 2 * k := by
  refine ⟨sumDb (retained s) / 2, ?_⟩
  have he := reachable_threshold_numerator_even s hr
  have hd := Int.emod_add_ediv (sumDb (retained s)) 2
  omega

def ExactEquivalent (a b : ExactMean) : Prop :=
  a.numerator * (b.denominator : Int) = b.numerator * (a.denominator : Int)

def fifthMean (k : Int) : ExactMean := ⟨k, 5, by decide⟩

/- The grid spacing is exactly 1/5 dB, i.e. 0.2 dB as a rational.
   It does not claim that 0.2 is exactly representable in binary64. -/
theorem reachable_threshold_on_one_fifth_db_grid (s : State) (hr : Reachable s) :
    ∃ k : Int, ExactEquivalent (threshold10 (retained s)) (fifthMean k) := by
  rcases reachable_threshold_numerator_is_twice_integer s hr with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  unfold ExactEquivalent threshold10 fifthMean
  dsimp
  omega

theorem present_threshold_requires_target (s : State) (m : ExactMean)
    (hm : threshold s = some m) : 14 ≤ s.reversals.length := by
  unfold threshold at hm
  split at hm
  · contradiction
  · omega

theorem reachable_present_threshold_certificate (s : State) (hr : Reachable s)
    (m : ExactMean) (hm : threshold s = some m) :
    m.denominator = 10 ∧ -500 ≤ m.numerator ∧ m.numerator ≤ 0 ∧
    m.numerator % 2 = 0 ∧ ∃ k : Int, ExactEquivalent m (fifthMean k) := by
  have ht := present_threshold_requires_target s m hm
  have hp := threshold_present_at_target s ht
  rw [hp] at hm
  have hmeq := Option.some.inj hm
  rw [← hmeq]
  have hb := reachable_threshold_numerator_bounds s hr ht
  exact ⟨rfl, hb.1, hb.2, reachable_threshold_numerator_even s hr,
    reachable_threshold_on_one_fifth_db_grid s hr⟩

theorem reachable_present_threshold_within_db_bounds (s : State) (hr : Reachable s)
    (m : ExactMean) (hm : threshold s = some m) :
    (-50 : Int) * (m.denominator : Int) ≤ m.numerator ∧
    m.numerator ≤ 0 * (m.denominator : Int) := by
  rcases reachable_present_threshold_certificate s hr m hm with ⟨hd, hl, hu, _⟩
  rw [hd]
  constructor <;> omega

end Stm.Threshold

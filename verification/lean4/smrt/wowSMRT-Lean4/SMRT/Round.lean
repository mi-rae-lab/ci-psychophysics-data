import SMRT.Exact

/-!
# 반올림의 정확한 값 (Claude, 2026-10-22)

앱은 부동소수로 셈한 뒤 `toFixed(k)` 로 보여 주거나 저장함 (역치 `+m.toFixed(4)`, SD `+sd.toFixed(4)`, 결과 화면 `toFixed(2)`).
여기서는 같은 값을 정수로 정확히 셈:
* `roundDiv n d` (Exact.lean) = n/d 에 가장 가까운 정수 (반은 올림), `isTie n d` = n/d 가 정확히 ‘정수 + 1/2’ (반올림이 갈리는 경우)
* `sqrtRound N D` = √(N/D) 에 가장 가까운 정수 — (2k−1)²·D ≤ 4N < (2k+1)²·D 인 k (곧 k − ½ ≤ √(N/D) < k + ½),
  정수 이분 탐색으로 찾고 그 성질(`sqrtRound_spec`) · 유일성(`sqLe_window_unique`) 을 증명. `sqTie` = √(N/D) 가 정확히 ‘정수 + 1/2’.
-/

namespace SMRT

/-! ## 나눗셈 반올림이 갈리는 경우 -/

/-- n/d 가 정확히 ‘정수 + 1/2’ ⇔ 2n + d 가 2d 로 나누어떨어짐 -/
def isTie (n d : Nat) : Bool := (2 * n + d) % (2 * d) == 0

theorem isTie_spec {n d : Nat} (hd : 0 < d) (h : isTie n d = true) : ∃ j, 2 * n = (2 * j + 1) * d := by
  unfold isTie at h
  have h0 : (2 * n + d) % (2 * d) = 0 := by simpa using h
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero h0
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; omega
    · exact h
  refine ⟨q - 1, ?_⟩
  have e : (2 * (q - 1) + 1) * d = 2 * d * q - d := by
    rw [show 2 * (q - 1) + 1 = 2 * q - 1 by omega, Nat.sub_mul, Nat.one_mul]
    rw [show 2 * q * d = 2 * d * q by rw [Nat.mul_assoc, Nat.mul_comm q d, ← Nat.mul_assoc]]
  rw [e]; omega

theorem not_isTie_of {n d : Nat} (hd : 0 < d) (h : ∀ j, 2 * n ≠ (2 * j + 1) * d) : isTie n d = false := by
  cases hT : isTie n d with
  | false => rfl
  | true => obtain ⟨j, hj⟩ := isTie_spec hd hT; exact absurd hj (h j)

/-! ## 제곱근 반올림 -/

/-- k − 1/2 ≤ √(N/D) 인가 — (2k−1)²·D ≤ 4N (k = 0 은 늘 참) -/
def sqLe (N D k : Nat) : Bool := k == 0 || decide ((2 * k - 1) ^ 2 * D ≤ 4 * N)

/-- 이분 탐색: sqLe lo 참 · sqLe hi 거짓 사이에서 참인 가장 큰 k -/
def bsearch (N D lo hi : Nat) : Nat :=
  if lo + 1 < hi then
    if sqLe N D ((lo + hi) / 2) then bsearch N D ((lo + hi) / 2) hi else bsearch N D lo ((lo + hi) / 2)
  else lo
termination_by hi - lo
decreasing_by all_goals omega

/-- √(N/D) 에 가장 가까운 정수 (반은 올림) -/
def sqrtRound (N D : Nat) : Nat := bsearch N D 0 (N + 2)

/-- √(N/D) 가 정확히 ‘k − 1/2’ (반올림이 갈리는 경우) — 고른 k 에서 4N = (2k−1)²·D -/
def sqTie (N D : Nat) : Bool := let k := sqrtRound N D; k != 0 && (2 * k - 1) ^ 2 * D == 4 * N

theorem bsearch_spec (N D : Nat) : ∀ lo hi, sqLe N D lo = true → sqLe N D hi = false → lo < hi →
    sqLe N D (bsearch N D lo hi) = true ∧ sqLe N D (bsearch N D lo hi + 1) = false := by
  intro lo hi
  induction lo, hi using bsearch.induct (N := N) (D := D) with
  | case1 lo hi hlt hmid ih =>
    intro hl hh _
    rw [bsearch, if_pos hlt, if_pos hmid]
    exact ih hmid hh (by omega)
  | case2 lo hi hlt hmid ih =>
    intro hl hh _
    rw [bsearch, if_pos hlt, if_neg hmid]
    exact ih hl (by simpa using hmid) (by omega)
  | case3 lo hi hlt =>
    intro hl hh hl2
    rw [bsearch, if_neg hlt]
    have : hi = lo + 1 := by omega
    subst this
    exact ⟨hl, hh⟩

/-- 결과 k 의 성질: (k = 0 ∨ (2k−1)²·D ≤ 4N) ∧ 4N < (2k+1)²·D -/
theorem sqrtRound_spec (N D : Nat) (hD : 0 < D) :
    sqLe N D (sqrtRound N D) = true ∧ sqLe N D (sqrtRound N D + 1) = false := by
  apply bsearch_spec
  · simp [sqLe]
  · simp only [sqLe, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, decide_eq_false_iff_not, Nat.not_le]
    refine ⟨by omega, ?_⟩
    have h1 : 4 * N < (2 * (N + 2) - 1) ^ 2 := by
      rw [show 2 * (N + 2) - 1 = 2 * N + 3 by omega, Nat.pow_two]
      have := Nat.mul_le_mul_left (2 * N + 3) (show 2 ≤ 2 * N + 3 by omega)
      omega
    have h2 : (2 * (N + 2) - 1) ^ 2 ≤ (2 * (N + 2) - 1) ^ 2 * D := Nat.le_mul_of_pos_right _ hD
    omega
  · omega

/-- sqLe 는 단조: 큰 k 에서 참이면 작은 k 에서도 참 -/
theorem sqLe_mono (N D : Nat) {k k' : Nat} (hk : k ≤ k') (h : sqLe N D k' = true) : sqLe N D k = true := by
  unfold sqLe at *
  by_cases hk0 : k = 0
  · simp [hk0]
  · simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h ⊢
    right
    rcases h with h | h
    · omega
    · have hle : (2 * k - 1) ^ 2 ≤ (2 * k' - 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have := Nat.mul_le_mul_right D hle
      omega

/-- (참, 다음은 거짓) 인 k 는 하나뿐 — 가장 가까운 정수는 유일 -/
theorem sqLe_window_unique (N D : Nat) {k k' : Nat}
    (h1 : sqLe N D k = true) (h2 : sqLe N D (k + 1) = false)
    (h1' : sqLe N D k' = true) (h2' : sqLe N D (k' + 1) = false) : k = k' := by
  rcases Nat.lt_trichotomy k k' with h | h | h
  · have := sqLe_mono N D (show k + 1 ≤ k' by omega) h1'; rw [h2] at this; cases this
  · exact h
  · have := sqLe_mono N D (show k' + 1 ≤ k by omega) h1; rw [h2'] at this; cases this

end SMRT

import Std

/-!
# 정확한 정수 계산의 기초 — 와우SRD (Claude, 2026-10-21)

core Lean 4.24 만 씀 (Mathlib 없음). 앱 `js/analysis.js` 의 BigInt 계산을 옮기기 위한 것:
* `sumTo f n` = Σ_{x<n} f x (자연수), `sumQ f n` = 같은 합 (유리수)
* `choose` = 파스칼 규칙으로 정의한 이항계수 (core 에는 Nat.choose 가 없음)
* `pascalRow n` = js `Exact.binomRow(n)` 의 만드는 법 그대로 (앞 행의 이웃 둘을 더함) —
  모든 n, x 에서 `(pascalRow n).getD x 0 = choose n x` (`pascalRow_getD`)
합 · choose 의 보조정리 일부는 와우포먼트 tools/lean/exact/Formant/ExactArith.lean (Claude, 2026-10-20) 에서 가져옴.
-/

namespace SRD

/-! ## 합 -/

/-- Σ_{x<n} f x -/
def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo f n + f n

/-- Σ_{x<n} f x (유리수) -/
def sumQ (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => sumQ f n + f n

/-- Σ_{x<n} f x (정수) -/
def sumZ (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => sumZ f n + f n

@[simp] theorem sumTo_zero (f : Nat → Nat) : sumTo f 0 = 0 := rfl
@[simp] theorem sumTo_succ (f : Nat → Nat) (n : Nat) : sumTo f (n + 1) = sumTo f n + f n := rfl
@[simp] theorem sumQ_zero (f : Nat → Rat) : sumQ f 0 = 0 := rfl
@[simp] theorem sumQ_succ (f : Nat → Rat) (n : Nat) : sumQ f (n + 1) = sumQ f n + f n := rfl
@[simp] theorem sumZ_zero (f : Nat → Int) : sumZ f 0 = 0 := rfl
@[simp] theorem sumZ_succ (f : Nat → Int) (n : Nat) : sumZ f (n + 1) = sumZ f n + f n := rfl

theorem sumTo_congr {f g : Nat → Nat} {n : Nat} (h : ∀ x, x < n → f x = g x) :
    sumTo f n = sumTo g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumTo_succ, sumTo_succ, ih (fun x hx => h x (by omega)), h n (by omega)]

theorem sumQ_congr {f g : Nat → Rat} {n : Nat} (h : ∀ x, x < n → f x = g x) :
    sumQ f n = sumQ g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumQ_succ, sumQ_succ, ih (fun x hx => h x (by omega)), h n (by omega)]

theorem sumTo_add (f g : Nat → Nat) (n : Nat) :
    sumTo (fun x => f x + g x) n = sumTo f n + sumTo g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumTo_succ, ih]; omega

theorem sumTo_le {f g : Nat → Nat} {n : Nat} (h : ∀ x, x < n → f x ≤ g x) :
    sumTo f n ≤ sumTo g n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    have h1 := ih (fun x hx => h x (by omega))
    have h2 := h n (by omega)
    simp only [sumTo_succ]; omega

theorem sumTo_eq_zero {f : Nat → Nat} {n : Nat} (h : ∀ x, x < n → f x = 0) : sumTo f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumTo_succ, ih (fun x hx => h x (by omega)), h n (by omega)]

theorem le_sumTo {f : Nat → Nat} {n x : Nat} (hx : x < n) : f x ≤ sumTo f n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sumTo_succ]
    by_cases h : x < n
    · have := ih h; omega
    · have : x = n := by omega
      subst this; omega

/-- 앞의 m 개와 그 뒤 n 개로 나눔 -/
theorem sumTo_split (f : Nat → Nat) (m n : Nat) :
    sumTo f (m + n) = sumTo f m + sumTo (fun x => f (m + x)) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [← Nat.add_assoc, sumTo_succ, ih, sumTo_succ]; omega

/-- 첫 항을 떼어 냄 -/
theorem sumTo_succ' (f : Nat → Nat) (n : Nat) :
    sumTo f (n + 1) = f 0 + sumTo (fun x => f (x + 1)) n := by
  have h := sumTo_split f 1 n
  rw [Nat.add_comm 1 n] at h
  rw [h]
  simp only [sumTo_succ, sumTo_zero, Nat.zero_add]
  congr 1
  apply sumTo_congr; intro x _; rw [Nat.add_comm]

theorem sumQ_div (f : Nat → Rat) (d : Rat) (n : Nat) :
    sumQ (fun x => f x / d) n = sumQ f n / d := by
  induction n with
  | zero => simp [Rat.div_def]
  | succ n ih => rw [sumQ_succ, sumQ_succ, ih]; simp only [Rat.div_def, Rat.add_mul]

theorem natCast_sumTo (f : Nat → Nat) (n : Nat) :
    ((sumTo f n : Nat) : Rat) = sumQ (fun x => (f x : Rat)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumTo_succ, Rat.natCast_add, ih, sumQ_succ]

/-! ## 유리수 나눗셈 보조정리 (grind 가 비선형이라 직접) -/

theorem div_le_div_iff_of_pos {a b d : Rat} (hd : 0 < d) : a / d ≤ b / d ↔ a ≤ b := by
  have hd0 : d ≠ 0 := Rat.ne_of_gt hd
  have hinv : 0 ≤ d⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hd)
  constructor
  · intro h
    have h2 := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hd)
    rwa [Rat.div_mul_cancel hd0, Rat.div_mul_cancel hd0] at h2
  · intro h
    rw [Rat.div_def, Rat.div_def]
    exact Rat.mul_le_mul_of_nonneg_right h hinv

theorem div_lt_div_iff_of_pos {a b d : Rat} (hd : 0 < d) : a / d < b / d ↔ a < b := by
  rw [← Rat.not_le, ← Rat.not_le, div_le_div_iff_of_pos hd]

/-- n/d < 1/20 ⇔ 20·n < d (자연수, d > 0) — 앱의 `lt05: 20n * num < den` -/
theorem frac_lt_twentieth {n d : Nat} (hd : 0 < d) :
    (n : Rat) / (d : Rat) < 1 / 20 ↔ 20 * n < d := by
  have hd' : (0 : Rat) < (d : Rat) := Rat.natCast_pos.mpr hd
  rw [Rat.div_lt_iff hd']
  have e : (1 : Rat) / 20 * (d : Rat) = (d : Rat) / 20 := by grind
  rw [e, Rat.lt_div_iff (by decide)]
  have e2 : (n : Rat) * 20 = ((20 * n : Nat) : Rat) := by rw [Rat.natCast_mul]; grind
  rw [e2, Rat.natCast_lt_natCast]

theorem natCast_ite (p : Prop) [Decidable p] (a b : Nat) :
    ((if p then a else b : Nat) : Rat) = if p then (a : Rat) else (b : Rat) := by
  split <;> rfl

/-- (if P then a/d else 0) = (if P then a else 0)/d -/
theorem ite_div_eq (p : Prop) [Decidable p] (a d : Nat) :
    (if p then (a : Rat) / (d : Rat) else 0) = ((if p then a else 0 : Nat) : Rat) / (d : Rat) := by
  split
  · rfl
  · simp [Rat.div_def]

/-! ## 이항계수 (파스칼 규칙) -/

/-- 이항계수 C(n, k) — 파스칼 삼각형 -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

@[simp] theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by cases n <;> rfl
@[simp] theorem choose_zero_succ (k : Nat) : choose 0 (k + 1) = 0 := rfl
theorem choose_succ_succ (n k : Nat) : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl

theorem choose_eq_zero_of_lt : ∀ {n k : Nat}, n < k → choose n k = 0
  | 0, 0, h => absurd h (Nat.lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k + 1, h => by
    rw [choose_succ_succ, choose_eq_zero_of_lt (n := n) (k := k) (by omega),
      choose_eq_zero_of_lt (n := n) (k := k + 1) (by omega)]

@[simp] theorem choose_self : ∀ n : Nat, choose n n = 1
  | 0 => rfl
  | n + 1 => by rw [choose_succ_succ, choose_self n, choose_eq_zero_of_lt (Nat.lt_succ_self n)]

theorem choose_pos : ∀ {n k : Nat}, k ≤ n → 0 < choose n k
  | _, 0, _ => by simp
  | 0, _ + 1, h => absurd h (by omega)
  | n + 1, k + 1, h => by
    rw [choose_succ_succ]
    have := choose_pos (n := n) (k := k) (by omega)
    omega

/-- Vandermonde: Σ_{x ≤ c} C(r1,x)·C(r2,c−x) = C(r1+r2, c) (와우포먼트 ExactStats 와 같은 증명) -/
theorem vandermonde (r2 : Nat) : ∀ (r1 c : Nat),
    sumTo (fun x => choose r1 x * choose r2 (c - x)) (c + 1) = choose (r1 + r2) c
  | 0, c => by
    rw [sumTo_succ', sumTo_eq_zero (fun x _ => by simp)]
    simp
  | r1 + 1, 0 => by simp
  | r1 + 1, c + 1 => by
    rw [sumTo_succ']
    have e : (fun x => choose (r1 + 1) (x + 1) * choose r2 (c + 1 - (x + 1)))
        = (fun x => choose r1 x * choose r2 (c - x) + choose r1 (x + 1) * choose r2 (c - x)) := by
      funext x
      rw [choose_succ_succ, Nat.add_sub_add_right, Nat.add_mul]
    rw [e, sumTo_add, vandermonde r2 r1 c]
    have h2 := vandermonde r2 r1 (c + 1)
    rw [sumTo_succ'] at h2
    have e2 : (fun x => choose r1 (x + 1) * choose r2 (c + 1 - (x + 1)))
        = (fun x => choose r1 (x + 1) * choose r2 (c - x)) := by
      funext x; rw [Nat.add_sub_add_right]
    rw [e2] at h2
    simp only [choose_zero_right, Nat.one_mul, Nat.sub_zero] at h2 ⊢
    rw [show r1 + 1 + r2 = (r1 + r2) + 1 by omega, choose_succ_succ]
    omega

/-! ## 파스칼 행 — js `Exact.binomRow` 의 만드는 법 그대로

js: `r[0] = 1; r[m] = 1; r[j] = prev[j − 1] + prev[j]` (1 ≤ j < m) = (0 :: prev) 와 (prev ++ [0]) 를 칸마다 더함 -/

/-- 다음 행: (0 :: r) + (r ++ [0]) 를 칸마다 -/
def pascalNext (r : List Nat) : List Nat := List.zipWith (· + ·) (0 :: r) (r ++ [0])

/-- n 번째 행 (행 0 = [1]) -/
def pascalRow : Nat → List Nat
  | 0 => [1]
  | n + 1 => pascalNext (pascalRow n)

theorem zipWith_add_getD : ∀ (xs ys : List Nat) (i : Nat), xs.length = ys.length →
    (List.zipWith (· + ·) xs ys).getD i 0 = xs.getD i 0 + ys.getD i 0
  | [], [], _, _ => by simp
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | x :: xs, y :: ys, 0, _ => by simp
  | x :: xs, y :: ys, i + 1, h => by
    simp only [List.zipWith_cons_cons, List.getD_cons_succ]
    exact zipWith_add_getD xs ys i (by simpa using h)

theorem append_zero_getD : ∀ (l : List Nat) (i : Nat), (l ++ [0]).getD i 0 = l.getD i 0
  | [], 0 => by simp
  | [], i + 1 => by simp
  | x :: l, 0 => by simp
  | x :: l, i + 1 => by simp only [List.cons_append, List.getD_cons_succ]; exact append_zero_getD l i

theorem pascalRow_length : ∀ n, (pascalRow n).length = n + 1
  | 0 => rfl
  | n + 1 => by
    simp only [pascalRow, pascalNext, List.length_zipWith, List.length_cons, List.length_append,
      pascalRow_length n]
    omega

/-- 파스칼 행의 x 번째 = C(n, x) (행 밖은 0 = C(n, x), x > n) -/
theorem pascalRow_getD : ∀ (n x : Nat), (pascalRow n).getD x 0 = choose n x
  | 0, 0 => rfl
  | 0, x + 1 => by simp [pascalRow]
  | n + 1, x => by
    simp only [pascalRow, pascalNext]
    rw [zipWith_add_getD _ _ _ (by simp [pascalRow_length])]
    rw [append_zero_getD]
    cases x with
    | zero =>
      rw [List.getD_cons_zero, pascalRow_getD n 0]
      simp
    | succ x =>
      simp only [List.getD_cons_succ]
      rw [pascalRow_getD n x, pascalRow_getD n (x + 1), choose_succ_succ]

/-! ## 계산은 빠르게 — 파스칼 재귀 `choose` 는 지수 시간이라, 컴파일된 코드는 행 `pascalRow` 로 셈 (같다는 증명으로 바꿈) -/

theorem arr_getD {α : Type} (l : List α) (i : Nat) (d : α) : l.toArray.getD i d = l.getD i d := by
  simp [Array.getD, List.getD_eq_getElem?_getD]
  split <;> simp_all

def chooseFast (n k : Nat) : Nat := (pascalRow n).getD k 0

@[csimp] theorem choose_eq_chooseFast : @choose = @chooseFast := by
  funext n k
  exact (pascalRow_getD n k).symm

end SRD

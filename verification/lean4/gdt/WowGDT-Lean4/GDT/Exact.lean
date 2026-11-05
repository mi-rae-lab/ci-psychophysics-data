import GDT.Arith

/-!
# 정확 검정 두 가지 — 유리수 명세 = 앱의 정수(BigInt) 구현 (Claude, 2026-11-01 · 와우SMD Exact.lean 을 구간 수 q 로 넓힘)

앱 `js/analysis.js` `Exact`:
* `binomGe(k, n, q)` (q = 구간 수 2 · 3) = { num: Σ_{j=max(0,k)}^{n} C(n,j)·(q−1)^(n−j), den: q^n } — n = 0 이면 null
  (GDT: 우연 관문 · track_not_above_chance — 시행 전체 정답률이 우연 1/q 보다 높은가)
* `fisherGreater(a, b, c, d)` — 표 [[a, b], [c, d]] 첫 행 정답 비율이 둘째 행보다 높은가: P(X ≥ a | 여백 고정),
  r1 = a+b · r2 = c+d · c1 = a+c 가운데 하나라도 0 이거나 c1 = n 이면 { 1, 1 } (GDT: 가장 긴 간격 정답률이 더 짧은 간격보다 낮은가)
* `lt05(p)` = 20·num < den

명세: `geSpec q n k` = P(X ≥ k), X ~ 이항(n, 1/q) = Σ_{j ≥ k} C(n,j)(1/q)^j(1 − 1/q)^(n−j)
      `fgSpec a b c d` = P(X ≥ a), X ~ 초기하(여백 r1, r2, c1) = Σ_{x ≥ a} C(r1,x)C(r2,c1−x)/C(r1+r2,c1)
증명: 모든 입력(q ≥ 1)에서 구현의 분수 = 명세, 구현의 판정 ⇔ 명세 < 1/20, 0 < p ≤ 1.
계산이 빠르도록 행을 밖에서 받는 꼴(`geNumW` · `fgNumW` · `fgDenW`) — 구현은 그 꼴에 그 행을 넣은 것 (정의상 같음).
JS 실행 자체는 증명 범위 밖 — JS ↔ 이 구현은 `CrossCheck.lean` 으로 전수 대조.
-/

namespace GDT

/-! ## 거듭제곱 보조정리 (core 에 Rat.div_pow 가 없어 직접) -/

theorem natCast_pow (a : Nat) : ∀ m : Nat, ((a ^ m : Nat) : Rat) = (a : Rat) ^ m
  | 0 => by simp
  | m + 1 => by rw [Nat.pow_succ, Rat.natCast_mul, natCast_pow a m, Rat.pow_succ]

theorem rat_pow_ne_zero {b : Rat} (hb : b ≠ 0) : ∀ m : Nat, b ^ m ≠ 0
  | 0 => by simp
  | m + 1 => by
    rw [Rat.pow_succ]
    intro h
    rcases Rat.mul_eq_zero.mp h with h1 | h1
    · exact rat_pow_ne_zero hb m h1
    · exact hb h1

theorem rat_one_pow : ∀ m : Nat, (1 : Rat) ^ m = 1
  | 0 => by simp
  | m + 1 => by rw [Rat.pow_succ, rat_one_pow m]; grind

/-- (1/b)^j · (a/b)^m = a^m / b^(j+m) (b ≠ 0) -/
theorem frac_pows (a b : Rat) (hb : b ≠ 0) : ∀ (j m : Nat), ((1 : Rat) / b) ^ j * (a / b) ^ m = a ^ m / b ^ (j + m)
  | 0, 0 => by simp only [Rat.pow_zero, Rat.mul_one]; grind
  | 0, m + 1 => by
    have ih := frac_pows a b hb 0 m
    have hbm := rat_pow_ne_zero hb m
    simp only [Rat.pow_zero, Rat.one_mul, Nat.zero_add] at ih ⊢
    rw [Rat.pow_succ, ih, Rat.pow_succ, Rat.pow_succ]
    grind
  | j + 1, m => by
    have ih := frac_pows a b hb j m
    have hbm := rat_pow_ne_zero hb (j + m)
    rw [Rat.pow_succ, show j + 1 + m = (j + m) + 1 by omega, Rat.pow_succ]
    have e : ((1 : Rat) / b) ^ j * ((1 : Rat) / b) * (a / b) ^ m
        = (((1 : Rat) / b) ^ j * (a / b) ^ m) * ((1 : Rat) / b) := by grind
    rw [e, ih]
    grind

theorem natCast_pred {q : Nat} (hq : 1 ≤ q) : ((q - 1 : Nat) : Rat) = (q : Rat) - 1 := by
  have h : ((q - 1 + 1 : Nat) : Rat) = (q : Rat) := by rw [Nat.sub_add_cancel hq]
  rw [Rat.natCast_add] at h
  have h1 : ((1 : Nat) : Rat) = 1 := rfl
  rw [h1] at h
  grind

/-! ## 한쪽 이항 P(X ≥ k), X ~ 이항(n, 1/q) — js `binomGe(k, n, q)` -/

/-- 명세 -/
def geSpec (q n k : Nat) : Rat :=
  sumQ (fun j => if k ≤ j then (choose n j : Rat) * ((1 : Rat) / q) ^ j * (1 - (1 : Rat) / q) ^ (n - j) else 0) (n + 1)

/-- 구현 (행을 밖에서 받는 꼴): j = k … n 에서 row[j] · (q−1)^(n−j) -/
def geNumW (row : Array Nat) (q n k : Nat) : Nat :=
  sumTo (fun j => if k ≤ j then row.getD j 0 * (q - 1) ^ (n - j) else 0) (n + 1)

/-- 구현 (js `binomGe` 의 num): 행 = `pascalRow n` -/
def geNum (q n k : Nat) : Nat := geNumW (pascalRow n).toArray q n k

/-- 구현: 분모 q^n -/
def geDen (q n : Nat) : Nat := q ^ n

/-- 구현 (js `lt05`): 20·num < den -/
def geSig (q n k : Nat) : Bool := decide (20 * geNum q n k < geDen q n)

theorem geDen_pos {q : Nat} (hq : 1 ≤ q) (n : Nat) : 0 < geDen q n := Nat.pow_pos (by omega)

/-- 구현의 분수 = 명세 (모든 q ≥ 1, n, k) -/
theorem ge_frac {q : Nat} (hq : 1 ≤ q) (n k : Nat) : (geNum q n k : Rat) / (geDen q n : Rat) = geSpec q n k := by
  simp only [geNum, geNumW, geDen, geSpec]
  rw [natCast_sumTo, ← sumQ_div]
  apply sumQ_congr
  intro j hj
  rw [arr_getD, pascalRow_getD]
  split
  · have hq0 : (q : Rat) ≠ 0 := Rat.ne_of_gt (Rat.natCast_pos.mpr (by omega))
    have e := frac_pows ((q - 1 : Nat) : Rat) (q : Rat) hq0 j (n - j)
    rw [show j + (n - j) = n by omega] at e
    have e1 : (1 : Rat) - 1 / (q : Rat) = ((q - 1 : Nat) : Rat) / (q : Rat) := by
      rw [natCast_pred hq]; grind
    rw [e1, Rat.mul_assoc, e, Rat.natCast_mul, natCast_pow, natCast_pow]
    have := rat_pow_ne_zero hq0 n
    grind
  · simp [Rat.div_def]

/-- 구현의 판정 ⇔ 명세 p < 1/20 (‘우연보다 높음’ 의 확인) -/
theorem geSig_iff {q : Nat} (hq : 1 ≤ q) (n k : Nat) : geSig q n k = true ↔ geSpec q n k < 1 / 20 := by
  rw [← ge_frac hq, frac_lt_twentieth (geDen_pos hq n)]
  simp [geSig]

/-- 앱의 두 경우: 2구간 (우연 1/2) · 3구간 (우연 1/3) -/
theorem geSig_iff_two (n k : Nat) : geSig 2 n k = true ↔
    sumQ (fun j => if k ≤ j then (choose n j : Rat) * ((1 : Rat) / 2) ^ j * (1 - (1 : Rat) / 2) ^ (n - j) else 0) (n + 1) < 1 / 20 :=
  geSig_iff (by decide) n k

theorem geSig_iff_three (n k : Nat) : geSig 3 n k = true ↔
    sumQ (fun j => if k ≤ j then (choose n j : Rat) * ((1 : Rat) / 3) ^ j * (1 - (1 : Rat) / 3) ^ (n - j) else 0) (n + 1) < 1 / 20 :=
  geSig_iff (by decide) n k

/-- 이항 정리의 한 꼴: Σ_j C(n,j)·b^(n−j) = (b+1)^n (k = 0 이면 분자 = 분모 → p = 1) -/
theorem sum_choose_pow (b : Nat) : ∀ n : Nat, sumTo (fun j => choose n j * b ^ (n - j)) (n + 1) = (b + 1) ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := sum_choose_pow b n
    rw [sumTo_succ']
    have e : (fun j => choose (n + 1) (j + 1) * b ^ (n + 1 - (j + 1)))
        = (fun j => choose n j * b ^ (n - j) + choose n (j + 1) * b ^ (n - j)) := by
      funext j; rw [choose_succ_succ, Nat.add_sub_add_right, Nat.add_mul]
    rw [e, sumTo_add, ih]
    have h2 : sumTo (fun j => choose n (j + 1) * b ^ (n - j)) (n + 1) + b ^ (n + 1)
        = b * sumTo (fun j => choose n j * b ^ (n - j)) (n + 1) := by
      have hs := sumTo_succ' (fun j => choose n j * b ^ (n + 1 - j)) (n + 1)
      have hz : choose n (n + 1) = 0 := choose_eq_zero_of_lt (by omega)
      have hl : sumTo (fun j => choose n j * b ^ (n + 1 - j)) (n + 1 + 1)
          = b * sumTo (fun j => choose n j * b ^ (n - j)) (n + 1) := by
        rw [sumTo_succ, hz, Nat.zero_mul, Nat.add_zero]
        have : (fun j => choose n j * b ^ (n + 1 - j)) = (fun j => b * (choose n j * b ^ (n - j))) := by
          funext j
          by_cases hj : j ≤ n
          · rw [show n + 1 - j = (n - j) + 1 by omega, Nat.pow_succ]
            rw [Nat.mul_comm b, Nat.mul_assoc]
          · rw [choose_eq_zero_of_lt (by omega)]; simp
        rw [this, sumTo_mul_left]
      have hr : sumTo (fun x => choose n (x + 1) * b ^ (n + 1 - (x + 1))) (n + 1)
          = sumTo (fun j => choose n (j + 1) * b ^ (n - j)) (n + 1) := by
        apply sumTo_congr; intro x _; rw [Nat.add_sub_add_right]
      rw [hl, hr] at hs
      simp only [choose_zero_right, Nat.one_mul, Nat.sub_zero] at hs
      omega
    rw [ih] at h2
    simp only [choose_zero_right, Nat.one_mul, Nat.sub_zero]
    have h4 : (b + 1) ^ (n + 1) = b * (b + 1) ^ n + (b + 1) ^ n := by
      rw [Nat.pow_succ, Nat.mul_add, Nat.mul_one, Nat.mul_comm]
    rw [h4]
    omega

theorem geNum_eq (q n k : Nat) :
    geNum q n k = sumTo (fun j => if k ≤ j then choose n j * (q - 1) ^ (n - j) else 0) (n + 1) := by
  simp only [geNum, geNumW]
  apply sumTo_congr; intro j _; rw [arr_getD, pascalRow_getD]

/-- p ≤ 1 -/
theorem geNum_le {q : Nat} (hq : 1 ≤ q) (n k : Nat) : geNum q n k ≤ geDen q n := by
  rw [geNum_eq, geDen]
  have h := sum_choose_pow (q - 1) n
  rw [Nat.sub_add_cancel hq] at h
  rw [← h]
  apply sumTo_le; intro j _; split <;> omega

/-- k ≤ n 이면 p > 0 -/
theorem geNum_pos {q n k : Nat} (h : k ≤ n) : 0 < geNum q n k := by
  rw [geNum_eq]
  have hle := le_sumTo (f := fun j => if k ≤ j then choose n j * (q - 1) ^ (n - j) else 0) (x := n) (n := n + 1) (by omega)
  simp only [h, ↓reduceIte, choose_self, Nat.one_mul, Nat.sub_self, Nat.pow_zero] at hle
  omega

/-- k = 0 이면 p = 1 -/
theorem geNum_zero {q : Nat} (hq : 1 ≤ q) (n : Nat) : geNum q n 0 = geDen q n := by
  rw [geNum_eq, geDen]
  have h := sum_choose_pow (q - 1) n
  rw [Nat.sub_add_cancel hq] at h
  rw [← h]
  apply sumTo_congr; intro j _; simp

/-! ## Fisher 한쪽: P(X ≥ a), X ~ 초기하 -/

/-- 왼쪽 위 칸이 x 인 표의 경우의 수 C(r1,x)·C(r2,c1−x) -/
def hyp (r1 r2 c1 x : Nat) : Nat := choose r1 x * choose r2 (c1 - x)

/-- 그 표의 확률 (초기하) -/
def hypP (r1 r2 c1 x : Nat) : Rat := (hyp r1 r2 c1 x : Rat) / (choose (r1 + r2) c1 : Rat)

/-- 명세 (여백): Σ_{x=0}^{c1} [a ≤ x] hypP x -/
def fgSpecM (r1 r2 c1 a : Nat) : Rat := sumQ (fun x => if a ≤ x then hypP r1 r2 c1 x else 0) (c1 + 1)

/-- 명세: 표 (a, b / c, d) 의 한쪽 Fisher p = P(X ≥ a) -/
def fgSpec (a b c d : Nat) : Rat := fgSpecM (a + b) (c + d) (a + c) a

/-- js 가 계산하지 않고 1/1 을 돌려주는 표: r1 = 0 · r2 = 0 · c1 = 0 · c1 = n -/
def fgDegenerate (a b c d : Nat) : Bool :=
  a + b == 0 || c + d == 0 || a + c == 0 || a + c == a + b + (c + d)

/-- 구현 (행을 밖에서 받는 꼴): x = a … min(r1, c1) 에서 R1[x]·R2[c1 − x] -/
def fgNumW (R1 R2 : Array Nat) (a b c d : Nat) : Nat :=
  if fgDegenerate a b c d then 1 else
  sumTo (fun j => R1.getD (a + j) 0 * R2.getD (a + c - (a + j)) 0) (min (a + b) (a + c) + 1 - a)

/-- 구현 (js `fisherGreater` 의 num): 행은 `pascalRow` -/
def fgNum (a b c d : Nat) : Nat := fgNumW (pascalRow (a + b)).toArray (pascalRow (c + d)).toArray a b c d

def fgDenW (Rn : Array Nat) (a b c d : Nat) : Nat :=
  if fgDegenerate a b c d then 1 else Rn.getD (a + c) 0

/-- 구현: 분모 C(n, c1) (막힌 표는 1) -/
def fgDen (a b c d : Nat) : Nat := fgDenW (pascalRow (a + b + (c + d))).toArray a b c d

/-- 구현 (js `lt05`) -/
def fgSig (a b c d : Nat) : Bool := decide (20 * fgNum a b c d < fgDen a b c d)

/-- 명세 = (Σ_{x ≤ c1} [a ≤ x] hyp x) / C(r1+r2, c1) -/
theorem fgSpecM_eq (r1 r2 c1 a : Nat) :
    fgSpecM r1 r2 c1 a = (sumTo (fun x => if a ≤ x then hyp r1 r2 c1 x else 0) (c1 + 1) : Rat) / (choose (r1 + r2) c1 : Rat) := by
  unfold fgSpecM
  rw [natCast_sumTo, ← sumQ_div]
  apply sumQ_congr; intro x _
  unfold hypP
  rw [← ite_div_eq]

/-- 창 합: Σ_{x<c1+1} [a ≤ x] h x = Σ_{j < min r1 c1 + 1 − a} h(a + j) (x > r1 이면 h x = 0) -/
theorem fg_window (r1 r2 c1 a : Nat) (ha : a ≤ min r1 c1) :
    sumTo (fun x => if a ≤ x then hyp r1 r2 c1 x else 0) (c1 + 1)
      = sumTo (fun j => hyp r1 r2 c1 (a + j)) (min r1 c1 + 1 - a) := by
  have hsplit := sumTo_split (fun x => if a ≤ x then hyp r1 r2 c1 x else 0) a (c1 + 1 - a)
  rw [show a + (c1 + 1 - a) = c1 + 1 by omega] at hsplit
  rw [hsplit, sumTo_eq_zero (fun x hx => by simp; omega), Nat.zero_add]
  have hsplit2 := sumTo_split (fun j => if a ≤ a + j then hyp r1 r2 c1 (a + j) else 0) (min r1 c1 + 1 - a) (c1 + 1 - a - (min r1 c1 + 1 - a))
  rw [show min r1 c1 + 1 - a + (c1 + 1 - a - (min r1 c1 + 1 - a)) = c1 + 1 - a by omega] at hsplit2
  rw [hsplit2]
  have hz : sumTo (fun x => (fun j => if a ≤ a + j then hyp r1 r2 c1 (a + j) else 0) (min r1 c1 + 1 - a + x))
      (c1 + 1 - a - (min r1 c1 + 1 - a)) = 0 := by
    apply sumTo_eq_zero; intro x hx
    simp only [Nat.le_add_right, ↓reduceIte]
    unfold hyp
    rw [choose_eq_zero_of_lt (n := r1) (by omega), Nat.zero_mul]
  rw [hz, Nat.add_zero]
  apply sumTo_congr; intro j _; simp

/-- 막힌 표에서는 명세가 1 (모든 표가 x ≥ a) -/
theorem fgSpec_degenerate {a b c d : Nat} (h : fgDegenerate a b c d = true) : fgSpec a b c d = 1 := by
  unfold fgSpec
  rw [fgSpecM_eq]
  have hall : sumTo (fun x => if a ≤ x then hyp (a + b) (c + d) (a + c) x else 0) (a + c + 1)
      = sumTo (fun x => hyp (a + b) (c + d) (a + c) x) (a + c + 1) := by
    apply sumTo_congr; intro x hx
    by_cases hax : a ≤ x
    · simp [hax]
    · simp only [hax, ↓reduceIte]
      unfold hyp
      unfold fgDegenerate at h
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with ((h | h) | h) | h
      · omega
      · rw [show c + d = 0 by omega]
        rw [choose_eq_zero_of_lt (n := 0) (k := a + c - x) (by omega), Nat.mul_zero]
      · omega
      · rw [choose_eq_zero_of_lt (n := c + d) (k := a + c - x) (by omega), Nat.mul_zero]
  rw [hall]
  have hv := vandermonde (c + d) (a + b) (a + c)
  unfold hyp
  rw [hv]
  have hpos : 0 < choose (a + b + (c + d)) (a + c) := choose_pos (by
    unfold fgDegenerate at h; simp only [Bool.or_eq_true, beq_iff_eq] at h; omega)
  have hp : (0 : Rat) < (choose (a + b + (c + d)) (a + c) : Rat) := Rat.natCast_pos.mpr hpos
  rw [Rat.div_def, Rat.mul_inv_cancel _ (Rat.ne_of_gt hp)]

/-- 구현의 분수 = 명세 (모든 표, 막힌 표 포함) -/
theorem fg_frac (a b c d : Nat) : (fgNum a b c d : Rat) / (fgDen a b c d : Rat) = fgSpec a b c d := by
  by_cases h : fgDegenerate a b c d = true
  · rw [fgSpec_degenerate h]
    simp only [fgNum, fgNumW, fgDen, fgDenW, h, ↓reduceIte]
    grind
  · have hf : fgDegenerate a b c d = false := by simpa using h
    have hnd : ¬ (a + b = 0 ∨ c + d = 0 ∨ a + c = 0 ∨ a + c = a + b + (c + d)) := by
      unfold fgDegenerate at hf; simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hf; omega
    simp only [fgNum, fgNumW, fgDen, fgDenW, hf, Bool.false_eq_true, ↓reduceIte]
    unfold fgSpec
    rw [fgSpecM_eq, fg_window _ _ _ _ (by omega), arr_getD, pascalRow_getD]
    congr 2
    apply sumTo_congr; intro j _
    rw [arr_getD, arr_getD, pascalRow_getD, pascalRow_getD]
    rfl

theorem fgDen_pos (a b c d : Nat) : 0 < fgDen a b c d := by
  unfold fgDen fgDenW
  split
  · decide
  · rw [arr_getD, pascalRow_getD]; exact choose_pos (by omega)

/-- 구현의 판정 ⇔ 명세 p < 1/20 (‘가장 긴 간격 정답률이 더 짧은 간격보다 낮음’ 의 확인) -/
theorem fgSig_iff (a b c d : Nat) : fgSig a b c d = true ↔ fgSpec a b c d < 1 / 20 := by
  rw [← fg_frac, frac_lt_twentieth (fgDen_pos a b c d)]
  simp [fgSig]

end GDT

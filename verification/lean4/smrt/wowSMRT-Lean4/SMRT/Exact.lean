import SMRT.Arith

/-!
# 우연 확인 — 1/3 한쪽 이항 검정 (Claude, 2026-10-22)

앱 `js/track.js` `SmrtTrack.verify()`:
  n = 시행 수, k = 맞힌 수, p = binomTail(k, n, 1/3) = P(X ≥ k), X ~ 이항(n, 1/3) (부동소수 로그 합),
  pAll = +p.toPrecision(4) (유효 숫자 4자리), unverified = (n = 0) ∨ p > 0.05.

명세 `geThirdSpec n k` = Σ_{j ≥ k} C(n,j)(1/3)^j(2/3)^(n−j).
정수 구현: 분자 Σ_{j ≥ k} C(n,j)·2^(n−j), 분모 3^n (와우SRD Exact 의 증명을 이름공간만 바꿔 가져옴).
더한 것:
* `unverifiedB_iff` 앱 판정 p > 0.05 ⇔ 명세 > 1/20
* `twenty_num_ne` 20·분자 ≠ 3^n (홀짝) → p = 1/20 인 경우는 없음 — ‘> 0.05’ 와 ‘≥ 0.05’ 가 같음
* `sig4` 저장되는 pAll (유효 숫자 4자리) 의 정확한 값: p·10^e ∈ [1000, 10000) 에서 가장 가까운 정수 —
  분모가 홀수(3^n)라 반올림이 갈리는 경우(정확히 .5)가 없음 (`sig4_no_tie`)
JS 실행 자체는 증명 범위 밖 — JS ↔ 이 구현은 `CrossCheck.lean` + `cross_check.js` 로 전수 대조.
-/

namespace SMRT

/-! ## 거듭제곱 보조정리 -/

theorem natCast_pow (a : Nat) : ∀ m : Nat, ((a ^ m : Nat) : Rat) = (a : Rat) ^ m
  | 0 => by simp
  | m + 1 => by rw [Nat.pow_succ, Rat.natCast_mul, natCast_pow a m, Rat.pow_succ]

theorem three_pow_pos (m : Nat) : (0 : Rat) < (3 : Rat) ^ m := Rat.pow_pos (by decide)

/-- (1/3)^j · (2/3)^m = 2^m / 3^(j+m) -/
theorem third_pows : ∀ (j m : Nat), ((1 : Rat) / 3) ^ j * ((2 : Rat) / 3) ^ m = (2 : Rat) ^ m / (3 : Rat) ^ (j + m)
  | 0, 0 => by simp only [Rat.pow_zero, Rat.mul_one]; grind
  | 0, m + 1 => by
    have ih := third_pows 0 m
    have h3 := three_pow_pos m
    simp only [Rat.pow_zero, Rat.one_mul, Nat.zero_add] at ih ⊢
    rw [Rat.pow_succ, ih, Rat.pow_succ, Rat.pow_succ]
    have : (3 : Rat) ^ m ≠ 0 := Rat.ne_of_gt h3
    grind
  | j + 1, m => by
    have ih := third_pows j m
    have h3 := three_pow_pos (j + m)
    rw [Rat.pow_succ, show j + 1 + m = (j + m) + 1 by omega, Rat.pow_succ]
    have : (3 : Rat) ^ (j + m) ≠ 0 := Rat.ne_of_gt h3
    have e : ((1 : Rat) / 3) ^ j * ((1 : Rat) / 3) * ((2 : Rat) / 3) ^ m
        = (((1 : Rat) / 3) ^ j * ((2 : Rat) / 3) ^ m) * ((1 : Rat) / 3) := by grind
    rw [e, ih]
    grind

/-! ## 한쪽 이항 P(X ≥ k), X ~ 이항(n, 1/3) -/

/-- 명세 -/
def geThirdSpec (n k : Nat) : Rat :=
  sumQ (fun j => if k ≤ j then (choose n j : Rat) * ((1 : Rat) / 3) ^ j * ((2 : Rat) / 3) ^ (n - j) else 0) (n + 1)

/-- 주어진 행(배열)에서 C(n, j) · 2^(n−j) 를 j = k … n 에서 더함 — 대조 실행 파일은 행을 n 마다 한 번만 만들어 넘김 -/
def geThirdNumWith (row : Array Nat) (n k : Nat) : Nat :=
  sumTo (fun j => if k ≤ j then row.getD j 0 * 2 ^ (n - j) else 0) (n + 1)

/-- 구현: 행 `pascalRow n` (배열) 로 `geThirdNumWith` -/
def geThirdNum (n k : Nat) : Nat := geThirdNumWith (pascalRow n).toArray n k

/-- 대조 실행 파일이 쓰는 꼴 = 증명된 정의 (정의 그대로) -/
theorem geThirdNum_with (n k : Nat) : geThirdNum n k = geThirdNumWith (pascalRow n).toArray n k := rfl

/-- 구현: 분모 3^n -/
def geThirdDen (n : Nat) : Nat := 3 ^ n

theorem geThirdDen_pos (n : Nat) : 0 < geThirdDen n := Nat.pow_pos (by decide)

/-- 구현의 분수 = 명세 (모든 n, k) -/
theorem geThird_frac (n k : Nat) : (geThirdNum n k : Rat) / (geThirdDen n : Rat) = geThirdSpec n k := by
  simp only [geThirdNum, geThirdNumWith, geThirdDen, geThirdSpec]
  rw [natCast_sumTo, ← sumQ_div]
  apply sumQ_congr
  intro j hj
  rw [arr_getD, pascalRow_getD]
  split
  · have hjn : j ≤ n := by omega
    have e := third_pows j (n - j)
    rw [show j + (n - j) = n by omega] at e
    rw [Rat.mul_assoc, e, Rat.natCast_mul, natCast_pow, natCast_pow]
    have h3 := three_pow_pos n
    have : (3 : Rat) ^ n ≠ 0 := Rat.ne_of_gt h3
    simp only [show ((3 : Nat) : Rat) = 3 by rfl, show ((2 : Nat) : Rat) = 2 by rfl]
    grind
  · simp [Rat.div_def]

/-- 이항 정리의 한 꼴: Σ_j C(n,j)·2^(n−j) = 3^n -/
theorem sum_choose_two_pow : ∀ n : Nat, sumTo (fun j => choose n j * 2 ^ (n - j)) (n + 1) = 3 ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := sum_choose_two_pow n
    rw [sumTo_succ']
    have e : (fun j => choose (n + 1) (j + 1) * 2 ^ (n + 1 - (j + 1)))
        = (fun j => choose n j * 2 ^ (n - j) + choose n (j + 1) * 2 ^ (n - j)) := by
      funext j; rw [choose_succ_succ, Nat.add_sub_add_right, Nat.add_mul]
    rw [e, sumTo_add, ih]
    have h2 : sumTo (fun j => choose n (j + 1) * 2 ^ (n - j)) (n + 1) + 2 ^ (n + 1)
        = 2 * sumTo (fun j => choose n j * 2 ^ (n - j)) (n + 1) := by
      have hs := sumTo_succ' (fun j => choose n j * 2 ^ (n + 1 - j)) (n + 1)
      have hz : choose n (n + 1) = 0 := choose_eq_zero_of_lt (by omega)
      have hl : sumTo (fun j => choose n j * 2 ^ (n + 1 - j)) (n + 1 + 1)
          = 2 * sumTo (fun j => choose n j * 2 ^ (n - j)) (n + 1) := by
        rw [sumTo_succ, hz, Nat.zero_mul, Nat.add_zero]
        have : (fun j => choose n j * 2 ^ (n + 1 - j)) = (fun j => 2 * (choose n j * 2 ^ (n - j))) := by
          funext j
          by_cases hj : j ≤ n
          · rw [show n + 1 - j = (n - j) + 1 by omega, Nat.pow_succ]; grind
          · rw [choose_eq_zero_of_lt (by omega)]; simp
        rw [this]
        induction (n + 1) with
        | zero => rfl
        | succ m ihm => simp only [sumTo_succ, ihm, Nat.mul_add]
      have hr : sumTo (fun x => choose n (x + 1) * 2 ^ (n + 1 - (x + 1))) (n + 1)
          = sumTo (fun j => choose n (j + 1) * 2 ^ (n - j)) (n + 1) := by
        apply sumTo_congr; intro x _; rw [Nat.add_sub_add_right]
      rw [hl, hr] at hs
      simp only [choose_zero_right, Nat.one_mul, Nat.sub_zero] at hs
      omega
    rw [ih] at h2
    simp only [choose_zero_right, Nat.one_mul, Nat.sub_zero]
    have h3 : 3 ^ (n + 1) = 3 * 3 ^ n := by rw [Nat.pow_succ]; omega
    rw [h3]
    omega

theorem geThirdNum_eq (n k : Nat) :
    geThirdNum n k = sumTo (fun j => if k ≤ j then choose n j * 2 ^ (n - j) else 0) (n + 1) := by
  simp only [geThirdNum, geThirdNumWith]
  apply sumTo_congr; intro j _; rw [arr_getD, pascalRow_getD]

/-- 0 < p ≤ 1 (k ≤ n 이면 0 보다 큼) -/
theorem geThirdNum_le (n k : Nat) : geThirdNum n k ≤ geThirdDen n := by
  rw [geThirdNum_eq, geThirdDen, ← sum_choose_two_pow n]
  apply sumTo_le; intro j _; split <;> omega

theorem geThirdNum_pos {n k : Nat} (h : k ≤ n) : 0 < geThirdNum n k := by
  rw [geThirdNum_eq]
  have hle := le_sumTo (f := fun j => if k ≤ j then choose n j * 2 ^ (n - j) else 0) (x := n) (n := n + 1) (by omega)
  simp only [h, ↓reduceIte, choose_self, Nat.one_mul, Nat.sub_self, Nat.pow_zero] at hle
  omega

/-- k = 0 이면 p = 1 (js `binomTail` 도 k ≤ 0 이면 1) -/
theorem geThirdNum_zero (n : Nat) : geThirdNum n 0 = geThirdDen n := by
  rw [geThirdNum_eq, geThirdDen, ← sum_choose_two_pow n]
  apply sumTo_congr; intro j _; simp

/-! ## 앱의 판정: unverified = (n = 0) ∨ p > 0.05 -/

/-- 앱 판정 (정수): n = 0 이거나 20·분자 > 분모 -/
def unverifiedB (n k : Nat) : Bool := n == 0 || decide (geThirdDen n < 20 * geThirdNum n k)

theorem three_pow_odd : ∀ n : Nat, 3 ^ n % 2 = 1
  | 0 => rfl
  | n + 1 => by rw [Nat.pow_succ, Nat.mul_mod, three_pow_odd n]

/-- 20·분자 ≠ 3^n — p 는 정확히 1/20 이 될 수 없음 (분모 홀수) -/
theorem twenty_num_ne (n k : Nat) : 20 * geThirdNum n k ≠ geThirdDen n := by
  intro h
  have h1 : (20 * geThirdNum n k) % 2 = 0 := by omega
  have h2 := three_pow_odd n
  unfold geThirdDen at h
  rw [h] at h1
  omega

/-- 1/20 < m/d ⇔ d < 20·m (자연수, d > 0) -/
theorem twentieth_lt_frac {m d : Nat} (hd : 0 < d) :
    (1 : Rat) / 20 < (m : Rat) / (d : Rat) ↔ d < 20 * m := by
  have hd' : (0 : Rat) < (d : Rat) := Rat.natCast_pos.mpr hd
  rw [Rat.lt_div_iff hd']
  have e : (1 : Rat) / 20 * (d : Rat) = (d : Rat) / 20 := by grind
  rw [e, Rat.div_lt_iff (by decide)]
  have e2 : (m : Rat) * 20 = ((20 * m : Nat) : Rat) := by rw [Rat.natCast_mul]; grind
  rw [e2, Rat.natCast_lt_natCast]

/-- 앱 판정 ‘확인 안 됨’ ⇔ 시행이 없거나 명세 p > 1/20 -/
theorem unverifiedB_iff (n k : Nat) : unverifiedB n k = true ↔ n = 0 ∨ (1 : Rat) / 20 < geThirdSpec n k := by
  rw [← geThird_frac, twentieth_lt_frac (geThirdDen_pos n)]
  simp [unverifiedB]

/-- ‘> 0.05’ 와 ‘≥ 0.05’ 는 늘 같은 판정 (경계 값이 나올 수 없음) -/
theorem unverified_ge_iff_gt (n k : Nat) :
    geThirdDen n ≤ 20 * geThirdNum n k ↔ geThirdDen n < 20 * geThirdNum n k := by
  have := twenty_num_ne n k
  omega

/-! ## pAll — 유효 숫자 4자리 (js `+p.toPrecision(4)`)

p = num/den ∈ (0, 1] 이면 p·10^e ∈ [1000, 10000) 인 e 가 하나 있고 (e ≥ 3), 가수 M = p·10^e 에 가장 가까운 정수.
M 이 10000 으로 올라가면 (1000, e − 1). 값 = M · 10^(−e). -/

/-- 가장 작은 e (≥ 0) 로 num·10^e ≥ 1000·den — 연료 fuel 안에서 -/
def findE (num den : Nat) : Nat → Nat → Nat
  | 0, e => e
  | fuel + 1, e => if 1000 * den ≤ num * 10 ^ e then e else findE num den fuel (e + 1)

/-- 가장 가까운 정수 (반은 올림): ⌊(2n + d)/(2d)⌋ -/
def roundDiv (n d : Nat) : Nat := (2 * n + d) / (2 * d)

/-- pAll 의 (가수, 지수): 값 = 가수 · 10^(−지수) -/
def sig4 (num den : Nat) : Nat × Nat :=
  let e := findE num den 2000 0
  let m := roundDiv (num * 10 ^ e) den
  if m = 10000 then (1000, e - 1) else (m, e)

/-- 가장 가까운 정수의 성질: 2·M·d ≤ 2n + d < 2·M·d + 2d (곧 |M − n/d| ≤ 1/2) -/
theorem roundDiv_spec (n d : Nat) (hd : 0 < d) :
    2 * roundDiv n d * d ≤ 2 * n + d ∧ 2 * n + d < 2 * roundDiv n d * d + 2 * d := by
  unfold roundDiv
  have h2d : 0 < 2 * d := by omega
  constructor
  · have := Nat.div_mul_le_self (2 * n + d) (2 * d)
    have e : 2 * ((2 * n + d) / (2 * d)) * d = (2 * n + d) / (2 * d) * (2 * d) := by
      rw [Nat.mul_comm 2, Nat.mul_assoc]
    omega
  · have := Nat.lt_div_mul_add (a := 2 * n + d) h2d
    have e : 2 * ((2 * n + d) / (2 * d)) * d = (2 * n + d) / (2 * d) * (2 * d) := by
      rw [Nat.mul_comm 2, Nat.mul_assoc]
    omega

/-- 분모가 홀수면 반올림이 갈리는 경우가 없음: n/d 는 정확히 ‘정수 + 1/2’ 이 될 수 없음 -/
theorem sig4_no_tie {n d : Nat} (hd : d % 2 = 1) (j : Nat) : 2 * n ≠ (2 * j + 1) * d := by
  intro h
  have h1 : (2 * n) % 2 = 0 := by omega
  have ha : (2 * j + 1) % 2 = 1 := by omega
  have h2 : ((2 * j + 1) * d) % 2 = 1 := by rw [Nat.mul_mod, ha, hd]
  omega

/-- 3^n 은 홀수 — pAll 의 반올림은 늘 한 가지 -/
theorem pAll_no_tie (n k e j : Nat) : 2 * (geThirdNum n k * 10 ^ e) ≠ (2 * j + 1) * geThirdDen n :=
  sig4_no_tie (three_pow_odd n) j

/-- findE 의 결과는 시작값 이상 -/
theorem findE_ge (num den : Nat) : ∀ fuel e, e ≤ findE num den fuel e
  | 0, e => Nat.le_refl e
  | fuel + 1, e => by
    simp only [findE]
    split
    · exact Nat.le_refl e
    · have := findE_ge num den fuel (e + 1); omega

/-- findE 가 연료를 다 쓰기 전에 멈췄으면 조건을 만족 -/
theorem findE_spec (num den : Nat) : ∀ fuel e, 1000 * den ≤ num * 10 ^ (e + fuel) →
    1000 * den ≤ num * 10 ^ (findE num den fuel e)
  | 0, e, h => by simpa [findE] using h
  | fuel + 1, e, h => by
    simp only [findE]
    split
    · assumption
    · exact findE_spec num den fuel (e + 1) (by rw [show e + 1 + fuel = e + (fuel + 1) by omega]; exact h)

/-- findE 가 고른 e 는 가장 작음: 그보다 작은 e' 에서는 조건이 거짓 -/
theorem findE_min (num den : Nat) : ∀ fuel e, (∀ e', e' < e → num * 10 ^ e' < 1000 * den) →
    ∀ e', e' < findE num den fuel e → num * 10 ^ e' < 1000 * den
  | 0, e, h, e', he' => h e' (by simpa [findE] using he')
  | fuel + 1, e, h, e', he' => by
    simp only [findE] at he'
    split at he'
    · exact h e' he'
    · rename_i hc
      apply findE_min num den fuel (e + 1) _ e' he'
      intro e'' he''
      by_cases hlt : e'' < e
      · exact h e'' hlt
      · have : e'' = e := by omega
        subst this; omega

end SMRT

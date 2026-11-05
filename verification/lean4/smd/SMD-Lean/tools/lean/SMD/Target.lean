import SMD.Arith

/-!
# 목표 정답률 1/√2 검정 — ℤ[√2] 정확 계산 (Claude, 2026-10-31 · 와우SRD Target.lean 그대로)

앱 `js/analysis.js` (SMD) 가 판정에 쓰는 검정:
* `pBelowTarget = Stats.le(k, n, 1/√2)` = P(X ≤ k) — ① 위 끝(60 dB)에 막힌 track 의 분석 구간 60 dB 정답률이 70.7 % 보다 낮은가 (< 0.05 → ‘> 60 dB’)
  ② 수렴 점검: 분석 구간 전체 정답률이 70.7 % 보다 낮은가 (< 0.05 → ‘계단이 아직 올라가는 중’)
* `pAboveTarget = Stats.ge(k, n, 1/√2)` = P(X ≥ k) — SMD 판정에는 쓰지 않음 (와우SRD 에서 옮겨 온 그대로 둠, 증명만)
앱은 이 둘을 로그 · exp 부동소수로 셈 (1/√2 가 무리수라 BigInt 로 못 씀). 여기서는 정확하게:
* p = 1/√2 = √2/2, 1 − p = (2 − √2)/2 이므로 2ⁿ·P(X = j) = C(n,j)·(√2)^j·(2 − √2)^(n−j) ∈ ℤ[√2]
  → 정수 쌍 (a, b) = a + b√2 로 정확히 셈 (`termZ2`, `tailLe`, `tailGe`)
* ‘x + y√2 < 0’ 은 √2 의 데데킨트 자름으로 정의 (유리수 q 에 대해 q < √2 ⇔ q ≤ 0 ∨ q² < 2, √2 < q ⇔ 0 < q ∧ 2 < q²) — `isNegQ`
* 정수 규칙 `negZ2` 가 그 정의와 같음 (`negZ2_iff`), 양수를 곱해도 부호가 같음 (`isNegQ_scale`)
* 그래서 `belowSig n k = true ⇔ P(X ≤ k) < 1/20` (`belowSig_iff`), `aboveSig` 도 같음 (`aboveSig_iff`)
JS 의 부동소수 판정이 이 정확 판정과 같은지는 `CrossCheck.lean` 이 n ≤ 200 의 모든 (k, n) 에서 대조 (SMD 유효 시행 상한 200).
-/

namespace SMD

/-! ## ℤ[√2] -/

/-- a + b√2 -/
structure Z2 where
  a : Int
  b : Int
deriving Repr, DecidableEq, Inhabited

namespace Z2
def zero : Z2 := ⟨0, 0⟩
def one : Z2 := ⟨1, 0⟩
def add (x y : Z2) : Z2 := ⟨x.a + y.a, x.b + y.b⟩
/-- (a + b√2)(c + d√2) = (ac + 2bd) + (ad + bc)√2 -/
def mul (x y : Z2) : Z2 := ⟨x.a * y.a + 2 * x.b * y.b, x.a * y.b + x.b * y.a⟩
def smul (c : Int) (x : Z2) : Z2 := ⟨c * x.a, c * x.b⟩
def pow (x : Z2) : Nat → Z2
  | 0 => one
  | n + 1 => mul (pow x n) x
end Z2

/-- √2 -/
def s2 : Z2 := ⟨0, 1⟩
/-- 2 − √2 -/
def t2 : Z2 := ⟨2, -1⟩

/-- 2ⁿ · P(X = j), X ~ 이항(n, 1/√2) = C(n,j)·(√2)^j·(2 − √2)^(n−j) -/
def termZ2 (n j : Nat) : Z2 := Z2.smul (choose n j) (Z2.mul (Z2.pow s2 j) (Z2.pow t2 (n - j)))

/-- ℤ[√2] 합 Σ_{j<m} f j -/
def zsum (f : Nat → Z2) : Nat → Z2
  | 0 => Z2.zero
  | m + 1 => Z2.add (zsum f m) (f m)

/-- 2ⁿ · P(X ≤ k) -/
def tailLe (n k : Nat) : Z2 := zsum (fun j => if j ≤ k then termZ2 n j else Z2.zero) (n + 1)
/-- 2ⁿ · P(X ≥ k) -/
def tailGe (n k : Nat) : Z2 := zsum (fun j => if k ≤ j then termZ2 n j else Z2.zero) (n + 1)

/-! ## 계산은 빠르게 — 행 · 거듭제곱을 한 번만 만들어 읽음 (같다는 증명으로 @[csimp] 바꿈) -/

/-- [x^0, x^1, …, x^N] -/
def powList (x : Z2) (N : Nat) : List Z2 := (List.range (N + 1)).map (Z2.pow x)

theorem powList_getD (x : Z2) (N j : Nat) (h : j ≤ N) : (powList x N).getD j Z2.zero = Z2.pow x j := by
  unfold powList
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega : j < N + 1)]

theorem zsum_congr {f g : Nat → Z2} {n : Nat} (h : ∀ j, j < n → f j = g j) : zsum f n = zsum g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [zsum]; rw [ih (fun j hj => h j (by omega)), h n (by omega)]

/-- 행 · 거듭제곱 배열이 주어졌을 때의 꼬리합 -/
def tailLeWith (row : Array Nat) (sp tp : Array Z2) (n k : Nat) : Z2 :=
  zsum (fun j => if j ≤ k then Z2.smul (row.getD j 0) (Z2.mul (sp.getD j Z2.zero) (tp.getD (n - j) Z2.zero)) else Z2.zero) (n + 1)

def tailGeWith (row : Array Nat) (sp tp : Array Z2) (n k : Nat) : Z2 :=
  zsum (fun j => if k ≤ j then Z2.smul (row.getD j 0) (Z2.mul (sp.getD j Z2.zero) (tp.getD (n - j) Z2.zero)) else Z2.zero) (n + 1)

def rowArr (n : Nat) : Array Nat := (pascalRow n).toArray
def spArr (n : Nat) : Array Z2 := (powList s2 n).toArray
def tpArr (n : Nat) : Array Z2 := (powList t2 n).toArray

theorem term_with (n j : Nat) (hj : j < n + 1) :
    Z2.smul ((rowArr n).getD j 0) (Z2.mul ((spArr n).getD j Z2.zero) ((tpArr n).getD (n - j) Z2.zero)) = termZ2 n j := by
  unfold rowArr spArr tpArr termZ2
  rw [arr_getD, arr_getD, arr_getD, pascalRow_getD, powList_getD _ _ _ (by omega), powList_getD _ _ _ (by omega)]

theorem tailLeWith_eq (n k : Nat) : tailLeWith (rowArr n) (spArr n) (tpArr n) n k = tailLe n k := by
  unfold tailLeWith tailLe
  apply zsum_congr; intro j hj
  split
  · exact term_with n j hj
  · rfl

theorem tailGeWith_eq (n k : Nat) : tailGeWith (rowArr n) (spArr n) (tpArr n) n k = tailGe n k := by
  unfold tailGeWith tailGe
  apply zsum_congr; intro j hj
  split
  · exact term_with n j hj
  · rfl

def tailLeFast (n k : Nat) : Z2 := tailLeWith (rowArr n) (spArr n) (tpArr n) n k
def tailGeFast (n k : Nat) : Z2 := tailGeWith (rowArr n) (spArr n) (tpArr n) n k

@[csimp] theorem tailLe_eq_tailLeFast : @tailLe = @tailLeFast := by
  funext n k; exact (tailLeWith_eq n k).symm

@[csimp] theorem tailGe_eq_tailGeFast : @tailGe = @tailGeFast := by
  funext n k; exact (tailGeWith_eq n k).symm

/-! ## 부호 — √2 의 데데킨트 자름 -/

/-- (a + b√2 < 0) 의 정의 (a, b 유리수):
  b = 0 이면 a < 0 · b > 0 이면 √2 < −a/b · b < 0 이면 −a/b < √2,
  여기서 유리수 q 와 √2 의 비교는 자름: q < √2 ⇔ q ≤ 0 ∨ q² < 2, √2 < q ⇔ 0 < q ∧ 2 < q² -/
def isNegQ (a b : Rat) : Prop :=
  if b = 0 then a < 0
  else if 0 < b then (0 < -a / b ∧ 2 < (-a / b) * (-a / b))
  else (-a / b ≤ 0 ∨ (-a / b) * (-a / b) < 2)

/-- 정수 규칙 (구현): A + B√2 < 0 -/
def negZ2 (A B : Int) : Bool :=
  if B = 0 then decide (A < 0)
  else if 0 < B then decide (A < 0 ∧ 2 * B * B < A * A)
  else decide (A ≤ 0 ∨ A * A < 2 * B * B)

/-- 2ⁿ·P(X ≤ k) = S 일 때 P < 1/20 ⇔ (20·S.a − 2ⁿ) + 20·S.b·√2 < 0 -/
def belowSig (n k : Nat) : Bool :=
  let S := tailLe n k
  negZ2 (20 * S.a - 2 ^ n) (20 * S.b)

def aboveSig (n k : Nat) : Bool :=
  let S := tailGe n k
  negZ2 (20 * S.a - 2 ^ n) (20 * S.b)

/-! ### 정수 규칙 = 자름 정의 -/

theorem intCast_pos_iff {A : Int} : (0 : Rat) < (A : Rat) ↔ 0 < A := by
  have h := Rat.intCast_lt_intCast (a := 0) (b := A)
  simpa using h

theorem intCast_neg_iff {A : Int} : (A : Rat) < 0 ↔ A < 0 := by
  have h := Rat.intCast_lt_intCast (a := A) (b := 0)
  simpa using h

theorem sq_div (x y : Rat) (hy : y ≠ 0) : (x / y) * (x / y) = (x * x) / (y * y) := by grind

theorem negZ2_iff (A B : Int) : negZ2 A B = true ↔ isNegQ (A : Rat) (B : Rat) := by
  unfold negZ2 isNegQ
  by_cases h0 : B = 0
  · subst h0
    simp only [↓reduceIte, decide_eq_true_eq, Rat.intCast_zero]
    exact intCast_neg_iff.symm
  · have hq0 : (B : Rat) ≠ 0 := by
      intro h; apply h0; exact Rat.intCast_inj.mp (by simpa using h)
    have hBB : (0 : Rat) < (B : Rat) * (B : Rat) := by
      rcases Int.lt_or_gt_of_ne h0 with hn | hp
      · have : (B : Rat) < 0 := intCast_neg_iff.mpr hn
        have h2 : (0 : Rat) < -(B : Rat) := by grind
        have := Rat.mul_pos h2 h2
        grind
      · have : (0 : Rat) < (B : Rat) := intCast_pos_iff.mpr hp
        exact Rat.mul_pos this this
    simp only [h0, ↓reduceIte, hq0]
    have hsq : (-(A : Rat) / (B : Rat)) * (-(A : Rat) / (B : Rat)) = ((A : Rat) * (A : Rat)) / ((B : Rat) * (B : Rat)) := by
      rw [sq_div _ _ hq0]; grind
    rw [hsq]
    have k1 : 2 < ((A : Rat) * (A : Rat)) / ((B : Rat) * (B : Rat)) ↔ 2 * B * B < A * A := by
      rw [Rat.lt_div_iff hBB]
      have e1 : (2 : Rat) * ((B : Rat) * (B : Rat)) = ((2 * B * B : Int) : Rat) := by
        rw [Rat.intCast_mul, Rat.intCast_mul]; grind
      have e2 : (A : Rat) * (A : Rat) = ((A * A : Int) : Rat) := by rw [Rat.intCast_mul]
      rw [e1, e2, Rat.intCast_lt_intCast]
    have k2 : ((A : Rat) * (A : Rat)) / ((B : Rat) * (B : Rat)) < 2 ↔ A * A < 2 * B * B := by
      rw [Rat.div_lt_iff hBB]
      have e1 : (2 : Rat) * ((B : Rat) * (B : Rat)) = ((2 * B * B : Int) : Rat) := by
        rw [Rat.intCast_mul, Rat.intCast_mul]; grind
      have e2 : (A : Rat) * (A : Rat) = ((A * A : Int) : Rat) := by rw [Rat.intCast_mul]
      rw [e1, e2, Rat.intCast_lt_intCast]
    by_cases hp : 0 < B
    · have hpq : (0 : Rat) < (B : Rat) := intCast_pos_iff.mpr hp
      simp only [hp, ↓reduceIte, hpq, decide_eq_true_eq]
      have k3 : (0 : Rat) < -(A : Rat) / (B : Rat) ↔ A < 0 := by
        rw [Rat.lt_div_iff hpq, Rat.zero_mul]
        constructor
        · intro h
          have : (A : Rat) < 0 := by grind
          exact intCast_neg_iff.mp this
        · intro h
          have : (A : Rat) < 0 := intCast_neg_iff.mpr h
          grind
      rw [k3, k1]
    · have hn : B < 0 := by omega
      have hpq : ¬ (0 : Rat) < (B : Rat) := fun h => hp (intCast_pos_iff.mp h)
      have hnq : (B : Rat) < 0 := intCast_neg_iff.mpr hn
      simp only [hp, ↓reduceIte, hpq, decide_eq_true_eq]
      have hmb : (0 : Rat) < -(B : Rat) := by grind
      have e3 : -(A : Rat) / (B : Rat) = (A : Rat) / (-(B : Rat)) := by grind
      have k4 : -(A : Rat) / (B : Rat) ≤ 0 ↔ A ≤ 0 := by
        rw [e3, ← Rat.not_lt, ← Int.not_lt, Rat.lt_div_iff hmb, Rat.zero_mul]
        constructor
        · intro h hA; apply h; exact intCast_pos_iff.mpr hA
        · intro h hA; apply h; exact intCast_pos_iff.mp hA
      rw [k4, k2]

/-- 양수 c 를 곱해도 부호가 같음 -/
theorem isNegQ_scale {a b c : Rat} (hc : 0 < c) : isNegQ (c * a) (c * b) ↔ isNegQ a b := by
  have hc0 : c ≠ 0 := Rat.ne_of_gt hc
  unfold isNegQ
  by_cases hb : b = 0
  · subst hb
    simp only [Rat.mul_zero, ↓reduceIte]
    constructor
    · intro h
      by_cases h1 : a < 0
      · exact h1
      · have h1' : 0 ≤ a := Rat.not_lt.mp h1
        exact absurd h (Rat.not_lt.mpr (by
          have := Rat.mul_le_mul_of_nonneg_left h1' (Rat.le_of_lt hc); simpa using this))
    · intro h
      have := Rat.mul_lt_mul_of_pos_left h hc; simpa using this
  · have hcb : c * b ≠ 0 := by
      intro h
      rcases Rat.mul_eq_zero.mp h with h1 | h1
      · exact hc0 h1
      · exact hb h1
    have eq : -(c * a) / (c * b) = -a / b := by grind
    simp only [hb, hcb, ↓reduceIte, eq]
    have hpos : 0 < c * b ↔ 0 < b := by
      constructor
      · intro h
        by_cases h1 : 0 < b
        · exact h1
        · have h1' : b ≤ 0 := Rat.not_lt.mp h1
          exact absurd h (Rat.not_lt.mpr (by
            have := Rat.mul_le_mul_of_nonneg_left h1' (Rat.le_of_lt hc); simpa using this))
      · intro h; exact Rat.mul_pos hc h
    by_cases hp : 0 < b
    · simp [hp, hpos.mpr hp]
    · have : ¬ 0 < c * b := fun h => hp (hpos.mp h)
      simp [hp, this]

/-- P = (A + B√2)/D (D > 0) 일 때 P < 1/20 ⇔ (20A − D) + 20B√2 < 0 -/
theorem lt_twentieth_iff (A B : Int) (D : Nat) (hD : 0 < D) :
    isNegQ ((A : Rat) / (D : Rat) - 1 / 20) ((B : Rat) / (D : Rat)) ↔ negZ2 (20 * A - D) (20 * B) = true := by
  rw [negZ2_iff]
  have hDq : (0 : Rat) < (D : Rat) := Rat.natCast_pos.mpr hD
  have hc : (0 : Rat) < 20 * (D : Rat) := Rat.mul_pos (by decide) hDq
  rw [← isNegQ_scale hc]
  have e1 : 20 * (D : Rat) * ((A : Rat) / (D : Rat) - 1 / 20) = ((20 * A - D : Int) : Rat) := by
    have : (D : Rat) ≠ 0 := Rat.ne_of_gt hDq
    rw [Rat.intCast_sub, Rat.intCast_mul]
    have hD' : ((D : Int) : Rat) = (D : Rat) := Rat.intCast_natCast D
    rw [hD']
    grind
  have e2 : 20 * (D : Rat) * ((B : Rat) / (D : Rat)) = ((20 * B : Int) : Rat) := by
    have : (D : Rat) ≠ 0 := Rat.ne_of_gt hDq
    rw [Rat.intCast_mul]
    grind
  rw [e1, e2]

/-- 정확 판정 (구현) ⇔ P(X ≤ k) < 1/20 (ℚ(√2) 안에서, P = tailLe/2ⁿ) -/
theorem belowSig_iff (n k : Nat) :
    belowSig n k = true ↔
      isNegQ (((tailLe n k).a : Rat) / ((2 ^ n : Nat) : Rat) - 1 / 20) (((tailLe n k).b : Rat) / ((2 ^ n : Nat) : Rat)) := by
  rw [lt_twentieth_iff _ _ _ (Nat.pow_pos (by decide))]
  simp [belowSig]

theorem aboveSig_iff (n k : Nat) :
    aboveSig n k = true ↔
      isNegQ (((tailGe n k).a : Rat) / ((2 ^ n : Nat) : Rat) - 1 / 20) (((tailGe n k).b : Rat) / ((2 ^ n : Nat) : Rat)) := by
  rw [lt_twentieth_iff _ _ _ (Nat.pow_pos (by decide))]
  simp [aboveSig]

end SMD

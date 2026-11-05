import Std

/-!
# 기초 — 와우TMTF 자극 형식 검증 (Claude, 2026-10-24)

core Lean 4.24 만 씀 (Mathlib 없음). 신호 = 표본 번호 → 유리수 (`Nat → Rat`) 와 표본 수 `n`.
* `sumQ f n` = Σ_{i<n} f i (와우SRD tools/lean/SRD/Arith.lean 의 정의를 그대로 가져옴)
* `ms x n`   = (1/n) Σ_{i<n} x i ² — 평균 세기(평균 제곱). 앱의 RMS = √ms 이므로 ‘RMS 가 같다’ ⇔ ‘ms 가 같다’.
-/

namespace TMTF

/-- Σ_{i<n} f i (유리수) -/
def sumQ (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => sumQ f n + f n

@[simp] theorem sumQ_zero (f : Nat → Rat) : sumQ f 0 = 0 := rfl
@[simp] theorem sumQ_succ (f : Nat → Rat) (n : Nat) : sumQ f (n + 1) = sumQ f n + f n := rfl

theorem sumQ_congr {f g : Nat → Rat} {n : Nat} (h : ∀ i, i < n → f i = g i) : sumQ f n = sumQ g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumQ_succ, sumQ_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem sumQ_add (f g : Nat → Rat) (n : Nat) : sumQ (fun i => f i + g i) n = sumQ f n + sumQ g n := by
  induction n with
  | zero => simp only [sumQ_zero]; grind
  | succ n ih => simp only [sumQ_succ, ih]; grind

theorem sumQ_mul_left (c : Rat) (f : Nat → Rat) (n : Nat) : sumQ (fun i => c * f i) n = c * sumQ f n := by
  induction n with
  | zero => simp only [sumQ_zero]; grind
  | succ n ih => simp only [sumQ_succ, ih]; grind

theorem sumQ_const (c : Rat) (n : Nat) : sumQ (fun _ => c) n = c * n := by
  induction n with
  | zero => simp only [sumQ_zero]; grind
  | succ n ih =>
    have e : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by rw [Rat.natCast_add]; rfl
    simp only [sumQ_succ, ih, e]; grind

/-- a ≤ b / c ⇔ a·c ≤ b (c > 0) — core 4.24 에는 lt 꼴만 있어 직접 -/
theorem le_div_of_pos {a b c : Rat} (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  rw [← Rat.not_lt, ← Rat.not_lt, Rat.div_lt_iff hc]

/-- a / c ≤ b ⇔ a ≤ b·c (c > 0) -/
theorem div_le_of_pos {a b c : Rat} (hc : 0 < c) : a / c ≤ b ↔ a ≤ b * c := by
  rw [← Rat.not_lt, ← Rat.not_lt, Rat.lt_div_iff hc]

/-- a < b ≤ c 이면 a < c — core 4.24 Rat 에 없어 직접 -/
theorem lt_le_trans {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  rw [← Rat.not_le]; intro h3; exact (Rat.not_le.mpr h1) (Rat.le_trans h2 h3)

/-- 평균 세기(평균 제곱) — 앱 `rms(x)² ` -/
def ms (x : Nat → Rat) (n : Nat) : Rat := sumQ (fun i => x i * x i) n / n

/-- 신호에 상수 c 를 곱함 (앱: 이득 g 를 곱하는 마지막 단계) -/
def scale (c : Rat) (x : Nat → Rat) : Nat → Rat := fun i => c * x i

/-- 표본마다 곱함 (경사 · 포락선) -/
def pmul (w x : Nat → Rat) : Nat → Rat := fun i => w i * x i

end TMTF

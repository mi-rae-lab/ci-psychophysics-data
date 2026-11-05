import TMTF.Basic

/-!
# De Ruiter 2015 의 대역 — 앱 `js/stim.js` `noise()` 의 'bp' (Claude, 2026-10-24)

논문: ‘a fourth-order band-pass filter with cut-off frequencies of 80 and 8500 Hz’. 앱은 가장자리마다 2차(곧 대역 통과 전체 4차)
버터워스 크기 응답으로 해석: 칸마다 복소 가우스 × g(f), g(f)² = 1 / ((1 + (80/f)⁴)(1 + (f/8500)⁴)) = `G2 f`
(복소 가우스의 기대 세기는 칸마다 같으므로 잡음의 세기 스펙트럼 ∝ G2).

* `G2_pos` · `G2_le_one`   0 < G2 ≤ 1 (어디서도 키우지 않음)
* `G2_at_80` · `G2_at_8500` 차단 주파수에서 1/2 바로 아래 (−3.01 dB): 0.49999 < G2 ≤ 1/2
* `G2_octave_out`          한 옥타브 밖(40 Hz · 17 kHz) G2 ≤ 1/17 (≤ −12.3 dB) — 가장자리마다 12 dB/옥타브
* `G2_lower`               a ≤ f ≤ b (0 < a) 이면 G2 f ≥ 1/((1 + (80/a)⁴)(1 + (b/8500)⁴))
* `G2_pass_200_2000`       200 – 2000 Hz: G2 ≥ 0.97 (−0.13 dB 안) · `G2_pass_2000_5000` 2 – 5 kHz: G2 ≥ 0.89 (−0.51 dB 안)
-/

namespace TMTF

/-- 네제곱 (x²)² -/
def p4 (x : Rat) : Rat := (x * x) * (x * x)

theorem sq_nonneg (x : Rat) : 0 ≤ x * x := by
  cases Rat.nonneg_total x with
  | inl h => exact Rat.mul_nonneg h h
  | inr h => have := Rat.mul_nonneg h h; grind

theorem p4_nonneg (x : Rat) : 0 ≤ p4 x := Rat.mul_nonneg (sq_nonneg x) (sq_nonneg x)

theorem sq_mono {x y : Rat} (hx : 0 ≤ x) (hxy : x ≤ y) : x * x ≤ y * y := by
  have hy : 0 ≤ y := Rat.le_trans hx hxy
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hxy hx) (Rat.mul_le_mul_of_nonneg_right hxy hy)

theorem p4_mono {x y : Rat} (hx : 0 ≤ x) (hxy : x ≤ y) : p4 x ≤ p4 y :=
  sq_mono (sq_nonneg x) (sq_mono hx hxy)

/-- c/b ≤ c/a (0 < a ≤ b, 0 ≤ c) -/
theorem div_anti {a b c : Rat} (ha : 0 < a) (hab : a ≤ b) (hc : 0 ≤ c) : c / b ≤ c / a := by
  have hb : 0 < b := lt_le_trans ha hab
  rw [div_le_of_pos hb]
  -- c ≤ (c/a)·b  ⇐  c·a ≤ c·b
  have h1 : c * a ≤ c * b := Rat.mul_le_mul_of_nonneg_left hab hc
  have h2 : c / a * b = (c * b) / a := by simp only [Rat.div_def]; grind
  rw [h2, le_div_of_pos ha]
  exact h1

/-- x/c ≤ y/c (x ≤ y, 0 < c) -/
theorem div_mono {x y c : Rat} (hc : 0 < c) (hxy : x ≤ y) : x / c ≤ y / c := by
  rw [div_le_of_pos hc, Rat.div_mul_cancel (Rat.ne_of_gt hc)]; exact hxy

/-- 크기 응답의 제곱 -/
def G2 (f : Rat) : Rat := 1 / ((1 + p4 (80 / f)) * (1 + p4 (f / 8500)))

theorem den_ge_one (f : Rat) : 1 ≤ (1 + p4 (80 / f)) * (1 + p4 (f / 8500)) := by
  have a := p4_nonneg (80 / f)
  have b := p4_nonneg (f / 8500)
  have hab := Rat.mul_nonneg a b
  have e : (1 + p4 (80 / f)) * (1 + p4 (f / 8500)) = 1 + p4 (80 / f) + p4 (f / 8500) + p4 (80 / f) * p4 (f / 8500) := by grind
  rw [e]; grind

theorem G2_pos (f : Rat) : 0 < G2 f := by
  unfold G2
  have hd := den_ge_one f
  have hpos : (0 : Rat) < (1 + p4 (80 / f)) * (1 + p4 (f / 8500)) := lt_le_trans (by grind) hd
  rw [Rat.lt_div_iff hpos]; grind

theorem G2_le_one (f : Rat) : G2 f ≤ 1 := by
  unfold G2
  have hd := den_ge_one f
  have hpos : (0 : Rat) < (1 + p4 (80 / f)) * (1 + p4 (f / 8500)) := lt_le_trans (by grind) hd
  rw [div_le_of_pos hpos]; grind

theorem G2_at_80 : 49999 / 100000 < G2 80 ∧ G2 80 ≤ 1 / 2 := by decide +kernel

theorem G2_at_8500 : 49999 / 100000 < G2 8500 ∧ G2 8500 ≤ 1 / 2 := by decide +kernel

theorem G2_octave_out : G2 40 ≤ 1 / 17 ∧ G2 17000 ≤ 1 / 17 := by decide +kernel

/-- a ≤ f ≤ b (0 < a) 이면 G2 f ≥ 1/((1 + (80/a)⁴)(1 + (b/8500)⁴)) -/
theorem G2_lower {a b f : Rat} (ha : 0 < a) (haf : a ≤ f) (hfb : f ≤ b) :
    1 / ((1 + p4 (80 / a)) * (1 + p4 (b / 8500))) ≤ G2 f := by
  have hf : 0 < f := lt_le_trans ha haf
  have h1 : p4 (80 / f) ≤ p4 (80 / a) :=
    p4_mono (Rat.le_of_lt (by rw [Rat.lt_div_iff hf]; grind)) (div_anti ha haf (by grind))
  have h2 : p4 (f / 8500) ≤ p4 (b / 8500) :=
    p4_mono (Rat.le_of_lt (by rw [Rat.lt_div_iff (by grind)]; grind)) (div_mono (by grind) hfb)
  have hA : 1 + p4 (80 / f) ≤ 1 + p4 (80 / a) := (Rat.add_le_add_left).mpr h1
  have hB : 1 + p4 (f / 8500) ≤ 1 + p4 (b / 8500) := (Rat.add_le_add_left).mpr h2
  have hA0 : 0 ≤ 1 + p4 (80 / f) := by have := p4_nonneg (80 / f); grind
  have hB0 : 0 ≤ 1 + p4 (b / 8500) := by have := p4_nonneg (b / 8500); grind
  have hD : (1 + p4 (80 / f)) * (1 + p4 (f / 8500)) ≤ (1 + p4 (80 / a)) * (1 + p4 (b / 8500)) :=
    Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hB hA0) (Rat.mul_le_mul_of_nonneg_right hA hB0)
  have hdf := den_ge_one f
  have hpf : (0 : Rat) < (1 + p4 (80 / f)) * (1 + p4 (f / 8500)) := lt_le_trans (by grind) hdf
  have hpb : (0 : Rat) < (1 + p4 (80 / a)) * (1 + p4 (b / 8500)) := lt_le_trans hpf hD
  unfold G2
  rw [div_le_of_pos hpb, Rat.div_def, Rat.one_mul]
  -- 1 ≤ Df⁻¹ · Db  ⇐  Df ≤ Db
  have hinv : 0 ≤ ((1 + p4 (80 / f)) * (1 + p4 (f / 8500)))⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr hpf)
  calc (1 : Rat) = (1 + p4 (80 / f)) * (1 + p4 (f / 8500)) * ((1 + p4 (80 / f)) * (1 + p4 (f / 8500)))⁻¹ :=
        (Rat.mul_inv_cancel _ (Rat.ne_of_gt hpf)).symm
    _ ≤ (1 + p4 (80 / a)) * (1 + p4 (b / 8500)) * ((1 + p4 (80 / f)) * (1 + p4 (f / 8500)))⁻¹ :=
        Rat.mul_le_mul_of_nonneg_right hD hinv
    _ = ((1 + p4 (80 / f)) * (1 + p4 (f / 8500)))⁻¹ * ((1 + p4 (80 / a)) * (1 + p4 (b / 8500))) := Rat.mul_comm _ _

theorem G2_pass_200_2000 {f : Rat} (h1 : 200 ≤ f) (h2 : f ≤ 2000) : 97 / 100 ≤ G2 f := by
  have := G2_lower (a := 200) (b := 2000) (by grind) h1 h2
  have hb : (97 : Rat) / 100 ≤ 1 / ((1 + p4 (80 / 200)) * (1 + p4 (2000 / 8500))) := by decide +kernel
  exact Rat.le_trans hb this

theorem G2_pass_2000_5000 {f : Rat} (h1 : 2000 ≤ f) (h2 : f ≤ 5000) : 89 / 100 ≤ G2 f := by
  have := G2_lower (a := 2000) (b := 5000) (by grind) h1 h2
  have hb : (89 : Rat) / 100 ≤ 1 / ((1 + p4 (80 / 2000)) * (1 + p4 (5000 / 8500))) := by decide +kernel
  exact Rat.le_trans hb this

end TMTF

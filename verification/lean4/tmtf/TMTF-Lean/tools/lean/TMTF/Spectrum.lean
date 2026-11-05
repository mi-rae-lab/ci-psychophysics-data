import TMTF.Basic

/-!
# 변조가 남기는 것 — 기대 스펙트럼의 옆띠 · 포락선 봉우리 (Claude, 2026-10-24)

SAM x(t) = (1 + m·sin 2πfm t)·n(t), n 은 세기 스펙트럼 S(f) (양쪽, S(−f) = S(f)) 인 정상 잡음.
x 의 시간 평균 세기 스펙트럼 = S(f) + (m²/4)(S(f − fm) + S(f + fm)) (서로 다른 주파수 성분의 교차 항은 기대값 0 — 표준 결과,
여기서는 이 식을 출발점으로 받아들임). 앱은 구간 세기를 맞추므로(전체 세기 (1 + m²/2) 배를 나눔) 변조 구간의 기대 스펙트럼은
`modSpec` = [S(f) + (m²/4)(S(f − fm) + S(f + fm))] / (1 + m²/2), 비변조 구간은 S(f). 아래에서 x = m² (0 ≤ x ≤ 1).

* `wide_flat`      광대역(Won/Park 판: 20 Hz ≤ |f| ≤ fs/2 에서 S = 1): f − fm · f · f + fm 이 모두 띠 안이면 두 구간의 기대 스펙트럼이 같음
* `wide_strip`     아래 옆띠의 원천 f − fm 이 띠 밖(|f − fm| < 20 Hz)이면 비 = (1 + x/4)/(1 + x/2)
* `strip_ge`       그 비 ≥ 5/6 (m ≤ 1), `strip_db`: 10·log10(5/6) ∈ (−0.80, −0.79) dB — m = 1 에서 fm ± 20 Hz 의 40 Hz 띠만 −0.79 dB
* `strip_small_m`  m² ≤ 1/10 (m ≤ 0.316, 깊이 −10 dB 이하)이면 비 ≥ 41/42 (−0.11 dB 안)
  → 인공와우 대역(188 Hz~)에 그 띠가 걸리는 것은 fm > 168 Hz 일 때뿐. 앱 오류가 아니라 띠 가장자리가 있는 모든 SAM 잡음의 성질.
* `crest_*`        같은 RMS 에서 느린 포락선의 봉우리 세기 = 평균의 (1 + m)²/(1 + m²/2) 배: m = 1 이면 8/3 (+4.26 dB), m² = 1/10 이면
                   약 1.65 배(+2.2 dB) — 변조 자체가 포락선이므로 없앨 수 없는 차이. 처리기 압축이 이 봉우리를 줄이면 실효 깊이 · 크기가
                   달라질 수 있음(경로의 한계).
-/

namespace TMTF

/-- 광대역 반송파의 세기 스펙트럼 (양쪽) -/
def Swide (fN f : Rat) : Rat := if (20 ≤ f ∧ f ≤ fN) ∨ (20 ≤ -f ∧ -f ≤ fN) then 1 else 0

/-- 세기를 맞춘 변조 구간의 기대 스펙트럼 (x = m²) -/
def modSpec (S : Rat → Rat) (x fm f : Rat) : Rat := (S f + x / 4 * (S (f - fm) + S (f + fm))) / (1 + x / 2)

theorem half_pos {x : Rat} (hx : 0 ≤ x) : 0 < 1 + x / 2 := by
  have : 0 ≤ x / 2 := by rw [le_div_of_pos (by decide +kernel)]; grind
  grind

theorem wide_flat {fN x fm f : Rat} (hx : 0 ≤ x) (h0 : Swide fN f = 1) (h1 : Swide fN (f - fm) = 1) (h2 : Swide fN (f + fm) = 1) :
    modSpec (Swide fN) x fm f = Swide fN f := by
  unfold modSpec
  rw [h0, h1, h2]
  have hp := half_pos hx
  have e : (1 : Rat) + x / 4 * (1 + 1) = 1 + x / 2 := by simp only [Rat.div_def]; grind
  rw [e, Rat.div_def, Rat.mul_inv_cancel _ (Rat.ne_of_gt hp)]

theorem wide_strip {fN x fm f : Rat} (h0 : Swide fN f = 1) (h1 : Swide fN (f - fm) = 0) (h2 : Swide fN (f + fm) = 1) :
    modSpec (Swide fN) x fm f = (1 + x / 4) / (1 + x / 2) := by
  unfold modSpec
  rw [h0, h1, h2]
  have e : (1 : Rat) + x / 4 * (0 + 1) = 1 + x / 4 := by simp only [Rat.div_def]; grind
  rw [e]

theorem strip_ge {x : Rat} (hx : 0 ≤ x) (h1 : x ≤ 1) : 5 / 6 ≤ (1 + x / 4) / (1 + x / 2) := by
  have hp := half_pos hx
  rw [le_div_of_pos hp, Rat.le_iff_sub_nonneg]
  have e : (1 + x / 4) - 5 / 6 * (1 + x / 2) = (1 - x) * (1 / 6) := by simp only [Rat.div_def]; grind
  rw [e]
  exact Rat.mul_nonneg ((Rat.le_iff_sub_nonneg x 1).mp h1) (by decide +kernel)

theorem strip_small_m {x : Rat} (hx : 0 ≤ x) (h1 : x ≤ 1 / 10) : 41 / 42 ≤ (1 + x / 4) / (1 + x / 2) := by
  have hp := half_pos hx
  rw [le_div_of_pos hp, Rat.le_iff_sub_nonneg]
  have e : (1 + x / 4) - 41 / 42 * (1 + x / 2) = (1 - 10 * x) * (1 / 42) := by simp only [Rat.div_def]; grind
  have h10 : 10 * x ≤ 1 := by
    have := Rat.mul_le_mul_of_nonneg_left h1 (show (0 : Rat) ≤ 10 by decide +kernel)
    have e2 : (10 : Rat) * (1 / 10) = 1 := by decide +kernel
    rw [e2] at this; exact this
  rw [e]
  exact Rat.mul_nonneg ((Rat.le_iff_sub_nonneg (10 * x) 1).mp h10) (by decide +kernel)

set_option exponentiation.threshold 2000 in
/-- 10·log10(5/6) ∈ (−0.80, −0.79) dB ⇔ 10^79 < (6/5)^1000 < 10^80 -/
theorem strip_db : 5 ^ 1000 * 10 ^ 79 < 6 ^ 1000 ∧ 6 ^ 1000 < 5 ^ 1000 * 10 ^ 80 := by decide

/-- 포락선 봉우리 세기 / 평균 세기 = (1 + m)²/(1 + m²/2) -/
def crest (m : Rat) : Rat := (1 + m) * (1 + m) / (1 + m * m / 2)

theorem crest_m1 : crest 1 = 8 / 3 := by decide +kernel

set_option exponentiation.threshold 2000 in
/-- 10·log10(8/3) ∈ (4.25, 4.26) dB ⇔ 10^425 < (8/3)^1000 < 10^426 -/
theorem crest_m1_db : 3 ^ 1000 * 10 ^ 425 < 8 ^ 1000 ∧ 8 ^ 1000 < 3 ^ 1000 * 10 ^ 426 := by decide

/-- m = 0.316 (≈ −10 dB) 이면 봉우리/평균 ∈ (1.64, 1.66) -/
theorem crest_m316 : 164 / 100 < crest (316 / 1000) ∧ crest (316 / 1000) < 166 / 100 := by decide +kernel

end TMTF

import TMTF.Basic

/-!
# 정현 진폭 변조(SAM)의 세기 — Won 2011 · Park 2015 · De Ruiter 2015 의 식 [1 + m·sin(2π·fm·t)] (Claude, 2026-10-24)

* `env_nonneg` · `env_le_two`   0 ≤ m ≤ 1, |sin| ≤ 1 이면 포락선 1 + m·sin 은 0 … 2 — 과변조(포락선이 음수 = 반송파 뒤집힘) 없음.
                                 앱의 깊이는 계단이 −40 … 0 dB 안에서만 고르므로(`TMTF.Track`) m = 10^(D/20) ≤ 1.
* `sam_power`                    Σ s = 0 · Σ s² = n/2 (사인을 주기의 정수배로 고르게 뽑은 값의 성질) 이면 Σ (1 + m s)² = n (1 + m²/2)
                                 — 논문들이 말하는 ‘변조로 늘어난 평균 세기’ 1 + m²/2 의 출처. `sine4_power`: 4 점 사인 (0, 1, 0, −1) 에서 그대로.
* `sine8_moments` · `sine12_moments`
                                 8 점 · 12 점 사인 표(값 = 표준 사인 값 ±√2/2 · ±√3/2 · ±1/2 · ±1 · 0)에서 Σ s = 0 · Σ s² = K/2 를
                                 ℚ(√2) · ℚ(√3) 의 정수 쌍 (a + b√k)/2 으로 정확히 계산 (사인 값 자체는 표준값을 넣은 것 — core 에 삼각함수가 없음).
* 논문 글자대로의 보정 ‘변조 파형을 1 + m²/2 로 나눔’(Won 2011; De Ruiter 2015 ‘long-term average power … 1 + m²/2 로 나눔’):
  `literal_power`   평균 세기가 (1 + m²/2)/(1 + m²/2)² = 1/(1 + m²/2) 배 → `literal_lt_one` m ≠ 0 이면 1 보다 작음(변조 구간이 작아짐),
  `literal_full`    m = 1 에서 2/3 (`db_three_halves`: 10·log₁₀(3/2) ∈ (1.76, 1.77) dB),
  `literal_small`   m ≤ 1/10 (−20 dB 이하)이면 모자람 ≤ 1/200 (약 0.02 dB) — 역치 근처의 얕은 깊이에서는 거의 차이 없고 깊은 깊이에서만 큼.
  `sqrt_gain_exact` 진폭을 1/√(1 + m²/2) 로 나누면(g² = 1/(1 + m²/2)) 기대 세기가 정확히 같음 — 논문이 밝힌 목적(‘평균 세기를 같게’)은 이쪽.
  앱은 기대값 보정에도 기대지 않고 구간마다 실제 세기를 맞춤(`TMTF.Level.ms_equalized`) — 사인 표본이 주기의 정수배가 아니어도
  (예: 0.5 초 × 5 Hz = 2.5 주기, 48 kHz 에서 55 Hz) 정확히 같음.
-/

namespace TMTF

/-- 포락선 1 + m·s (s = 그 순간의 사인 값) -/
def env (m s : Rat) : Rat := 1 + m * s

theorem env_nonneg {m s : Rat} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hs0 : -1 ≤ s) : 0 ≤ env m s := by
  unfold env
  have h1 : m * (-1) ≤ m * s := Rat.mul_le_mul_of_nonneg_left hs0 hm0
  have h2 : m * (-1) = -m := by grind
  rw [h2] at h1
  -- 0 ≤ 1 - m ≤ 1 + m s
  have h3 : (0 : Rat) ≤ 1 + -m := by
    have := (Rat.add_le_add_left (c := -m)).mpr hm1
    grind
  exact Rat.le_trans h3 ((Rat.add_le_add_left (c := 1)).mpr h1)

theorem env_le_two {m s : Rat} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hs1 : s ≤ 1) : env m s ≤ 2 := by
  unfold env
  have h1 : m * s ≤ m * 1 := Rat.mul_le_mul_of_nonneg_left hs1 hm0
  have h2 : m * 1 = m := by grind
  rw [h2] at h1
  have h3 : m * s ≤ 1 := Rat.le_trans h1 hm1
  have := (Rat.add_le_add_left (c := 1)).mpr h3
  grind

/-- 평균 세기: Σ s = 0, Σ s² = n/2 이면 Σ (1 + m s)² = n (1 + m²/2) -/
theorem sam_power {s : Nat → Rat} {n : Nat} (m : Rat) (h1 : sumQ s n = 0) (h2 : sumQ (fun i => s i * s i) n = n / 2) :
    sumQ (fun i => env m (s i) * env m (s i)) n = n * (1 + m * m / 2) := by
  have e : (fun i => env m (s i) * env m (s i)) = (fun i => (1 + (2 * m) * s i) + (m * m) * (s i * s i)) := by
    funext i; unfold env; grind
  rw [e, sumQ_add, sumQ_add, sumQ_const, sumQ_mul_left, sumQ_mul_left, h1, h2]
  grind

/-- 4 점 사인 sin(2π k/4) = 0, 1, 0, −1 -/
def sine4 : Nat → Rat := fun k => if k = 1 then 1 else if k = 3 then -1 else 0

theorem sine4_moments : sumQ sine4 4 = 0 ∧ sumQ (fun i => sine4 i * sine4 i) 4 = (4 : Nat) / 2 := by
  constructor <;> simp [sumQ, sine4] <;> grind

theorem sine4_power (m : Rat) : sumQ (fun i => env m (sine4 i) * env m (sine4 i)) 4 = (4 : Nat) * (1 + m * m / 2) :=
  sam_power m sine4_moments.1 sine4_moments.2

/-- 8 점 사인의 2 배 = a + b√2 : (0,0) (0,1) (2,0) (0,1) (0,0) (0,−1) (−2,0) (0,−1) -/
def sine8x2 : List (Int × Int) := [(0, 0), (0, 1), (2, 0), (0, 1), (0, 0), (0, -1), (-2, 0), (0, -1)]
/-- 12 점 사인의 2 배 = a + b√3 : 0, 1, √3, 2, √3, 1, 0, −1, −√3, −2, −√3, −1 -/
def sine12x2 : List (Int × Int) := [(0, 0), (1, 0), (0, 1), (2, 0), (0, 1), (1, 0), (0, 0), (-1, 0), (0, -1), (-2, 0), (0, -1), (-1, 0)]

/-- (a + b√k)² = a² + k b² + 2ab√k 이고 모든 칸에서 ab = 0 → 제곱의 합은 Σ (a² + k b²), √k 부분 0.
    Σ (2s) = 0 (두 부분 모두) · Σ (2s)² = 4 · K/2 = 2K -/
def momentsOK (t : List (Int × Int)) (k : Int) (K : Nat) : Bool :=
  (t.map (·.1)).sum == 0 && (t.map (·.2)).sum == 0 && t.all (fun p => p.1 * p.2 == 0) &&
    (t.map (fun p => p.1 * p.1 + k * p.2 * p.2)).sum == 2 * (K : Int) && t.length == K

theorem sine8_moments : momentsOK sine8x2 2 8 = true := by decide
theorem sine12_moments : momentsOK sine12x2 3 12 = true := by decide

/-! ## 논문 글자대로의 보정과 제곱근 보정 -/

theorem one_add_half_sq_pos (m : Rat) : 0 < 1 + m * m / 2 := by
  have h : 0 ≤ m * m := by
    cases Rat.nonneg_total m with
    | inl h => exact Rat.mul_nonneg h h
    | inr h => have := Rat.mul_nonneg h h; grind
  have h2 : 0 ≤ m * m / 2 := by
    have := Rat.mul_nonneg h (show (0 : Rat) ≤ 1 / 2 by grind); grind
  have : (0 : Rat) < 1 := by grind
  grind

/-- ‘파형을 1 + m²/2 로 나눔’ → 평균 세기는 (1 + m²/2) · (1/(1 + m²/2))² = 1/(1 + m²/2) 배 -/
theorem literal_power (m : Rat) : (1 + m * m / 2) * (1 / (1 + m * m / 2)) * (1 / (1 + m * m / 2)) = 1 / (1 + m * m / 2) := by
  have hp := one_add_half_sq_pos m
  have hne : 1 + m * m / 2 ≠ 0 := Rat.ne_of_gt hp
  have : (1 + m * m / 2) * (1 / (1 + m * m / 2)) = 1 := by
    rw [Rat.mul_comm]; exact Rat.div_mul_cancel hne
  rw [this, Rat.one_mul]

theorem literal_lt_one {m : Rat} (hm : m ≠ 0) : 1 / (1 + m * m / 2) < 1 := by
  have hp := one_add_half_sq_pos m
  rw [Rat.div_lt_iff hp]
  have hmm : 0 < m * m := by
    cases Rat.nonneg_total m with
    | inl h => exact Rat.mul_pos (Rat.lt_of_le_of_ne h (Ne.symm hm)) (Rat.lt_of_le_of_ne h (Ne.symm hm))
    | inr h =>
      have h' : 0 < -m := Rat.lt_of_le_of_ne h (by intro e; apply hm; grind)
      have := Rat.mul_pos h' h'
      grind
  have : 0 < m * m / 2 := by
    have := Rat.mul_pos hmm (show (0 : Rat) < 1 / 2 by grind); grind
  grind

theorem literal_full : (1 : Rat) / (1 + 1 * 1 / 2) = 2 / 3 := by grind

/-- m ≤ 1/10 이면 모자람 1 − 1/(1 + m²/2) ≤ 1/200 -/
theorem literal_small {m : Rat} (h0 : 0 ≤ m) (h1 : m ≤ 1 / 10) : 1 - 1 / (1 + m * m / 2) ≤ 1 / 200 := by
  have hp := one_add_half_sq_pos m
  have hmm : m * m ≤ 1 / 100 := by
    have a := Rat.mul_le_mul_of_nonneg_left h1 h0          -- m*m ≤ m*(1/10)
    have b := Rat.mul_le_mul_of_nonneg_right h1 (show (0 : Rat) ≤ 1 / 10 by grind)  -- m*(1/10) ≤ (1/10)*(1/10)
    have c : (1 : Rat) / 10 * (1 / 10) = 1 / 100 := by grind
    rw [c] at b
    exact Rat.le_trans a b
  have hx0 : 0 ≤ m * m / 2 := by
    have := Rat.mul_nonneg (Rat.mul_nonneg h0 h0) (show (0 : Rat) ≤ 1 / 2 by grind); grind
  have hx1 : m * m / 2 ≤ 1 / 200 := by
    rw [div_le_of_pos (show (0 : Rat) < 2 by grind)]
    have : (1 : Rat) / 200 * 2 = 1 / 100 := by grind
    rw [this]; exact hmm
  -- 1 − x ≤ 1/(1 + x)  ((1 − x)(1 + x) = 1 − x² ≤ 1)
  have hinv : 1 - m * m / 2 ≤ 1 / (1 + m * m / 2) := by
    rw [le_div_of_pos hp]
    have hsq : 0 ≤ (m * m / 2) * (m * m / 2) := Rat.mul_nonneg hx0 hx0
    grind
  generalize 1 / (1 + m * m / 2) = q at *
  generalize m * m / 2 = x at *
  grind

/-- 제곱근 보정: g² = 1/(1 + m²/2) 이면 g²·(1 + m²/2) = 1 (기대 세기 같음) -/
theorem sqrt_gain_exact {m g : Rat} (hg : g * g = 1 / (1 + m * m / 2)) : g * g * (1 + m * m / 2) = 1 := by
  rw [hg]
  exact Rat.div_mul_cancel (Rat.ne_of_gt (one_add_half_sq_pos m))

set_option exponentiation.threshold 2000 in
/-- 10·log₁₀(3/2) ∈ (1.76, 1.77) dB  ⇔  10^176 < (3/2)^1000 < 10^177 (m = 1 일 때 논문 글자대로면 변조 구간이 약 1.76 dB 작아짐) -/
theorem db_three_halves : 2 ^ 1000 * 10 ^ 176 < 3 ^ 1000 ∧ 3 ^ 1000 < 2 ^ 1000 * 10 ^ 177 := by decide

end TMTF

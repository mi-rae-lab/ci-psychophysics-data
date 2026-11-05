import TMTF.Basic

/-!
# 켜짐 · 꺼짐 경사 — 앱 `js/stim.js` `make` (Claude, 2026-10-24)

앱: `R = min(round(fs·rampMs/1000), floor(N/2))`, i = 0 … R−1 에 대해 `a = (i + 0.5)/R`, `x[i] *= a; x[N−1−i] *= a` (직선).
Won 2011 · Park 2015 ‘10 ms linear ramps’, De Ruiter 2015 ‘30-msec linear ramps’ — 변조 구간 · 비변조 구간에 똑같이.

* `ramp_pos` · `ramp_lt_one`  0 < a_i < 1
* `ramp_mono`                 a_i 는 i 에 대해 늘어남
* `ramp_symm`                 a_i + a_{R−1−i} = 1 (직선 경사가 가운데 1/2 를 두고 대칭)
* `rampLen_half`              2R ≤ N — 앞 경사와 뒤 경사가 겹치지 않음 (`ramp_ends_disjoint`: 뒤 경사 표본 N−1−i ≥ R), 그래서 표본마다 많아야 한 번 곱함
* `rampW_*`                   표본별 이득 w(j): 0 < w ≤ 1, 앞뒤 대칭 w(j) = w(N−1−j)
* w 의 인자는 (R, N, j) 뿐 — 변조 깊이 · 주파수 · 위상 · 씨앗이 들어갈 자리가 없음 → 같은 절차의 모든 구간에 같은 경사, 경사로 구간을 가를 단서 없음
* `rampLen_values`            48 kHz: 10 ms = 480 표본 · 30 ms = 1,440 표본, 44.1 kHz: 441 · 1,323
코사인² 경사(‘직접 정하기’만)는 sin² 이라 유리수 모형 밖.
-/

namespace TMTF

/-- 직선 경사 i 번째 이득 (i + 0.5)/R = (2i + 1)/(2R) -/
def rampGain (R i : Nat) : Rat := ((2 * i + 1 : Nat) : Rat) / ((2 * R : Nat) : Rat)

theorem two_R_pos {R : Nat} (hR : 0 < R) : (0 : Rat) < ((2 * R : Nat) : Rat) := Rat.natCast_pos.mpr (by omega)

theorem ramp_pos {R i : Nat} (hR : 0 < R) : 0 < rampGain R i := by
  unfold rampGain
  rw [Rat.lt_div_iff (two_R_pos hR)]
  have : (0 : Rat) < ((2 * i + 1 : Nat) : Rat) := Rat.natCast_pos.mpr (by omega)
  grind

theorem ramp_lt_one {R i : Nat} (hi : i < R) : rampGain R i < 1 := by
  unfold rampGain
  rw [Rat.div_lt_iff (two_R_pos (by omega)), Rat.one_mul]
  exact Rat.natCast_lt_natCast.mpr (by omega)

theorem ramp_mono {R i j : Nat} (hR : 0 < R) (hij : i < j) : rampGain R i < rampGain R j := by
  unfold rampGain
  have hc := two_R_pos hR
  rw [Rat.div_lt_iff hc, Rat.div_mul_cancel (Rat.ne_of_gt hc)]
  exact Rat.natCast_lt_natCast.mpr (by omega)

theorem ramp_symm {R i : Nat} (hi : i < R) : rampGain R i + rampGain R (R - 1 - i) = 1 := by
  have hc := two_R_pos (R := R) (by omega)
  have hsum : ((2 * i + 1 : Nat) : Rat) + ((2 * (R - 1 - i) + 1 : Nat) : Rat) = ((2 * R : Nat) : Rat) := by
    rw [← Rat.natCast_add]; congr 1; omega
  unfold rampGain
  rw [Rat.div_def, Rat.div_def, ← Rat.add_mul, hsum, Rat.mul_inv_cancel _ (Rat.ne_of_gt hc)]

/-- 앱의 경사 길이: Math.round(fs·rampMs/1000) (= ⌊x + 1/2⌋, x ≥ 0) 와 ⌊N/2⌋ 중 작은 것 -/
def rampLen (fs rampMs N : Nat) : Nat := min ((2 * fs * rampMs + 1000) / 2000) (N / 2)

theorem rampLen_half (fs rampMs N : Nat) : 2 * rampLen fs rampMs N ≤ N := by
  unfold rampLen; omega

theorem ramp_ends_disjoint {R N i : Nat} (h : 2 * R ≤ N) (hi : i < R) : R ≤ N - 1 - i := by omega

/-- 표본 j 에 곱해지는 경사 이득 (2R ≤ N 이면 앞 · 뒤 경사가 겹치지 않음) -/
def rampW (R N j : Nat) : Rat := if j < R then rampGain R j else if N - R ≤ j then rampGain R (N - 1 - j) else 1

theorem rampW_pos {R N j : Nat} (hR : 0 < R) : 0 < rampW R N j := by
  unfold rampW
  split
  · exact ramp_pos hR
  · split
    · exact ramp_pos hR
    · grind

theorem rampW_le_one {R N j : Nat} (h : 2 * R ≤ N) (hj : j < N) : rampW R N j ≤ 1 := by
  unfold rampW
  split
  · exact Rat.le_of_lt (ramp_lt_one (by omega))
  · split
    · exact Rat.le_of_lt (ramp_lt_one (by omega))
    · exact Rat.le_refl

theorem rampW_symm {R N j : Nat} (h : 2 * R ≤ N) (hj : j < N) : rampW R N j = rampW R N (N - 1 - j) := by
  unfold rampW
  by_cases h1 : j < R
  · have h2 : ¬ (N - 1 - j < R) := by omega
    have h3 : N - R ≤ N - 1 - j := by omega
    have h4 : N - 1 - (N - 1 - j) = j := by omega
    simp only [h1, h2, h3, h4, if_true, if_false]
  · by_cases h5 : N - R ≤ j
    · have h6 : N - 1 - j < R := by omega
      simp only [h1, h5, h6, if_true, if_false]
    · have h7 : ¬ (N - 1 - j < R) := by omega
      have h8 : ¬ (N - R ≤ N - 1 - j) := by omega
      simp only [h1, h5, h7, h8, if_false]

theorem rampLen_values :
    rampLen 48000 10 48000 = 480 ∧ rampLen 48000 30 24000 = 1440 ∧ rampLen 44100 10 44100 = 441 ∧ rampLen 44100 30 22050 = 1323 := by
  decide

end TMTF

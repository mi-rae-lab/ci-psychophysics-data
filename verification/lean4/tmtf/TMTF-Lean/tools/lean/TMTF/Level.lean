import TMTF.Basic

/-!
# 세기 맞춤 — 앱 `js/stim.js` `make` 의 마지막 단계 (Claude, 2026-10-24)

앱: 잡음 n → 변조 포락선을 곱함 → 켜짐·꺼짐 경사를 곱함 → **그 결과의** RMS 를 재서 g = 목표 RMS / RMS(그 결과) 를 곱함.
곧 g² = T / ms(그 결과) (T = 목표 RMS²). 여기서 증명:

* `ms_scale`        ms(c·x) = c²·ms(x)
* `ms_equalized`    g² = T / ms(x) 이면 ms(g·x) = T — x 가 무엇이든(변조 깊이 · 주파수 · 위상 · 잡음 씨앗 · 경사 · 길이)
* `equal_power`     그래서 변조 구간과 비변조 구간(또는 세 구간 모두)의 평균 세기는 정확히 같음 → 평균 세기(크기) 단서 없음
* `old_order_power` · `old_order_can_differ`
                    3.0 전 판처럼 경사 **전에** 맞추면 ms(경사 · g·x) = g²·ms(경사 · x) 라 같다는 보장이 없음 — 구체적인 반례
                    (실제 자극에서 잰 차이는 +0.017 · +0.021 dB 였고 3.0 에서 고침, 검증.md)
* `guard_changes_power`
                    봉우리가 0.99 를 넘어 구간 하나만 s 배로 줄이면(앱 `scaled`) 그 구간 세기는 s²·T ≠ T — 그래서 앱은 줄이면 기록하고
                    기록 점검이 잡음. 실제 기록에서 가장 큰 봉우리 −7.2 dBFS 로 한 번도 줄이지 않았음.
RMS 의 제곱근은 유리수가 아니므로 ‘g² = T / ms’ 로 적음 (앱의 g = √T / √ms 와 같은 조건).
-/

namespace TMTF

theorem ms_scale (c : Rat) (x : Nat → Rat) (n : Nat) : ms (scale c x) n = c * c * ms x n := by
  unfold ms scale
  have e : (fun i => c * x i * (c * x i)) = (fun i => (c * c) * (x i * x i)) := by funext i; grind
  rw [e, sumQ_mul_left]
  simp only [Rat.div_def]
  grind

/-- 세기 맞춤: g² = T / ms(x) 이면 결과의 평균 세기는 정확히 T -/
theorem ms_equalized {x : Nat → Rat} {n : Nat} {g T : Rat} (hx : ms x n ≠ 0) (hg : g * g = T / ms x n) :
    ms (scale g x) n = T := by
  rw [ms_scale, hg, Rat.div_mul_cancel hx]

/-- 두 구간을 따로 맞추면(구간마다 자기 g) 평균 세기는 같음 — 길이 · 내용이 달라도 -/
theorem equal_power {a b : Nat → Rat} {na nb : Nat} {ga gb T : Rat} (ha : ms a na ≠ 0) (hb : ms b nb ≠ 0)
    (hga : ga * ga = T / ms a na) (hgb : gb * gb = T / ms b nb) : ms (scale ga a) na = ms (scale gb b) nb := by
  rw [ms_equalized ha hga, ms_equalized hb hgb]

/-- 앱의 지금 순서: 포락선 e · 경사 r 을 곱한 **뒤** 맞춤 → 평균 세기 T (e · r · 잡음 x 가 무엇이든) -/
theorem current_order {e r x : Nat → Rat} {n : Nat} {g T : Rat} (h : ms (pmul r (pmul e x)) n ≠ 0)
    (hg : g * g = T / ms (pmul r (pmul e x)) n) : ms (scale g (pmul r (pmul e x))) n = T :=
  ms_equalized h hg

/-- 3.0 전 순서: 맞춘 뒤 경사 → ms(r · g·x) = g²·ms(r · x) -/
theorem old_order_power (r x : Nat → Rat) (g : Rat) (n : Nat) : ms (pmul r (scale g x)) n = g * g * ms (pmul r x) n := by
  have e : pmul r (scale g x) = scale g (pmul r x) := by funext i; simp only [pmul, scale]; grind
  rw [e, ms_scale]

/-- 반례 (4 표본): 경사 (1/2, 1, 1, 1/2), 목표 T = 4.
    비변조 꼴 xu = (1, 1, 1, 1): ms 1 → g = 2, 변조 꼴 xm = (4, 0, 0, 0): ms 4 → g = 1 (둘 다 경사 전 세기는 T 로 같음).
    경사 뒤 세기: 5/2 와 1 — 같지 않음 -/
def rEx : Nat → Rat := fun i => if i = 0 ∨ i = 3 then 1 / 2 else 1
def xuEx : Nat → Rat := fun _ => 1
def xmEx : Nat → Rat := fun i => if i = 0 then 4 else 0

theorem old_order_can_differ :
    ms xuEx 4 = 1 ∧ ms xmEx 4 = 4 ∧
    ms (scale 2 xuEx) 4 = 4 ∧ ms (scale 1 xmEx) 4 = 4 ∧
    ms (pmul rEx (scale 2 xuEx)) 4 = 5 / 2 ∧ ms (pmul rEx (scale 1 xmEx)) 4 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [ms, sumQ, scale, pmul, rEx, xuEx, xmEx] <;> grind

/-- 봉우리 막기로 구간 하나만 s 배(s² ≠ 1) 하면 그 구간 세기는 T 가 아님 -/
theorem guard_changes_power {x : Nat → Rat} {n : Nat} {s T : Rat} (h : ms x n = T) (hs : s * s ≠ 1) (hT : T ≠ 0) :
    ms (scale s x) n ≠ T := by
  rw [ms_scale, h]
  intro heq
  apply hs
  have h2 : s * s * T * T⁻¹ = T * T⁻¹ := by rw [heq]
  rw [Rat.mul_assoc, Rat.mul_inv_cancel T hT, Rat.mul_one] at h2
  exact h2

end TMTF

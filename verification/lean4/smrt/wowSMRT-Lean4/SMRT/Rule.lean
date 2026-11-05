import SMRT.Rove

/-!
# 로빙 실험 1차 판정 규칙 — `tools/rove_analysis.py` `verdict` 의 모형 (Claude, 2026-11-02 — 와우SMRT 1.2, 검증.md §9 · §10)

C − A (또는 B − A) 의 점추정 est · 표준오차 se · t 분위수 t90 (0.95) · t95 (0.975) 로:
  같음 = 90 % 신뢰구간 ⊂ (−0.7, +0.7) · 낮아짐 = 95 % 상한 < 0 · 높아짐 = 95 % 하한 > 0 (동등 범위 0.7 RPO = Aronoff 2016 재검 SD).

증명한 것:
* `not_low_and_high` 낮아짐과 높아짐은 함께 참일 수 없음 (se · t95 ≥ 0)
* `same_small` 같음이면 |est| < 0.7
* `overlap_exists` 같음과 낮아짐이 함께 참인 경우가 있음 — 고치기 전 규칙(`ruleOld`, 같음을 먼저 봄)은 이런 경우를
  그냥 ‘같음’ 으로 적어 95 % 로 확인된 작은 낮아짐을 감춤. 고친 규칙(`ruleV`)은 ‘같음 · 작게 낮아짐’ 으로 따로 적음.
* `ruleV_old` 두 규칙은 겹치는 두 경우(같음+낮아짐 · 같음+높아짐)만 다르고 나머지는 같음.
-/

namespace SMRT

/-- 고치기 전 (2026-11-02 첫 판): 0 같음 · 3 낮아짐 · 4 높아짐 · 5 판단 보류 — 같음을 먼저 봄 -/
def ruleOld (est se t90 t95 : Rat) : Nat :=
  if -(7 / 10 : Rat) < est - t90 * se ∧ est + t90 * se < 7 / 10 then 0
  else if est + t95 * se < 0 then 3
  else if 0 < est - t95 * se then 4
  else 5

/-- 고친 판정: 0 같음 · 1 같음 · 작게 낮아짐 · 2 같음 · 작게 높아짐 · 3 낮아짐 · 4 높아짐 · 5 판단 보류 -/
def ruleV (est se t90 t95 : Rat) : Nat :=
  if -(7 / 10 : Rat) < est - t90 * se ∧ est + t90 * se < 7 / 10 then
    (if est + t95 * se < 0 then 1 else if 0 < est - t95 * se then 2 else 0)
  else if est + t95 * se < 0 then 3
  else if 0 < est - t95 * se then 4
  else 5

theorem not_low_and_high (est se t95 : Rat) (hse : 0 ≤ se) (ht : 0 ≤ t95) :
    ¬ (est + t95 * se < 0 ∧ 0 < est - t95 * se) := by
  intro ⟨h1, h2⟩
  have hm : 0 ≤ t95 * se := Rat.mul_nonneg ht hse
  grind

theorem same_small (est se t90 : Rat) (hse : 0 ≤ se) (ht : 0 ≤ t90)
    (h : -(7 / 10 : Rat) < est - t90 * se ∧ est + t90 * se < 7 / 10) : -(7 / 10 : Rat) < est ∧ est < 7 / 10 := by
  have hm : 0 ≤ t90 * se := Rat.mul_nonneg ht hse
  grind

/-- 보기: est −0.30 · se 0.05 · t90 1.7 · t95 2.1 → 90 % [−0.385, −0.215] ⊂ ±0.7 이고 95 % 상한 −0.195 < 0 -/
theorem overlap_exists : ruleOld (-3 / 10) (1 / 20) (17 / 10) (21 / 10) = 0 ∧ ruleV (-3 / 10) (1 / 20) (17 / 10) (21 / 10) = 1 := by
  decide +kernel

theorem ruleV_old (est se t90 t95 : Rat) :
    (ruleV est se t90 t95 = ruleOld est se t90 t95) ∨ (ruleOld est se t90 t95 = 0 ∧ (ruleV est se t90 t95 = 1 ∨ ruleV est se t90 t95 = 2)) := by
  unfold ruleV ruleOld
  split
  · split
    · right; exact ⟨rfl, Or.inl rfl⟩
    · split
      · right; exact ⟨rfl, Or.inr rfl⟩
      · left; rfl
  · left; rfl

end SMRT

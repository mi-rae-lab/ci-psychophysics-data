import SMRT.Arith

/-!
# 양측 Fisher 정확 검정 — 기준음 두 개가 같은 파일인 시행의 정답률 (Claude, 2026-10-22)

앱 `js/audit.js` `Audit.fisher(a, b, c, d)` (표 [[a, b], [c, d]] — a: 같은 파일·맞음, b: 같은 파일·틀림,
c: 다른 파일·맞음, d: 다른 파일·틀림), `sameRef` 가 `p < 0.05` 면 ‘차이 있음’:
  여백 r1 = a+b · r2 = c+d · c1 = a+c 를 고정한 초기하 분포에서, 관찰 표(왼쪽 위 = a)보다 확률이 크지 않은 표의 확률 합.
  js 는 로그 감마(Lanczos 근사)로 log P 를 구하고 `log P(x) ≤ log P(a) + 1e-7` 이면 더함 (부동소수).

명세 `f2Spec` = Σ_{x=0}^{c1} [hyp x ≤ hyp a] · hyp x / C(r1+r2, c1),  hyp x = C(r1,x)·C(r2,c1−x) (경우의 수 — 정수로 정확히 비교).
증명: 정수 구현(파스칼 행) 의 분수 = 명세 (`f2_frac`), 0 < p ≤ 1 (`f2Num_pos` · `f2Num_le_den`, Vandermonde),
판정 20·분자 < 분모 ⇔ 명세 < 1/20 (`f2Sig_iff`).
js 의 허용 오차 1e-7 (확률이 관찰 표보다 1e-7 배 이내로 큰 표까지 더함) 이 정확한 판정과 갈리는지는 전수 대조로 봄.
-/

namespace SMRT

/-- 왼쪽 위 칸이 x 인 표의 경우의 수 C(r1,x)·C(r2,c1−x) -/
def hyp (r1 r2 c1 x : Nat) : Nat := choose r1 x * choose r2 (c1 - x)

/-- 그 표의 확률 (초기하) -/
def hypP (r1 r2 c1 x : Nat) : Rat := (hyp r1 r2 c1 x : Rat) / (choose (r1 + r2) c1 : Rat)

/-- 양측 명세 (여백): 관찰 표(왼쪽 위 a)보다 확률이 크지 않은 표의 확률을 x = 0 … c1 에서 더함 -/
def f2SpecM (r1 r2 c1 a : Nat) : Rat :=
  sumQ (fun x => if hyp r1 r2 c1 x ≤ hyp r1 r2 c1 a then hypP r1 r2 c1 x else 0) (c1 + 1)

/-- 양측 명세: 표 (a, b / c, d) -/
def f2Spec (a b c d : Nat) : Rat := f2SpecM (a + b) (c + d) (a + c) a

/-- 주어진 행 R1 = 행(r1) · R2 = 행(r2) 에서 C(r1,x)·C(r2,c1−x) 를 읽어 정수로 비교 · 합산 (대조 실행 파일은 행을 미리 만들어 넘김) -/
def f2NumWith (R1 R2 : Array Nat) (a c : Nat) : Nat :=
  let ha := R1.getD a 0 * R2.getD (a + c - a) 0
  sumTo (fun x => if R1.getD x 0 * R2.getD (a + c - x) 0 ≤ ha then R1.getD x 0 * R2.getD (a + c - x) 0 else 0) (a + c + 1)

/-- 구현: 행 두 개(배열)로 `f2NumWith` -/
def f2Num (a b c d : Nat) : Nat := f2NumWith (pascalRow (a + b)).toArray (pascalRow (c + d)).toArray a c

/-- 구현: 분모 C(n, c1) -/
def f2Den (a b c d : Nat) : Nat := (pascalRow (a + b + (c + d))).toArray.getD (a + c) 0

/-- 대조 실행 파일이 쓰는 꼴 = 증명된 정의 (정의 그대로) -/
theorem f2Num_with (a b c d : Nat) : f2Num a b c d = f2NumWith (pascalRow (a + b)).toArray (pascalRow (c + d)).toArray a c := rfl
theorem f2Den_with (a b c d : Nat) : f2Den a b c d = (pascalRow (a + b + (c + d))).toArray.getD (a + c) 0 := rfl

/-- 구현 (js `p < 0.05`) -/
def f2Sig (a b c d : Nat) : Bool := decide (20 * f2Num a b c d < f2Den a b c d)

theorem f2Num_eq (a b c d : Nat) :
    f2Num a b c d = sumTo (fun x => if hyp (a + b) (c + d) (a + c) x ≤ hyp (a + b) (c + d) (a + c) a
      then hyp (a + b) (c + d) (a + c) x else 0) (a + c + 1) := by
  unfold f2Num f2NumWith hyp
  apply sumTo_congr; intro x _
  simp only [arr_getD, pascalRow_getD]

theorem f2Den_eq (a b c d : Nat) : f2Den a b c d = choose (a + b + (c + d)) (a + c) := by
  unfold f2Den; rw [arr_getD, pascalRow_getD]

/-- 구현의 분수 = 명세 (모든 표) -/
theorem f2_frac (a b c d : Nat) : (f2Num a b c d : Rat) / (f2Den a b c d : Rat) = f2Spec a b c d := by
  rw [f2Num_eq, f2Den_eq]
  unfold f2Spec f2SpecM
  rw [natCast_sumTo, ← sumQ_div]
  apply sumQ_congr; intro x _
  unfold hypP
  rw [← ite_div_eq]

theorem f2Den_pos (a b c d : Nat) : 0 < f2Den a b c d := by
  rw [f2Den_eq]; exact choose_pos (by omega)

/-- 관찰 표 자체가 늘 들어가므로 p > 0 -/
theorem f2Num_pos (a b c d : Nat) : 0 < f2Num a b c d := by
  rw [f2Num_eq]
  have hpos : 0 < hyp (a + b) (c + d) (a + c) a := by
    unfold hyp
    have h1 := choose_pos (n := a + b) (k := a) (by omega)
    have h2 := choose_pos (n := c + d) (k := a + c - a) (by omega)
    exact Nat.mul_pos h1 h2
  have hle := le_sumTo (f := fun x => if hyp (a + b) (c + d) (a + c) x ≤ hyp (a + b) (c + d) (a + c) a
      then hyp (a + b) (c + d) (a + c) x else 0) (x := a) (n := a + c + 1) (by omega)
  simp only [Nat.le_refl, ↓reduceIte] at hle
  omega

/-- p ≤ 1: 모든 표의 경우의 수 합 = C(n, c1) (Vandermonde) -/
theorem f2Num_le_den (a b c d : Nat) : f2Num a b c d ≤ f2Den a b c d := by
  rw [f2Num_eq, f2Den_eq]
  have hv := vandermonde (c + d) (a + b) (a + c)
  rw [← hv]
  apply sumTo_le; intro x _
  unfold hyp
  split <;> omega

/-- 구현의 판정 ⇔ 명세 p < 1/20 (‘기준음 같은 파일인 시행의 정답률이 다름’) -/
theorem f2Sig_iff (a b c d : Nat) : f2Sig a b c d = true ↔ f2Spec a b c d < 1 / 20 := by
  rw [← f2_frac, frac_lt_twentieth (f2Den_pos a b c d)]
  simp [f2Sig]

end SMRT

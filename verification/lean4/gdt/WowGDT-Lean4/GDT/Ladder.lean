import GDT.Arith

/-!
# 간격 사다리 — 앱 `js/protocol.js` `LADDERS` · `gapNOf` · `js/staircase.js` `Stair.valueOf` (Claude, 2026-11-01)

* geo20 (zeng): 반 옥타브 칸 k = i − 12 (k = −12 … 7), 이름값 20·2^(k/2) ms, 표본 수 = round(960·2^(k/2)) (표 그대로)
* xie: 1–10 ms 는 1 ms, 10–40 ms 는 2 ms, 40–100 ms 는 5 ms 칸 (37칸, 정수 ms)
* blank: 2–20 ms 는 2 ms, 20–120 ms 는 5 ms 칸 (30칸, 정수 ms)
계단 · 역치가 쓰는 값 (js `Stair.valueOf`): geo = k (정수), list = 정수 ms. 표본 수 (js `gapNOf`): geo = 표, list = ms × 48 (48 kHz).

증명한 것: 길이 20 · 37 · 30 · `geo20_round` (표의 20칸이 모두 round(960·2^(k/2)) — 정수 부등식으로 정확히, 홀수 k 의 √2 도) ·
`valueOf_strict` (세 사다리 모두 칸이 길수록 값이 큼) · `valueOf_bounds` (칸 0 … M−1 의 값은 [첫 값, 끝 값] 안 —
geo −12 … 7 (0.3125 … 226.27 ms), xie 1 … 100 ms, blank 2 … 120 ms) · `gapN_list` (list 사다리 표본 = ms × 48)
-/

namespace GDT

inductive LKind
  | geo | list
deriving DecidableEq, Repr, Inhabited

structure Ladder where
  kind : LKind
  /-- geo: values_n (표본 수) · list: values_ms -/
  vals : List Nat
  /-- geo 의 kmin (−12) — list 는 쓰지 않음 -/
  kmin : Int
deriving Repr, Inhabited

def geo20 : Ladder :=
  { kind := .geo, vals := [15, 21, 30, 42, 60, 85, 120, 170, 240, 339, 480, 679, 960, 1358, 1920, 2715, 3840, 5431, 7680, 10861], kmin := -12 }

def xieL : Ladder :=
  { kind := .list, vals := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 45, 50, 55, 60, 65, 70, 75, 80, 85, 90, 95, 100], kmin := 0 }

def blankL : Ladder :=
  { kind := .list, vals := [2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70, 75, 80, 85, 90, 95, 100, 105, 110, 115, 120], kmin := 0 }

def Ladder.len (L : Ladder) : Nat := L.vals.length

/-- js `Stair.valueOf(cfg, i)`: geo = i + kmin (반 옥타브 칸 k) · list = values_ms[i] (정수 ms) -/
def valueOf (L : Ladder) (i : Nat) : Int :=
  match L.kind with
  | .geo => (i : Int) + L.kmin
  | .list => ((L.vals.getD i 0 : Nat) : Int)

/-- js `gapNOf(L, i)`: geo = values_n[i] · list = values_ms[i] × 48 -/
def gapN (L : Ladder) (i : Nat) : Nat :=
  match L.kind with
  | .geo => L.vals.getD i 0
  | .list => L.vals.getD i 0 * 48

/-- 사다리 값의 아래 · 위 끝 (칸 0 · 칸 M−1) -/
def vlo (L : Ladder) : Int := valueOf L 0
def vhi (L : Ladder) : Int := valueOf L (L.len - 1)

theorem geo20_len : geo20.len = 20 := rfl
theorem xieL_len : xieL.len = 37 := rfl
theorem blankL_len : blankL.len = 30 := rfl

theorem geo20_ends : vlo geo20 = -12 ∧ vhi geo20 = 7 := by decide
theorem xieL_ends : vlo xieL = 1 ∧ vhi xieL = 100 := by decide
theorem blankL_ends : vlo blankL = 2 ∧ vhi blankL = 120 := by decide

/-! ## geo20 표 = round(960·2^(k/2))

x = 960·2^(k/2) > 0 에서 n = round(x) ⇔ n − ½ ≤ x < n + ½ ⇔ (2n − 1)² ≤ 4x² < (2n + 1)² (n ≥ 1),
4x² = 3,686,400 · 2^k 는 유리수 — k < 0 이면 양변에 2^(−k) 를 곱해 정수로 (홀수 k 의 √2 를 근사 없이 비교). -/

def roundSpec (n : Nat) (k : Int) : Bool :=
  if 0 ≤ k then decide ((2 * n - 1) ^ 2 ≤ 3686400 * 2 ^ k.toNat ∧ 3686400 * 2 ^ k.toNat < (2 * n + 1) ^ 2)
  else decide ((2 * n - 1) ^ 2 * 2 ^ (-k).toNat ≤ 3686400 ∧ 3686400 < (2 * n + 1) ^ 2 * 2 ^ (-k).toNat)

/-- 표의 20칸 모두: 표본 수 = round(960·2^(k/2)), k = i − 12 -/
theorem geo20_round : ∀ i, i < 20 → roundSpec (geo20.vals.getD i 0) ((i : Int) - 12) = true := by decide

/-! ## 칸이 길수록 값이 큼 · 값의 범위 -/

theorem geo20_strict : ∀ i, i < 19 → valueOf geo20 i < valueOf geo20 (i + 1) := by
  intro i _; simp only [valueOf, geo20]; omega

theorem xieL_strict : ∀ i, i < 36 → valueOf xieL i < valueOf xieL (i + 1) := by decide
theorem blankL_strict : ∀ i, i < 29 → valueOf blankL i < valueOf blankL (i + 1) := by decide

/-- geo20 표본 수도 칸이 길수록 큼 -/
theorem geo20_gapN_strict : ∀ i, i < 19 → gapN geo20 i < gapN geo20 (i + 1) := by decide

theorem geo20_bounds : ∀ i, i < 20 → vlo geo20 ≤ valueOf geo20 i ∧ valueOf geo20 i ≤ vhi geo20 := by
  intro i hi; simp only [vlo, vhi, valueOf, geo20, Ladder.len, List.length_cons, List.length_nil]; omega

theorem xieL_bounds : ∀ i, i < 37 → vlo xieL ≤ valueOf xieL i ∧ valueOf xieL i ≤ vhi xieL := by decide
theorem blankL_bounds : ∀ i, i < 30 → vlo blankL ≤ valueOf blankL i ∧ valueOf blankL i ≤ vhi blankL := by decide

/-- list 사다리 표본 수 = 정수 ms × 48 (48 kHz 에서 1 ms = 48 표본) -/
theorem gapN_list (L : Ladder) (h : L.kind = .list) (i : Nat) : (gapN L i : Int) = valueOf L i * 48 := by
  simp [gapN, valueOf, h]

/-- 세 사다리의 공통 성질 (계단 · 역치 증명이 씀) -/
def LadderOK (L : Ladder) : Prop :=
  0 < L.len ∧ ∀ i, i < L.len → vlo L ≤ valueOf L i ∧ valueOf L i ≤ vhi L

theorem geo20_ok : LadderOK geo20 := ⟨by decide, geo20_bounds⟩
theorem xieL_ok : LadderOK xieL := ⟨by decide, xieL_bounds⟩
theorem blankL_ok : LadderOK blankL := ⟨by decide, blankL_bounds⟩

end GDT

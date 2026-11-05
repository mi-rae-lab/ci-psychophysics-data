import SRD.Arith

/-!
# 난수 · 시행 계획 · 임상 순서 — 앱 `js/rng.js` · `js/analysis.js` `TrialPlan` · `ConstPlan` (Claude, 2026-10-21)

* xoshiro128** (Blackman & Vigna): js 와 같은 순서로 UInt32 연산 (곱 · 자리 옮김은 2³² 나머지 — js `Math.imul` · `<<` · `>>>` 와 같음)
* `int(n)` 기각 표집: lim = ⌊2³²/n⌋·n, x ≥ lim 이면 다시 뽑음, x mod n. 여기서는 다시 뽑기에 상한(fuel)을 둠 — 다시 뽑을 확률이
  n/2³² 이하라 상한에 닿을 일은 없고, 닿아도 0 을 돌려 범위 안 (`int_lt`)
* 시행 계획 (js `TrialPlan.draw`, 이 순서 그대로): 다른 소리 자리 int(3)+1 → 무늬 위상 u32 → 구간 1·2·3 씨앗 u32×4 씩 → 흔들기 int(9)−4 ×3
* 임상 순서 (js `ConstPlan.order`): [0×6, 1×6, …, 11×6] 을 뒤에서부터 Fisher–Yates (j = int(i+1))

증명한 것: `int_lt` (0 ≤ int(n) < n) · `plan_targetPos` (자리 1 … 3) · `plan_roves` (흔들기 −4 … +4) ·
`fy_perm` (섞은 순서는 원래 목록의 순열) · `clinOrder_count` (12 밀도 × 6 — 섞은 뒤에도 밀도마다 정확히 6번).
xoshiro 출력 · 계획 · 순서가 js 와 비트까지 같은지는 `CrossCheck.lean` 이 씨앗 여러 개로 대조.
-/

namespace SRD

/-- xoshiro128** 상태 (128비트) -/
structure Xo where
  s0 : UInt32
  s1 : UInt32
  s2 : UInt32
  s3 : UInt32
deriving Repr, Inhabited, DecidableEq

def rotl (x k : UInt32) : UInt32 := (x <<< k) ||| (x >>> (32 - k))

/-- js `u32()` — 출력과 다음 상태 -/
def Xo.next (x : Xo) : UInt32 × Xo :=
  let r := rotl (x.s1 * 5) 7 * 9
  let t := x.s1 <<< 9
  let s2 := x.s2 ^^^ x.s0
  let s3 := x.s3 ^^^ x.s1
  let s1 := x.s1 ^^^ s2
  let s0 := x.s0 ^^^ s3
  let s2 := s2 ^^^ t
  let s3 := rotl s3 11
  (r, ⟨s0, s1, s2, s3⟩)

/-- js `int(n)` (n ≥ 1): lim = ⌊2³²/n⌋·n 이상은 버리고 다시 (다시 뽑기 상한 fuel) -/
def Xo.intF (n : Nat) : Nat → Xo → Nat × Xo
  | 0, x => (0, x)
  | fuel + 1, x =>
    let (u, x') := x.next
    if u.toNat < (4294967296 / n) * n then (u.toNat % n, x') else Xo.intF n fuel x'

def Xo.int (x : Xo) (n : Nat) : Nat × Xo := Xo.intF n 100 x

theorem intF_lt (n : Nat) (hn : 0 < n) : ∀ (fuel : Nat) (x : Xo), (Xo.intF n fuel x).1 < n
  | 0, _ => hn
  | fuel + 1, x => by
    simp only [Xo.intF]
    split
    · exact Nat.mod_lt _ hn
    · exact intF_lt n hn fuel _

/-- 0 ≤ int(n) < n -/
theorem int_lt (x : Xo) {n : Nat} (hn : 0 < n) : (x.int n).1 < n := intF_lt n hn 100 x

/-! ## 16진 (js `hexOf`: 단어마다 소문자 8자리) -/

def hex8 (u : UInt32) : String :=
  let d := Nat.toDigits 16 u.toNat
  String.mk (List.replicate (8 - d.length) '0' ++ d)

def Xo.hex (x : Xo) : String := hex8 x.s0 ++ hex8 x.s1 ++ hex8 x.s2 ++ hex8 x.s3

/-- js `seedHexOf([w0, w1, w2, w3])`: 모두 0 이면 첫 단어를 1 로 -/
def seedHexOf (w0 w1 w2 w3 : UInt32) : String :=
  if w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0 then hex8 1 ++ hex8 0 ++ hex8 0 ++ hex8 0
  else hex8 w0 ++ hex8 w1 ++ hex8 w2 ++ hex8 w3

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def parseHex (s : List Char) : Option Nat :=
  s.foldl (fun acc c => match acc, hexDigit c with | some a, some d => some (a * 16 + d) | _, _ => none) (some 0)

/-- js `Rng.fromHex` (32자 소문자 16진 → 상태; 모두 0 이면 js 는 오류) -/
def Xo.fromHex (h : String) : Option Xo :=
  let cs := h.toList
  if cs.length ≠ 32 then none else
  match parseHex (cs.take 8), parseHex ((cs.drop 8).take 8), parseHex ((cs.drop 16).take 8), parseHex (cs.drop 24) with
  | some a, some b, some c, some d =>
    if a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 then none else some ⟨a.toUInt32, b.toUInt32, c.toUInt32, d.toUInt32⟩
  | _, _, _, _ => none

/-! ## 시행 계획 (js `TrialPlan.draw`) -/

structure Plan where
  targetPos : Nat
  thetaU : UInt32
  seeds : List String
  roves : List Int
deriving Repr, Inhabited

def drawSeed (x : Xo) : String × Xo :=
  let (a, x1) := x.next
  let (b, x2) := x1.next
  let (c, x3) := x2.next
  let (d, x4) := x3.next
  (seedHexOf a b c d, x4)

def drawRove (x : Xo) : Int × Xo :=
  let (r, x') := x.int 9
  ((r : Int) - 4, x')

def drawPlan (x : Xo) : Plan × Xo :=
  let (p, x1) := x.int 3
  let (th, x2) := x1.next
  let (sa, x3) := drawSeed x2
  let (sb, x4) := drawSeed x3
  let (sc, x5) := drawSeed x4
  let (ra, x6) := drawRove x5
  let (rb, x7) := drawRove x6
  let (rc, x8) := drawRove x7
  ({ targetPos := p + 1, thetaU := th, seeds := [sa, sb, sc], roves := [ra, rb, rc] }, x8)

theorem drawRove_bounds (x : Xo) : -4 ≤ (drawRove x).1 ∧ (drawRove x).1 ≤ 4 := by
  have h := int_lt x (n := 9) (by decide)
  simp only [drawRove]
  omega

/-- 다른 소리 자리는 1 … 3 -/
theorem plan_targetPos (x : Xo) : 1 ≤ (drawPlan x).1.targetPos ∧ (drawPlan x).1.targetPos ≤ 3 := by
  have h := int_lt x (n := 3) (by decide)
  simp only [drawPlan]
  omega

/-- 흔들기는 셋 다 −4 … +4 dB -/
theorem plan_roves (x : Xo) : ∀ r ∈ (drawPlan x).1.roves, -4 ≤ r ∧ r ≤ 4 := by
  intro r hr
  simp only [drawPlan, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h <;> subst h <;> exact drawRove_bounds _

/-! ## 임상 순서 (js `ConstPlan.order`) — Fisher–Yates 의 순열 성질 -/

/-- 자리 i 와 j 바꾸기 (js `t = a[i]; a[i] = a[j]; a[j] = t`) -/
def swapL (l : List Nat) (i j : Nat) : List Nat := (l.set i (l.getD j 0)).set j (l.getD i 0)

theorem swapL_length (l : List Nat) (i j : Nat) : (swapL l i j).length = l.length := by
  simp [swapL]

theorem swapL_perm (l : List Nat) {i j : Nat} (hi : i < l.length) (hj : j < l.length) : (swapL l i j).Perm l := by
  have e : swapL l i j = (l.toArray.swap i j (by simpa using hi) (by simpa using hj)).toList := by
    rw [Array.toList_swap]
    simp [swapL, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
  rw [e]
  exact (Array.perm_iff_toList_perm.mp (Array.swap_perm _ _))

/-- 뒤에서부터: 자리 m (≥ 1) 과 j = int(m + 1) 를 바꾸고 m − 1 로 -/
def fy : Xo → List Nat → Nat → List Nat × Xo
  | x, l, 0 => (l, x)
  | x, l, m + 1 =>
    let (j, x') := x.int (m + 2)
    fy x' (swapL l (m + 1) j) m

theorem fy_perm : ∀ (m : Nat) (x : Xo) (l : List Nat), m < l.length → (fy x l m).1.Perm l
  | 0, x, l, _ => by simp [fy]
  | m + 1, x, l, hm => by
    simp only [fy]
    have hj := int_lt x (n := m + 2) (by omega)
    have p1 := swapL_perm l (i := m + 1) (j := (x.int (m + 2)).1) hm (by omega)
    have p2 := fy_perm m (x.int (m + 2)).2 (swapL l (m + 1) (x.int (m + 2)).1) (by rw [swapL_length]; omega)
    exact p2.trans p1

/-- js: k 를 [0×per, 1×per, …] 로 늘어놓음 -/
def baseOrder (dens : List Nat) (per : Nat) : List Nat := (dens.map (fun k => List.replicate per k)).flatten

/-- 임상 순서: 72개를 뒤에서부터 섞음 (run 씨앗 RNG 의 맨 처음 소비) -/
def clinOrder (x : Xo) : List Nat × Xo :=
  let a := baseOrder (List.range 12) 6
  fy x a (a.length - 1)

theorem baseOrder_count (k : Nat) (hk : k < 12) : (baseOrder (List.range 12) 6).count k = 6 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11) with
    h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

theorem baseOrder_length : (baseOrder (List.range 12) 6).length = 72 := by decide

/-- 섞은 임상 순서는 72개이고 밀도 0 … 11 이 정확히 6번씩 -/
theorem clinOrder_count (x : Xo) (k : Nat) (hk : k < 12) : ((clinOrder x).1).count k = 6 ∧ ((clinOrder x).1).length = 72 := by
  have hp := fy_perm ((baseOrder (List.range 12) 6).length - 1) x (baseOrder (List.range 12) 6) (by rw [baseOrder_length]; decide)
  refine ⟨?_, ?_⟩
  · simp only [clinOrder]
    rw [hp.count_eq k]
    exact baseOrder_count k hk
  · simp only [clinOrder]
    rw [hp.length_eq]
    exact baseOrder_length

end SRD

import SMD.Arith

/-!
# 난수 · 시행 계획 · QSMD 순서 — 앱 `js/rng.js` · `js/analysis.js` `TrialPlan` · `ConstPlan` · `qsmdCell` (Claude, 2026-10-31)

* xoshiro128** (Blackman & Vigna): js 와 같은 순서로 UInt32 연산 (곱 · 자리 옮김은 2³² 나머지 — js `Math.imul` · `<<` · `>>>` 와 같음) — 와우SRD Rng.lean 그대로
* `int(n)` 기각 표집: lim = ⌊2³²/n⌋·n, x ≥ lim 이면 다시 뽑음, x mod n (다시 뽑기 상한 fuel — 닿을 일이 없고 닿아도 범위 안)
* Won 시행 계획 (js `TrialPlan.draw`, 이 순서 그대로): 다른 소리 자리 int(3)+1 → 무늬 위상 u32 → 구간 1·2·3 씨앗 u32×4 씩 → 흔들기 int(5)−2 ×3
* QSMD 순서 (js `ConstPlan.order(rng, [0…59], 1)`): 공식 파일 0…59 를 뒤에서부터 Fisher–Yates (j = int(i+1)) — run 씨앗 RNG 의 맨 처음 소비
* QSMD 파일 표 (js/official.js 의 cell · answer — 파이썬이 공식 파일 표에서 만든 값을 그대로 옮김; JS ↔ Lean 대조가 같은지 봄)

증명한 것: `int_lt` · `plan_targetPos` (자리 1 … 3) · `plan_roves` (흔들기 −2 … +2) · `fy_perm` (섞은 순서는 원래 목록의 순열) ·
`qsmdOrder_each_once` (60개가 정확히 한 번씩) · `qsmdOrder_cell_count` (섞은 뒤에도 밀도 × 깊이 칸마다 정확히 6번) ·
`answer_counts` (정답 자리 1 · 2 · 3 = 21 · 17 · 22) · `cellTable_count` (칸마다 파일 6개).
-/

namespace SMD

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

/-! ## Won 시행 계획 (js `TrialPlan.draw`) -/

structure Plan where
  targetPos : Nat
  phiU : UInt32
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
  let (r, x') := x.int 5
  ((r : Int) - 2, x')

def drawPlan (x : Xo) : Plan × Xo :=
  let (p, x1) := x.int 3
  let (ph, x2) := x1.next
  let (sa, x3) := drawSeed x2
  let (sb, x4) := drawSeed x3
  let (sc, x5) := drawSeed x4
  let (ra, x6) := drawRove x5
  let (rb, x7) := drawRove x6
  let (rc, x8) := drawRove x7
  ({ targetPos := p + 1, phiU := ph, seeds := [sa, sb, sc], roves := [ra, rb, rc] }, x8)

theorem drawRove_bounds (x : Xo) : -2 ≤ (drawRove x).1 ∧ (drawRove x).1 ≤ 2 := by
  have h := int_lt x (n := 5) (by decide)
  simp only [drawRove]
  omega

/-- 다른 소리 자리는 1 … 3 -/
theorem plan_targetPos (x : Xo) : 1 ≤ (drawPlan x).1.targetPos ∧ (drawPlan x).1.targetPos ≤ 3 := by
  have h := int_lt x (n := 3) (by decide)
  simp only [drawPlan]
  omega

/-- 흔들기는 셋 다 −2 … +2 dB (Won 2015 ‘±2 dB in 1-dB increments’) -/
theorem plan_roves (x : Xo) : ∀ r ∈ (drawPlan x).1.roves, -2 ≤ r ∧ r ≤ 2 := by
  intro r hr
  simp only [drawPlan, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h <;> subst h <;> exact drawRove_bounds _

/-! ## QSMD 순서 (js `ConstPlan.order`) — Fisher–Yates 의 순열 성질 -/

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

/-- QSMD 순서: 공식 파일 0 … 59 (per 1) 를 뒤에서부터 섞음 -/
def qsmdOrder (x : Xo) : List Nat × Xo := fy x (List.range 60) 59

/-- [0 … 59] 에는 0 … 59 가 한 번씩 -/
theorem range60_count : ∀ k, k < 60 → (List.range 60).count k = 1 := by decide

/-- 섞은 순서에 파일 0 … 59 가 정확히 한 번씩, 길이 60 -/
theorem qsmdOrder_each_once (x : Xo) (k : Nat) (hk : k < 60) : ((qsmdOrder x).1).count k = 1 ∧ ((qsmdOrder x).1).length = 60 := by
  have hp := fy_perm 59 x (List.range 60) (by simp)
  refine ⟨?_, ?_⟩
  · simp only [qsmdOrder]
    rw [hp.count_eq k, range60_count k hk]
  · simp only [qsmdOrder]
    rw [hp.length_eq]
    simp

/-! ## QSMD 파일 표 — js/official.js 의 `cell` · `answer` (파일 번호 순서, 파이썬이 QSMD_Electric_*.txt 에서 만든 값)
  칸 = 밀도 번호 × 5 + 깊이 번호 (밀도 0.5 · 1 c/o, 깊이 10 · 11 · 13 · 14 · 16 dB) -/

def cellTable : List Nat :=
  [0, 3, 9, 6, 8, 5, 4, 7, 1, 2, 7, 0, 4, 6, 2, 3, 9, 1, 8, 5, 8, 3, 6, 1, 7, 5, 0, 4, 2, 9,
   2, 1, 6, 9, 3, 4, 5, 0, 7, 8, 5, 8, 3, 7, 4, 2, 9, 6, 0, 1, 7, 0, 2, 1, 6, 4, 8, 3, 5, 9]

def answerTable : List Nat :=
  [2, 1, 3, 3, 2, 2, 3, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 3, 1, 1, 1, 2, 3, 1, 1, 3, 3,
   1, 2, 3, 3, 1, 3, 2, 3, 3, 2, 2, 1, 3, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3]

def cellOf (i : Nat) : Nat := cellTable.getD i 0
def answerOf (i : Nat) : Nat := answerTable.getD i 0

theorem cellTable_length : cellTable.length = 60 := by decide
theorem answerTable_length : answerTable.length = 60 := by decide

/-- 칸 0 … 9 마다 파일 6개 -/
theorem cellTable_count (c : Nat) (hc : c < 10) : cellTable.count c = 6 := by
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9) with
    h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- 정답 자리 1 · 2 · 3 = 21 · 17 · 22 (모두 1 … 3) -/
theorem answer_counts : answerTable.count 1 = 21 ∧ answerTable.count 2 = 17 ∧ answerTable.count 3 = 22 ∧ answerTable.all (fun a => 1 ≤ a && a ≤ 3) := by
  decide

/-- 섞은 순서의 칸들 (파일 → 칸) -/
def orderCells (o : List Nat) : List Nat := o.map cellOf

/-- (List.range 60).map cellOf = cellTable -/
theorem range_map_cellOf : (List.range 60).map cellOf = cellTable := by decide

/-- 섞은 뒤에도 밀도 × 깊이 칸마다 정확히 6번 -/
theorem qsmdOrder_cell_count (x : Xo) (c : Nat) (hc : c < 10) : (orderCells (qsmdOrder x).1).count c = 6 := by
  have hp := fy_perm 59 x (List.range 60) (by simp)
  have hm : (orderCells (qsmdOrder x).1).Perm ((List.range 60).map cellOf) := by
    simp only [orderCells, qsmdOrder]
    exact hp.map cellOf
  rw [hm.count_eq c, range_map_cellOf]
  exact cellTable_count c hc

end SMD

import GDT.Arith

/-!
# 난수 · 시행 계획 — 앱 `js/rng.js` · `js/analysis.js` `TrialPlan.draw` · `seedHexOf` (Claude, 2026-11-01)

* xoshiro128** (Blackman & Vigna): js 와 같은 순서로 UInt32 연산 (곱 · 자리 옮김은 2³² 나머지 — js `Math.imul` · `<<` · `>>>` 와 같음) — 와우SMD Rng.lean 그대로
* `int(n)` 기각 표집: lim = ⌊2³²/n⌋·n, x ≥ lim 이면 다시 뽑음, x mod n (다시 뽑기 상한 fuel — 닿을 일이 없고 닿아도 범위 안)
* 시행 계획 (js `TrialPlan.draw(rng, nAfc, cond)`, 이 순서 그대로): 간격 있는 자리 int(q)+1 → 구간 1 … q 씨앗 u32×4 씩 →
  (표지음 길이를 흔드는 조건만) 구간마다 [lo + int(hi − lo + 1), lo + int(hi − lo + 1)] (앞 · 뒤 표지음 ms)
* 소리 조건 (js/protocol.js `CONDS`): n500 · n800 은 가운데 간격(흔들기 없음), t2k · t2k1k 는 앞뒤 표지음 250–350 ms

증명한 것: `int_lt` (0 ≤ int(n) < n) · `plan_targetPos` (자리 1 … q) · `plan_seeds_length` (씨앗 q 개) ·
`plan_roves` (흔들기 q 쌍, 모두 lo … hi) · `cond_roves` (t2k · t2k1k 는 모두 250 … 350 ms, n500 · n800 은 흔들기 없음)
-/

namespace GDT

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
  seeds : List String
  roves : Option (List (Nat × Nat))
deriving Repr, Inhabited

def drawSeed (x : Xo) : String × Xo :=
  let (a, x1) := x.next
  let (b, x2) := x1.next
  let (c, x3) := x2.next
  let (d, x4) := x3.next
  (seedHexOf a b c d, x4)

/-- 구간 m 개의 씨앗 (js `Array.from({ length: nAfc }, () => seedHexOf([u32 ×4]))`) -/
def drawSeeds : Nat → Xo → List String × Xo
  | 0, x => ([], x)
  | m + 1, x =>
    let r1 := drawSeed x
    let r2 := drawSeeds m r1.2
    (r1.1 :: r2.1, r2.2)

/-- 구간 m 개의 [앞, 뒤] 표지음 ms (js `[lo + rng.int(span), lo + rng.int(span)]` — 앞을 먼저 뽑음) -/
def drawRoves (lo span : Nat) : Nat → Xo → List (Nat × Nat) × Xo
  | 0, x => ([], x)
  | m + 1, x =>
    let a := x.int span
    let b := a.2.int span
    let r := drawRoves lo span m b.2
    ((lo + a.1, lo + b.1) :: r.1, r.2)

/-- js `TrialPlan.draw(rng, q, cond)` — rove = 그 조건의 rove_ms (흔들지 않는 조건은 none) -/
def drawPlan (x : Xo) (q : Nat) (rove : Option (Nat × Nat)) : Plan × Xo :=
  let p := x.int q
  let s := drawSeeds q p.2
  match rove with
  | none => ({ targetPos := p.1 + 1, seeds := s.1, roves := none }, s.2)
  | some (lo, hi) =>
    let r := drawRoves lo (hi - lo + 1) q s.2
    ({ targetPos := p.1 + 1, seeds := s.1, roves := some r.1 }, r.2)

/-- 간격 있는 자리는 1 … q -/
theorem plan_targetPos (x : Xo) (q : Nat) (hq : 0 < q) (rv : Option (Nat × Nat)) :
    1 ≤ (drawPlan x q rv).1.targetPos ∧ (drawPlan x q rv).1.targetPos ≤ q := by
  have h := int_lt x hq
  cases rv with
  | none => simp only [drawPlan]; omega
  | some p => obtain ⟨lo, hi⟩ := p; simp only [drawPlan]; omega

theorem drawSeeds_length : ∀ (m : Nat) (x : Xo), (drawSeeds m x).1.length = m
  | 0, _ => rfl
  | m + 1, x => by simp only [drawSeeds, List.length_cons]; rw [drawSeeds_length m]

/-- 씨앗은 구간마다 하나 (q 개) -/
theorem plan_seeds_length (x : Xo) (q : Nat) (rv : Option (Nat × Nat)) : (drawPlan x q rv).1.seeds.length = q := by
  cases rv with
  | none => simp only [drawPlan]; exact drawSeeds_length q _
  | some p => obtain ⟨lo, hi⟩ := p; simp only [drawPlan]; exact drawSeeds_length q _

theorem drawRoves_props (lo span : Nat) (hs : 0 < span) : ∀ (m : Nat) (x : Xo),
    (drawRoves lo span m x).1.length = m ∧
    ∀ r ∈ (drawRoves lo span m x).1, lo ≤ r.1 ∧ r.1 < lo + span ∧ lo ≤ r.2 ∧ r.2 < lo + span
  | 0, _ => by simp [drawRoves]
  | m + 1, x => by
    have ha := int_lt x hs
    have hb := int_lt (x.int span).2 hs
    obtain ⟨ih1, ih2⟩ := drawRoves_props lo span hs m ((x.int span).2.int span).2
    simp only [drawRoves, List.length_cons, List.mem_cons]
    refine ⟨by rw [ih1], ?_⟩
    intro r hr
    rcases hr with hr | hr
    · subst hr; simp only; omega
    · exact ih2 r hr

/-- 흔드는 조건: 쌍이 q 개, 앞 · 뒤 표지음 ms 가 모두 lo … hi -/
theorem plan_roves (x : Xo) (q lo hi : Nat) (hlh : lo ≤ hi) (rs : List (Nat × Nat))
    (h : (drawPlan x q (some (lo, hi))).1.roves = some rs) :
    rs.length = q ∧ ∀ r ∈ rs, lo ≤ r.1 ∧ r.1 ≤ hi ∧ lo ≤ r.2 ∧ r.2 ≤ hi := by
  simp only [drawPlan, Option.some.injEq] at h
  subst h
  obtain ⟨h1, h2⟩ := drawRoves_props lo (hi - lo + 1) (by omega) q (drawSeeds q (x.int q).2).2
  refine ⟨h1, ?_⟩
  intro r hr
  have := h2 r hr
  omega

/-- 흔들지 않는 조건은 roves = null -/
theorem plan_no_roves (x : Xo) (q : Nat) : (drawPlan x q none).1.roves = none := by
  simp [drawPlan]

/-! ## 소리 조건 (js/protocol.js `CONDS`) — 흔들기 범위 -/

/-- 조건 id → rove_ms (layout 'rove' 만) -/
def condRove : String → Option (Nat × Nat)
  | "t2k" => some (250, 350)
  | "t2k1k" => some (250, 350)
  | _ => none

/-- t2k · t2k1k: 앞 · 뒤 표지음은 모두 250 … 350 ms (Blankenship 2022 ‘250 to 350 ms’) · n500 · n800 은 흔들기 없음 -/
theorem cond_roves (x : Xo) (q : Nat) (c : String) (hc : c = "t2k" ∨ c = "t2k1k") (rs : List (Nat × Nat))
    (h : (drawPlan x q (condRove c)).1.roves = some rs) :
    rs.length = q ∧ ∀ r ∈ rs, 250 ≤ r.1 ∧ r.1 ≤ 350 ∧ 250 ≤ r.2 ∧ r.2 ≤ 350 := by
  rcases hc with hc | hc <;> subst hc <;> exact plan_roves x q 250 350 (by decide) rs h

theorem cond_center (x : Xo) (q : Nat) : (drawPlan x q (condRove "n500")).1.roves = none ∧ (drawPlan x q (condRove "n800")).1.roves = none :=
  ⟨plan_no_roves x q, plan_no_roves x q⟩

end GDT

import SMRT.Fast
import SMRT.Round

/-!
# 크기 구별 확인 — 앱 `js/loud.js` `LoudTrack` 의 모형과 성질 (Claude, 2026-11-02 — 와우SMRT 1.2)

로빙 실험의 조작 확인 (검증.md §9-1): 2구간 ‘더 큰 소리’, 2-down 1-up, ΔL 정수 dB.
`js/loud.js` `LOUD`: 시작 8 · 큰 칸 2 · 작은 칸 1 · 반전 2번부터 작은 칸 · 바닥 1 · 천장 15 · 반전 10번에서 끝 · 마지막 6 반전 평균 · 시행 상한 120.

js 와 같은 순서 · 같은 값으로 상태를 바꿈 (`lrespond` = js `respond(correct)`, `lmove` = js `move(d)`):
  끝났으면 아무것도 안 함 → 바닥(db ≤ 1)이면 floorHits + 1 → 천장(db ≥ 15)이면 ceilHits + 1 → 시행 기록 →
  맞힘: cRun + 1, cRun ≥ 2 이면 cRun 0 · move(−1) / 틀림: cRun 0 · move(+1) → 반전 ≥ 10 이면 끝 → 시행 ≥ 120 이면 끝 · 미완.
  move(d): 앞 방향이 있고 d 가 다르면 반전(값 = 이동 전 db, 시행 번호 = 시행 수 − 1) → 방향 = d →
           칸 = (반전 수 < 2 ? 2 : 1) — 이번 이동에서 생긴 반전까지 셈 → db = min(15, max(1, db + d·칸)).
  js 의 `db − 칸` 은 음수가 될 수 있으나 max(1, ·) 를 거치면 자연수 뺄셈(0 에서 멈춤)과 같은 값.

증명한 것 (`loudCfg`, 처음부터 돌린 모든 응답 순서):
* `lgood_run` db 는 늘 1 … 15, 반전 값도 모두 1 … 15, 진행 중이면 시행 < 120 · 반전 < 10,
  맞힘 · 바닥 시행 · 천장 시행 ≤ 시행 수, 반전 수 = 반전 시행 번호 수
* `lrun_ends` 응답이 120 개 이상이면 반드시 끝남
* `lthr_bounds` 역치 = 마지막 6 반전 합 S / 6 dB, 6 ≤ S ≤ 90 (1 … 15 dB)
* `lthr4_no_tie` 저장 값 thrDb = S/6 의 소수 넷째 자리 반올림은 늘 한 가지
* 우연 확인 (2구간, js `binomTail(k, n, 1/2)`): 분자 Σ_{j≥k} C(n,j), 분모 2ⁿ — `geHalfNum_le` (p ≤ 1) · `geHalfNum_pos` ·
  `twenty_half_ne` (p = 1/20 정확히는 없음 → ‘> 0.05’ 와 ‘≥ 0.05’ 가 같음). pAll 유효 숫자 4자리는 분모가 짝수라
  반올림 동점(정확히 .5)이 있을 수 있음 → 대조에서 `T:` 로 따로 셈.
* 해석 구역 · 쌍 비율의 정확한 값 (`lzone` · `pairCnt`): 평균 m = ΣS / (6 · 측정 수) 를 정수 비교로.
-/

namespace SMRT

structure LCfg where
  startDb : Nat
  stepBig : Nat
  stepSmall : Nat
  switchRev : Nat
  minDb : Nat
  maxDb : Nat
  nDown : Nat
  totalRev : Nat
  avgLast : Nat
  maxTrials : Nat
deriving Repr

/-- js `LOUD` -/
def loudCfg : LCfg :=
  { startDb := 8, stepBig := 2, stepSmall := 1, switchRev := 2, minDb := 1, maxDb := 15, nDown := 2,
    totalRev := 10, avgLast := 6, maxTrials := 120 }

structure LSt where
  db : Nat
  cRun : Nat
  dir : Int
  revs : List Nat
  revAt : List Nat
  nTrials : Nat
  nCorrect : Nat
  floorHits : Nat
  ceilHits : Nat
  done : Bool
  incomplete : Bool
deriving Repr, Inhabited

def linit (c : LCfg) : LSt :=
  { db := c.startDb, cRun := 0, dir := 0, revs := [], revAt := [], nTrials := 0, nCorrect := 0,
    floorHits := 0, ceilHits := 0, done := false, incomplete := false }

/-- js `step()` — r = 이번 이동에서 생긴 반전까지 센 반전 수 -/
def lstep (c : LCfg) (r : Nat) : Nat := if r < c.switchRev then c.stepBig else c.stepSmall

/-- js `Math.min(maxDb, Math.max(minDb, x))` -/
def lclamp (c : LCfg) (x : Nat) : Nat := min c.maxDb (max c.minDb x)

/-- 반전인가: 앞 방향이 있고 (≠ 0) 이번 방향이 다름 -/
def lisRev (s : LSt) (d : Int) : Bool := s.dir != 0 && d != s.dir

/-- js `move(d)` — 시행을 기록한 뒤 부름 (revAt = 시행 수 − 1) -/
def lmove (c : LCfg) (s : LSt) (d : Int) : LSt :=
  let s1 : LSt := if lisRev s d then { s with revs := s.revs ++ [s.db], revAt := s.revAt ++ [s.nTrials - 1] } else s
  let st := lstep c s1.revs.length
  { s1 with dir := d, db := if 0 < d then lclamp c (s.db + st) else lclamp c (s.db - st) }

/-- 시행 기록까지 (js: 바닥 · 천장 시행, trials.push) -/
def lrecord (c : LCfg) (s : LSt) (b : Bool) : LSt :=
  { s with floorHits := if s.db ≤ c.minDb then s.floorHits + 1 else s.floorHits,
           ceilHits := if c.maxDb ≤ s.db then s.ceilHits + 1 else s.ceilHits,
           nTrials := s.nTrials + 1,
           nCorrect := if b then s.nCorrect + 1 else s.nCorrect }

/-- 정오에 따른 연속 수 · 이동 (js respond 의 가운데) -/
def lreact (c : LCfg) (s : LSt) (b : Bool) : LSt :=
  if b then (if c.nDown ≤ s.cRun + 1 then lmove c { s with cRun := 0 } (-1) else { s with cRun := s.cRun + 1 })
  else lmove c { s with cRun := 0 } 1

/-- 끝 판정 (js: 반전 수 먼저, 그다음 시행 상한) -/
def lfinish (c : LCfg) (s : LSt) : LSt :=
  if c.totalRev ≤ s.revs.length then { s with done := true }
  else if c.maxTrials ≤ s.nTrials then { s with done := true, incomplete := true }
  else s

/-- js `respond(correct)` -/
def lrespond (c : LCfg) (s : LSt) (b : Bool) : LSt :=
  if s.done then s else lfinish c (lreact c (lrecord c s b) b)

/-- 응답 순서대로 — 끝난 뒤의 응답은 받지 않음. 시행마다 제시한 ΔL 을 함께 돌려줌 -/
def lrun (c : LCfg) : LSt → List Bool → LSt × List Nat
  | s, [] => (s, [])
  | s, b :: bs =>
    if s.done then (s, [])
    else
      let r := lrun c (lrespond c s b) bs
      (r.1, s.db :: r.2)

/-! ## 결과 (js `result()`) -/

/-- 역치에 쓰는 반전 = 마지막 avgLast 개 (js `reversals.slice(-avgLast)`) -/
def lused (c : LCfg) (s : LSt) : List Nat := s.revs.drop (s.revs.length - c.avgLast)

/-- 역치 (합, 개수): 반전이 모자라면 없음 — thrDb = 합 / 개수 dB -/
def lthrSum (c : LCfg) (s : LSt) : Option (Nat × Nat) :=
  if (lused c s).length < c.avgLast then none else some ((lused c s).sum, (lused c s).length)

/-- 결과의 incomplete (js `this.incomplete || thrDb === null`) -/
def lresIncomplete (c : LCfg) (s : LSt) : Bool := s.incomplete || decide ((lused c s).length < c.avgLast)

/-- 저장 값 thrDb 의 4자리 정수 (thrDb·10⁴): 합·10⁴/개수 에 가장 가까운 정수 -/
def lthr4 (S cnt : Nat) : Nat := roundDiv (S * 10000) cnt

/-! ## 2구간 우연 확인 (js `binomTail(k, n, 1/2)`) -/

/-- 분자 Σ_{j ≥ k} C(n, j) (주어진 파스칼 행으로) — 분모 2ⁿ -/
def geHalfNumWith (row : Array Nat) (n k : Nat) : Nat := sumTo (fun j => if k ≤ j then row.getD j 0 else 0) (n + 1)

def geHalfNum (n k : Nat) : Nat := geHalfNumWith (pascalRow n).toArray n k

def geHalfDen (n : Nat) : Nat := 2 ^ n

/-- 저장 pAll 의 넷째 유효 숫자 반올림이 정확히 ‘.5’ 에 걸리는가 (분모 2ⁿ 이라 있을 수 있음) -/
def sig4Tie (num den : Nat) : Bool := isTie (num * 10 ^ findE num den 2000 0) den

theorem sum_choose : ∀ n : Nat, sumTo (fun j => choose n j) (n + 1) = 2 ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := sum_choose n
    rw [sumTo_succ']
    have e : (fun x => choose (n + 1) (x + 1)) = (fun x => choose n x + choose n (x + 1)) := by
      funext x; exact choose_succ_succ n x
    rw [e, sumTo_add, ih]
    have L : sumTo (fun j => choose n j) (n + 1 + 1) = 2 ^ n := by
      rw [sumTo_succ, ih]
      simp only [choose_eq_zero_of_lt (by omega : n < n + 1), Nat.add_zero]
    have a := sumTo_succ' (fun j => choose n j) (n + 1)
    rw [L] at a
    simp only [choose_zero_right] at a
    rw [choose_zero_right, Nat.pow_succ]
    omega

theorem geHalfNum_eq (n k : Nat) : geHalfNum n k = sumTo (fun j => if k ≤ j then choose n j else 0) (n + 1) := by
  simp only [geHalfNum, geHalfNumWith]
  apply sumTo_congr; intro j _; rw [arr_getD, pascalRow_getD]

/-- 0 < p ≤ 1 -/
theorem geHalfNum_le (n k : Nat) : geHalfNum n k ≤ geHalfDen n := by
  rw [geHalfNum_eq, geHalfDen, ← sum_choose n]
  apply sumTo_le; intro j _; split <;> omega

theorem geHalfNum_pos {n k : Nat} (h : k ≤ n) : 0 < geHalfNum n k := by
  rw [geHalfNum_eq]
  have hle := le_sumTo (f := fun j => if k ≤ j then choose n j else 0) (x := n) (n := n + 1) (by omega)
  simp only [h, ↓reduceIte, choose_self] at hle
  omega

theorem two_pow_mod_five : ∀ n : Nat, 2 ^ n % 5 ≠ 0
  | 0 => by decide
  | n + 1 => by
    have ih := two_pow_mod_five n
    rw [Nat.pow_succ]
    omega

/-- p = 1/20 인 경우는 없음 (5 는 2ⁿ 을 나누지 않음) -/
theorem twenty_half_ne (n k : Nat) : 20 * geHalfNum n k ≠ geHalfDen n := by
  intro h
  have := two_pow_mod_five n
  unfold geHalfDen at h
  omega

/-- 대조 실행 파일이 파스칼 행 0 … m 을 한 번 만들어 쓰는 길 = 증명된 `geHalfNum` -/
theorem geHalfNum_fast (m n k : Nat) (h : n ≤ m) : geHalfNumWith ((rowsArr m).getD n #[]) n k = geHalfNum n k := by
  rw [rowsArr_getD m n h]; rfl

/-! ## 해석 구역 · 쌍 비율 (검증.md §9-1, js `loudZone` · `loudPairFrac`) — 평균 m = sumS / cnt (cnt = 6 · 측정 수) -/

/-- 1 = m ≤ 2 dB (로빙이 들림) · 2 = m ≤ 7.5 dB (일부만) · 3 = 그 위 (거의 안 들림) -/
def lzone (sumS cnt : Nat) : Nat := if sumS ≤ 2 * cnt then 1 else if 2 * sumS ≤ 15 * cnt then 2 else 3

/-- 값 집합(반 dB 단위 정수)의 모든 순서쌍 중 크기 차이가 m 보다 큰 쌍의 수: |a − b|/2 > sumS/cnt ⇔ |a − b|·cnt > 2·sumS -/
def pairCnt (vals : List Int) (sumS cnt : Nat) : Nat :=
  (vals.flatMap (fun a => vals.map (fun b => (a - b).natAbs))).countP (fun d => 2 * sumS < d * cnt)

/-- 화면 m.toFixed(2) 의 정확한 값 (m·100 에 가장 가까운 정수) -/
def lmean2 (sumS cnt : Nat) : Nat := roundDiv (sumS * 100) cnt

/-! ## 기본 성질 -/

theorem lrespond_done (c : LCfg) (s : LSt) (b : Bool) (h : s.done = true) : lrespond c s b = s := by
  simp [lrespond, h]

theorem lclamp_bounds (c : LCfg) (x : Nat) (h : c.minDb ≤ c.maxDb) : c.minDb ≤ lclamp c x ∧ lclamp c x ≤ c.maxDb := by
  unfold lclamp; omega

theorem lmove_fields (c : LCfg) (s : LSt) (d : Int) :
    (lmove c s d).nTrials = s.nTrials ∧ (lmove c s d).nCorrect = s.nCorrect ∧ (lmove c s d).floorHits = s.floorHits ∧
    (lmove c s d).ceilHits = s.ceilHits ∧ (lmove c s d).done = s.done ∧ (lmove c s d).incomplete = s.incomplete ∧
    (lmove c s d).dir = d := by
  unfold lmove; split <;> simp

theorem lmove_revs (c : LCfg) (s : LSt) (d : Int) :
    ((lmove c s d).revs = s.revs ∧ (lmove c s d).revAt = s.revAt) ∨
    ((lmove c s d).revs = s.revs ++ [s.db] ∧ (lmove c s d).revAt = s.revAt ++ [s.nTrials - 1]) := by
  unfold lmove; split
  · right; simp
  · left; simp

theorem lmove_db (c : LCfg) (s : LSt) (d : Int) (h : c.minDb ≤ c.maxDb) :
    c.minDb ≤ (lmove c s d).db ∧ (lmove c s d).db ≤ c.maxDb := by
  unfold lmove; split <;> (simp only; split <;> exact lclamp_bounds c _ h)

/-- 반전 ⇔ 앞 방향이 있고 이번 방향이 다름 -/
theorem lmove_rev_iff (c : LCfg) (s : LSt) (d : Int) :
    (lmove c s d).revs = s.revs ++ [s.db] ↔ (s.dir ≠ 0 ∧ d ≠ s.dir) := by
  unfold lmove
  by_cases hc : s.dir ≠ 0 ∧ d ≠ s.dir
  · have h1 : lisRev s d = true := by simp [lisRev, hc.1, hc.2]
    simp [h1, hc]
  · have h1 : lisRev s d = false := by
      unfold lisRev; simp only [ne_eq] at hc; by_cases h2 : s.dir = 0 <;> simp_all
    simp only [h1, Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro hh; have := congrArg List.length hh; simp at this
    · intro hh; exact absurd hh hc

/-- 칸: 이번 이동까지 센 반전이 2개 미만이면 2 dB, 그 뒤 1 dB -/
theorem lstep_loud (r : Nat) : lstep loudCfg r = if r < 2 then 2 else 1 := rfl

theorem lfinish_fields (c : LCfg) (x : LSt) :
    (lfinish c x).db = x.db ∧ (lfinish c x).revs = x.revs ∧ (lfinish c x).revAt = x.revAt ∧
    (lfinish c x).nTrials = x.nTrials ∧ (lfinish c x).nCorrect = x.nCorrect ∧
    (lfinish c x).floorHits = x.floorHits ∧ (lfinish c x).ceilHits = x.ceilHits := by
  unfold lfinish; split <;> (try split) <;> simp

theorem lfinish_not_done (c : LCfg) (x : LSt) (h : (lfinish c x).done = false) :
    x.revs.length < c.totalRev ∧ x.nTrials < c.maxTrials ∧ x.done = false := by
  unfold lfinish at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i h1 h2; exact ⟨by omega, by omega, h⟩

theorem lreact_fields (c : LCfg) (x : LSt) (b : Bool) :
    (lreact c x b).nTrials = x.nTrials ∧ (lreact c x b).nCorrect = x.nCorrect ∧ (lreact c x b).floorHits = x.floorHits ∧
    (lreact c x b).ceilHits = x.ceilHits ∧ (lreact c x b).done = x.done := by
  unfold lreact
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · have := lmove_fields c { x with cRun := 0 } 1; simp_all
  · split
    · have := lmove_fields c { x with cRun := 0 } (-1); simp_all
    · simp

theorem lreact_revs (c : LCfg) (x : LSt) (b : Bool) :
    ((lreact c x b).revs = x.revs ∧ (lreact c x b).revAt = x.revAt) ∨
    ((lreact c x b).revs = x.revs ++ [x.db] ∧ (lreact c x b).revAt = x.revAt ++ [x.nTrials - 1]) := by
  unfold lreact
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact lmove_revs c { x with cRun := 0 } 1
  · split
    · exact lmove_revs c { x with cRun := 0 } (-1)
    · left; simp

theorem lreact_db (c : LCfg) (x : LSt) (b : Bool) (h : c.minDb ≤ c.maxDb) (hx : c.minDb ≤ x.db ∧ x.db ≤ c.maxDb) :
    c.minDb ≤ (lreact c x b).db ∧ (lreact c x b).db ≤ c.maxDb := by
  unfold lreact
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact lmove_db c _ 1 h
  · split
    · exact lmove_db c _ (-1) h
    · simpa using hx

/-- 끝나지 않은 상태에서 한 시행: 시행 수 + 1 -/
theorem lrespond_nTrials (c : LCfg) (s : LSt) (b : Bool) (h : s.done = false) :
    (lrespond c s b).nTrials = s.nTrials + 1 := by
  simp only [lrespond, h, Bool.false_eq_true, ↓reduceIte]
  rw [(lfinish_fields c _).2.2.2.1, (lreact_fields c _ b).1]
  simp [lrecord]

/-! ## 불변식 (loudCfg) -/

def LGood (s : LSt) : Prop :=
  1 ≤ s.db ∧ s.db ≤ 15 ∧ (∀ r ∈ s.revs, 1 ≤ r ∧ r ≤ 15) ∧
  (s.done = false → s.nTrials < 120 ∧ s.revs.length < 10) ∧
  s.nCorrect ≤ s.nTrials ∧ s.floorHits ≤ s.nTrials ∧ s.ceilHits ≤ s.nTrials ∧ s.revs.length = s.revAt.length

theorem linit_good : LGood (linit loudCfg) := by
  simp [LGood, linit, loudCfg]

theorem lrespond_good (s : LSt) (b : Bool) (hs : LGood s) : LGood (lrespond loudCfg s b) := by
  by_cases hd : s.done = true
  · rw [lrespond_done loudCfg s b hd]; exact hs
  have hf : s.done = false := by simpa using hd
  obtain ⟨h1, h15, hrev, hrun, hc, hfl, hce, hla⟩ := hs
  -- x = 기록한 상태, y = 이동까지 한 상태, z = 끝 판정까지
  have hx := lfinish_fields loudCfg (lreact loudCfg (lrecord loudCfg s b) b)
  have hy := lreact_fields loudCfg (lrecord loudCfg s b) b
  have hcfg : loudCfg.minDb ≤ loudCfg.maxDb := by decide
  have hdb := lreact_db loudCfg (lrecord loudCfg s b) b hcfg (by simp [lrecord, loudCfg]; omega)
  simp only [lrespond, hf, Bool.false_eq_true, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hx.1]; simpa [loudCfg] using hdb.1
  · rw [hx.1]; simpa [loudCfg] using hdb.2
  · rw [hx.2.1]
    rcases lreact_revs loudCfg (lrecord loudCfg s b) b with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]; simpa [lrecord] using hrev
    · rw [he]; intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hrev r (by simpa [lrecord] using hr)
      · simp [lrecord] at hr; subst hr; exact ⟨h1, h15⟩
  · intro hz
    have := lfinish_not_done loudCfg _ hz
    rw [hx.2.2.2.1, hx.2.1]
    simp only [loudCfg] at this
    exact ⟨this.2.1, this.1⟩
  · rw [hx.2.2.2.2.1, hx.2.2.2.1, hy.2.1, hy.1]; simp only [lrecord]; cases b <;> simp <;> omega
  · rw [hx.2.2.2.2.2.1, hx.2.2.2.1, hy.2.2.1, hy.1]; simp only [lrecord]; split <;> omega
  · rw [hx.2.2.2.2.2.2, hx.2.2.2.1, hy.2.2.2.1, hy.1]; simp only [lrecord]; split <;> omega
  · rw [hx.2.1, hx.2.2.1]
    rcases lreact_revs loudCfg (lrecord loudCfg s b) b with ⟨he, ha⟩ | ⟨he, ha⟩
    · rw [he, ha]; simpa [lrecord] using hla
    · rw [he, ha]; simp [lrecord, hla]

theorem lrun_good : ∀ (bs : List Bool) (s : LSt), LGood s → LGood (lrun loudCfg s bs).1
  | [], s, hs => by simpa [lrun] using hs
  | b :: bs, s, hs => by
    simp only [lrun]
    split
    · exact hs
    · exact lrun_good bs (lrespond loudCfg s b) (lrespond_good s b hs)

/-- 처음부터 돌린 계단: db · 반전 값은 늘 1 … 15 dB -/
theorem lgood_run (bs : List Bool) : LGood (lrun loudCfg (linit loudCfg) bs).1 :=
  lrun_good bs _ linit_good

theorem lrun_ends_aux : ∀ (bs : List Bool) (s : LSt), LGood s → bs.length + s.nTrials ≥ 120 →
    (lrun loudCfg s bs).1.done = true
  | [], s, hs, hl => by
    simp only [lrun]
    cases hd : s.done with
    | true => rfl
    | false =>
      have := (hs.2.2.2.1 hd).1
      simp at hl; omega
  | b :: bs, s, hs, hl => by
    simp only [lrun]
    split
    · assumption
    · rename_i hd
      apply lrun_ends_aux bs (lrespond loudCfg s b) (lrespond_good s b hs)
      rw [lrespond_nTrials loudCfg s b (by simpa using hd)]
      simp at hl; omega

/-- 응답이 120 개 이상이면 반드시 끝남 -/
theorem lrun_ends (bs : List Bool) (h : bs.length ≥ 120) : (lrun loudCfg (linit loudCfg) bs).1.done = true :=
  lrun_ends_aux bs _ linit_good (by simp [linit]; omega)

theorem sum_bounds15 : ∀ (l : List Nat), (∀ r ∈ l, 1 ≤ r ∧ r ≤ 15) → l.length ≤ l.sum ∧ l.sum ≤ 15 * l.length
  | [], _ => by simp
  | r :: l, h => by
    have h1 := h r (by simp)
    have h2 := sum_bounds15 l (fun x hx => h x (by simp [hx]))
    simp only [List.sum_cons, List.length_cons]
    omega

/-- 역치 = 합 S / 6 dB (마지막 6 반전), 6 ≤ S ≤ 90 (1 … 15 dB) -/
theorem lthr_bounds (bs : List Bool) {S cnt : Nat}
    (h : lthrSum loudCfg (lrun loudCfg (linit loudCfg) bs).1 = some (S, cnt)) :
    cnt = 6 ∧ 6 ≤ S ∧ S ≤ 90 := by
  have hg := lgood_run bs
  unfold lthrSum at h
  split at h
  · cases h
  · rename_i hlen
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hS, hc⟩ := h
    have hl : (lused loudCfg (lrun loudCfg (linit loudCfg) bs).1).length = 6 := by
      unfold lused at hlen ⊢
      simp [loudCfg] at hlen ⊢; omega
    have hb := sum_bounds15 (lused loudCfg (lrun loudCfg (linit loudCfg) bs).1)
      (fun r hr => hg.2.2.1 r (List.mem_of_mem_drop hr))
    rw [hl] at hb
    subst hS; subst hc
    exact ⟨hl, hb.1, hb.2⟩

/-- 저장 값 thrDb = S/6 의 넷째 자리 반올림이 갈리는 경우는 없음: S·10⁴/6 은 정확히 ‘정수 + 1/2’ 이 될 수 없음 -/
theorem lthr4_no_tie (S j : Nat) : 2 * (S * 10000) ≠ (2 * j + 1) * 6 := by omega

end SMRT

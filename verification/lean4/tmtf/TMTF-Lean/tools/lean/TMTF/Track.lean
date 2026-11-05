import TMTF.Basic

/-!
# 적응 계단 — 앱 `js/track.js` `Track` 을 줄마다 옮긴 모형 (Claude, 2026-10-24)

계단이 정하는 깊이 D(dB) 가 그 시행의 변조 깊이 m = 10^(D/20) 이 됨 (연습은 0 dB). 그래서 자극의 범위는 계단의 성질.

* `runTrack_inv`        어떤 응답 순서에서도: −40 ≤ D ≤ 0 (m ≤ 1 → 포락선 1 + m·sin ≥ 0, 과변조 없음 — Sam.lean `env_nonneg`),
                        D 는 짝수(시작 · 보폭 4 · 2 · 끝 −40 · 0 이 모두 짝수), 기록된 반전 값도 모두 [−40, 0] · 짝수
* `runTrack_done`       응답이 160개(maxTrials) 이상이면 반드시 끝 — 계단이 끝없이 이어지는 경우 없음
* `thr_bounds`          역치(마지막 avgLast 개 반전의 산술 평균, 정확한 유리수)는 [−40, 0]
* `levitt_target`       2-down 1-up 이 모이는 정답률 p 는 p² = 1/2 → 0.7071 < p < 0.7072 (Levitt 1971 의 70.7%)
* `uw_params` · `dr_params`  두 절차의 값(시작 0 / −2 dB, 4 dB 보폭은 반전 4 / 2 번까지, 반전 14 / 8 번, 마지막 10 / 6 개 평균)
반전 = 이동 방향이 바뀐 때, 값 = 이동 **전** 깊이, 보폭은 반전을 센 **뒤** 고름 (js 와 같은 순서). 0 dB 에서 틀려도(위로 막혀
깊이는 그대로) 방향이 바뀌면 반전으로 셈 — js 그대로이며, 천장 근처 평균이 0 쪽으로 끌리는 바닥 효과의 원인(앱 설명에 있음).
-/

namespace TMTF

structure TrackP where
  nAFC : Nat
  startDb : Int
  bigUntil : Nat
  big : Int
  small : Int
  totalRev : Nat
  avgLast : Nat
  stop4 : Bool
  maxTrials : Nat

/-- Won 2011 · Park 2015 (`PROTOCOLS.uw`) -/
def uwP : TrackP :=
  { nAFC := 2, startDb := 0, bigUntil := 4, big := 4, small := 2, totalRev := 14, avgLast := 10, stop4 := false, maxTrials := 160 }
/-- De Ruiter 2015 (`PROTOCOLS.deruiter`) -/
def drP : TrackP :=
  { nAFC := 3, startDb := -2, bigUntil := 2, big := 4, small := 2, totalRev := 8, avgLast := 6, stop4 := true, maxTrials := 160 }

structure TrackS where
  depth : Int
  run : Nat
  dir : Int
  reversals : List Int
  revAt : List Nat
  trials : List (Int × Bool)
  ceilMiss : Nat
  n0 : Nat
  k0 : Nat
  done : Bool
  ceiling : Bool
  incomplete : Bool

def TrackS.init (P : TrackP) : TrackS :=
  { depth := P.startDb, run := 0, dir := 0, reversals := [], revAt := [], trials := [], ceilMiss := 0, n0 := 0, k0 := 0,
    done := false, ceiling := false, incomplete := false }

/-- `Math.max(minDb, Math.min(maxDb, x))` -/
def clampDb (x : Int) : Int := max (-40) (min 0 x)

/-- `step()` -/
def stepOf (P : TrackP) (S : TrackS) : Int := if S.reversals.length < P.bigUntil then P.big else P.small

/-- `move` 의 앞부분: 방향이 바뀌면 반전 기록(이동 전 깊이, 그 반전을 만든 시행 번호) -/
def markRev (S : TrackS) (d : Int) : TrackS :=
  if S.dir ≠ 0 ∧ d ≠ S.dir then { S with reversals := S.reversals ++ [S.depth], revAt := S.revAt ++ [S.trials.length - 1] } else S

/-- `move(d)` — 보폭은 반전을 센 뒤에 고름 -/
def move (P : TrackP) (S : TrackS) (d : Int) : TrackS :=
  { markRev S d with dir := d, depth := clampDb ((markRev S d).depth + d * stepOf P (markRev S d)) }

/-- 0 dB(천장) 시행 세기: n0 · k0 · ceilMiss -/
def tally (S : TrackS) (c : Bool) : TrackS :=
  if 0 ≤ S.depth then
    (if c then { S with n0 := S.n0 + 1, k0 := S.k0 + 1 } else { S with n0 := S.n0 + 1, ceilMiss := S.ceilMiss + 1 })
  else S

/-- 맞으면 run++ (2 가 되면 0 으로 · 아래로), 틀리면 run = 0 · 위로 -/
def afterAnswer (P : TrackP) (S : TrackS) (c : Bool) : TrackS :=
  if c then (if 2 ≤ S.run + 1 then move P { S with run := 0 } (-1) else { S with run := S.run + 1 })
  else move P { S with run := 0 } 1

/-- 멈춤 규칙 (js 와 같은 순서: 천장 4번 → 반전 수 → 시행 수) -/
def finish (P : TrackP) (S : TrackS) : TrackS :=
  if P.stop4 = true ∧ 4 ≤ S.ceilMiss then { S with done := true, ceiling := true }
  else if P.totalRev ≤ S.reversals.length then { S with done := true }
  else if P.maxTrials ≤ S.trials.length then { S with done := true, incomplete := true }
  else S

/-- `respond(correct)` -/
def respond (P : TrackP) (S : TrackS) (c : Bool) : TrackS :=
  if S.done = true then S else finish P (afterAnswer P (tally { S with trials := S.trials ++ [(S.depth, c)] } c) c)

def runTrack (P : TrackP) (cs : List Bool) : TrackS := cs.foldl (respond P) (TrackS.init P)

/-- 마지막 k 개 (`slice(-k)`) -/
def lastK (k : Nat) (l : List Int) : List Int := l.drop (l.length - k)

def sumI (l : List Int) : Int := l.foldr (· + ·) 0

/-- `result().thr` 의 정확한 값 (js 는 이 값을 소수 둘째 자리로 반올림) — 천장 멈춤이면 0, 반전이 4개 미만이면 없음 -/
def thrQ (P : TrackP) (S : TrackS) : Option Rat :=
  if S.ceiling = true then some 0
  else if (lastK P.avgLast S.reversals).length < 4 then none
  else some ((sumI (lastK P.avgLast S.reversals) : Rat) / ((lastK P.avgLast S.reversals).length : Rat))

/-! ## 불변식 -/

/-- 깊이 · 반전 값이 [−40, 0] 이고 짝수 -/
def Inv (S : TrackS) : Prop :=
  (-40 ≤ S.depth ∧ S.depth ≤ 0 ∧ S.depth % 2 = 0) ∧ ∀ r ∈ S.reversals, -40 ≤ r ∧ r ≤ 0 ∧ r % 2 = 0

/-- 절차 값이 짝수 · 시작이 범위 안 -/
def GoodP (P : TrackP) : Prop :=
  -40 ≤ P.startDb ∧ P.startDb ≤ 0 ∧ P.startDb % 2 = 0 ∧ P.big % 2 = 0 ∧ P.small % 2 = 0

theorem uw_good : GoodP uwP := by unfold GoodP uwP; decide
theorem dr_good : GoodP drP := by unfold GoodP drP; decide

theorem clampDb_ok {x : Int} (h : x % 2 = 0) : -40 ≤ clampDb x ∧ clampDb x ≤ 0 ∧ clampDb x % 2 = 0 := by
  unfold clampDb; omega

theorem markRev_inv {S : TrackS} {d : Int} (h : Inv S) : Inv (markRev S d) := by
  unfold markRev
  split
  · refine ⟨h.1, ?_⟩
    intro r hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact h.2 r hr
    · exact h.1
  · exact h

theorem stepOf_even {P : TrackP} (hP : GoodP P) (S : TrackS) : stepOf P S % 2 = 0 := by
  unfold stepOf; split
  · exact hP.2.2.2.1
  · exact hP.2.2.2.2

theorem move_inv {P : TrackP} (hP : GoodP P) {S : TrackS} {d : Int} (hd : d = 1 ∨ d = -1) (h : Inv S) : Inv (move P S d) := by
  have h1 := markRev_inv (d := d) h
  have h0 : (markRev S d).depth % 2 = 0 := h1.1.2.2
  have hs := stepOf_even hP (markRev S d)
  have he : ((markRev S d).depth + d * stepOf P (markRev S d)) % 2 = 0 := by
    rcases hd with rfl | rfl <;> omega
  exact ⟨clampDb_ok he, h1.2⟩

theorem tally_inv {S : TrackS} {c : Bool} (h : Inv S) : Inv (tally S c) := by
  unfold tally; split
  · split
    · exact h
    · exact h
  · exact h

theorem afterAnswer_inv {P : TrackP} (hP : GoodP P) {S : TrackS} {c : Bool} (h : Inv S) : Inv (afterAnswer P S c) := by
  unfold afterAnswer; split
  · split
    · exact move_inv hP (Or.inr rfl) h
    · exact h
  · exact move_inv hP (Or.inl rfl) h

theorem finish_inv {P : TrackP} {S : TrackS} (h : Inv S) : Inv (finish P S) := by
  unfold finish; split
  · exact h
  · split
    · exact h
    · split
      · exact h
      · exact h

theorem respond_inv {P : TrackP} (hP : GoodP P) {S : TrackS} {c : Bool} (h : Inv S) : Inv (respond P S c) := by
  unfold respond; split
  · exact h
  · exact finish_inv (afterAnswer_inv hP (tally_inv h))

theorem foldl_inv {α β : Type} (f : β → α → β) (I : β → Prop) (hf : ∀ b a, I b → I (f b a)) :
    ∀ (l : List α) (b : β), I b → I (l.foldl f b) := by
  intro l
  induction l with
  | nil => intro b hb; exact hb
  | cons a l ih => intro b hb; exact ih (f b a) (hf b a hb)

theorem init_inv {P : TrackP} (hP : GoodP P) : Inv (TrackS.init P) :=
  ⟨⟨hP.1, hP.2.1, hP.2.2.1⟩, fun r hr => by simp [TrackS.init] at hr⟩

/-- 어떤 응답 순서에서도 깊이 · 반전 값은 [−40, 0] 의 짝수 -/
theorem runTrack_inv {P : TrackP} (hP : GoodP P) (cs : List Bool) : Inv (runTrack P cs) :=
  foldl_inv (respond P) Inv (fun _ _ hb => respond_inv hP hb) cs _ (init_inv hP)

/-! ## 끝남 -/

theorem markRev_trials (S : TrackS) (d : Int) : (markRev S d).trials = S.trials := by
  unfold markRev; split <;> rfl

theorem move_trials (P : TrackP) (S : TrackS) (d : Int) : (move P S d).trials = S.trials := by
  unfold move; exact markRev_trials S d

theorem tally_trials (S : TrackS) (c : Bool) : (tally S c).trials = S.trials := by
  unfold tally; split
  · split <;> rfl
  · rfl

theorem afterAnswer_trials (P : TrackP) (S : TrackS) (c : Bool) : (afterAnswer P S c).trials = S.trials := by
  unfold afterAnswer; split
  · split
    · exact move_trials P _ _
    · rfl
  · exact move_trials P _ _

theorem finish_trials (P : TrackP) (S : TrackS) : (finish P S).trials = S.trials := by
  unfold finish; split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- 끝나지 않았으면 시행 기록이 정확히 하나 늘어남 -/
theorem respond_len {P : TrackP} {S : TrackS} {c : Bool} (h : S.done = false) :
    (respond P S c).trials.length = S.trials.length + 1 := by
  unfold respond
  rw [if_neg (by rw [h]; decide), finish_trials, afterAnswer_trials, tally_trials]
  simp

/-- 끝났거나, 시행 수가 아직 상한 아래 -/
def Live (P : TrackP) (S : TrackS) : Prop := S.done = true ∨ S.trials.length < P.maxTrials

theorem finish_live (P : TrackP) (S : TrackS) : Live P (finish P S) := by
  unfold finish Live; split
  · left; rfl
  · split
    · left; rfl
    · split
      · left; rfl
      · right; omega

theorem respond_live (P : TrackP) (S : TrackS) (c : Bool) (h : Live P S) : Live P (respond P S c) := by
  unfold respond; split
  · exact h
  · exact finish_live P _

theorem respond_done {P : TrackP} {S : TrackS} {c : Bool} (h : S.done = true) : respond P S c = S := by
  unfold respond; simp [h]

theorem foldl_done_stays (P : TrackP) : ∀ (cs : List Bool) (S : TrackS), S.done = true → (cs.foldl (respond P) S).done = true := by
  intro cs
  induction cs with
  | nil => intro S h; exact h
  | cons c cs ih => intro S h; simp only [List.foldl_cons]; rw [respond_done h]; exact ih S h

theorem foldl_done (P : TrackP) : ∀ (cs : List Bool) (S : TrackS), Live P S →
    (S.done = true ∨ P.maxTrials ≤ S.trials.length + cs.length) → (cs.foldl (respond P) S).done = true := by
  intro cs
  induction cs with
  | nil =>
    intro S hl hc
    simp only [List.foldl_nil]
    unfold Live at hl
    simp only [List.length_nil] at hc
    rcases hc with hc | hc
    · exact hc
    · rcases hl with hl | hl
      · exact hl
      · omega
  | cons c cs ih =>
    intro S hl hc
    simp only [List.foldl_cons]
    by_cases hd : S.done = true
    · rw [respond_done hd]; exact foldl_done_stays P cs S hd
    · have hf : S.done = false := by simpa using hd
      apply ih (respond P S c) (respond_live P S c hl)
      right
      rcases hc with hc | hc
      · exact absurd hc hd
      · rw [respond_len hf]; simp only [List.length_cons] at hc; omega

/-- 응답이 maxTrials(160) 개 이상이면 반드시 끝 -/
theorem runTrack_done (P : TrackP) (hm : 0 < P.maxTrials) (cs : List Bool) (h : P.maxTrials ≤ cs.length) :
    (runTrack P cs).done = true := by
  unfold runTrack
  apply foldl_done P cs _ (Or.inr (by simp [TrackS.init]; exact hm))
  right; simp [TrackS.init]; exact h

/-! ## 역치 -/

theorem sumI_bounds : ∀ (l : List Int), (∀ r ∈ l, -40 ≤ r ∧ r ≤ 0) → -40 * (l.length : Int) ≤ sumI l ∧ sumI l ≤ 0 := by
  intro l
  induction l with
  | nil => intro _; simp [sumI]
  | cons a l ih =>
    intro h
    have ha := h a (by simp)
    have hl := ih (fun r hr => h r (by simp [hr]))
    simp only [sumI, List.foldr_cons, List.length_cons] at hl ⊢
    constructor <;> omega

theorem lastK_sub (k : Nat) (l : List Int) : ∀ r ∈ lastK k l, r ∈ l := by
  intro r hr; unfold lastK at hr; exact List.mem_of_mem_drop hr

/-- 역치(정확한 평균)는 [−40, 0] -/
theorem thr_bounds {P : TrackP} {S : TrackS} (h : Inv S) {q : Rat} (hq : thrQ P S = some q) : -40 ≤ q ∧ q ≤ 0 := by
  unfold thrQ at hq
  split at hq
  · cases hq; exact ⟨by decide, by decide⟩
  · split at hq
    · cases hq
    · rename_i h2
      cases hq
      have hlen : 4 ≤ (lastK P.avgLast S.reversals).length := by omega
      have hb := sumI_bounds (lastK P.avgLast S.reversals)
        (fun r hr => let hh := h.2 r (lastK_sub _ _ r hr); ⟨hh.1, hh.2.1⟩)
      have hpos : (0 : Rat) < ((lastK P.avgLast S.reversals).length : Rat) := Rat.natCast_pos.mpr (by omega)
      have hcast : ((-40 * ((lastK P.avgLast S.reversals).length : Int) : Int) : Rat)
          = -40 * ((lastK P.avgLast S.reversals).length : Rat) := by
        rw [Rat.intCast_mul]; rfl
      have h1 : ((-40 * ((lastK P.avgLast S.reversals).length : Int) : Int) : Rat) ≤ (sumI (lastK P.avgLast S.reversals) : Rat) :=
        Rat.intCast_le_intCast.mpr hb.1
      have h2 : (sumI (lastK P.avgLast S.reversals) : Rat) ≤ ((0 : Int) : Rat) := Rat.intCast_le_intCast.mpr hb.2
      rw [hcast] at h1
      constructor
      · rw [le_div_of_pos hpos]; grind
      · rw [div_le_of_pos hpos]; grind

/-! ## 70.7% · 절차 값 -/

/-- 2-down 1-up: 아래로 갈 확률 p², 위로 1 − p² — 같아지는 곳 p² = 1/2, p = 1/√2 ∈ (0.7071, 0.7072) -/
theorem levitt_target : (7071 / 10000 : Rat) * (7071 / 10000) < 1 / 2 ∧ 1 / 2 < (7072 / 10000 : Rat) * (7072 / 10000) := by
  decide +kernel

theorem uw_params : uwP.startDb = 0 ∧ uwP.big = 4 ∧ uwP.small = 2 ∧ uwP.bigUntil = 4 ∧ uwP.totalRev = 14 ∧ uwP.avgLast = 10 ∧
    uwP.stop4 = false ∧ uwP.maxTrials = 160 := by decide

theorem dr_params : drP.startDb = -2 ∧ drP.big = 4 ∧ drP.small = 2 ∧ drP.bigUntil = 2 ∧ drP.totalRev = 8 ∧ drP.avgLast = 6 ∧
    drP.stop4 = true ∧ drP.maxTrials = 160 := by decide

end TMTF

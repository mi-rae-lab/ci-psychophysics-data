import SRD.Arith

/-!
# 계단 — 앱 `js/staircase.js` `Stair.step` · `Stair.threshold` 의 모형과 성질 (Claude, 2026-10-21)

Won 2007: 2-up 1-down, 0.176 rpo(칸 1) 시작, 한 칸 ×1.414, 반전 13번에서 끝, 마지막 8번 평균.
밀도 칸 k = 0 (0.125 rpo) … 13 (11.314 rpo), 반전 값은 milli-rpo 정수 `densMilli k`.
js 와 같은 순서 · 같은 값으로 상태를 바꿈 — 계산을 칸별 함수로 펼쳐 씀:
요청 방향 `reqDir` (+1 어렵게 · 0 머묾 · −1 쉽게) → 막힘 `isBlocked` → 이동 `moved` → 새 칸 `newK` → 반전 `isRev` → 끝 판정 `endCheck`.
`lastDir` 의 0 은 js 의 null (아직 실제 이동 없음).

증명한 것 (모든 상태 · 모든 응답):
* `step_k_le` 칸은 늘 0 … 13 · `step_k_near` 한 번에 많아야 한 칸
* `step_wrong` 틀리면 한 칸 쉽게 (0 에서는 막힘) · `step_second_correct` 두 번째 연속 정답이면 한 칸 어렵게 (13 에서는 막힘)
  · `step_first_correct` 첫 정답은 머묾 · `step_invalid` 기술적 실패는 칸 · 연속 정답 · 방향 · 반전 · 유효 수를 바꾸지 않음
* `step_revs` 반전은 실제 이동에서 방향이 바뀔 때만 하나 늘고, 그 값은 이동 전 칸 · `step_blocked_no_rev` 막힌 이동은 반전 아님
* `run_ends` 응답이 160개 이상이면 반드시 끝남 (유효 150 + 기술적 실패 10 상한)
* `run_threshold_bounds` 역치(마지막 8 반전 평균)는 0.125 … 11.314 rpo 안
-/

namespace SRD

/-- 밀도 표 (milli-rpo) — js `DENS_MILLI` (Won 2007 원문 표 값) -/
def densTable : List Nat := [125, 176, 250, 354, 500, 707, 1000, 1414, 2000, 2828, 4000, 5657, 8000, 11314]

def densMilli (k : Nat) : Nat := densTable.getD k 0

inductive StStatus
  | running | reversalTarget | trialCap | techFail
deriving DecidableEq, Repr, Inhabited

inductive Move
  | stay | move | blocked | invalid
deriving DecidableEq, Repr, Inhabited

inductive Outcome
  | correct | wrong | invalid
deriving DecidableEq, Repr, Inhabited

/-- 설정 — js `Stair.cfgFrom(PROTOCOLS.won2007)` -/
structure Cfg where
  startK : Nat
  minK : Nat
  maxK : Nat
  nHarder : Nat
  totalRev : Nat
  retained : Nat
  maxValid : Nat
  maxTech : Nat
deriving Repr

def wonCfg : Cfg := { startK := 1, minK := 0, maxK := 13, nHarder := 2, totalRev := 13, retained := 8, maxValid := 150, maxTech := 10 }

/-- 반전 기록: 이동 전 칸 · 유효 시행 번호 · 끝 표시 (0 없음, 1 쉬운 끝, 2 어려운 끝) -/
structure Rev where
  k : Nat
  validNo : Nat
  atBound : Nat
deriving DecidableEq, Repr, Inhabited

structure St where
  k : Nat
  streak : Nat
  lastDir : Int
  revs : List Rev
  attempts : Nat
  valid : Nat
  tech : Nat
  moves : Nat
  status : StStatus
deriving Repr, Inhabited

/-- 시행 기록 (js `tr` 의 판정에 쓰는 칸) -/
structure Tr where
  k : Nat
  isValid : Bool
  correct : Bool
  validNo : Nat
  move : Move
  blockedAt : Nat
  reversal : Bool
deriving Repr, Inhabited

def init (c : Cfg) : St := { k := c.startK, streak := 0, lastDir := 0, revs := [], attempts := 0, valid := 0, tech := 0, moves := 0, status := .running }

/-! ## 한 시행 — 칸별 함수 -/

/-- 요청 방향: 맞히면 연속 정답 + 1 이 nHarder 에 닿을 때 +1 (아니면 0), 틀리면 −1 -/
def reqDir (c : Cfg) (s : St) (correct : Bool) : Int :=
  if correct then (if s.streak + 1 ≥ c.nHarder then 1 else 0) else -1

/-- 새 연속 정답 (이동에 쓴 정답 쌍은 다시 쓰지 않음) -/
def newStreak (c : Cfg) (s : St) (correct : Bool) : Nat :=
  if correct then (if s.streak + 1 ≥ c.nHarder then 0 else s.streak + 1) else 0

/-- 끝에 막힌 이동: 13 에서 더 어렵게 · 0 에서 더 쉽게 -/
def isBlocked (c : Cfg) (s : St) (dir : Int) : Bool :=
  (decide (dir > 0) && decide (s.k ≥ c.maxK)) || (decide (dir < 0) && decide (s.k ≤ c.minK))

/-- 실제 이동 -/
def moved (c : Cfg) (s : St) (dir : Int) : Bool := decide (dir ≠ 0) && !isBlocked c s dir

def newK (c : Cfg) (s : St) (dir : Int) : Nat :=
  if moved c s dir then (if dir > 0 then s.k + 1 else s.k - 1) else s.k

/-- 반전: 실제 이동이고, 앞의 실제 이동이 있었고, 방향이 바뀜 -/
def isRev (c : Cfg) (s : St) (dir : Int) : Bool := moved c s dir && decide (s.lastDir ≠ 0) && decide (dir ≠ s.lastDir)

def atB (c : Cfg) (k : Nat) : Nat := if k = c.minK then 1 else if k = c.maxK then 2 else 0

def newRevs (c : Cfg) (s : St) (dir : Int) (validNo : Nat) : List Rev :=
  if isRev c s dir then s.revs ++ [{ k := s.k, validNo := validNo, atBound := atB c s.k }] else s.revs

/-- 유효 시행 뒤 끝 판정 (js: 반전 수 먼저, 그다음 유효 시행 상한) -/
def endCheck (c : Cfg) (revs : List Rev) (valid : Nat) : StStatus :=
  if revs.length ≥ c.totalRev then .reversalTarget
  else if valid ≥ c.maxValid then .trialCap
  else .running

def moveOf (c : Cfg) (s : St) (dir : Int) : Move :=
  if dir = 0 then .stay else if isBlocked c s dir then .blocked else .move

def stepValid (c : Cfg) (s : St) (correct : Bool) : St × Tr :=
  let dir := reqDir c s correct
  let valid := s.valid + 1
  let revs := newRevs c s dir valid
  ({ k := newK c s dir, streak := newStreak c s correct, lastDir := if moved c s dir then dir else s.lastDir, revs := revs,
     attempts := s.attempts + 1, valid := valid, tech := s.tech, moves := if moved c s dir then s.moves + 1 else s.moves,
     status := endCheck c revs valid },
   { k := s.k, isValid := true, correct := correct, validNo := valid, move := moveOf c s dir,
     blockedAt := if moveOf c s dir = .blocked then (if dir > 0 then 2 else 1) else 0, reversal := isRev c s dir })

def stepInvalid (c : Cfg) (s : St) : St × Tr :=
  ({ s with attempts := s.attempts + 1, tech := s.tech + 1, status := if s.tech + 1 ≥ c.maxTech then .techFail else s.status },
   { k := s.k, isValid := false, correct := false, validNo := 0, move := .invalid, blockedAt := 0, reversal := false })

/-- 한 시행 (js `Stair.step`, 진행 중일 때) -/
def step (c : Cfg) (s : St) : Outcome → St × Tr
  | .correct => stepValid c s true
  | .wrong => stepValid c s false
  | .invalid => stepInvalid c s

/-- 응답 순서대로 (끝나면 멈춤 — 끝난 계단에는 시행을 내지 않음) -/
def run (c : Cfg) : St → List Outcome → St × List Tr
  | s, [] => (s, [])
  | s, o :: os =>
    if s.status = .running then
      let r := step c s o
      let rest := run c r.1 os
      (rest.1, r.2 :: rest.2)
    else (s, [])

/-- 역치: 반전이 13번 이상이면 마지막 8번의 milli 합과 개수 (thr = 합 / (1000 · 개수)) -/
def threshold (c : Cfg) (s : St) : Option (Nat × Nat) :=
  if s.revs.length < c.totalRev then none
  else
    let kept := s.revs.drop (s.revs.length - c.retained)
    some ((kept.map (fun r => densMilli r.k)).sum, kept.length)

/-! ## 칸별 보조정리 -/

section props
variable (c : Cfg)

theorem reqDir_cases (s : St) (b : Bool) : reqDir c s b = 1 ∨ reqDir c s b = 0 ∨ reqDir c s b = -1 := by
  unfold reqDir; split <;> (try split) <;> simp

theorem newK_le (s : St) (dir : Int) (hd : dir = 1 ∨ dir = 0 ∨ dir = -1) (h : s.k ≤ c.maxK) : newK c s dir ≤ c.maxK := by
  unfold newK moved isBlocked
  rcases hd with hd | hd | hd <;> subst hd <;> by_cases h1 : s.k ≥ c.maxK <;> by_cases h2 : s.k ≤ c.minK <;> simp_all <;> omega

theorem newK_near (s : St) (dir : Int) (hd : dir = 1 ∨ dir = 0 ∨ dir = -1) : newK c s dir + 1 ≥ s.k ∧ newK c s dir ≤ s.k + 1 := by
  unfold newK moved isBlocked
  rcases hd with hd | hd | hd <;> subst hd <;> by_cases h1 : s.k ≥ c.maxK <;> by_cases h2 : s.k ≤ c.minK <;> simp_all <;> omega

theorem step_k_le (s : St) (o : Outcome) (h : s.k ≤ c.maxK) : (step c s o).1.k ≤ c.maxK := by
  cases o
  · exact newK_le c s _ (reqDir_cases c s true) h
  · exact newK_le c s _ (reqDir_cases c s false) h
  · simpa [step, stepInvalid] using h

theorem step_k_near (s : St) (o : Outcome) : (step c s o).1.k + 1 ≥ s.k ∧ (step c s o).1.k ≤ s.k + 1 := by
  cases o
  · exact newK_near c s _ (reqDir_cases c s true)
  · exact newK_near c s _ (reqDir_cases c s false)
  · simp [step, stepInvalid]

/-- 틀리면 한 칸 쉽게 (칸 0 = 쉬운 끝에서는 막힘), 연속 정답 0 -/
theorem step_wrong (s : St) (hmin : c.minK = 0) :
    (step c s .wrong).1.k = s.k - 1 ∧ (step c s .wrong).1.streak = 0 ∧
    (step c s .wrong).2.move = (if s.k = 0 then .blocked else .move) := by
  simp only [step, stepValid, newK, moved, isBlocked, reqDir, newStreak, moveOf, hmin]
  by_cases hk : s.k = 0 <;> simp [hk] <;> omega

/-- 두 번째 연속 정답이면 한 칸 어렵게 (어려운 끝에서는 막힘), 연속 정답은 0 으로 -/
theorem step_second_correct (s : St) (hn : c.nHarder = 2) (hs : s.streak = 1) :
    (step c s .correct).1.k = (if s.k ≥ c.maxK then s.k else s.k + 1) ∧ (step c s .correct).1.streak = 0 ∧
    (step c s .correct).2.move = (if s.k ≥ c.maxK then .blocked else .move) := by
  simp only [step, stepValid, newK, moved, isBlocked, reqDir, newStreak, moveOf, hn, hs]
  by_cases hk : s.k ≥ c.maxK <;> simp [hk]

/-- 첫 정답(연속 정답 0)은 머묾, 연속 정답 1 -/
theorem step_first_correct (s : St) (hn : c.nHarder = 2) (hs : s.streak = 0) :
    (step c s .correct).1.k = s.k ∧ (step c s .correct).1.streak = 1 ∧ (step c s .correct).2.move = .stay := by
  simp [step, stepValid, newK, moved, isBlocked, reqDir, newStreak, moveOf, hn, hs]

/-- 기술적 실패는 칸 · 연속 정답 · 방향 · 반전 · 유효 시행 수를 바꾸지 않음 -/
theorem step_invalid (s : St) :
    (step c s .invalid).1.k = s.k ∧ (step c s .invalid).1.streak = s.streak ∧ (step c s .invalid).1.lastDir = s.lastDir ∧
    (step c s .invalid).1.revs = s.revs ∧ (step c s .invalid).1.valid = s.valid ∧ (step c s .invalid).1.tech = s.tech + 1 := by
  simp [step, stepInvalid]

theorem isRev_moved (s : St) (dir : Int) (h : isRev c s dir = true) : moved c s dir = true := by
  simp only [isRev, Bool.and_eq_true] at h
  exact h.1.1

theorem moveOf_of_moved (s : St) (dir : Int) (h : moved c s dir = true) : moveOf c s dir = .move := by
  simp only [moved, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  simp [moveOf, h.1, h.2]

theorem stepValid_revs (s : St) (b : Bool) :
    (stepValid c s b).1.revs = s.revs ∨
    (∃ r : Rev, (stepValid c s b).1.revs = s.revs ++ [r] ∧ r.k = s.k ∧ (stepValid c s b).2.move = .move ∧ (stepValid c s b).2.reversal = true) := by
  by_cases hr : isRev c s (reqDir c s b) = true
  · right
    refine ⟨{ k := s.k, validNo := s.valid + 1, atBound := atB c s.k }, by simp [stepValid, newRevs, hr], rfl, ?_, by simpa [stepValid] using hr⟩
    simpa [stepValid] using moveOf_of_moved c s _ (isRev_moved c s _ hr)
  · left
    simp [stepValid, newRevs, hr]

/-- 반전: 실제 이동에서 방향이 바뀔 때만 하나 늘고, 그 값은 이동 전 칸 -/
theorem step_revs (s : St) (o : Outcome) :
    (step c s o).1.revs = s.revs ∨
    (∃ r : Rev, (step c s o).1.revs = s.revs ++ [r] ∧ r.k = s.k ∧ (step c s o).2.move = .move ∧ (step c s o).2.reversal = true) := by
  cases o
  · exact stepValid_revs c s true
  · exact stepValid_revs c s false
  · left; simp [step, stepInvalid]

/-- 막힌 이동은 반전이 아님 (반전 목록 그대로) -/
theorem step_blocked_no_rev (s : St) (o : Outcome) (h : (step c s o).2.move = .blocked) : (step c s o).1.revs = s.revs := by
  rcases step_revs c s o with h1 | ⟨_, _, _, hm, _⟩
  · exact h1
  · rw [hm] at h; cases h

end props

/-! ### 끝남 -/

/-- 진행 중 상태의 불변식: 시도 = 유효 + 기술적 실패, 진행 중이면 유효 < 150 · 기술적 실패 < 10 -/
def Inv (c : Cfg) (s : St) : Prop :=
  s.attempts = s.valid + s.tech ∧ (s.status = .running → s.valid < c.maxValid ∧ s.tech < c.maxTech)

theorem init_inv (c : Cfg) (h1 : 0 < c.maxValid) (h2 : 0 < c.maxTech) : Inv c (init c) := by
  simp [Inv, init, h1, h2]

theorem endCheck_running {c : Cfg} {revs : List Rev} {v : Nat} (h : endCheck c revs v = .running) : v < c.maxValid := by
  unfold endCheck at h
  split at h
  · cases h
  · split at h
    · cases h
    · omega

theorem step_attempts (c : Cfg) (s : St) (o : Outcome) : (step c s o).1.attempts = s.attempts + 1 := by
  cases o <;> simp [step, stepValid, stepInvalid]

theorem step_inv (c : Cfg) (s : St) (o : Outcome) (hs : Inv c s) (hr : s.status = .running) : Inv c (step c s o).1 := by
  obtain ⟨ha, hb⟩ := hs
  have hb' := hb hr
  cases o
  · refine ⟨by simp [step, stepValid]; omega, fun h => ⟨endCheck_running (by simpa [step, stepValid] using h), by simpa [step, stepValid] using hb'.2⟩⟩
  · refine ⟨by simp [step, stepValid]; omega, fun h => ⟨endCheck_running (by simpa [step, stepValid] using h), by simpa [step, stepValid] using hb'.2⟩⟩
  · refine ⟨by simp [step, stepInvalid]; omega, fun h => ?_⟩
    simp only [step, stepInvalid] at h ⊢
    by_cases ht : s.tech + 1 ≥ c.maxTech
    · simp [ht] at h
    · exact ⟨hb'.1, by omega⟩

/-- 진행 중인 한 시도 수 < 유효 상한 + 기술적 실패 상한 → 응답이 그만큼 있으면 끝남 -/
theorem run_ends_aux (c : Cfg) : ∀ (os : List Outcome) (s : St), Inv c s →
    os.length + s.attempts ≥ c.maxValid + c.maxTech → (run c s os).1.status ≠ .running
  | [], s, hs, hl => by
    simp only [run]
    intro hr
    have h1 := hs.2 hr
    have h2 := hs.1
    simp at hl
    omega
  | o :: os, s, hs, hl => by
    simp only [run]
    split
    · rename_i hr
      apply run_ends_aux c os (step c s o).1 (step_inv c s o hs hr)
      rw [step_attempts]
      simp at hl
      omega
    · assumption

/-- Won 설정에서 응답이 160개 이상이면 반드시 끝남 -/
theorem run_ends (os : List Outcome) (h : os.length ≥ 160) : (run wonCfg (init wonCfg) os).1.status ≠ .running :=
  run_ends_aux wonCfg os (init wonCfg) (init_inv wonCfg (by decide) (by decide)) (by simp [init, wonCfg]; omega)

/-! ### 역치 범위 -/

theorem densMilli_bounds {k : Nat} (hk : k ≤ 13) : 125 ≤ densMilli k ∧ densMilli k ≤ 11314 := by
  unfold densMilli densTable
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13) with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

theorem sum_bounds : ∀ (l : List Rev), (∀ r ∈ l, r.k ≤ 13) →
    125 * l.length ≤ (l.map (fun r => densMilli r.k)).sum ∧ (l.map (fun r => densMilli r.k)).sum ≤ 11314 * l.length
  | [], _ => by simp
  | r :: l, h => by
    have h1 := densMilli_bounds (h r (by simp))
    have h2 := sum_bounds l (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    constructor <;> omega

/-- 반전 값이 모두 0 … 13 이면 역치 = 합 / (1000 · 개수) 는 0.125 … 11.314 rpo -/
theorem threshold_bounds (s : St) (hk : ∀ r ∈ s.revs, r.k ≤ 13) {sum cnt : Nat} (h : threshold wonCfg s = some (sum, cnt)) :
    cnt = 8 ∧ 125 * 8 ≤ sum ∧ sum ≤ 11314 * 8 := by
  unfold threshold at h
  split at h
  · cases h
  · rename_i hlen
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hl : (s.revs.drop (s.revs.length - wonCfg.retained)).length = 8 := by
      simp [wonCfg] at hlen ⊢; omega
    have hb := sum_bounds (s.revs.drop (s.revs.length - wonCfg.retained)) (fun r hr => hk r (List.mem_of_mem_drop hr))
    rw [hl] at hb
    subst h1; subst h2
    exact ⟨hl, hb.1, hb.2⟩

/-- 반전 값(이동 전 칸)은 늘 0 … 13 — 한 시행 -/
theorem step_revs_le (s : St) (o : Outcome) (hk : s.k ≤ 13) (hr : ∀ r ∈ s.revs, r.k ≤ 13) :
    ∀ r ∈ (step wonCfg s o).1.revs, r.k ≤ 13 := by
  rcases step_revs wonCfg s o with h | ⟨r0, h, hk0, _, _⟩
  · rw [h]; exact hr
  · rw [h]; intro r hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hr r hm
    · simp at hm; subst hm; omega

/-- 응답 순서 전체: 칸과 반전 값이 늘 0 … 13 -/
theorem run_bounds : ∀ (os : List Outcome) (s : St), s.k ≤ 13 → (∀ r ∈ s.revs, r.k ≤ 13) →
    (run wonCfg s os).1.k ≤ 13 ∧ ∀ r ∈ (run wonCfg s os).1.revs, r.k ≤ 13
  | [], s, hk, hr => by simp only [run]; exact ⟨hk, hr⟩
  | o :: os, s, hk, hr => by
    simp only [run]
    split
    · exact run_bounds os (step wonCfg s o).1 (step_k_le wonCfg s o (by simpa [wonCfg] using hk)) (step_revs_le s o hk hr)
    · exact ⟨hk, hr⟩

/-- 처음부터 돌린 track 의 역치는 0.125 … 11.314 rpo (8개 평균) -/
theorem run_threshold_bounds (os : List Outcome) {sum cnt : Nat}
    (h : threshold wonCfg (run wonCfg (init wonCfg) os).1 = some (sum, cnt)) : cnt = 8 ∧ 125 * 8 ≤ sum ∧ sum ≤ 11314 * 8 :=
  threshold_bounds _ (run_bounds os (init wonCfg) (by decide) (by simp [init])).2 h

end SRD

import SMD.Rng
import SMD.Stair
import SMD.Exact

/-!
# QSMD 측정 — 앱 `js/analysis.js` `ConstRun.step` · `classifyConstant` 의 모형과 성질 (Claude, 2026-10-31)

공식 EasyQSMD 1.0 Electric 파일 60개를 run 씨앗으로 섞은 순서(`qsmdOrder`)대로 한 번씩 냄 (js 와 같은 순서로 상태를 바꿈):
* 유효 시행 → 다음 자리 (slot + 1) · 60번째 유효 시행 뒤 완료
* 기술적 실패 → 같은 자리(같은 파일)를 바로 다시 · 기술적 실패 10번이면 중단
* 분류: 기술적 실패면 'technical_failure' · 완료이고 유효 60이면 'complete' (점수 = 정답 / 60) · 그 밖 자료 부족
  (멈춤 `participant_aborted` 은 화면 입력이라 모형 밖. 정답 자리 = 파일의 정답 표 · 정오 = 응답 = 정답 자리 는 app.js 에서 — 표 자체는 Rng.lean · CrossCheck QTAB)

증명한 것: `cstep_invalid_same` (기술적 실패 뒤 같은 파일을 다시) · `cstep_valid_next` (유효 시행 뒤 다음 자리) ·
`crun_props` (유효 시행의 파일 = 순서의 앞에서부터 차례로, 건너뛰거나 되풀이하지 않음) ·
`crun_complete` (완료면 유효 60 · 유효 시행의 파일 목록 = 섞은 순서 그대로 · 파일 60개가 정확히 한 번씩 · 밀도 × 깊이 칸마다 정확히 6번) ·
`crun_ends` (응답이 69개면 반드시 끝남 — 유효 60 + 기술적 실패 10 − 1) · `score_only_complete` (점수는 완료일 때만, 분모 60)
-/

namespace SMD

inductive CStatus
  | running | complete | techFail
deriving DecidableEq, Repr, Inhabited

structure CSt where
  slot : Nat
  valid : Nat
  tech : Nat
  attempts : Nat
  status : CStatus
deriving Repr, Inhabited

def cinit : CSt := { slot := 0, valid := 0, tech := 0, attempts := 0, status := .running }

/-- 시행 기록: 자리 · 낸 파일 번호 · 유효 · 정답 · 유효 번호 · 다음 자리 · 뒤 상태 -/
structure CTr where
  slot : Nat
  idx : Nat
  isValid : Bool
  correct : Bool
  validNo : Nat
  nextSlot : Nat
  statusAfter : CStatus
deriving Repr, Inhabited

def cstepValid (total : Nat) (ord : List Nat) (s : CSt) (correct : Bool) : CSt × CTr :=
  ({ s with attempts := s.attempts + 1, valid := s.valid + 1, slot := s.slot + 1,
            status := if s.slot + 1 ≥ total then .complete else s.status },
   { slot := s.slot, idx := ord.getD s.slot 0, isValid := true, correct := correct, validNo := s.valid + 1,
     nextSlot := s.slot + 1, statusAfter := if s.slot + 1 ≥ total then .complete else s.status })

def cstepInvalid (maxTech : Nat) (ord : List Nat) (s : CSt) : CSt × CTr :=
  ({ s with attempts := s.attempts + 1, tech := s.tech + 1, status := if s.tech + 1 ≥ maxTech then .techFail else s.status },
   { slot := s.slot, idx := ord.getD s.slot 0, isValid := false, correct := false, validNo := 0,
     nextSlot := s.slot, statusAfter := if s.tech + 1 ≥ maxTech then .techFail else s.status })

/-- 한 시행 (js `ConstRun.step`, 진행 중일 때) -/
def cstep (total maxTech : Nat) (ord : List Nat) (s : CSt) : Outcome → CSt × CTr
  | .correct => cstepValid total ord s true
  | .wrong => cstepValid total ord s false
  | .invalid => cstepInvalid maxTech ord s

/-- 응답 순서대로 (끝나면 멈춤) -/
def crun (total maxTech : Nat) (ord : List Nat) : CSt → List Outcome → CSt × List CTr
  | s, [] => (s, [])
  | s, o :: os =>
    if s.status = .running then
      let r := cstep total maxTech ord s o
      let rest := crun total maxTech ord r.1 os
      (rest.1, r.2 :: rest.2)
    else (s, [])

/-- 유효 시행에서 낸 파일 번호들 (차례대로) -/
def validIdx (trs : List CTr) : List Nat := (trs.filter (·.isValid)).map (·.idx)
def nValidOf (trs : List CTr) : Nat := (trs.filter (·.isValid)).length
def nCorrectOf (trs : List CTr) : Nat := (trs.filter (fun t => t.isValid && t.correct)).length

inductive QStatus
  | complete | techFail | insufficient
deriving DecidableEq, Repr, Inhabited

/-- js `classifyConstant` 의 상태 -/
def qclassify (total : Nat) (s : CSt) : QStatus :=
  if s.status = .techFail then .techFail
  else if s.status = .complete ∧ s.valid = total then .complete
  else .insufficient

/-- 점수 (정답 수, 유효 수) — 완료일 때만 (js `pc = done ? k / n : null`) -/
def qscore (total : Nat) (s : CSt) (trs : List CTr) : Option (Nat × Nat) :=
  if qclassify total s = .complete then some (nCorrectOf trs, nValidOf trs) else none

/-! ## 성질 -/

theorem cstep_invalid_same (total maxTech : Nat) (ord : List Nat) (s : CSt) :
    (cstep total maxTech ord s .invalid).1.slot = s.slot ∧ (cstep total maxTech ord s .invalid).1.valid = s.valid ∧
    (cstep total maxTech ord s .invalid).2.isValid = false ∧ (cstep total maxTech ord s .invalid).2.idx = ord.getD s.slot 0 := by
  simp [cstep, cstepInvalid]

theorem cstep_valid_next (total maxTech : Nat) (ord : List Nat) (s : CSt) (o : Outcome) (ho : o ≠ .invalid) :
    (cstep total maxTech ord s o).1.slot = s.slot + 1 ∧ (cstep total maxTech ord s o).1.valid = s.valid + 1 ∧
    (cstep total maxTech ord s o).2.isValid = true ∧ (cstep total maxTech ord s o).2.idx = ord.getD s.slot 0 := by
  cases o <;> simp_all [cstep, cstepValid]

/-- 불변식: 자리 = 유효 수 · 시도 = 유효 + 기술적 실패 · 진행 중이면 두 상한 아래 · 완료면 유효 = total -/
def CInv (total maxTech : Nat) (s : CSt) : Prop :=
  s.slot = s.valid ∧ s.attempts = s.valid + s.tech ∧ (s.status = .running → s.valid < total ∧ s.tech < maxTech) ∧
  (s.status = .complete → s.valid = total)

theorem cinit_inv (total maxTech : Nat) (ht : 0 < total) (hm : 0 < maxTech) : CInv total maxTech cinit := by
  refine ⟨rfl, rfl, fun _ => ⟨ht, hm⟩, fun h => by simp [cinit] at h⟩

theorem cstep_inv {total maxTech : Nat} {ord : List Nat} {s : CSt} (o : Outcome) (hi : CInv total maxTech s)
    (hr : s.status = .running) : CInv total maxTech (cstep total maxTech ord s o).1 := by
  obtain ⟨h1, h2, h3, _⟩ := hi
  obtain ⟨hv, ht⟩ := h3 hr
  cases o with
  | invalid =>
    simp only [cstep, cstepInvalid, CInv]
    by_cases hc : s.tech + 1 ≥ maxTech
    · rw [if_pos hc]; exact ⟨h1, by omega, fun h => by simp at h, fun h => by simp at h⟩
    · rw [if_neg hc, hr]; exact ⟨h1, by omega, fun _ => ⟨hv, by omega⟩, fun h => by simp at h⟩
  | correct =>
    simp only [cstep, cstepValid, CInv]
    by_cases hc : s.slot + 1 ≥ total
    · rw [if_pos hc]; exact ⟨by omega, by omega, fun h => by simp at h, fun _ => by omega⟩
    · rw [if_neg hc, hr]; exact ⟨by omega, by omega, fun _ => ⟨by omega, ht⟩, fun h => by simp at h⟩
  | wrong =>
    simp only [cstep, cstepValid, CInv]
    by_cases hc : s.slot + 1 ≥ total
    · rw [if_pos hc]; exact ⟨by omega, by omega, fun h => by simp at h, fun _ => by omega⟩
    · rw [if_neg hc, hr]; exact ⟨by omega, by omega, fun _ => ⟨by omega, ht⟩, fun h => by simp at h⟩

theorem cstep_valid_mono (total maxTech : Nat) (ord : List Nat) (s : CSt) (o : Outcome) :
    s.valid ≤ (cstep total maxTech ord s o).1.valid := by
  cases o <;> simp [cstep, cstepValid, cstepInvalid]

/-- 불변식을 지키는 상태에서 돌리면: 불변식 유지 · 유효 수는 줄지 않음 ·
  유효 시행에서 낸 파일 = 순서의 자리 slot, slot + 1, … (늘어난 유효 수만큼) 차례 — 건너뛰거나 되풀이하지 않음 -/
theorem crun_props (total maxTech : Nat) (ord : List Nat) :
    ∀ (os : List Outcome) (s : CSt), CInv total maxTech s →
      CInv total maxTech (crun total maxTech ord s os).1 ∧ s.valid ≤ (crun total maxTech ord s os).1.valid ∧
      validIdx (crun total maxTech ord s os).2 =
        (List.range' s.slot ((crun total maxTech ord s os).1.valid - s.valid)).map (fun i => ord.getD i 0)
  | [], s, hi => by simp [crun, validIdx, hi]
  | o :: os, s, hi => by
    by_cases hr : s.status = .running
    · have hi' := cstep_inv (ord := ord) o hi hr
      obtain ⟨ih1, ih2, ih3⟩ := crun_props total maxTech ord os _ hi'
      simp only [crun]
      rw [if_pos hr]
      refine ⟨ih1, Nat.le_trans (cstep_valid_mono total maxTech ord s o) ih2, ?_⟩
      cases o with
      | invalid =>
        obtain ⟨e1, e2, e3, _⟩ := cstep_invalid_same total maxTech ord s
        rw [e1, e2] at ih3
        simp only [validIdx, List.filter_cons, e3] at ih3 ⊢
        simpa using ih3
      | correct =>
        obtain ⟨e1, e2, e3, e4⟩ := cstep_valid_next total maxTech ord s .correct (by simp)
        rw [e1, e2] at ih3
        rw [e2] at ih2
        simp only [validIdx, List.filter_cons, e3, if_true, List.map_cons, e4] at ih3 ⊢
        rw [ih3]
        have hk : (crun total maxTech ord (cstep total maxTech ord s .correct).1 os).1.valid - s.valid =
            ((crun total maxTech ord (cstep total maxTech ord s .correct).1 os).1.valid - (s.valid + 1)) + 1 := by omega
        rw [hk, List.range'_succ]
        simp
      | wrong =>
        obtain ⟨e1, e2, e3, e4⟩ := cstep_valid_next total maxTech ord s .wrong (by simp)
        rw [e1, e2] at ih3
        rw [e2] at ih2
        simp only [validIdx, List.filter_cons, e3, if_true, List.map_cons, e4] at ih3 ⊢
        rw [ih3]
        have hk : (crun total maxTech ord (cstep total maxTech ord s .wrong).1 os).1.valid - s.valid =
            ((crun total maxTech ord (cstep total maxTech ord s .wrong).1 os).1.valid - (s.valid + 1)) + 1 := by omega
        rw [hk, List.range'_succ]
        simp
    · simp only [crun]
      rw [if_neg hr]
      simp [validIdx, hi]

/-- 끝남: 불변식을 지키고 (유효 + 기술적 실패 + 남은 응답 + 1) ≥ total + maxTech 이면 끝난 상태로 멈춤 -/
theorem crun_ends_gen (total maxTech : Nat) (ord : List Nat) :
    ∀ (os : List Outcome) (s : CSt), CInv total maxTech s → total + maxTech ≤ s.valid + s.tech + os.length + 1 →
      (crun total maxTech ord s os).1.status ≠ .running
  | [], s, hi, hl => by
    simp only [crun]
    intro hr
    have := hi.2.2.1 hr
    simp at hl
    omega
  | o :: os, s, hi, hl => by
    by_cases hr : s.status = .running
    · simp only [crun]
      rw [if_pos hr]
      apply crun_ends_gen total maxTech ord os _ (cstep_inv o hi hr)
      simp only [List.length_cons] at hl
      cases o <;> simp [cstep, cstepValid, cstepInvalid] <;> omega
    · simp only [crun]
      rw [if_neg hr]
      exact hr

/-- 처음부터 응답이 69개(= 60 + 10 − 1) 이상이면 반드시 끝남 -/
theorem crun_ends (ord : List Nat) (os : List Outcome) (h : 69 ≤ os.length) :
    (crun 60 10 ord cinit os).1.status ≠ .running :=
  crun_ends_gen 60 10 ord os cinit (cinit_inv 60 10 (by decide) (by decide)) (by simp [cinit]; omega)

theorem range_map_getD (l : List Nat) : (List.range l.length).map (fun i => l.getD i 0) = l := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- 완료면: 유효 60 · 유효 시행에서 낸 파일 목록 = 섞은 순서 그대로 · 파일 60개가 정확히 한 번씩 · 밀도 × 깊이 칸마다 정확히 6번 -/
theorem crun_complete (x : Xo) (os : List Outcome) (h : (crun 60 10 (qsmdOrder x).1 cinit os).1.status = .complete) :
    (crun 60 10 (qsmdOrder x).1 cinit os).1.valid = 60 ∧
    validIdx (crun 60 10 (qsmdOrder x).1 cinit os).2 = (qsmdOrder x).1 ∧
    (∀ k, k < 60 → (validIdx (crun 60 10 (qsmdOrder x).1 cinit os).2).count k = 1) ∧
    (∀ c, c < 10 → ((validIdx (crun 60 10 (qsmdOrder x).1 cinit os).2).map cellOf).count c = 6) := by
  obtain ⟨h1, _, h3⟩ := crun_props 60 10 (qsmdOrder x).1 os cinit (cinit_inv 60 10 (by decide) (by decide))
  have hv : (crun 60 10 (qsmdOrder x).1 cinit os).1.valid = 60 := h1.2.2.2 h
  have hidx : validIdx (crun 60 10 (qsmdOrder x).1 cinit os).2 = (qsmdOrder x).1 := by
    rw [h3, hv]
    have hl := (qsmdOrder_each_once x 0 (by decide)).2
    have e := range_map_getD (qsmdOrder x).1
    rw [hl, List.range_eq_range'] at e
    simpa [cinit] using e
  refine ⟨hv, hidx, ?_, ?_⟩
  · intro k hk; rw [hidx]; exact (qsmdOrder_each_once x k hk).1
  · intro c hc; rw [hidx]; exact qsmdOrder_cell_count x c hc

/-- 점수는 완료(유효 60)일 때만 있고, 그때 분모는 60 -/
theorem score_only_complete (s : CSt) (trs : List CTr) (k n : Nat) (h : qscore 60 s trs = some (k, n)) :
    qclassify 60 s = .complete ∧ s.valid = 60 := by
  unfold qscore at h
  split at h
  · rename_i hc
    refine ⟨hc, ?_⟩
    unfold qclassify at hc
    split at hc
    · simp at hc
    · split at hc
      · rename_i hh; exact hh.2
      · simp at hc
  · simp at h

/-- 처음부터 돌린 run 의 유효 시행 수는 상태의 유효 수와 같음 (분모 = 60) -/
theorem crun_nValid (total maxTech : Nat) (ord : List Nat) :
    ∀ (os : List Outcome) (s : CSt), nValidOf (crun total maxTech ord s os).2 + s.valid = (crun total maxTech ord s os).1.valid
  | [], s => by simp [crun, nValidOf]
  | o :: os, s => by
    by_cases hr : s.status = .running
    · simp only [crun]
      rw [if_pos hr]
      have ih := crun_nValid total maxTech ord os (cstep total maxTech ord s o).1
      cases o <;> simp_all [nValidOf, cstep, cstepValid, cstepInvalid] <;> omega
    · simp only [crun]
      rw [if_neg hr]
      simp [nValidOf]

end SMD

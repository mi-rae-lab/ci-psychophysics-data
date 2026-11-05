import SRD.Stair
import SRD.Rng

/-!
# 임상 측정 진행 — 앱 `js/analysis.js` `ConstRun` 의 모형과 성질 (Claude, 2026-10-21)

Drennan 2014: 12 밀도 × 6 = 72시행을 섞은 순서대로. 이 앱: 기술적 실패 시행은 채점하지 않고 같은 밀도를 바로 다시.
js 와 같음: 유효 시행이면 자리(slot) + 1 (72 에 닿으면 끝), 무효면 기술적 실패 + 1 (10 이면 중단), 제시 밀도 = 순서[자리].

증명한 것:
* `cstep_invalid_same` 무효 시행 뒤에도 자리 · 제시 밀도가 그대로 (같은 밀도를 다시)
* `crun_inv` 진행 내내 유효 시행 수 = 자리, 시도 = 유효 + 기술적 실패
* `crun_cinv` 진행 중이면 자리 < 72, 끝났으면 자리 = 72
* `crun_valid_ks` 유효 시행의 밀도를 차례로 적으면 = 순서의 앞 (자리) 개
* `crun_complete_counts` 72 유효 시행으로 끝나면 유효 시행의 밀도가 섞은 순서 그대로 → 밀도마다 정확히 6번
-/

namespace SRD

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

structure CTr where
  slot : Nat
  k : Nat
  isValid : Bool
  correct : Bool
deriving Repr, Inhabited

def cinit : CSt := { slot := 0, valid := 0, tech := 0, attempts := 0, status := .running }

/-- 한 시행 (js `ConstRun.step`) — 제시 밀도 = 순서[자리] -/
def cstep (order : List Nat) (total maxTech : Nat) (s : CSt) : Outcome → CSt × CTr
  | .invalid =>
    ({ s with attempts := s.attempts + 1, tech := s.tech + 1, status := if s.tech + 1 ≥ maxTech then .techFail else s.status },
     { slot := s.slot, k := order.getD s.slot 0, isValid := false, correct := false })
  | o =>
    ({ s with attempts := s.attempts + 1, valid := s.valid + 1, slot := s.slot + 1,
               status := if s.slot + 1 ≥ total then .complete else s.status },
     { slot := s.slot, k := order.getD s.slot 0, isValid := true, correct := o == .correct })

def crun (order : List Nat) (total maxTech : Nat) : CSt → List Outcome → CSt × List CTr
  | s, [] => (s, [])
  | s, o :: os =>
    if s.status = .running then
      let r := cstep order total maxTech s o
      let rest := crun order total maxTech r.1 os
      (rest.1, r.2 :: rest.2)
    else (s, [])

theorem cstep_invalid_same (order : List Nat) (total maxTech : Nat) (s : CSt) :
    (cstep order total maxTech s .invalid).1.slot = s.slot ∧ (cstep order total maxTech s .invalid).2.k = order.getD s.slot 0 ∧
    (cstep order total maxTech s .invalid).2.isValid = false := by
  simp [cstep]

theorem cstep_valid_slot (order : List Nat) (total maxTech : Nat) (s : CSt) (o : Outcome) (h : o ≠ .invalid) :
    (cstep order total maxTech s o).1.slot = s.slot + 1 ∧ (cstep order total maxTech s o).2.isValid = true ∧
    (cstep order total maxTech s o).2.k = order.getD s.slot 0 := by
  cases o <;> simp_all [cstep]

/-- 불변식: 유효 시행 수 = 자리, 시도 = 유효 + 기술적 실패 -/
theorem crun_inv (order : List Nat) (total maxTech : Nat) : ∀ (os : List Outcome) (s : CSt),
    s.valid = s.slot → s.attempts = s.valid + s.tech →
    (crun order total maxTech s os).1.valid = (crun order total maxTech s os).1.slot ∧
    (crun order total maxTech s os).1.attempts = (crun order total maxTech s os).1.valid + (crun order total maxTech s os).1.tech
  | [], s, h1, h2 => by simp [crun, h1, h2]
  | o :: os, s, h1, h2 => by
    simp only [crun]
    split
    · apply crun_inv order total maxTech os
      · cases o <;> simp [cstep, h1]
      · cases o <;> simp [cstep] <;> omega
    · exact ⟨h1, h2⟩

/-- 진행 중이면 자리 < total, 끝났으면 자리 = total -/
def CInv (total : Nat) (s : CSt) : Prop := (s.status = .running → s.slot < total) ∧ (s.status = .complete → s.slot = total)

theorem cstep_cinv (order : List Nat) (total maxTech : Nat) (s : CSt) (o : Outcome) (h : CInv total s) (hr : s.status = .running) :
    CInv total (cstep order total maxTech s o).1 := by
  have hs := h.1 hr
  cases o
  · unfold CInv cstep
    by_cases hc : s.slot + 1 ≥ total <;> simp [hc, hr] <;> omega
  · unfold CInv cstep
    by_cases hc : s.slot + 1 ≥ total <;> simp [hc, hr] <;> omega
  · unfold CInv cstep
    by_cases ht : s.tech + 1 ≥ maxTech <;> simp [ht, hr, hs]

theorem crun_cinv (order : List Nat) (total maxTech : Nat) : ∀ (os : List Outcome) (s : CSt),
    CInv total s → CInv total (crun order total maxTech s os).1
  | [], s, h => by simpa [crun] using h
  | o :: os, s, h => by
    simp only [crun]
    split
    · rename_i hr
      exact crun_cinv order total maxTech os _ (cstep_cinv order total maxTech s o h hr)
    · exact h

theorem take_drop_succ (l : List Nat) (n m : Nat) (h : n < l.length) :
    (l.drop n).take (m + 1) = l.getD n 0 :: (l.drop (n + 1)).take m := by
  rw [List.drop_eq_getElem_cons h, List.take_succ_cons]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- 유효 시행의 밀도를 차례로 = 순서[s.slot …] 의 앞 (늘어난 자리 수) 개 (total ≤ 순서 길이) -/
theorem crun_valid_ks (order : List Nat) (total maxTech : Nat) (hT : total ≤ order.length) : ∀ (os : List Outcome) (s : CSt),
    CInv total s →
    ((crun order total maxTech s os).2.filter (·.isValid)).map (·.k)
      = ((order.drop s.slot).take ((crun order total maxTech s os).1.slot - s.slot)) ∧
    s.slot ≤ (crun order total maxTech s os).1.slot
  | [], s, _ => by simp [crun]
  | o :: os, s, hc => by
    simp only [crun]
    split
    · rename_i hr
      have hlt : s.slot < order.length := by have := hc.1 hr; omega
      have hc' := cstep_cinv order total maxTech s o hc hr
      have ih := crun_valid_ks order total maxTech hT os (cstep order total maxTech s o).1 hc'
      by_cases hv : o = .invalid
      · subst hv
        have hs : (cstep order total maxTech s .invalid).1.slot = s.slot := by simp [cstep]
        rw [hs] at ih
        refine ⟨?_, ih.2⟩
        have hiv : (cstep order total maxTech s .invalid).2.isValid = false := by simp [cstep]
        simp only [List.filter_cons, hiv, Bool.false_eq_true, ↓reduceIte]
        exact ih.1
      · have hs := cstep_valid_slot order total maxTech s o hv
        rw [hs.1] at ih
        have ih2 := ih.2
        have hs1 := hs.1
        refine ⟨?_, by dsimp only; omega⟩
        simp only [List.filter_cons, hs.2.1, ↓reduceIte, List.map_cons, hs.2.2]
        rw [ih.1]
        rw [show (crun order total maxTech (cstep order total maxTech s o).1 os).1.slot - s.slot
            = ((crun order total maxTech (cstep order total maxTech s o).1 os).1.slot - (s.slot + 1)) + 1 by omega]
        rw [take_drop_succ order s.slot _ hlt]
    · simp

/-- 72 유효 시행으로 끝나면(상태 ‘끝남’) 유효 시행의 밀도 = 섞은 순서 그대로 → 밀도 0 … 11 이 정확히 6번씩 -/
theorem crun_complete_counts (x : Xo) (os : List Outcome) (k : Nat) (hk : k < 12)
    (h : (crun (clinOrder x).1 72 10 cinit os).1.status = .complete) :
    (((crun (clinOrder x).1 72 10 cinit os).2.filter (·.isValid)).map (·.k)).count k = 6 := by
  have hlen := (clinOrder_count x k hk).2
  have hci : CInv 72 cinit := ⟨fun _ => by simp [cinit], fun h => by simp [cinit] at h⟩
  have hv := crun_valid_ks (clinOrder x).1 72 10 (by omega) os cinit hci
  have hfin := (crun_cinv (clinOrder x).1 72 10 os cinit hci).2 h
  rw [hv.1, hfin]
  simp only [cinit, List.drop_zero, Nat.sub_zero]
  rw [List.take_of_length_le (by omega)]
  exact (clinOrder_count x k hk).1

end SRD

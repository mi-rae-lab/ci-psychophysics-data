import SRD.Arith

/-!
# Won 회기 요약 — 앱 `js/analysis.js` `wonSummary` 의 판정 (Claude, 2026-10-21)

track 마다 결과 종류: 숫자(milli 합 · 개수) · ‘< 0.125’ · 쉬운 끝 막힘 · ‘> 11.314’ · 어려운 끝 막힘 · 결정 안 됨(멈춤 · 실패 · 신뢰성 부족 · 절차 어긋남 …).
js 와 같음: 결정된 track 이 6개 미만이면 잠정 · 6개 이상이면 앞의 6개로 — 모두 숫자면 확정(6개 평균, 정확한 유리수) ·
모두 쉬운 끝 쪽이면 ‘< 0.125’(모두 확인) / 쉬운 끝 쪽 · 모두 어려운 끝 쪽이면 ‘> 11.314’ / 어려운 끝 쪽 · 그 밖은 섞임(평균 안 냄).

증명한 것: `final_iff` (확정 ⇔ 결정된 track 6개 이상이고 앞 6개가 모두 숫자) · `provisional_iff` (잠정 ⇔ 결정된 track < 6) ·
`final_value` (확정 값 = 앞 6개 역치의 산술 평균) · `mixed_has_num` (섞임이면 앞 6개에 숫자와 숫자 아님이 함께)
-/

namespace SRD

inductive TKind
  | num (sum cnt : Nat) | below | easy | above | hard | none
deriving DecidableEq, Repr, Inhabited

inductive SState
  | provisional | final | below | low | above | high | mixed
deriving DecidableEq, Repr, Inhabited

def TKind.isDet : TKind → Bool | .none => false | _ => true
def TKind.isNum : TKind → Bool | .num _ _ => true | _ => false
def TKind.isLow : TKind → Bool | .below => true | .easy => true | _ => false
def TKind.isHigh : TKind → Bool | .above => true | .hard => true | _ => false
def TKind.isBelow : TKind → Bool | .below => true | _ => false
def TKind.isAbove : TKind → Bool | .above => true | _ => false

/-- track 역치 (js `Q.of(sumMilli, 1000 · count)`) -/
def TKind.thr : TKind → Rat
  | .num s c => (s : Rat) / ((1000 * c : Nat) : Rat)
  | _ => 0

def sumR : List Rat → Rat
  | [] => 0
  | x :: xs => x + sumR xs

/-- 회기 요약 (js `wonSummary`, need = 6) -/
def wonSummary (ts : List TKind) (need : Nat := 6) : SState × Option Rat :=
  let det := ts.filter (·.isDet)
  if det.length < need then (.provisional, none)
  else
    let use := det.take need
    if use.all (·.isNum) then (.final, some (sumR (use.map (·.thr)) / (need : Rat)))
    else if use.all (·.isLow) then (if use.all (·.isBelow) then .below else .low, none)
    else if use.all (·.isHigh) then (if use.all (·.isAbove) then .above else .high, none)
    else (.mixed, none)

theorem provisional_iff (ts : List TKind) : (wonSummary ts).1 = .provisional ↔ (ts.filter (·.isDet)).length < 6 := by
  unfold wonSummary
  by_cases h : (ts.filter (·.isDet)).length < 6
  · simp [h]
  · simp only [h, ↓reduceIte, iff_false]
    split
    · simp
    · split
      · split <;> simp
      · split
        · split <;> simp
        · simp

theorem final_iff (ts : List TKind) :
    (wonSummary ts).1 = .final ↔ 6 ≤ (ts.filter (·.isDet)).length ∧ ((ts.filter (·.isDet)).take 6).all (·.isNum) = true := by
  unfold wonSummary
  by_cases h : (ts.filter (·.isDet)).length < 6
  · simp only [h, ↓reduceIte]
    constructor
    · intro h'; cases h'
    · intro ⟨h1, _⟩; omega
  · simp only [h, ↓reduceIte]
    by_cases hn : ((ts.filter (·.isDet)).take 6).all (·.isNum) = true
    · simp only [hn, ↓reduceIte, true_iff]; exact ⟨by omega, trivial⟩
    · simp only [hn, ↓reduceIte, Bool.false_eq_true, and_false, iff_false]
      split
      · split <;> simp
      · split
        · split <;> simp
        · simp

/-- 확정 값 = 앞 6개 역치의 산술 평균 -/
theorem final_value (ts : List TKind) (v : Rat) (h : (wonSummary ts).2 = some v) :
    v = sumR (((ts.filter (·.isDet)).take 6).map (·.thr)) / 6 := by
  unfold wonSummary at h
  by_cases h1 : (ts.filter (·.isDet)).length < 6
  · simp [h1] at h
  · simp only [h1, ↓reduceIte] at h
    by_cases hn : ((ts.filter (·.isDet)).take 6).all (·.isNum) = true
    · simp only [hn, ↓reduceIte, Option.some.injEq] at h
      rw [← h]; rfl
    · simp only [hn, ↓reduceIte, Bool.false_eq_true] at h
      split at h
      · split at h <;> cases h
      · split at h
        · split at h <;> cases h
        · cases h

/-- 섞임이면 앞 6개가 모두 숫자도, 모두 쉬운 끝 쪽도, 모두 어려운 끝 쪽도 아님 -/
theorem mixed_has_num (ts : List TKind) (h : (wonSummary ts).1 = .mixed) :
    ((ts.filter (·.isDet)).take 6).all (·.isNum) = false ∧ ((ts.filter (·.isDet)).take 6).all (·.isLow) = false ∧
    ((ts.filter (·.isDet)).take 6).all (·.isHigh) = false := by
  unfold wonSummary at h
  by_cases h1 : (ts.filter (·.isDet)).length < 6
  · simp [h1] at h
  · simp only [h1, ↓reduceIte] at h
    by_cases hn : ((ts.filter (·.isDet)).take 6).all (·.isNum) = true
    · simp [hn] at h
    · by_cases hl : ((ts.filter (·.isDet)).take 6).all (·.isLow) = true
      · simp only [hn, hl, ↓reduceIte, Bool.false_eq_true] at h; split at h <;> cases h
      · by_cases hh : ((ts.filter (·.isDet)).take 6).all (·.isHigh) = true
        · simp only [hn, hl, hh, ↓reduceIte, Bool.false_eq_true] at h; split at h <;> cases h
        · simp_all

end SRD

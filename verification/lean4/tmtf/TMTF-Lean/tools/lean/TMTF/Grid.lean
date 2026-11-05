import TMTF.Basic

/-!
# 변조 주파수 격자 · 구간 길이 · 정답 자리 — 앱 `js/protocols.js` · `js/app.js` (Claude, 2026-10-24)

* `fine_length` · `fine_mem_iff` · `fine_sorted`  3.2 의 5 Hz 간격 격자 = 5, 10, …, 300 (60칸, 오름차순, 겹침 없음)
* `papers_in_fine`         논문 주파수(Won 7 · Park 6 · De Ruiter 7)는 모두 격자 안 → 논문 주파수는 하나도 빠지지 않음
* `off_paper_counts`       격자 60칸 중 논문 밖: Won 기준 53칸 · De Ruiter 기준 53칸
* `interval_samples`       구간 표본 수 N = round(fs·길이): 44.1 kHz · 48 kHz 에서 1 s · 0.5 s 모두 정확히 정수
                           (쉼 0.5 · 0.8 · 1 s 도) → 버퍼 길이 = 정확히 그 길이, Won/Park 의 ‘이어 붙임’(쉼 0)은 틈 · 겹침 0 표본
* `cycles_min`             가장 느린 5 Hz 도 한 구간에 2.5 주기(De Ruiter 0.5 s) · 5 주기(Won/Park 1 s) 이상
* `countMod3_closed` · `target_counts`
                           정답 자리 = crypto 32비트 난수 u 를 `u % n`. u 가 0 … 2³²−1 에서 고르면
                           2구간: 두 자리 정확히 2³¹ 개씩(완전 균등), 3구간: 자리 0 이 1,431,655,766 개 · 자리 1 · 2 가 1,431,655,765 개
                           → 자리 0 이 2/(3·2³²) ≈ 1.6×10⁻¹⁰ 만큼 더 자주 (무시할 크기, 정확한 값)
-/

namespace TMTF

/-- 5 Hz 간격 격자 (js `FINE_FMS`) -/
def fineFms : List Nat := (List.range 60).map (fun i => (i + 1) * 5)
/-- Won 2011 실험 1 -/
def wonFms : List Nat := [10, 50, 75, 100, 150, 200, 300]
/-- Park 2015 -/
def parkFms : List Nat := [10, 50, 100, 150, 200, 300]
/-- De Ruiter 2015 -/
def drFms : List Nat := [5, 10, 50, 75, 100, 150, 200]

theorem fine_length : fineFms.length = 60 := by decide

theorem fine_mem_iff (f : Nat) : f ∈ fineFms ↔ (5 ≤ f ∧ f ≤ 300 ∧ f % 5 = 0) := by
  unfold fineFms
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h; exact ⟨f / 5 - 1, by omega, by omega⟩

theorem fine_sorted : fineFms.Pairwise (· < ·) := by decide

theorem papers_in_fine :
    (∀ f ∈ wonFms, f ∈ fineFms) ∧ (∀ f ∈ parkFms, f ∈ wonFms) ∧ (∀ f ∈ drFms, f ∈ fineFms) := by decide

theorem off_paper_counts :
    (fineFms.filter (fun f => f ∉ wonFms)).length = 53 ∧ (fineFms.filter (fun f => f ∉ drFms)).length = 53 := by decide

/-- js `Math.round(x)` = ⌊x + 1/2⌋ -/
def jsRound (x : Rat) : Int := (x + 1 / 2).floor

theorem interval_samples :
    jsRound (44100 * 1) = 44100 ∧ jsRound (48000 * 1) = 48000 ∧
    jsRound (44100 * (1 / 2)) = 22050 ∧ jsRound (48000 * (1 / 2)) = 24000 ∧
    jsRound (44100 * (8 / 10)) = 35280 ∧ jsRound (48000 * (8 / 10)) = 38400 := by decide +kernel

/-- 표본 수 / fs = 길이 (정확히) → 버퍼가 정확히 그 길이만큼 나감 -/
theorem interval_exact :
    ((44100 : Int) : Rat) / 44100 = 1 ∧ ((48000 : Int) : Rat) / 48000 = 1 ∧
    ((22050 : Int) : Rat) / 44100 = 1 / 2 ∧ ((24000 : Int) : Rat) / 48000 = 1 / 2 := by decide +kernel

theorem cycles_min : ∀ f ∈ fineFms, (5 : Rat) / 2 ≤ (f : Rat) * (1 / 2) ∧ (5 : Rat) ≤ (f : Rat) * 1 := by decide +kernel

/-- 0 … M−1 중 `u % 3 = r` 인 것의 수 -/
def countMod3 (M r : Nat) : Nat := ((List.range M).filter (fun u => u % 3 = r)).length

theorem countMod3_succ (M r : Nat) : countMod3 (M + 1) r = countMod3 M r + (if M % 3 = r then 1 else 0) := by
  unfold countMod3
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : M % 3 = r <;> simp [h]

theorem countMod3_closed (M r : Nat) (hr : r < 3) : countMod3 M r = M / 3 + (if r < M % 3 then 1 else 0) := by
  induction M with
  | zero => simp [countMod3]
  | succ M ih =>
    rw [countMod3_succ, ih]
    by_cases h1 : M % 3 = r <;> by_cases h2 : r < M % 3 <;> by_cases h3 : r < (M + 1) % 3 <;> simp [h1, h2, h3] <;> omega

/-- 0 … M−1 중 짝수 · 홀수의 수 (2구간) -/
def countMod2 (M r : Nat) : Nat := ((List.range M).filter (fun u => u % 2 = r)).length

theorem countMod2_succ (M r : Nat) : countMod2 (M + 1) r = countMod2 M r + (if M % 2 = r then 1 else 0) := by
  unfold countMod2
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : M % 2 = r <;> simp [h]

theorem countMod2_closed (M r : Nat) (hr : r < 2) : countMod2 M r = M / 2 + (if r < M % 2 then 1 else 0) := by
  induction M with
  | zero => simp [countMod2]
  | succ M ih =>
    rw [countMod2_succ, ih]
    by_cases h1 : M % 2 = r <;> by_cases h2 : r < M % 2 <;> by_cases h3 : r < (M + 1) % 2 <;> simp [h1, h2, h3] <;> omega

theorem target_counts :
    countMod2 4294967296 0 = 2147483648 ∧ countMod2 4294967296 1 = 2147483648 ∧
    countMod3 4294967296 0 = 1431655766 ∧ countMod3 4294967296 1 = 1431655765 ∧ countMod3 4294967296 2 = 1431655765 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [countMod2_closed _ _ (by decide)]; decide
  · rw [countMod2_closed _ _ (by decide)]; decide
  · rw [countMod3_closed _ _ (by decide)]; decide
  · rw [countMod3_closed _ _ (by decide)]; decide
  · rw [countMod3_closed _ _ (by decide)]; decide

/-- 3구간 자리 0 의 확률 − 1/3 = 2/(3·2³²) -/
theorem target_bias3 : (1431655766 : Rat) / 4294967296 - 1 / 3 = 2 / (3 * 4294967296) := by decide +kernel

end TMTF

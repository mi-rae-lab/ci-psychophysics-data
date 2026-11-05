import SMRT.Stair

/-!
# 결과 화면 · 보고서의 요약 계산과 판정 (Claude, 2026-10-22)

저장된 역치는 소수 넷째 자리 값(`+m.toFixed(4)`)이라 정수 k = thr·10⁴ 로 다룸 (`thr4` 와 같음).
앱 `js/app.js` 의 부동소수 계산:
* `mean = a => a.reduce((s, x) => s + x, 0) / a.length`, `sdv` = 표본 SD (n−1), 화면 `toFixed(2)`
* 회기 비교: `cd = 1.96 * RETEST_SD * Math.sqrt(1/a.n + 1/b.n)` (RETEST_SD 0.7, Aronoff 2016), `Math.abs(dlt) > cd` 이면 ‘우연 변동 범위 밖’
* DiNino 2018: `Math.abs(tests[0].thr − tests[1].thr) > 1` 이면 본 측정 한 번 더 (finishTrack · 기록 점검 completeness)
* 해석 구역: `m < AM_CUE_RPO`(2) · `m > lim.alias`(Cochlear·AB 2, MED-EL 1.1) · `m <= 0.3`

명세는 유리수(평균 = Σk / (n·10⁴)), 구현은 정수 비교 — 모든 입력에서 같음을 증명:
`amZone_iff` · `limitZone_iff` · `floorZone_iff` · `dinino_iff` · `beyond_iff` (제곱 꼴: |Δ| > c·√w ⇔ Δ² > c²·w, 양변 ≥ 0).
반올림: `mean2` = 100·평균에 가장 가까운 정수, `sd2` · `cd2` = √ 반올림(`sqrtRound_spec`), `isTie` · `sqTie` = 정확히 .5 인 경우.
-/

namespace SMRT

/-- 평균 (유리수 명세): Σk / (n · 10⁴) RPO -/
def meanQ (ks : List Nat) : Rat := (ks.sum : Rat) / ((ks.length : Rat) * 10000)

/-- 100·평균에 가장 가까운 정수 (화면의 소수 둘째 자리) -/
def mean2 (ks : List Nat) : Nat := roundDiv ks.sum (100 * ks.length)
def mean2Tie (ks : List Nat) : Bool := isTie ks.sum (100 * ks.length)

/-- 표본 SD (n−1) 의 둘째 자리 정수: √((n·Q − S²) / (10⁴·n·(n−1))) 에 가장 가까운 정수 -/
def sd2Arg (ks : List Nat) : Nat × Nat :=
  (ks.length * (ks.map (fun x => x * x)).sum - ks.sum * ks.sum, 10000 * ks.length * (ks.length - 1))
def sd2 (ks : List Nat) : Nat := sqrtRound (sd2Arg ks).1 (sd2Arg ks).2
def sd2Tie (ks : List Nat) : Bool := sqTie (sd2Arg ks).1 (sd2Arg ks).2

/-- 두 회기 평균의 차의 분자: Δ = m₂ − m₁ = (S₂·n₁ − S₁·n₂) / (n₁·n₂·10⁴) -/
def diffNum (k1 k2 : List Nat) : Int := (k2.sum * k1.length : Nat) - (k1.sum * k2.length : Nat)

/-- |Δ|·100 에 가장 가까운 정수, 부호 따로 -/
def diff2 (k1 k2 : List Nat) : Int :=
  let d := diffNum k1 k2
  let r := (roundDiv d.natAbs (100 * k1.length * k2.length) : Int)
  if d < 0 then -r else r
def diff2Tie (k1 k2 : List Nat) : Bool := isTie (diffNum k1 k2).natAbs (100 * k1.length * k2.length)

/-- 우연 변동 범위 밖: Δ² > (1.96·0.7)²·(1/n₁ + 1/n₂) ⇔ D² > 188 238 400·(n₁+n₂)·n₁·n₂ (D = diffNum) -/
def beyondB (k1 k2 : List Nat) : Bool :=
  decide ((188238400 : Int) * ((k1.length + k2.length : Nat) : Int) * (k1.length : Int) * (k2.length : Int) < diffNum k1 k2 * diffNum k1 k2)

/-- 우연 범위 ±1.96·0.7·√(1/n₁ + 1/n₂) 의 둘째 자리 정수: √(1 882 384·(n₁+n₂) / (100·n₁·n₂)) -/
def cd2 (n1 n2 : Nat) : Nat := sqrtRound (1882384 * (n1 + n2)) (100 * n1 * n2)
def cd2Tie (n1 n2 : Nat) : Bool := sqTie (1882384 * (n1 + n2)) (100 * n1 * n2)

/-- DiNino 2018: 두 역치가 1 RPO 넘게 다름 (k 는 thr·10⁴) -/
def dininoB (k1 k2 : Nat) : Bool := decide (10000 < (if k1 ≤ k2 then k2 - k1 else k1 - k2))

/-- 해석 구역: 평균 < 2 RPO (한 채널 진폭 변조 단서, Archer-Boyd 2018) -/
def amZoneB (ks : List Nat) : Bool := decide (ks.sum < 20000 * ks.length)
/-- 평균 > 장치 한계 (aliasK = 한계·10⁴: Cochlear·AB 20000, MED-EL 11000 — Winn & O'Brien 2022) -/
def limitZoneB (ks : List Nat) (aliasK : Nat) : Bool := decide (aliasK * ks.length < ks.sum)
/-- 평균 ≤ 0.3 RPO (바닥 근처) -/
def floorZoneB (ks : List Nat) : Bool := decide (ks.sum ≤ 3000 * ks.length)

/-! ## 명세와 같음 -/

theorem len_pos_q {ks : List Nat} (h : ks ≠ []) : (0 : Rat) < (ks.length : Rat) * 10000 := by
  have hl : 0 < ks.length := List.length_pos_iff.mpr h
  have : (0 : Rat) < (ks.length : Rat) := Rat.natCast_pos.mpr hl
  exact Rat.mul_pos this (by decide)

/-- 평균 < 2 RPO ⇔ Σk < 20000·n -/
theorem amZone_iff (ks : List Nat) (h : ks ≠ []) : amZoneB ks = true ↔ meanQ ks < 2 := by
  unfold amZoneB meanQ
  rw [Rat.div_lt_iff (len_pos_q h)]
  have e : (2 : Rat) * ((ks.length : Rat) * 10000) = ((20000 * ks.length : Nat) : Rat) := by
    rw [Rat.natCast_mul]; grind
  rw [e, Rat.natCast_lt_natCast]
  simp

/-- 평균 > 한계 ⇔ aliasK·n < Σk -/
theorem limitZone_iff (ks : List Nat) (aliasK : Nat) (h : ks ≠ []) :
    limitZoneB ks aliasK = true ↔ (aliasK : Rat) / 10000 < meanQ ks := by
  unfold limitZoneB meanQ
  rw [Rat.lt_div_iff (len_pos_q h)]
  have e : (aliasK : Rat) / 10000 * ((ks.length : Rat) * 10000) = ((aliasK * ks.length : Nat) : Rat) := by
    rw [Rat.natCast_mul]; grind
  rw [e, Rat.natCast_lt_natCast]
  simp

/-- 평균 ≤ 0.3 RPO ⇔ Σk ≤ 3000·n -/
theorem floorZone_iff (ks : List Nat) (h : ks ≠ []) : floorZoneB ks = true ↔ meanQ ks ≤ 3 / 10 := by
  unfold floorZoneB meanQ
  rw [← Rat.not_lt, Rat.lt_div_iff (len_pos_q h)]
  have e : (3 : Rat) / 10 * ((ks.length : Rat) * 10000) = ((3000 * ks.length : Nat) : Rat) := by
    rw [Rat.natCast_mul]; grind
  rw [e, Rat.natCast_lt_natCast]
  simp

/-- DiNino: 정수 판정 ⇔ |t₁ − t₂| > 1 RPO (t = k/10⁴) -/
theorem dinino_iff (k1 k2 : Nat) :
    dininoB k1 k2 = true ↔ (1 < (k1 : Rat) / 10000 - (k2 : Rat) / 10000 ∨ 1 < (k2 : Rat) / 10000 - (k1 : Rat) / 10000) := by
  have key : ∀ a b : Nat, (1 < (a : Rat) / 10000 - (b : Rat) / 10000 ↔ b + 10000 < a) := by
    intro a b
    have e : (a : Rat) / 10000 - (b : Rat) / 10000 = ((a : Rat) - (b : Rat)) / 10000 := by grind
    rw [e, Rat.lt_div_iff (by decide), Rat.one_mul]
    constructor
    · intro hh
      have : ((b + 10000 : Nat) : Rat) < (a : Rat) := by rw [Rat.natCast_add]; grind
      exact Rat.natCast_lt_natCast.mp this
    · intro hh
      have := Rat.natCast_lt_natCast.mpr hh
      rw [Rat.natCast_add] at this
      grind
  rw [key, key]
  unfold dininoB
  by_cases hk : k1 ≤ k2 <;> simp [hk] <;> omega

/-- 회기 비교: 정수 판정 ⇔ (1.96·0.7)²·(1/n₁ + 1/n₂) < Δ² (Δ = 평균₂ − 평균₁) -/
theorem beyond_iff (k1 k2 : List Nat) (h1 : k1 ≠ []) (h2 : k2 ≠ []) :
    beyondB k1 k2 = true ↔
      ((343 : Rat) / 250) ^ 2 * (1 / (k1.length : Rat) + 1 / (k2.length : Rat)) < (meanQ k2 - meanQ k1) * (meanQ k2 - meanQ k1) := by
  have hn1 : 0 < k1.length := List.length_pos_iff.mpr h1
  have hn2 : 0 < k2.length := List.length_pos_iff.mpr h2
  have q1 : (0 : Rat) < (k1.length : Rat) := Rat.natCast_pos.mpr hn1
  have q2 : (0 : Rat) < (k2.length : Rat) := Rat.natCast_pos.mpr hn2
  have q1' : (k1.length : Rat) ≠ 0 := Rat.ne_of_gt q1
  have q2' : (k2.length : Rat) ≠ 0 := Rat.ne_of_gt q2
  -- Δ = D / (n₁ n₂ 10⁴)
  have hD : meanQ k2 - meanQ k1 = ((diffNum k1 k2 : Int) : Rat) / ((k1.length : Rat) * (k2.length : Rat) * 10000) := by
    unfold meanQ diffNum
    rw [Rat.intCast_sub, Rat.intCast_natCast, Rat.intCast_natCast, Rat.natCast_mul, Rat.natCast_mul]
    grind
  have hP : (0 : Rat) < (k1.length : Rat) * (k2.length : Rat) * 10000 := Rat.mul_pos (Rat.mul_pos q1 q2) (by decide)
  have hP' : (k1.length : Rat) * (k2.length : Rat) * 10000 ≠ 0 := Rat.ne_of_gt hP
  have hM := Rat.mul_pos hP hP
  rw [hD, ← Rat.mul_lt_mul_right hM]
  -- 양변 × (n₁ n₂ 10⁴)²: 왼쪽 = 188 238 400·(n₁+n₂)·n₁·n₂, 오른쪽 = D²
  have eL : ((343 : Rat) / 250) ^ 2 * (1 / (k1.length : Rat) + 1 / (k2.length : Rat)) *
      (((k1.length : Rat) * (k2.length : Rat) * 10000) * ((k1.length : Rat) * (k2.length : Rat) * 10000))
      = (((188238400 : Int) * ((k1.length + k2.length : Nat) : Int) * (k1.length : Int) * (k2.length : Int) : Int) : Rat) := by
    simp only [Rat.intCast_mul, Rat.intCast_natCast, Rat.natCast_add, Rat.intCast_ofNat]
    grind
  have eR : ((diffNum k1 k2 : Int) : Rat) / ((k1.length : Rat) * (k2.length : Rat) * 10000) *
      (((diffNum k1 k2 : Int) : Rat) / ((k1.length : Rat) * (k2.length : Rat) * 10000)) *
      (((k1.length : Rat) * (k2.length : Rat) * 10000) * ((k1.length : Rat) * (k2.length : Rat) * 10000))
      = ((diffNum k1 k2 * diffNum k1 k2 : Int) : Rat) := by
    rw [Rat.intCast_mul]
    grind
  rw [eL, eR, Rat.intCast_lt_intCast]
  simp [beyondB]

/-! ## 반올림 값의 성질 (화면의 소수 둘째 자리) -/

/-- mean2 = 100·평균에 가장 가까운 정수: M − ½ ≤ 100·평균 < M + ½ (정수 꼴) -/
theorem mean2_spec (ks : List Nat) (h : ks ≠ []) :
    2 * mean2 ks * (100 * ks.length) ≤ 2 * ks.sum + 100 * ks.length ∧
    2 * ks.sum + 100 * ks.length < 2 * mean2 ks * (100 * ks.length) + 2 * (100 * ks.length) :=
  roundDiv_spec _ _ (by have := List.length_pos_iff.mpr h; omega)

/-- cd2 = 100·(1.96·0.7·√(1/n₁+1/n₂)) 에 가장 가까운 정수 — (2k−1)²·100n₁n₂ ≤ 4·1 882 384·(n₁+n₂) < (2k+1)²·100n₁n₂ -/
theorem cd2_spec (n1 n2 : Nat) (h1 : 0 < n1) (h2 : 0 < n2) :
    sqLe (1882384 * (n1 + n2)) (100 * n1 * n2) (cd2 n1 n2) = true ∧
    sqLe (1882384 * (n1 + n2)) (100 * n1 * n2) (cd2 n1 n2 + 1) = false :=
  sqrtRound_spec _ _ (Nat.mul_pos (Nat.mul_pos (by decide) h1) h2)

/-- sd2 = 100·SD 에 가장 가까운 정수 (n ≥ 2) -/
theorem sd2_spec (ks : List Nat) (h : 2 ≤ ks.length) :
    sqLe (sd2Arg ks).1 (sd2Arg ks).2 (sd2 ks) = true ∧ sqLe (sd2Arg ks).1 (sd2Arg ks).2 (sd2 ks + 1) = false := by
  apply sqrtRound_spec
  unfold sd2Arg
  exact Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (by omega)

end SMRT

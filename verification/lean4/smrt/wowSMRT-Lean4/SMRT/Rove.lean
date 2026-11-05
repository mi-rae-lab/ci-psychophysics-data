import SMRT.Loud

/-!
# 크기 로빙 — 앱 `js/app.js` 의 ROVE · ROVE_DAYS · roveVals · randUnbiased 모형, 보호 범위의 정확한 값 (Claude, 2026-11-02 — 와우SMRT 1.2)

값은 반 dB 단위 정수 (js 값 × 2): B −4 … +4 dB (1 dB 간격 9값) · C −7.5 … +7.5 dB (16값). (1.3, 2026-11-02: 로빙 없는 A 와 1.2 의 날마다 섞는 순서는 앱에서 뺐음 → 여기서도 뺌)

증명한 것:
* `roveH_len` · `roveH_symm` · `roveH_sum` · `roveH_step` 값 수 9 · 16, 0 을 가운데로 대칭(평균 0), 1 dB 간격, 끝 ±4 · ±7.5 dB
* `seq_counts` 1.3 로빙 단독 회기 순서 B C C B B C (js ROVE_SEQ): 조건마다 회기 3번, 연습 1 + 본 3 이면 조건마다 본 측정 9번 ·
  `seq_pos` 회기 자리 합 B 10 · C 11 (6번으로는 똑같이 나눌 수 없어 평균 자리가 1/3 회기 다름 — 검증.md §9-3 에 적음)
* `ru_uniform` 치우침 없는 뽑기 (js `randUnbiased(n)`): 받아들이는 32비트 값 [0, lim) 중 나머지가 r 인 값은 r 마다 정확히 lim/n 개
  (lim = 2³² − 2³² mod n) · `ruLim_ge` 버리는 값은 n − 1 개 이하
* 보호 범위 (검증.md §9 · §9-2, `tools/rove_protect.py` 와 같은 규칙): 소리 크기만 쓰는 잡음 없는 관찰자의 맞힘 수를
  세 구간 이득 전수 열거로 정확히 셈 — 규칙 L(가장 큰 소리) · 규칙 D(차이가 가장 작은 쌍을 버림, 파이썬 `rove_protect.py` 의
  동점 나눔 그대로). `protect_C_L` 등: 정답률 1/2 · 0.7071 을 넘는 크기 차이(반 dB 사이)와 `won15_eq_C` (Won 2011 15 dB = C).
* `pairSum_B` · `pairSum_C` 두 구간 크기 차이 평균 (n² − 1)/(3n) dB: B 80/27 (2.96) · C 255/48 (5.31) — js loud.js 주석 · 검증.md §9-1.
-/

namespace SMRT

/-! ## 값 집합 -/

/-- js `roveVals(ROVE[c])` × 2 (반 dB 단위) -/
def roveH (c : Char) : List Int :=
  if c = 'B' then (List.range 9).map (fun (k : Nat) => (-8 : Int) + 2 * (k : Int))
  else if c = 'C' then (List.range 16).map (fun (k : Nat) => (-15 : Int) + 2 * (k : Int))
  else []

/-- Won 2011 실험 1 의 15 dB 로빙 49 … 64 dBA (반 dB 단위) · 7 dB 로빙 57 … 64 dBA -/
def won15H : List Int := (List.range 16).map (fun (k : Nat) => (98 : Int) + 2 * (k : Int))
def won7H : List Int := (List.range 8).map (fun (k : Nat) => (114 : Int) + 2 * (k : Int))

theorem roveH_len : (roveH 'B').length = 9 ∧ (roveH 'C').length = 16 ∧ roveH 'A' = [] := by decide +kernel

theorem roveH_symm : ∀ c ∈ ['B', 'C'], (roveH c).map (fun v => -v) = (roveH c).reverse := by decide +kernel

theorem roveH_sum : ∀ c ∈ ['B', 'C'], (roveH c).sum = 0 := by decide +kernel

/-- 이웃한 값의 차이는 모두 2 (1 dB), 끝은 B ±8 (±4 dB) · C ±15 (±7.5 dB) -/
theorem roveH_step : ∀ c ∈ ['B', 'C'], ((roveH c).zip (roveH c).tail).all (fun p => p.2 - p.1 == 2) = true := by decide +kernel

theorem roveH_ends : (roveH 'B').head? = some (-8) ∧ (roveH 'B').getLast? = some 8 ∧
    (roveH 'C').head? = some (-15) ∧ (roveH 'C').getLast? = some 15 := by decide +kernel

/-! ## 1.3 로빙 단독 회기 순서 -/

/-- js `ROVE_SEQ` (이 참가자 · 귀의 n번째 로빙 회기 → 조건) -/
def roveSeq : List Char := ['B', 'C', 'C', 'B', 'B', 'C']

/-- js `ROVE_PLAN` (연습, 본) — 공식 기본(Landsberger 2018 · SLRM 2019)과 같은 틀 -/
def rovePlan : Nat × Nat := (1, 3)

/-- 조건 ch 가 놓인 자리(1 … 6)의 합 -/
def posSum (p : List Char) (ch : Char) : Nat := sumTo (fun i => if p.getD i ' ' = ch then i + 1 else 0) p.length

/-- 6번 = B 3 · C 3, 연습 1 + 본 3 이면 조건마다 본 측정 9번 -/
theorem seq_counts : roveSeq.length = 6 ∧ roveSeq.count 'B' = 3 ∧ roveSeq.count 'C' = 3 ∧ 3 * rovePlan.2 = 9 := by decide +kernel

/-- 회기 자리 합: B 1+4+5 = 10 · C 2+3+6 = 11 — 날 사이 직선 오름세는 C 쪽에 1/3 회기만큼 더 실림 -/
theorem seq_pos : posSum roveSeq 'B' = 10 ∧ posSum roveSeq 'C' = 11 := by decide +kernel

/-! ## 치우침 없는 뽑기 (js `randUnbiased(n)`) -/

/-- 2³² -/
def u32 : Nat := 4294967296

theorem u32_eq : u32 = 2 ^ 32 := by decide +kernel

/-- js `lim = 2 ** 32 − (2 ** 32 % n)` -/
def ruLim (n : Nat) : Nat := u32 - u32 % n

/-- js: 32비트 값을 차례로 받아 lim 보다 작은 첫 값의 나머지 (그리고 받은 값의 수) -/
def ruDraw (n : Nat) : List Nat → Option (Nat × Nat)
  | [] => none
  | x :: xs => if x < ruLim n then some (x % n, 1) else (ruDraw n xs).map (fun p => (p.1, p.2 + 1))

theorem ruLim_eq (n : Nat) : ruLim n = (u32 / n) * n := by
  unfold ruLim
  have := Nat.div_add_mod u32 n
  rw [Nat.mul_comm] at this
  omega

/-- 버리는 값은 n − 1 개 이하 (n = 16 이면 하나도 없음, n = 9 면 4개) -/
theorem ruLim_ge (n : Nat) (hn : 0 < n) : u32 - (n - 1) ≤ ruLim n := by
  unfold ruLim
  have := Nat.mod_lt u32 hn
  omega

theorem ruLim_9 : ruLim 9 = u32 - 4 := by decide +kernel
theorem ruLim_16 : ruLim 16 = u32 := by decide +kernel

theorem count_range_eq (r : Nat) : ∀ n, ((List.range n).filter (fun i => i == r)).length = if r < n then 1 else 0
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, count_range_eq r n]
    by_cases h : r < n
    · have h2 : (n == r) = false := by simp; omega
      simp [h2, h]; omega
    · by_cases h3 : r = n
      · subst h3; simp
      · have h2 : (n == r) = false := by simp; omega
        simp [h2, h]; omega

theorem count_mod_blocks (n r : Nat) (hr : r < n) :
    ∀ q, ((List.range (q * n)).filter (fun x => x % n == r)).length = q
  | 0 => by simp
  | q + 1 => by
    rw [Nat.succ_mul, List.range_add, List.filter_append, List.length_append, count_mod_blocks n r hr q,
      List.filter_map, List.length_map]
    have e : (List.range n).filter ((fun x => x % n == r) ∘ (fun i => q * n + i)) = (List.range n).filter (fun i => i == r) := by
      apply List.filter_congr
      intro i hi
      simp only [Function.comp, List.mem_range] at hi ⊢
      rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hi]
    rw [e, count_range_eq]
    simp [hr]

/-- 고르게: 받아들이는 값 [0, lim) 가운데 나머지가 r 인 값은 r 마다 정확히 lim / n 개 -/
theorem ru_uniform (n r : Nat) (hn : 0 < n) (hr : r < n) :
    ((List.range (ruLim n)).filter (fun x => x % n == r)).length = ruLim n / n := by
  rw [ruLim_eq, count_mod_blocks n r hr, Nat.mul_div_cancel _ hn]

/-- 뽑은 값은 늘 0 … n − 1 -/
theorem ruDraw_lt (n : Nat) (hn : 0 < n) : ∀ (xs : List Nat) (r k : Nat), ruDraw n xs = some (r, k) → r < n
  | [], _, _, h => by simp [ruDraw] at h
  | x :: xs, r, k, h => by
    simp only [ruDraw] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; exact Nat.mod_lt x hn
    · cases hx : ruDraw n xs with
      | none => rw [hx] at h; simp at h
      | some p =>
        rw [hx] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]; exact ruDraw_lt n hn xs p.1 p.2 hx

/-! ## 보호 범위: 크기만 쓰는 잡음 없는 관찰자 (검증.md §9 · §9-2) -/

/-- 세 구간 이득의 모든 조합 (a = 표적, b · c = 기준) -/
def triples (V : List Int) : List (Int × Int × Int) := V.flatMap (fun a => V.flatMap (fun b => V.map (fun c => (a, b, c))))

/-- 규칙 L (가장 큰 소리 고름) 의 맞힘 점수 × 6: 표적 크기 x0 = a + Δh, 가장 큰 값과 같은 구간을 고르게 나눔 (파이썬 rove_protect.py 와 같음) -/
def creditL (dh : Int) (t : Int × Int × Int) : Nat :=
  let x0 := t.1 + dh
  let m := max x0 (max t.2.1 t.2.2)
  let n := (if x0 = m then 1 else 0) + (if t.2.1 = m then 1 else 0) + (if t.2.2 = m then 1 else 0)
  if x0 = m then 6 / n else 0

/-- 규칙 D (차이가 가장 작은 쌍을 버리고 남은 하나) 의 맞힘 점수 × 6: 가장 작은 차이의 쌍이 여럿이면 남는 구간들 사이에서 고르게 -/
def creditD (dh : Int) (t : Int × Int × Int) : Nat :=
  let x0 := t.1 + dh
  let d12 := (t.2.1 - t.2.2).natAbs
  let d02 := (x0 - t.2.2).natAbs
  let d01 := (x0 - t.2.1).natAbs
  let m := min d12 (min d02 d01)
  let n := (if d12 = m then 1 else 0) + (if d02 = m then 1 else 0) + (if d01 = m then 1 else 0)
  if d12 = m then 6 / n else 0

/-- 맞힘 점수 합 × 6 (정답률 = 이 값 / (6 · n³)) -/
def protL (V : List Int) (dh : Int) : Nat := ((triples V).map (creditL dh)).sum
def protD (V : List Int) (dh : Int) : Nat := ((triples V).map (creditD dh)).sum

/-- 정답률 < 목표 ⇔ 점수·den < 목표분자·6·n³ (목표 1/2 = 1/2, 0.7071 = 7071/10000) -/
def below (score n num den : Nat) : Bool := score * den < num * 6 * n ^ 3
def above (score n num den : Nat) : Bool := num * 6 * n ^ 3 < score * den

/-- C (16값): 가장 큰 소리 규칙은 2.5 dB 에서 1/2 아래 · 3.5 dB 에서 1/2 위, 0.7071 은 5.5 · 6.5 dB 사이 -/
theorem protect_C_L : below (protL (roveH 'C') 5) 16 1 2 = true ∧ above (protL (roveH 'C') 7) 16 1 2 = true ∧
    below (protL (roveH 'C') 11) 16 7071 10000 = true ∧ above (protL (roveH 'C') 13) 16 7071 10000 = true := by decide +kernel

/-- B (9값): 0.5 dB 에서 1/2 아래 · 1.5 dB 에서 위, 0.7071 은 3.5 · 4.5 dB 사이 -/
theorem protect_B_L : below (protL (roveH 'B') 1) 9 1 2 = true ∧ above (protL (roveH 'B') 3) 9 1 2 = true ∧
    below (protL (roveH 'B') 7) 9 7071 10000 = true ∧ above (protL (roveH 'B') 9) 9 7071 10000 = true := by decide +kernel

/-- 차이 작은 쌍 버림(방향 모름): C 는 6.5 · 7.5 dB 사이에서 1/2, B 는 3.5 · 4.5 dB 사이 -/
theorem protect_D : below (protD (roveH 'C') 13) 16 1 2 = true ∧ above (protD (roveH 'C') 15) 16 1 2 = true ∧
    below (protD (roveH 'B') 7) 9 1 2 = true ∧ above (protD (roveH 'B') 9) 9 1 2 = true := by decide +kernel

/-- Won 2011 15 dB 로빙(49 … 64 dBA)과 C 는 값의 모양이 같아 정답률도 같음 (보기: 2.5 · 3.5 dB, 두 규칙) -/
theorem won15_eq_C : protL won15H 5 = protL (roveH 'C') 5 ∧ protL won15H 7 = protL (roveH 'C') 7 ∧
    protD won15H 13 = protD (roveH 'C') 13 ∧ protD won15H 15 = protD (roveH 'C') 15 := by decide +kernel

/-! ## 두 구간 크기 차이의 평균 (js loud.js 주석 (n² − 1)/(3n) dB) -/

/-- 모든 순서쌍의 |a − b| 합 (반 dB 단위) -/
def pairSum (V : List Int) : Nat := (V.flatMap (fun a => V.map (fun b => (a - b).natAbs))).sum

/-- B: 합 480 반 dB = 240 dB, 81 쌍 → 240/81 = 80/27 dB (= (9² − 1)/(3·9)) -/
theorem pairSum_B : pairSum (roveH 'B') = 480 ∧ 240 * 27 = 80 * 81 := by decide +kernel

/-- C: 합 2720 반 dB = 1360 dB, 256 쌍 → 1360/256 = 255/48 dB (= (16² − 1)/(3·16)) -/
theorem pairSum_C : pairSum (roveH 'C') = 2720 ∧ 1360 * 48 = 255 * 256 := by decide +kernel

end SMRT

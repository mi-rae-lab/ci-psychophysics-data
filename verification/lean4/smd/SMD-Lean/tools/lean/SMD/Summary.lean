import SMD.Arith

/-!
# 밀도 하나의 회기 요약 — 앱 `js/analysis.js` `condSummary` (Won 반복 규칙) (Claude, 2026-10-31)

입력: track 결과 종류를 순서대로 — 숫자(h 합 · 개수, 역치 dB = 합 / (2 · 개수)) · above(> 60 dB 확인) · ceil(쉬운 끝에 막힘) · up(계단이 아직 올라가는 중) ·
floor(바닥에 막힘) · none(결정 안 됨: 멈춤 · 실패 · 신뢰성 부족 · 절차 어긋남 · 값 검증 실패 …).
js 와 같은 규칙:
* 결정된 track(none 이 아닌 것)이 2개 미만 → 잠정 (needMore = 2 − 개수)
* 앞 둘이 모두 숫자: |q₁ − q₂| > 3 dB (정확한 유리수) 이면 3번째 — 없으면 잠정(needMore 1), 있으면 셋으로 정함 · 아니면 둘로 정함
* 앞 둘이 숫자 · 숫자 아님으로 섞임: 같은 종류이거나 둘 다 높은 쪽(above · ceil · up)이면 둘로 정함, 아니면 3번째 (없으면 잠정)
* 정하기(settle): 모두 숫자 → 확정 (값 = 정확한 산술 평균) · 모두 높은 쪽 → above(모두 above) / ceil(모두 above · ceil) / high · 모두 floor → floor · 그 밖 → mixed

증명한 것: `final_all_num` (확정이면 쓴 track(앞 2개 또는 3개)이 모두 숫자이고 값 = 그 평균) · `provisional_iff` (잠정 ⇔ 더 필요한 track 이 있음) ·
`decided_of_three` (결정된 track 이 3개면 잠정 아님) · `third_needed_iff` (앞 둘이 숫자면 ‘3번째 필요’ ⇔ |q₁ − q₂| > 3) ·
`two_final_close` (둘로 확정되면 |q₁ − q₂| ≤ 3, 값 = 평균) · `final_value_bounds` (쓴 숫자가 모두 0 … 60 dB 이면 확정 값도 0 … 60)
-/

namespace SMD

inductive TKind
  | num (sum cnt : Nat) | above | ceil | up | floor | none
deriving DecidableEq, Repr, Inhabited

inductive SState
  | provisional | final | above | ceil | high | floor | mixed
deriving DecidableEq, Repr, Inhabited

def TKind.isNum : TKind → Bool | .num _ _ => true | _ => false
def TKind.isUp : TKind → Bool | .above => true | .ceil => true | .up => true | _ => false
def TKind.isNone : TKind → Bool | .none => true | _ => false
def TKind.tag : TKind → Nat | .num _ _ => 0 | .above => 1 | .ceil => 2 | .up => 3 | .floor => 4 | .none => 5

/-- 역치 (dB, 정확한 유리수) = 합 / (2 · 개수) -/
def TKind.q : TKind → Rat | .num s c => (s : Rat) / (2 * (c : Rat)) | _ => 0

def meanQ (l : List TKind) : Rat := (l.map TKind.q).sum / (l.length : Rat)

/-- 정하기 (js `settle`) -/
def settle (use : List TKind) : SState × Option Rat :=
  if use.all TKind.isNum then (.final, some (meanQ use))
  else if use.all TKind.isUp then
    (if use.all (· == .above) then .above else if use.all (fun k => k == .above || k == .ceil) then .ceil else .high, none)
  else if use.all (· == .floor) then (.floor, none)
  else (.mixed, none)

def absQ (x : Rat) : Rat := if x < 0 then -x else x

/-- 결과: (상태, 값, 더 필요한 track 수, 쓴 track 수) -/
abbrev SRes := SState × Option Rat × Nat × Nat

def twoDone (a b : TKind) : SRes := ((settle [a, b]).1, (settle [a, b]).2, 0, 2)

def three (a b : TKind) : List TKind → SRes
  | c :: _ => ((settle [a, b, c]).1, (settle [a, b, c]).2, 0, 3)
  | [] => (.provisional, none, 1, 0)

/-- 결정된 track 들(순서대로)의 요약 -/
def summaryOf : List TKind → SRes
  | a :: b :: rest =>
    if a.isNum && b.isNum then (if 3 < absQ (a.q - b.q) then three a b rest else twoDone a b)
    else if a.tag == b.tag || (a.isUp && b.isUp) then twoDone a b
    else three a b rest
  | [] => (.provisional, none, 2, 0)
  | [_] => (.provisional, none, 1, 0)

def condSummary (kinds : List TKind) : SRes := summaryOf (kinds.filter (fun k => !k.isNone))

/-! ## 성질 -/

theorem settle_final_iff (use : List TKind) : (settle use).1 = .final ↔ use.all TKind.isNum = true := by
  unfold settle
  split
  · simp_all
  · rename_i h; simp only [h, Bool.false_eq_true, iff_false]
    split
    · split <;> (try split) <;> simp
    · split <;> simp

theorem settle_ne_provisional (use : List TKind) : (settle use).1 ≠ .provisional := by
  unfold settle
  repeat' split
  all_goals simp

theorem twoDone_final {a b : TKind} (h : (twoDone a b).1 = .final) :
    [a, b].all TKind.isNum = true ∧ (twoDone a b).2.1 = some (meanQ [a, b]) := by
  have h' : (settle [a, b]).1 = .final := h
  have hall := (settle_final_iff _).mp h'
  refine ⟨hall, ?_⟩
  show (settle [a, b]).2 = _
  unfold settle; rw [if_pos hall]

theorem three_final {a b : TKind} {rest : List TKind} (h : (three a b rest).1 = .final) :
    ∃ c t, rest = c :: t ∧ [a, b, c].all TKind.isNum = true ∧ (three a b rest).2.1 = some (meanQ [a, b, c]) := by
  match rest, h with
  | [], h => simp [three] at h
  | c :: t, h =>
    have h' : (settle [a, b, c]).1 = .final := h
    have hall := (settle_final_iff _).mp h'
    refine ⟨c, t, rfl, hall, ?_⟩
    show (settle [a, b, c]).2 = _
    unfold settle; rw [if_pos hall]

theorem summaryOf_cases (a b : TKind) (rest : List TKind) :
    summaryOf (a :: b :: rest) = twoDone a b ∨ summaryOf (a :: b :: rest) = three a b rest := by
  simp only [summaryOf]
  split
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- 확정이면: 쓴 track = 결정된 앞 2개 또는 3개, 모두 숫자, 값 = 그 정확한 평균 — 숫자와 숫자 아님을 섞어 평균하지 않음 -/
theorem summaryOf_final (det : List TKind) (h : (summaryOf det).1 = .final) :
    ∃ use, (use = det.take 2 ∨ use = det.take 3) ∧ 2 ≤ use.length ∧ use.all TKind.isNum = true ∧
      (summaryOf det).2.1 = some (meanQ use) := by
  match det, h with
  | [], h => simp [summaryOf] at h
  | [_], h => simp [summaryOf] at h
  | a :: b :: rest, h =>
    rcases summaryOf_cases a b rest with he | he <;> rw [he] at h ⊢
    · obtain ⟨hall, hv⟩ := twoDone_final h
      exact ⟨[a, b], Or.inl (by simp), by simp, hall, hv⟩
    · obtain ⟨c, t, hr, hall, hv⟩ := three_final h
      subst hr
      exact ⟨[a, b, c], Or.inr (by simp), by simp, hall, hv⟩

theorem final_all_num (kinds : List TKind) (h : (condSummary kinds).1 = .final) :
    ∃ use, (use = (kinds.filter (fun k => !k.isNone)).take 2 ∨ use = (kinds.filter (fun k => !k.isNone)).take 3) ∧
      2 ≤ use.length ∧ use.all TKind.isNum = true ∧ (condSummary kinds).2.1 = some (meanQ use) :=
  summaryOf_final _ h

/-- 잠정 ⇔ 더 필요한 track 이 있음 (needMore > 0) -/
theorem provisional_iff (det : List TKind) : (summaryOf det).1 = .provisional ↔ 0 < (summaryOf det).2.2.1 := by
  match det with
  | [] => simp [summaryOf]
  | [_] => simp [summaryOf]
  | a :: b :: rest =>
    rcases summaryOf_cases a b rest with he | he <;> rw [he]
    · constructor
      · intro h; exact absurd h (settle_ne_provisional _)
      · intro h; simp [twoDone] at h
    · match rest with
      | [] => simp [three]
      | c :: _ =>
        constructor
        · intro h; exact absurd h (settle_ne_provisional _)
        · intro h; simp [three] at h

/-- 결정된 track 이 3개 이상이면 잠정이 아님 (4번째는 쓰지 않음) -/
theorem decided_of_three (det : List TKind) (h : 3 ≤ det.length) : (summaryOf det).1 ≠ .provisional := by
  match det, h with
  | a :: b :: c :: t, _ =>
    rcases summaryOf_cases a b (c :: t) with he | he <;> rw [he]
    · exact settle_ne_provisional _
    · exact settle_ne_provisional _

/-- 앞 둘이 숫자면: ‘3번째 필요’(셋째가 없을 때 잠정 · needMore 1) ⇔ |q₁ − q₂| > 3 (정확한 유리수 비교) -/
theorem third_needed_iff (s1 c1 s2 c2 : Nat) :
    summaryOf [.num s1 c1, .num s2 c2] = (if 3 < absQ ((TKind.num s1 c1).q - (TKind.num s2 c2).q) then (.provisional, none, 1, 0)
      else twoDone (.num s1 c1) (.num s2 c2)) := by
  first | rfl | simp [summaryOf, three, TKind.isNum]

/-- 둘로 확정되면 두 역치의 차는 3 dB 이하이고 값은 두 역치의 평균 -/
theorem two_final_close (s1 c1 s2 c2 : Nat) (h : (summaryOf [.num s1 c1, .num s2 c2]).1 = .final) :
    absQ ((TKind.num s1 c1).q - (TKind.num s2 c2).q) ≤ 3 ∧
      (summaryOf [.num s1 c1, .num s2 c2]).2.1 = some (((TKind.num s1 c1).q + (TKind.num s2 c2).q) / 2) := by
  rw [third_needed_iff] at h ⊢
  by_cases hc : 3 < absQ ((TKind.num s1 c1).q - (TKind.num s2 c2).q)
  · rw [if_pos hc] at h; simp at h
  · rw [if_neg hc] at h ⊢
    refine ⟨Rat.not_lt.mp hc, ?_⟩
    simp [twoDone, settle, TKind.isNum, meanQ] <;> grind

/-- 쓴 숫자가 모두 0 … 60 dB 이면 평균도 0 … 60 dB -/
theorem meanQ_bounds (l : List TKind) (hl : l ≠ []) (h : ∀ k ∈ l, 0 ≤ k.q ∧ k.q ≤ 60) : 0 ≤ meanQ l ∧ meanQ l ≤ 60 := by
  have hsum : ∀ (m : List TKind), (∀ k ∈ m, 0 ≤ k.q ∧ k.q ≤ 60) →
      0 ≤ (m.map TKind.q).sum ∧ (m.map TKind.q).sum ≤ 60 * (m.length : Rat) := by
    intro m
    induction m with
    | nil => intro _; refine ⟨?_, ?_⟩ <;> simp [Rat.le_refl]
    | cons k m ih =>
      intro hm
      have hk := hm k (by simp)
      have ih' := ih (fun x hx => hm x (by simp [hx]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Rat.natCast_add]
      constructor <;> grind
  have hs := hsum l h
  have hpos : (0 : Rat) < (l.length : Rat) := Rat.natCast_pos.mpr (List.length_pos_iff.mpr hl)
  unfold meanQ
  constructor
  · apply Rat.not_lt.mp
    intro hlt
    rw [Rat.div_lt_iff hpos] at hlt
    have h0 : (0 : Rat) * (l.length : Rat) = 0 := by grind
    rw [h0] at hlt
    exact absurd hs.1 (Rat.not_le.mpr hlt)
  · apply Rat.not_lt.mp
    intro hlt
    rw [Rat.lt_div_iff hpos] at hlt
    exact absurd hs.2 (Rat.not_le.mpr hlt)

theorem final_value_bounds (kinds : List TKind) (hb : ∀ k ∈ kinds, 0 ≤ k.q ∧ k.q ≤ 60) {v : Rat}
    (h : (condSummary kinds).1 = .final) (hv : (condSummary kinds).2.1 = some v) : 0 ≤ v ∧ v ≤ 60 := by
  obtain ⟨use, huse, hlen, _, hval⟩ := final_all_num kinds h
  rw [hval] at hv
  obtain rfl : meanQ use = v := Option.some.inj hv
  have hsub : ∀ k ∈ use, k ∈ kinds := by
    intro k hk
    rcases huse with hu | hu <;> subst hu <;> exact (List.mem_filter.mp (List.mem_of_mem_take hk)).1
  have hne : use ≠ [] := by intro h0; rw [h0] at hlen; simp at hlen
  exact meanQ_bounds use hne (fun k hk => hb k (hsub k hk))

end SMD

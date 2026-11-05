import GDT.Classify

/-!
# 한 조건의 회기 요약 — 앱 `js/analysis.js` `outcome` · `condSummary` (절차의 반복 규칙) (Claude, 2026-11-01)

track 결과 종류 (js `outcome`): num(숫자 역치 — valueOf 합 s · 개수 c, 값 q = s/c: zeng = k̄ (반 옥타브 칸 평균), xie = ms) ·
paper(blank 의 논문 방식 값 — 역치 아님) · above(긴 끝보다 김 확인) · ceil(긴 끝에 막힘) · up(올라가는 중 · 우연 관문) ·
below(짧은 끝보다 짧음 확인) · floor(짧은 끝에 막힘) · none(결정 안 됨: 멈춤 · 실패 · 신뢰성 부족 · 절차 어긋남 · 측정 중 설정 바뀜 …) ·
bad(숫자 결과인데 값 검증 실패 — none 과 같이 빼고 따로 셈).
js 와 같은 규칙 (need = tracks_per_condition, third = third_if_k_diff_gt):
* 결정된 track(none · bad 가 아닌 것)이 need 개 미만 → 잠정 (needMore = need − 개수)
* third 가 없거나 need ≠ 2 → 앞 need 개로 정함 (xie: 3개 · blank: 2개)
* zeng (need 2, third 1): 앞 둘이 모두 숫자 → |q₁ − q₂| > 1 (정확한 유리수, k 칸 = √2 배) 이면 3번째 (없으면 잠정 · needMore 1), 아니면 둘로 정함 ·
  숫자와 숫자 아님이 섞임 → 같은 종류이거나 둘 다 긴 쪽(above · ceil · up) · 둘 다 짧은 쪽(below · floor)이면 둘로 정함, 아니면 3번째
* 정하기 (`settle`): 모두 num → 확정(final, 값 = 정확한 산술 평균 — zeng 은 k̄ 의 평균 = 기하 평균 ms 의 지수) · 모두 paper → 논문 방식 값(paper) ·
  모두 긴 쪽 → above(모두 above) / ceil(모두 above · ceil) / high · 모두 짧은 쪽 → below(모두 below) / floor · 그 밖 → mixed

증명한 것: `final_mean` (확정이면 쓴 track(결정된 것의 앞 2개 · 3개)이 모두 num, 값 = 그 정확한 평균) · `provisional_iff` (잠정 ⇔ 더 필요한 track 있음) ·
`zeng_third_iff` (앞 둘이 숫자면 ‘3번째 필요’ ⇔ |q₁ − q₂| > 1) · `zeng_two_final` (둘로 확정되면 |q₁ − q₂| ≤ 1, 값 = 평균) ·
`xie_final_three` (xie 확정 = 결정된 앞 3개가 모두 숫자, 값 = 그 평균) · `xie_provisional_iff` (xie 잠정 ⇔ 결정된 track < 3) ·
`blank_never_final` · `blank_paper_mean` (blank 은 확정이 아니라 ‘논문 방식 값’, 값 = 쓴 2개의 평균) · `final_value_bounds` (쓴 값이 모두 [lo, hi] 면 평균도) ·
`kindOf_blank_not_num` (blank 의 숫자 결과는 늘 paper)
-/

namespace GDT

inductive TKind
  | num (s : Int) (c : Nat) | paper (s : Int) (c : Nat) | above | ceil | up | below | floor | none | bad
deriving DecidableEq, Repr, Inhabited

inductive SState
  | provisional | final | paper | above | ceil | high | below | floor | mixed
deriving DecidableEq, Repr, Inhabited

def TKind.isNum : TKind → Bool | .num _ _ => true | _ => false
def TKind.isPaper : TKind → Bool | .paper _ _ => true | _ => false
/-- js `isN`: num 또는 paper -/
def TKind.isN (k : TKind) : Bool := k.isNum || k.isPaper
def TKind.isUp : TKind → Bool | .above => true | .ceil => true | .up => true | _ => false
def TKind.isDown : TKind → Bool | .below => true | .floor => true | _ => false
def TKind.isNone : TKind → Bool | .none => true | .bad => true | _ => false
def TKind.isBad : TKind → Bool | .bad => true | _ => false
def TKind.tag : TKind → Nat
  | .num _ _ => 0 | .paper _ _ => 1 | .above => 2 | .ceil => 3 | .up => 4 | .below => 5 | .floor => 6 | .none => 7 | .bad => 8

/-- 값 (js `qOf = Q.of(sumV, count)`) = 합 / 개수 (정확한 유리수) -/
def TKind.q : TKind → Rat
  | .num s c => (s : Rat) / (c : Rat)
  | .paper s c => (s : Rat) / (c : Rat)
  | _ => 0

def meanQ (l : List TKind) : Rat := (l.map TKind.q).sum / (l.length : Rat)

/-- 정하기 (js `settle`) -/
def settle (use : List TKind) : SState × Option Rat :=
  if use.all TKind.isNum then (.final, some (meanQ use))
  else if use.all TKind.isPaper then (.paper, some (meanQ use))
  else if use.all TKind.isUp then
    (if use.all (· == .above) then .above else if use.all (fun k => k == .above || k == .ceil) then .ceil else .high, none)
  else if use.all TKind.isDown then (if use.all (· == .below) then .below else .floor, none)
  else (.mixed, none)

def absQ (x : Rat) : Rat := if x < 0 then -x else x

/-- 요약 결과 (js `out` 의 대조 칸): 상태 · 값 · 더 필요 · 쓴 수 · 결정된 수 · 값 검증 실패 수 · 규칙(3번째 필요, 섞임, |q₁ − q₂|) -/
structure SRes where
  state : SState
  value : Option Rat
  needMore : Nat
  used : Nat
  det : Nat
  nInvalid : Nat
  rule : Option (Bool × Bool × Option Rat)
deriving Repr, Inhabited

def settleRes (use : List TKind) (nDet nInv : Nat) (rule : Option (Bool × Bool × Option Rat)) : SRes :=
  { state := (settle use).1, value := (settle use).2, needMore := 0, used := use.length, det := nDet, nInvalid := nInv, rule := rule }

def provRes (more nDet nInv : Nat) (rule : Option (Bool × Bool × Option Rat)) : SRes :=
  { state := .provisional, value := none, needMore := more, used := 0, det := nDet, nInvalid := nInv, rule := rule }

/-- 셋째가 있으면 셋으로, 없으면 잠정 (needMore 1) -/
def withThird (a b : TKind) (rest : List TKind) (nDet nInv : Nat) (rule : Option (Bool × Bool × Option Rat)) : SRes :=
  match rest with
  | c :: _ => settleRes [a, b, c] nDet nInv rule
  | [] => provRes 1 nDet nInv rule

/-- 둘 다 숫자일 때의 규칙 (zeng): |q₁ − q₂| > t 이면 3번째 -/
def numRule (t : Nat) (a b : TKind) (rest : List TKind) (nDet nInv : Nat) : SRes :=
  if (t : Rat) < absQ (a.q - b.q) then withThird a b rest nDet nInv (some (true, false, some (absQ (a.q - b.q))))
  else settleRes [a, b] nDet nInv (some (false, false, some (absQ (a.q - b.q))))

def sameSide (a b : TKind) : Bool := a.tag == b.tag || (a.isUp && b.isUp) || (a.isDown && b.isDown)

/-- 섞였을 때의 규칙: 같은 종류 · 같은 쪽이면 둘로 정함, 아니면 3번째 -/
def censRule (a b : TKind) (rest : List TKind) (nDet nInv : Nat) : SRes :=
  if sameSide a b then settleRes [a, b] nDet nInv (some (false, true, none))
  else withThird a b rest nDet nInv (some (true, true, none))

/-- 두 track 규칙 (need = 2 이고 third 가 있을 때) -/
def twoRule (t : Nat) (det : List TKind) (nInv : Nat) : SRes :=
  match det with
  | a :: b :: rest => if a.isN && b.isN then numRule t a b rest det.length nInv else censRule a b rest det.length nInv
  | _ => provRes (2 - det.length) det.length nInv none

def detOf (kinds : List TKind) : List TKind := kinds.filter (fun k => !k.isNone)
def invOf (kinds : List TKind) : Nat := (kinds.filter TKind.isBad).length

/-- 한 조건의 요약 (js `condSummary(runs, P)`) -/
def condSummary (need : Nat) (third : Option Nat) (kinds : List TKind) : SRes :=
  if (detOf kinds).length < need then provRes (need - (detOf kinds).length) (detOf kinds).length (invOf kinds) none
  else match third with
    | none => settleRes ((detOf kinds).take need) (detOf kinds).length (invOf kinds) none
    | some t => if need = 2 then twoRule t (detOf kinds) (invOf kinds)
                else settleRes ((detOf kinds).take need) (detOf kinds).length (invOf kinds) none

/-- 절차의 요약 -/
def protoSummary (P : Proto) (kinds : List TKind) : SRes := condSummary P.need P.third kinds

/-! ## track 결과 → 종류 (js `outcome`) -/

/-- 분류 결과 → 종류. valueOk: 숫자 결과의 값 검증(js `numericResultIssue`) 통과 · changed: 측정 중 제시 설정이 바뀜 -/
def kindOf (P : Proto) (st : AStatus) (thr : Option (Int × Nat)) (valueOk changed : Bool) : TKind :=
  if changed then .none
  else match st with
    | .completeInRange =>
      match thr with
      | some (s, c) => if valueOk then (if P.paper then .paper s c else .num s c) else .bad
      | none => .bad
    | .aboveRange => .above
    | .nearCeiling => .ceil
    | .aboveWindow => .up
    | .notAboveChance => .up
    | .belowRange => .below
    | .nearFloor => .floor
    | _ => .none

/-- blank (value_kind = paper_value) 의 숫자 결과는 늘 paper — num 이 되지 않음 -/
theorem kindOf_blank_not_num (st : AStatus) (thr : Option (Int × Nat)) (v ch : Bool) : (kindOf blank st thr v ch).isNum = false := by
  rcases thr with _ | ⟨s, c⟩ <;> cases st <;> cases v <;> cases ch <;> simp [kindOf, blank, TKind.isNum]

/-- zeng · xie (value_kind = threshold) 의 숫자 결과는 늘 num — paper 가 되지 않음 -/
theorem kindOf_paper_iff_blank (P : Proto) (hP : P.paper = false) (st : AStatus) (thr : Option (Int × Nat)) (v ch : Bool) :
    (kindOf P st thr v ch).isPaper = false := by
  rcases thr with _ | ⟨s, c⟩ <;> cases st <;> cases v <;> cases ch <;> simp [kindOf, hP, TKind.isPaper]

/-! ## 성질 -/

theorem settle_ne_provisional (use : List TKind) : (settle use).1 ≠ .provisional := by
  unfold settle
  repeat' split
  all_goals simp

theorem settle_final_iff (use : List TKind) : (settle use).1 = .final ↔ use.all TKind.isNum = true := by
  unfold settle
  constructor
  · intro h
    split at h
    · assumption
    · exfalso; repeat' (split at h <;> try simp at h)
  · intro h; simp [h]

theorem settle_final_value (use : List TKind) (h : use.all TKind.isNum = true) : (settle use).2 = some (meanQ use) := by
  unfold settle; simp [h]

theorem settleRes_final {use : List TKind} {d i : Nat} {r : Option (Bool × Bool × Option Rat)}
    (h : (settleRes use d i r).state = .final) : use.all TKind.isNum = true ∧ (settleRes use d i r).value = some (meanQ use) := by
  have hf := (settle_final_iff use).mp h
  exact ⟨hf, settle_final_value use hf⟩

theorem withThird_cases (a b : TKind) (rest : List TKind) (d i : Nat) (r : Option (Bool × Bool × Option Rat)) :
    (∃ c t, rest = c :: t ∧ withThird a b rest d i r = settleRes [a, b, c] d i r) ∨ (rest = [] ∧ withThird a b rest d i r = provRes 1 d i r) := by
  cases rest with
  | nil => right; exact ⟨rfl, rfl⟩
  | cons c t => left; exact ⟨c, t, rfl, rfl⟩

/-- 두 track 규칙의 결과는 앞 둘로 정함 · 앞 셋으로 정함 · 잠정(needMore 1) 가운데 하나 -/
theorem twoRule_cases (t : Nat) (a b : TKind) (rest : List TKind) (i : Nat) :
    (∃ r, twoRule t (a :: b :: rest) i = settleRes [a, b] (rest.length + 2) i r) ∨
    (∃ c tl r, rest = c :: tl ∧ twoRule t (a :: b :: rest) i = settleRes [a, b, c] (rest.length + 2) i r) ∨
    (∃ r, rest = [] ∧ twoRule t (a :: b :: rest) i = provRes 1 2 i r) := by
  simp only [twoRule, List.length_cons]
  split
  · unfold numRule
    split
    · rcases withThird_cases a b rest (rest.length + 1 + 1) i _ with ⟨c, tl, hr, he⟩ | ⟨hr, he⟩
      · right; left; exact ⟨c, tl, _, hr, he⟩
      · right; right; subst hr; exact ⟨_, rfl, he⟩
    · left; exact ⟨_, rfl⟩
  · unfold censRule
    split
    · left; exact ⟨_, rfl⟩
    · rcases withThird_cases a b rest (rest.length + 1 + 1) i _ with ⟨c, tl, hr, he⟩ | ⟨hr, he⟩
      · right; left; exact ⟨c, tl, _, hr, he⟩
      · right; right; subst hr; exact ⟨_, rfl, he⟩

/-- 확정이면: 쓴 track = 결정된 것의 앞 2개 · 3개 (또는 앞 need 개), 모두 num, 값 = 그 정확한 평균 — 숫자와 숫자 아님을 섞어 평균하지 않음 -/
theorem final_mean (need : Nat) (third : Option Nat) (kinds : List TKind) (h : (condSummary need third kinds).state = .final) :
    ∃ use, (use = (detOf kinds).take need ∨ use = (detOf kinds).take 2 ∨ use = (detOf kinds).take 3) ∧
      need ≤ (detOf kinds).length ∧ use.all TKind.isNum = true ∧ (condSummary need third kinds).value = some (meanQ use) := by
  unfold condSummary at h ⊢
  split at h
  · simp [provRes] at h
  · rename_i hlen
    have hl : need ≤ (detOf kinds).length := by omega
    rw [if_neg hlen]
    cases third with
    | none =>
      obtain ⟨h1, h2⟩ := settleRes_final h
      exact ⟨_, Or.inl rfl, hl, h1, h2⟩
    | some t =>
      simp only at h ⊢
      split at h
      · rename_i h2
        rw [if_pos h2]
        subst h2
        match hd : detOf kinds, h with
        | [], h => simp [twoRule, provRes] at h
        | [_], h => simp [twoRule, provRes] at h
        | a :: b :: rest, h =>
          rcases twoRule_cases t a b rest (invOf kinds) with ⟨r, he⟩ | ⟨c, tl, r, hr, he⟩ | ⟨r, hr, he⟩
          · rw [he] at h ⊢
            obtain ⟨h1, h2⟩ := settleRes_final h
            exact ⟨[a, b], Or.inr (Or.inl (by simp)), by simp, h1, h2⟩
          · rw [he] at h ⊢
            obtain ⟨h1, h2⟩ := settleRes_final h
            subst hr
            exact ⟨[a, b, c], Or.inr (Or.inr (by simp)), by simp, h1, h2⟩
          · rw [he] at h; simp [provRes] at h
      · rename_i h2
        rw [if_neg h2]
        obtain ⟨h1, h3⟩ := settleRes_final h
        exact ⟨_, Or.inl rfl, hl, h1, h3⟩

theorem use_ne_nil {need : Nat} {det use : List TKind} (hn : 1 ≤ need) (hl : need ≤ det.length)
    (hu : use = det.take need ∨ use = det.take 2 ∨ use = det.take 3) : use ≠ [] := by
  intro h0
  rcases hu with hu | hu | hu <;> rw [h0] at hu <;>
  · have := congrArg List.length hu
    simp at this
    omega

/-- 잠정 ⇔ 더 필요한 track 이 있음 (needMore > 0) — need ≥ 1 일 때 -/
theorem provisional_iff (need : Nat) (third : Option Nat) (kinds : List TKind) (hn : 1 ≤ need) :
    (condSummary need third kinds).state = .provisional ↔ 0 < (condSummary need third kinds).needMore := by
  unfold condSummary
  split
  · simp [provRes]; omega
  · rename_i hlen
    cases third with
    | none => simp [settleRes, settle_ne_provisional]
    | some t =>
      simp only
      split
      · rename_i h2
        subst h2
        match hd : detOf kinds with
        | [] => simp [hd] at hlen
        | [_] => simp [hd] at hlen
        | a :: b :: rest =>
          rcases twoRule_cases t a b rest (invOf kinds) with ⟨r, he⟩ | ⟨c, tl, r, _, he⟩ | ⟨r, _, he⟩ <;> rw [he]
          · simp [settleRes, settle_ne_provisional]
          · simp [settleRes, settle_ne_provisional]
          · simp [provRes]
      · simp [settleRes, settle_ne_provisional]

/-! ### zeng (need 2, third 1) -/

/-- 앞 둘이 숫자(뒤 track 없음): ‘3번째 필요’(잠정 · needMore 1) ⇔ |q₁ − q₂| > 1 (정확한 유리수 비교, k 칸) -/
theorem zeng_third_iff (s1 s2 : Int) (c1 c2 : Nat) :
    (protoSummary zeng [.num s1 c1, .num s2 c2]).state = .provisional ↔
      1 < absQ ((TKind.num s1 c1).q - (TKind.num s2 c2).q) := by
  simp only [protoSummary, zeng, condSummary, detOf, invOf]
  simp only [List.filter, TKind.isNone, Bool.not_false, List.length_cons, List.length_nil]
  simp only [Nat.lt_irrefl, ↓reduceIte, twoRule, TKind.isN, TKind.isNum, numRule]
  by_cases hd : (1 : Rat) < absQ ((TKind.num s1 c1).q - (TKind.num s2 c2).q)
  · simp [hd, withThird, provRes]
  · simp [hd, settleRes, settle_ne_provisional]

/-- 둘로 확정되면 두 값(k̄)의 차는 1 이하 (√2 배 이하)이고 값은 두 값의 평균 -/
theorem zeng_two_final (s1 s2 : Int) (c1 c2 : Nat) (h : (protoSummary zeng [.num s1 c1, .num s2 c2]).state = .final) :
    absQ ((TKind.num s1 c1).q - (TKind.num s2 c2).q) ≤ 1 ∧
      (protoSummary zeng [.num s1 c1, .num s2 c2]).value = some (((TKind.num s1 c1).q + (TKind.num s2 c2).q) / 2) := by
  have hnp : ¬ (1 < absQ ((TKind.num s1 c1).q - (TKind.num s2 c2).q)) := by
    intro hlt
    have := (zeng_third_iff s1 s2 c1 c2).mpr hlt
    rw [h] at this; cases this
  refine ⟨Rat.not_lt.mp hnp, ?_⟩
  have hd' : ¬ ((1 : Nat) : Rat) < absQ ((TKind.num s1 c1).q - (TKind.num s2 c2).q) := hnp
  simp only [protoSummary, zeng, condSummary, detOf, invOf]
  simp only [List.filter, TKind.isNone, Bool.not_false, List.length_cons, List.length_nil]
  simp only [Nat.lt_irrefl, ↓reduceIte, twoRule, TKind.isN, TKind.isNum, numRule, hd']
  simp [settleRes, settle, TKind.isNum, meanQ]
  grind

/-! ### xie (need 3, third 없음) · blank (need 2, paper) -/

/-- xie: 잠정 ⇔ 결정된 track 이 3개 미만 -/
theorem xie_provisional_iff (kinds : List TKind) :
    (protoSummary xie kinds).state = .provisional ↔ (detOf kinds).length < 3 := by
  simp only [protoSummary, xie, condSummary]
  split
  · rename_i h; simp [provRes, h]
  · rename_i h; simp [settleRes, settle_ne_provisional, h]

/-- xie: 확정이면 결정된 앞 3개가 모두 숫자이고 값 = 그 셋의 정확한 평균 (원문 ‘3번 잰 평균’) -/
theorem xie_final_three (kinds : List TKind) (h : (protoSummary xie kinds).state = .final) :
    3 ≤ (detOf kinds).length ∧ ((detOf kinds).take 3).all TKind.isNum = true ∧
      (protoSummary xie kinds).value = some (meanQ ((detOf kinds).take 3)) ∧ (protoSummary xie kinds).used = 3 := by
  simp only [protoSummary, xie, condSummary] at h ⊢
  split at h
  · simp [provRes] at h
  · rename_i hlen
    rw [if_neg hlen]
    obtain ⟨h1, h2⟩ := settleRes_final h
    refine ⟨by omega, h1, h2, ?_⟩
    simp only [settleRes, List.length_take]
    omega

/-- 종류 목록에 num 이 없으면 (blank 의 결과는 그럼) 확정이 나오지 않음 -/
theorem no_num_never_final (need : Nat) (third : Option Nat) (kinds : List TKind) (hn : 1 ≤ need)
    (h : ∀ k ∈ kinds, k.isNum = false) : (condSummary need third kinds).state ≠ .final := by
  intro hf
  obtain ⟨use, huse, hl, hall, _⟩ := final_mean need third kinds hf
  have hsub : ∀ k ∈ use, k ∈ kinds := by
    intro k hk
    rcases huse with hu | hu | hu <;> subst hu <;> exact (List.mem_filter.mp (List.mem_of_mem_take hk)).1
  have hne : use ≠ [] := use_ne_nil hn hl huse
  obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil use hne
  have := List.all_eq_true.mp hall k hk
  rw [h k (hsub k hk)] at this
  cases this

/-- blank: 확정(final)이 나오지 않음 — 숫자 결과는 모두 ‘논문 방식 값’ -/
theorem blank_never_final (sts : List (AStatus × Option (Int × Nat) × Bool × Bool)) :
    (protoSummary blank (sts.map (fun x => kindOf blank x.1 x.2.1 x.2.2.1 x.2.2.2))).state ≠ .final := by
  apply no_num_never_final _ _ _ (by decide)
  intro k hk
  obtain ⟨x, _, hx⟩ := List.mem_map.mp hk
  subst hx
  exact kindOf_blank_not_num _ _ _ _

/-- blank: 쓴 2개가 모두 paper 이면 상태 paper, 값 = 둘의 정확한 평균 (역치가 아님) -/
theorem blank_paper_mean (s1 s2 : Int) (c1 c2 : Nat) :
    protoSummary blank [.paper s1 c1, .paper s2 c2] =
      { state := .paper, value := some (meanQ [.paper s1 c1, .paper s2 c2]), needMore := 0, used := 2, det := 2, nInvalid := 0, rule := none } := by
  simp [protoSummary, blank, condSummary, detOf, invOf, settleRes, settle, TKind.isNone, TKind.isNum, TKind.isPaper, TKind.isBad]

/-- 쓴 값이 모두 [lo, hi] 면 평균도 [lo, hi] (사다리 범위 — zeng k̄ ∈ [−12, 7], xie [1, 100], blank [2, 120]) -/
theorem meanQ_bounds (l : List TKind) (hl : l ≠ []) (lo hi : Rat) (h : ∀ k ∈ l, lo ≤ k.q ∧ k.q ≤ hi) :
    lo ≤ meanQ l ∧ meanQ l ≤ hi := by
  have hsum : ∀ (m : List TKind), (∀ k ∈ m, lo ≤ k.q ∧ k.q ≤ hi) →
      lo * (m.length : Rat) ≤ (m.map TKind.q).sum ∧ (m.map TKind.q).sum ≤ hi * (m.length : Rat) := by
    intro m
    induction m with
    | nil => intro _; refine ⟨?_, ?_⟩ <;> simp [Rat.le_refl]
    | cons k m ih =>
      intro hm
      have hk := hm k (by simp)
      have ih' := ih (fun x hx => hm x (by simp [hx]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Rat.natCast_add]
      have e1 : lo * ((m.length : Rat) + ((1 : Nat) : Rat)) = lo * (m.length : Rat) + lo := by
        have : ((1 : Nat) : Rat) = 1 := rfl
        rw [this, Rat.mul_add, Rat.mul_one]
      have e2 : hi * ((m.length : Rat) + ((1 : Nat) : Rat)) = hi * (m.length : Rat) + hi := by
        have : ((1 : Nat) : Rat) = 1 := rfl
        rw [this, Rat.mul_add, Rat.mul_one]
      rw [e1, e2]
      have a1 := ih'.1
      have a2 := ih'.2
      have b1 := hk.1
      have b2 := hk.2
      constructor <;> grind
  have hs := hsum l h
  have hpos : (0 : Rat) < (l.length : Rat) := Rat.natCast_pos.mpr (List.length_pos_iff.mpr hl)
  unfold meanQ
  constructor
  · apply Rat.not_lt.mp
    intro hlt
    rw [Rat.div_lt_iff hpos] at hlt
    exact absurd hs.1 (Rat.not_le.mpr hlt)
  · apply Rat.not_lt.mp
    intro hlt
    rw [Rat.lt_div_iff hpos] at hlt
    exact absurd hs.2 (Rat.not_le.mpr hlt)

/-- 확정 값은 쓴 track 의 값 범위 안 (모든 결정된 값이 [lo, hi] 면) -/
theorem final_value_bounds (need : Nat) (third : Option Nat) (kinds : List TKind) (hn : 1 ≤ need) (lo hi : Rat)
    (hb : ∀ k ∈ kinds, lo ≤ k.q ∧ k.q ≤ hi) {v : Rat}
    (h : (condSummary need third kinds).state = .final) (hv : (condSummary need third kinds).value = some v) :
    lo ≤ v ∧ v ≤ hi := by
  obtain ⟨use, huse, hl, _, hval⟩ := final_mean need third kinds h
  rw [hval] at hv
  obtain rfl : meanQ use = v := Option.some.inj hv
  have hsub : ∀ k ∈ use, k ∈ kinds := by
    intro k hk
    rcases huse with hu | hu | hu <;> subst hu <;> exact (List.mem_filter.mp (List.mem_of_mem_take hk)).1
  exact meanQ_bounds use (use_ne_nil hn hl huse) lo hi (fun k hk => hb k (hsub k hk))

end GDT

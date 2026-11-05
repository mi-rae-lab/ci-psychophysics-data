import TMTF.Basic

/-!
# 잡음 씨앗 난수 — 앱 `js/stim.js` `makeRng` (mulberry32) 를 32비트 그대로 (Claude, 2026-10-24)

js: `a = (a + 0x6D2B79F5) >>> 0; t = imul(a ^ (a >>> 15), a | 1); t ^= t + imul(t ^ (t >>> 7), t | 61); u = (t ^ (t >>> 14)) >>> 0`.
`Math.imul` = 32비트 곱의 아래 32비트, `>>>` = 부호 없는 오른쪽 이동, `^` `|` 는 비트 연산, `t + imul(…)` 는 2³³ 보다 작아 정확한
수 덧셈 뒤 `^` 가 32비트로 자름 → 모두 UInt32(2³² 로 나눈 나머지) 연산과 같음. 같은 씨앗에서 js 와 같은 수가 나오는지는
cross_check.js 의 RNG 줄(씨앗 수백 개)로 대조.

* `uniform_range`     uniform = u / 2³² ∈ [0, 1) — 0 은 나올 수 있어 js gauss 는 u = 0 이면 다시 뽑음(log 0 막음)
* `state_injective`   상태는 씨앗 + k·0x6D2B79F5 (mod 2³²) 이고 0x6D2B79F5 가 홀수라 k = 0 … 2³²−1 에서 모두 다름
                      → 한 구간을 만드는 데 쓰는 수(≤ 65,536 개)는 상태가 되풀이되지 않음
* `state_formula`     k 번 뒤 상태 = (씨앗 + k·γ) mod 2³²
-/

namespace TMTF

def gammaU : UInt32 := 0x6D2B79F5
def gammaN : Nat := 1831565813

theorem gamma_eq : gammaU.toNat = gammaN := by decide

/-- 출력 섞기 (상태 → 32비트 출력) -/
def mbMix (a : UInt32) : UInt32 :=
  let t := (a ^^^ (a >>> 15)) * (a ||| 1)
  let t := t ^^^ (t + (t ^^^ (t >>> 7)) * (t ||| 61))
  t ^^^ (t >>> 14)

/-- 한 번 뽑기: (다음 상태, 출력) -/
def mbNext (a : UInt32) : UInt32 × UInt32 := (a + gammaU, mbMix (a + gammaU))

/-- k 번 뽑은 뒤 상태 -/
def mbState (s : UInt32) : Nat → UInt32
  | 0 => s
  | k + 1 => (mbNext (mbState s k)).1

/-- 처음 k 개 출력 -/
def mbOutputs (s : UInt32) (k : Nat) : List UInt32 := (List.range k).map (fun i => mbMix (mbState s (i + 1)))

def uniformQ (u : UInt32) : Rat := (u.toNat : Rat) / 4294967296

theorem uniform_range (u : UInt32) : 0 ≤ uniformQ u ∧ uniformQ u < 1 := by
  have hu : u.toNat < 4294967296 := u.toNat_lt_size
  have hpos : (0 : Rat) < 4294967296 := by decide +kernel
  unfold uniformQ
  constructor
  · rw [le_div_of_pos hpos]; have := Rat.natCast_nonneg (a := u.toNat); grind
  · rw [Rat.div_lt_iff hpos, Rat.one_mul]
    have : ((u.toNat : Nat) : Rat) < ((4294967296 : Nat) : Rat) := Rat.natCast_lt_natCast.mpr hu
    exact this

theorem state_formula (s : UInt32) (k : Nat) : (mbState s k).toNat = (s.toNat + k * gammaN) % 4294967296 := by
  induction k with
  | zero => simp [mbState]
  | succ k ih =>
    simp only [mbState, mbNext]
    rw [UInt32.toNat_add, ih, gamma_eq]
    show (_ % 4294967296 + gammaN) % 4294967296 = _
    rw [Nat.mod_add_mod, Nat.succ_mul, Nat.add_assoc]

theorem gamma_coprime : Nat.Coprime 4294967296 gammaN := by decide +kernel

/-- 상태는 2³² 번 안에서 되풀이되지 않음 -/
theorem state_injective (s : UInt32) {j k : Nat} (hjk : j < k) (hk : k < 4294967296) : mbState s j ≠ mbState s k := by
  intro heq
  have h := congrArg UInt32.toNat heq
  rw [state_formula, state_formula] at h
  -- (X + D) % M = X % M (X = s + jγ, D = (k−j)γ) → D % M = 0
  have hsplit : s.toNat + k * gammaN = (s.toNat + j * gammaN) + (k - j) * gammaN := by
    rw [Nat.add_assoc, ← Nat.add_mul, Nat.add_sub_cancel' (Nat.le_of_lt hjk)]
  rw [hsplit, Nat.add_mod] at h
  have hx : (s.toNat + j * gammaN) % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
  have hd : (k - j) * gammaN % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
  have h0 : (k - j) * gammaN % 4294967296 = 0 := by omega
  have hdvd : 4294967296 ∣ (k - j) * gammaN := Nat.dvd_of_mod_eq_zero h0
  have hdvd' : 4294967296 ∣ (k - j) := Nat.Coprime.dvd_of_dvd_mul_right gamma_coprime hdvd
  have hle : 4294967296 ≤ k - j := Nat.le_of_dvd (by omega) hdvd'
  omega

end TMTF

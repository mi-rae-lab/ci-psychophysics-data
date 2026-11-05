import TMTF.Basic

/-!
# ‘우연 수준’ 판정 — 앱 `js/track.js` `binomTail` · `chance()` 의 정확한 유리수판 (Claude, 2026-10-24)

js: `c = 1; for j < i: c = c·(n − j)/(j + 1)` (= C(n, i)), `s += c·p0^i·(1 − p0)^(n − i)` (i = k … n), `Math.min(1, s)`,
판정: 0 dB 시행이 6번 이상일 때 p > 0.05 이면 ‘우연 수준’ (p0 = 1/nAFC). 여기서는 같은 식을 정확한 유리수로 (`cQ` · `tailQ`).
js 부동소수 값 · 판정과의 대조는 cross_check.js 의 TRACK · PV 줄.

* `cQ_small`        C(n, i) 의 곱 공식이 작은 경우 파스칼 값과 같음(보기)
* `report_*`        종합 보고서의 ‘모르겠음 뺀’ 이항 검정 6개의 p 값을 정확히: 28/46 · 18/28 (p0 = 1/2), 5/11 · 6/12 (p0 = 1/3),
                    7/7 = 1/128, 24/41 — 모두 보고서 숫자(0.092 · 0.0925 · 0.289 · 0.178 · 0.0078 · 0.174)와 같음
-/

namespace TMTF

/-- js 의 곱 공식 c_i = Π_{j<i} (n − j)/(j + 1) -/
def cQ (n : Nat) : Nat → Rat
  | 0 => 1
  | i + 1 => cQ n i * ((n - i : Nat) : Rat) / ((i + 1 : Nat) : Rat)

/-- js `binomTail(k, n, p0)` 의 합 (Math.min(1, ·) 앞) -/
def tailQ (k n : Nat) (p : Rat) : Rat :=
  ((List.range (n + 1 - k)).map (fun t => cQ n (k + t) * p ^ (k + t) * (1 - p) ^ (n - (k + t)))).foldr (· + ·) 0

/-- `chance()` 의 판정: 0 dB 시행 n0 < 6 이면 판정 없음, 아니면 p > 1/20 이면 ‘우연 수준’ -/
def atChanceQ (k0 n0 nAFC : Nat) : Option Bool :=
  if n0 < 6 then none else some (decide ((1 : Rat) / 20 < tailQ k0 n0 (1 / (nAFC : Rat))))

theorem cQ_small : cQ 5 2 = 10 ∧ cQ 10 3 = 120 ∧ cQ 46 23 = 8233430727600 := by decide +kernel

theorem report_uw75_right : 919 / 10000 < tailQ 28 46 (1 / 2) ∧ tailQ 28 46 (1 / 2) < 920 / 10000 := by decide +kernel
theorem report_uw100_right : 924 / 10000 < tailQ 18 28 (1 / 2) ∧ tailQ 18 28 (1 / 2) < 925 / 10000 := by decide +kernel
theorem report_dr75_right : 2889 / 10000 < tailQ 5 11 (1 / 3) ∧ tailQ 5 11 (1 / 3) < 2890 / 10000 := by decide +kernel
theorem report_dr100_right : 1777 / 10000 < tailQ 6 12 (1 / 3) ∧ tailQ 6 12 (1 / 3) < 1778 / 10000 := by decide +kernel
theorem report_uw75_left2 : tailQ 7 7 (1 / 2) = 1 / 128 := by decide +kernel
theorem report_uw100_left2 : 1744 / 10000 < tailQ 24 41 (1 / 2) ∧ tailQ 24 41 (1 / 2) < 1745 / 10000 := by decide +kernel

/-- 판정: 7/7 만 ‘우연 수준 아님’, 나머지 다섯은 ‘우연 수준’ (p > 0.05) -/
theorem report_decisions :
    atChanceQ 28 46 2 = some true ∧ atChanceQ 18 28 2 = some true ∧ atChanceQ 5 11 3 = some true ∧
    atChanceQ 6 12 3 = some true ∧ atChanceQ 7 7 2 = some false ∧ atChanceQ 24 41 2 = some true := by decide +kernel

end TMTF

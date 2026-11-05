import SRD

/-!
JS ↔ Lean 전수 대조의 Lean 쪽 (Claude, 2026-10-21 — 와우SRD 1.0.0)
  lake build crosscheck && .lake/build/bin/crosscheck.exe <입력> <출력>
증명된 정의(SRD.* — 계산은 증명된 @[csimp] 등식으로 빠른 쪽)를 그대로 불러 줄마다 씀. tools/lean/cross_check.js 가
같은 입력으로 앱의 js 함수를 불러 같은 꼴의 줄을 만들고 한 줄씩 비교함.
입력 줄 → 출력 줄:
  RNG 씨앗 개수          → RNG 씨앗 u32들 다음상태
  INT 씨앗 n들           → INT 씨앗 결과들 다음상태                  (js `int(n)`)
  PLAN 씨앗 개수         → PLAN 씨앗 번호 자리 위상u32 씨앗3 흔들기3 다음상태   (js `TrialPlan.draw` 를 차례로)
  ORDER 씨앗             → ORDER 씨앗 72칸 다음상태                 (js `ConstPlan.order`)
  STAIR 번호 응답        → STAIR 번호 상태 칸 연속정답 방향 유효 기술실패 시도 이동 반전칸들 반전유효번호들 반전끝 역치 이동들 막힌끝들
  CLASS 번호 응답        → CLASS 번호 상태 이유 쉬운끝근처 어려운끝근처 앞쉬운막힘 우연이상아님 역치 창셈 Fisher신뢰성부족 아래확인 위확인
  CLIN 번호 씨앗 응답    → CLIN 번호 상태 자리 유효 기술실패 시도 유효밀도들
  SUM 번호 종류들        → SUM 번호 상태 값                         (js `wonSummary`)
  BTAB N                 → B n k 분자 분모 판정      (1 ≤ n ≤ N, 0 ≤ k ≤ n — js `binomGeThird` · `lt05`)
  FTAB N                 → F a b c d 분자 분모 판정  (a+b+c+d ≤ N — js `fisherGreater` · `lt05`)
  FONE a b c d           → F a b c d 분자 분모 판정  (표 하나 — 합 41–150 의 앱 꼴 · 끝 표, 2026-10-22)
  TTAB N                 → T n k 아래 위            (1 ≤ n ≤ N — 정확 ℤ[√2] 판정; js 는 부동소수 `Stats.le/ge(…, 1/√2) < 0.05`)
  TSUM N                 → TSUM n a b               (Σ_j 2ⁿ·P(X = j) = a + b√2 — 확률 합 1 이면 a = 2ⁿ, b = 0)
응답 글자: C 맞힘 · W 틀림 · X 기술적 실패.
-/

open SRD

def b01 (b : Bool) : String := if b then "1" else "0"
def csvN (l : List Nat) : String := if l.isEmpty then "-" else ",".intercalate (l.map toString)
def csvI (l : List Int) : String := if l.isEmpty then "-" else ",".intercalate (l.map toString)

def stStr : StStatus → String
  | .running => "running" | .reversalTarget => "reversal_target_reached"
  | .trialCap => "trial_cap_before_reversal_target" | .techFail => "technical_failure"

def moveChar : Move → Char
  | .stay => 'S' | .move => 'M' | .blocked => 'B' | .invalid => 'X'

def aStStr : AStatus → String
  | .completeInRange => "complete_in_range" | .trialCap => "trial_cap_before_reversal_target" | .techFail => "technical_failure"
  | .insufficient => "insufficient_data" | .unreliable => "unreliable_responses" | .belowRange => "threshold_below_range"
  | .nearEasy => "threshold_near_easy_end" | .aboveRange => "threshold_above_range" | .nearHard => "threshold_near_hard_end"

def aRsStr : AReason → String
  | .none => "-" | .bothEnds => "both_ends_blocked" | .easyWorse => "easy_worse_than_harder" | .easyBelow => "easy_below_target"
  | .easyBlocked => "easy_blocked" | .hardAbove => "hard_above_target" | .hardBlocked => "hard_blocked"

def cStStr : CStatus → String
  | .running => "running" | .complete => "complete" | .techFail => "technical_failure"

def sStStr : SState → String
  | .provisional => "provisional" | .final => "final" | .below => "below" | .low => "low"
  | .above => "above" | .high => "high" | .mixed => "mixed"

def outcomesOf (s : String) : List Outcome :=
  s.toList.map (fun c => if c == 'C' then .correct else if c == 'W' then .wrong else .invalid)

def thrStr : Option (Nat × Nat) → String
  | some (s, c) => s!"{s}/{c}"
  | none => "-"

def kindOf (s : String) : TKind :=
  match s.splitOn ":" with
  | ["n", a, b] => .num a.toNat! b.toNat!
  | ["below"] => .below | ["easy"] => .easy | ["above"] => .above | ["hard"] => .hard
  | _ => .none

def boundStr : Option Bound → String
  | none => "-"
  | some b => s!"{b.nWin},{b.easyBlocksWin},{b.hardBlocksWin},{b.easyBlocksBefore},{b01 b.touchedEasy},{b01 b.touchedHard},{b.n0},{b.k0},{b.nHarder},{b.kHarder},{b.nH},{b.kH}"

def main (args : List String) : IO Unit := do
  let inPath := args.getD 0 "cross_in.txt"
  let outPath := args.getD 1 "cross_lean.txt"
  let lines ← IO.FS.lines inPath
  IO.FS.withFile outPath .write fun h => do
    for ln in lines do
      match ln.trimRight.splitOn " " with
      | ["RNG", seed, cnt] =>
        match Xo.fromHex seed with
        | none => h.putStrLn s!"RNG {seed} 씨앗오류"
        | some x0 =>
          let mut x := x0
          let mut out : List Nat := []
          for _ in [0:cnt.toNat!] do
            let (u, x') := x.next
            out := out ++ [u.toNat]
            x := x'
          h.putStrLn s!"RNG {seed} {csvN out} {x.hex}"
      | ["INT", seed, ns] =>
        match Xo.fromHex seed with
        | none => h.putStrLn s!"INT {seed} 씨앗오류"
        | some x0 =>
          let mut x := x0
          let mut out : List Nat := []
          for n in (ns.splitOn ",").map String.toNat! do
            let (r, x') := x.int n
            out := out ++ [r]
            x := x'
          h.putStrLn s!"INT {seed} {csvN out} {x.hex}"
      | ["PLAN", seed, cnt] =>
        match Xo.fromHex seed with
        | none => h.putStrLn s!"PLAN {seed} 씨앗오류"
        | some x0 =>
          let mut x := x0
          for i in [0:cnt.toNat!] do
            let (p, x') := drawPlan x
            x := x'
            h.putStrLn s!"PLAN {seed} {i} {p.targetPos} {p.thetaU.toNat} {",".intercalate p.seeds} {csvI p.roves} {x.hex}"
      | ["ORDER", seed] =>
        match Xo.fromHex seed with
        | none => h.putStrLn s!"ORDER {seed} 씨앗오류"
        | some x0 =>
          let (o, x) := clinOrder x0
          h.putStrLn s!"ORDER {seed} {csvN o} {x.hex}"
      | ["STAIR", id, seq] =>
        let (s, trs) := run wonCfg (init wonCfg) (outcomesOf seq)
        h.putStrLn s!"STAIR {id} {stStr s.status} {s.k} {s.streak} {s.lastDir} {s.valid} {s.tech} {s.attempts} {s.moves} {csvN (s.revs.map (·.k))} {csvN (s.revs.map (·.validNo))} {csvN (s.revs.map (·.atBound))} {thrStr (threshold wonCfg s)} {String.mk (trs.map (moveChar ·.move))} {String.mk (trs.map (fun t => Char.ofNat (48 + t.blockedAt)))}"
      | ["CLASS", id, seq] =>
        let (s, trs) := run wonCfg (init wonCfg) (outcomesOf seq)
        let r := classify wonCfg s trs
        h.putStrLn s!"CLASS {id} {aStStr r.status} {aRsStr r.reason} {b01 r.nearEasy} {b01 r.nearHard} {b01 r.earlyEasy} {b01 r.notAboveChance} {thrStr r.thr} {boundStr r.bound} {b01 r.sigEasyWorse} {b01 r.below} {b01 r.above}"
      | ["CLIN", id, seed, seq] =>
        match Xo.fromHex seed with
        | none => h.putStrLn s!"CLIN {id} 씨앗오류"
        | some x0 =>
          let (ord, _) := clinOrder x0
          let (s, trs) := crun ord 72 10 cinit (outcomesOf seq)
          h.putStrLn s!"CLIN {id} {cStStr s.status} {s.slot} {s.valid} {s.tech} {s.attempts} {csvN ((trs.filter (·.isValid)).map (·.k))}"
      | ["SUM", id, kinds] =>
        let r := wonSummary ((kinds.splitOn ",").map kindOf)
        let v := match r.2 with | some q => s!"{q.num}/{q.den}" | none => "-"
        h.putStrLn s!"SUM {id} {sStStr r.1} {v}"
      | ["BTAB", nn] =>
        for n in [1:nn.toNat! + 1] do
          for k in [0:n + 1] do
            h.putStrLn s!"B {n} {k} {geThirdNum n k} {geThirdDen n} {b01 (geThirdSig n k)}"
      | ["FONE", a, b, c, d] =>
        let a := a.toNat!
        let b := b.toNat!
        let c := c.toNat!
        let d := d.toNat!
        h.putStrLn s!"F {a} {b} {c} {d} {fgNum a b c d} {fgDen a b c d} {b01 (fgSig a b c d)}"
      | ["FTAB", nn] =>
        let N := nn.toNat!
        for n in [0:N + 1] do
          for a in [0:n + 1] do
            for b in [0:n + 1 - a] do
              for c in [0:n + 1 - a - b] do
                let d := n - a - b - c
                h.putStrLn s!"F {a} {b} {c} {d} {fgNum a b c d} {fgDen a b c d} {b01 (fgSig a b c d)}"
      | ["TTAB", nn] =>
        for n in [1:nn.toNat! + 1] do
          let R := rowArr n
          let SP := spArr n
          let TP := tpArr n
          for k in [0:n + 1] do
            let L := tailLeWith R SP TP n k
            let G := tailGeWith R SP TP n k
            h.putStrLn s!"T {n} {k} {b01 (negZ2 (20 * L.a - 2 ^ n) (20 * L.b))} {b01 (negZ2 (20 * G.a - 2 ^ n) (20 * G.b))}"
      | ["TSUM", nn] =>
        for n in [0:nn.toNat! + 1] do
          let S := tailLe n n
          h.putStrLn s!"TSUM {n} {S.a} {S.b}"
      | _ => h.putStrLn s!"? {ln}"

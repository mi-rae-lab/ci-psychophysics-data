import GDT

/-!
JS ↔ Lean 전수 대조의 Lean 쪽 (Claude, 2026-11-01 — 와우GDT 1.0.0, 와우SMD CrossCheck.lean 의 틀)
  lake build crosscheck && .lake/build/bin/crosscheck.exe <입력> <출력>
증명된 정의(GDT.* — 계산은 증명된 @[csimp] 등식 · 행을 밖에서 받는 꼴 `geNumW` · `fgNumW` · `halfLeNumW` 로 빠른 쪽)를 그대로 불러 줄마다 씀.
tools/lean/cross_check.js 가 같은 입력으로 앱의 js 함수를 불러 같은 꼴의 줄을 만들고 한 줄씩 비교함.
입력 줄 → 출력 줄 (절차 = zeng · xie · blank):
  RNG 씨앗 개수               → RNG 씨앗 u32들 다음상태
  INT 씨앗 n들                → INT 씨앗 결과들 다음상태                          (js `int(n)`)
  PLAN 씨앗 조건 q 개수       → PLAN 씨앗 조건 q 번호 자리 씨앗q개 흔들기 다음상태 (js `TrialPlan.draw(rng, q, cond)` 를 차례로)
  LAD 절차                    → LAD 절차 종류 M 표 valueOf들 표본수들            (js LADDERS · Stair.valueOf · gapNOf)
  PCFG 절차                   → PCFG 절차 계단 설정 · 분석 · 반복 값               (js Stair.cfgFrom(P) · P.task · P.analysis · P.repeat)
  STAIR 절차 번호 응답        → STAIR … 상태 i 연속정답 방향 유효 실패 시도 이동 막힌짧은끝 막힌긴끝 반전i들 반전유효번호들 반전시도번호들 반전끝 반전방향
                                  역치(합/개수) 제시i들 이동들 막힌끝들 요청방향들 요청step들 실제step들 잘림들 뒤연속정답들 뒤상태들
  CLASS 절차 번호 응답        → CLASS … 상태 이유 표시5 숫자역치 계단역치 창셈15 판정4 우연p 유효 정답 시도 실패 막힘 최대i 최소i
  SUM 절차 번호 종류들        → SUM … 상태 정확값 더필요 쓴수 결정수 값검증실패 규칙   (js `condSummary`)
  BTAB q N                    → B q n k 분자 분모 판정  (1 ≤ n ≤ N, 0 ≤ k ≤ n — js `binomGe(k, n, q)` · `lt05`)
  FTAB N · FONE a b c d       → F a b c d 분자 분모 판정 (a+b+c+d ≤ N 전부 · 표 하나 — js `fisherGreater` · `lt05`)
  TTAB N                      → T n k 아래 위   (목표 1/√2 — 정확 ℤ[√2] 판정; js 는 부동소수 `Stats.le/ge(…, targetPOf(zeng)) < 0.05`)
  HTAB N                      → H n k 아래 위   (목표 1/2 — 정확한 유리수; js `Stats.le/ge(…, targetPOf(blank)) < 0.05`)
  TSUM N                      → TSUM n a b      (Σ_j 2ⁿ·P(X = j) = a + b√2 — 확률 합 1 이면 a = 2ⁿ, b = 0)
응답 글자: C 맞힘 · W 틀림 · X 기술적 실패.
-/

open GDT

def b01 (b : Bool) : String := if b then "1" else "0"
def csvN (l : List Nat) : String := if l.isEmpty then "-" else ",".intercalate (l.map toString)
def csvI (l : List Int) : String := if l.isEmpty then "-" else ",".intercalate (l.map toString)
def digits (l : List Nat) : String := String.mk (l.map (fun d => Char.ofNat (48 + d)))
def ratStr (q : Rat) : String := s!"{q.num}/{q.den}"

def stStr : StStatus → String
  | .running => "running" | .reversalTarget => "reversal_target_reached" | .floorStop => "floor_stop"
  | .ceilingStop => "ceiling_stop" | .trialCap => "trial_cap_before_reversal_target" | .techFail => "technical_failure"

def stChar : StStatus → Char
  | .running => 'R' | .reversalTarget => 'T' | .floorStop => 'F' | .ceilingStop => 'C' | .trialCap => 'P' | .techFail => 'X'

def moveChar : Move → Char
  | .stay => 'S' | .move => 'M' | .blocked => 'B' | .invalid => 'X'

def dirChar (d : Int) : Char := if d < 0 then '-' else if d > 0 then '+' else '0'

def aStStr : AStatus → String
  | .completeInRange => "complete_in_range" | .trialCap => "trial_cap_before_reversal_target" | .techFail => "technical_failure"
  | .insufficient => "insufficient_data" | .nearFloor => "threshold_near_floor" | .nearCeiling => "threshold_near_ceiling"
  | .unreliable => "unreliable_responses" | .aboveRange => "threshold_above_range" | .belowRange => "threshold_below_range"
  | .aboveWindow => "threshold_above_window" | .notAboveChance => "threshold_not_above_chance"

def aRsStr : AReason → String
  | .none => "-" | .floorStop => "floor_stop" | .ceilingStop => "ceiling_stop" | .bothEnds => "both_ends_blocked"
  | .ceilWorse => "ceiling_worse_than_lower" | .ceilBelow => "ceiling_below_target" | .ceilBlocked => "ceiling_blocked"
  | .floorAbove => "floor_above_target" | .floorBlocked => "floor_blocked" | .windowBelow => "window_below_target"
  | .notAboveChance => "not_above_chance"

def sStStr : SState → String
  | .provisional => "provisional" | .final => "final" | .paper => "paper" | .above => "above" | .ceil => "ceil"
  | .high => "high" | .below => "below" | .floor => "floor" | .mixed => "mixed"

def outcomesOf (s : String) : List Outcome :=
  s.toList.map (fun c => if c == 'C' then .correct else if c == 'W' then .wrong else .invalid)

def pairStr : Option (Int × Nat) → String
  | some (s, c) => s!"{s}/{c}"
  | none => "-"

def optN : Option Nat → String
  | some n => toString n
  | none => "-"

def boundStr : Option Bound → String
  | none => "-"
  | some b => s!"{b.nWin},{b.kWin},{b.ceilBlocksWin},{b.floorBlocksWin},{b.ceilBlocksBefore},{b.floorBlocksBefore}," ++
      s!"{b01 b.touchedCeil},{b01 b.touchedFloor},{b.nC},{b.kC},{b.nL},{b.kL},{b.nF},{b.kF},{optN b.firstValidNo}"

def toIntD (s : String) : Int := (s.toInt?).getD 0

/-- SUM 입력의 결과 종류 글자 → (분류 상태 · 역치 · 값 검증 · 설정 바뀜) → js `outcome` 의 종류 (`kindOf`) -/
def tokKind (P : Proto) (tok : String) : TKind :=
  match tok.splitOn ":" with
  | ["n", a, b] => kindOf P .completeInRange (some (toIntD a, b.toNat!)) true false
  | ["bad", a, b] => kindOf P .completeInRange (some (toIntD a, b.toNat!)) false false
  | ["chg", a, b] => kindOf P .completeInRange (some (toIntD a, b.toNat!)) true true
  | ["above"] => kindOf P .aboveRange none true false
  | ["ceil"] => kindOf P .nearCeiling none true false
  | ["up"] => kindOf P .aboveWindow none true false
  | ["upc"] => kindOf P .notAboveChance none true false
  | ["below"] => kindOf P .belowRange none true false
  | ["floor"] => kindOf P .nearFloor none true false
  | ["unrel"] => kindOf P .unreliable none true false
  | ["cap"] => kindOf P .trialCap none true false
  | ["ins"] => kindOf P .insufficient none true false
  | _ => kindOf P .techFail none true false

def ruleStr : Option (Bool × Bool × Option Rat) → String
  | none => "-"
  | some (t, c, d) => b01 t ++ b01 c ++ (match d with | some q => ":" ++ ratStr q | none => "")

def targetStr : TargetP → String
  | .sqrtHalf => "s2"
  | .half => "h"

def main (args : List String) : IO Unit := do
  let inPath := args.getD 0 "cross_in.txt"
  let outPath := args.getD 1 "cross_lean.txt"
  let lines ← IO.FS.lines inPath
  -- 파스칼 행 0 … 200 을 한 번만 (FONE · FTAB 이 읽음) — 값은 `pascalRow m` 그대로
  let rows : Array (Array Nat) := ((List.range 201).map (fun m => (pascalRow m).toArray)).toArray
  IO.FS.withFile outPath .write fun h => do
    for ln in lines do
      match ln.trimRight.splitOn " " with
      | ["RNG", seed, cnt] =>
        match Xo.fromHex seed with
        | none => h.putStrLn s!"RNG {seed} 씨앗오류"
        | some x0 =>
          let mut x := x0
          let mut out : Array Nat := #[]
          for _ in [0:cnt.toNat!] do
            let (u, x') := x.next
            out := out.push u.toNat
            x := x'
          h.putStrLn s!"RNG {seed} {csvN out.toList} {x.hex}"
      | ["INT", seed, ns] =>
        match Xo.fromHex seed with
        | none => h.putStrLn s!"INT {seed} 씨앗오류"
        | some x0 =>
          let mut x := x0
          let mut out : Array Nat := #[]
          for n in (ns.splitOn ",").map String.toNat! do
            let (r, x') := x.int n
            out := out.push r
            x := x'
          h.putStrLn s!"INT {seed} {csvN out.toList} {x.hex}"
      | ["PLAN", seed, cond, qs, cnt] =>
        match Xo.fromHex seed with
        | none => h.putStrLn s!"PLAN {seed} 씨앗오류"
        | some x0 =>
          let q := qs.toNat!
          let mut x := x0
          for i in [0:cnt.toNat!] do
            let (p, x') := drawPlan x q (condRove cond)
            x := x'
            let rv := match p.roves with
              | none => "-"
              | some rs => ",".intercalate (rs.map (fun (r : Nat × Nat) => s!"{r.1}:{r.2}"))
            h.putStrLn s!"PLAN {seed} {cond} {q} {i} {p.targetPos} {",".intercalate p.seeds} {rv} {x.hex}"
      | ["LAD", pn] =>
        match protoOf pn with
        | none => h.putStrLn s!"LAD {pn} 절차오류"
        | some P =>
          let L := P.cfg.ladder
          let is := List.range L.len
          let kind := match L.kind with | .geo => "geo" | .list => "list"
          h.putStrLn s!"LAD {pn} {kind} {L.len} {csvN L.vals} {csvI (is.map (valueOf L))} {csvN (is.map (gapN L))}"
      | ["PCFG", pn] =>
        match protoOf pn with
        | none => h.putStrLn s!"PCFG {pn} 절차오류"
        | some P =>
          let c := P.cfg
          let third := match P.third with | some t => toString t | none => "-"
          let vk := if P.paper then "paper_value" else "threshold"
          let mean := match c.ladder.kind with | .geo => "geo" | .list => "arith"
          h.putStrLn (s!"PCFG {pn} {c.startI} {c.ceilI} 0 {c.nHarder} 1 {c.coarseI} {c.fineI} {c.switchFrom} {c.totalRev} {c.retained} " ++
            s!"{c.boundaryStop} {c.maxValid} {c.maxTech} {P.blocksMax} {P.q} {targetStr P.target} {b01 P.gate} {vk} {P.need} {third} {mean} " ++
            s!"{b01 (convOk P.target P.q)} 1/{P.q}")
      | ["STAIR", pn, id, seq] =>
        match protoOf pn with
        | none => h.putStrLn s!"STAIR {pn} {id} 절차오류"
        | some P =>
          let (s, trs) := run P.cfg (init P.cfg) (outcomesOf seq)
          h.putStrLn (s!"STAIR {pn} {id} {stStr s.status} {s.i} {s.streak} {s.lastDir} {s.valid} {s.tech} {s.attempts} {s.moves} " ++
            s!"{s.blockedFloor} {s.blockedCeil} {csvN (s.revs.map (·.i))} {csvN (s.revs.map (·.validNo))} {csvN (s.revs.map (·.attemptNo))} " ++
            s!"{csvN (s.revs.map (·.atBound))} {csvI (s.revs.map (·.dirAfter))} {pairStr (threshold P.cfg s)} " ++
            s!"{csvN (trs.map (·.i))} {String.mk (trs.map (moveChar ·.move))} {digits (trs.map (·.blockedAt))} {String.mk (trs.map (dirChar ·.reqDir))} " ++
            s!"{digits (trs.map (·.reqStep))} {digits (trs.map (·.effStep))} {String.mk (trs.map (fun t => if t.clamped then '1' else '0'))} " ++
            s!"{digits (trs.map (·.postStreak))} {String.mk (trs.map (stChar ·.statusAfter))}")
      | ["CLASS", pn, id, seq] =>
        match protoOf pn with
        | none => h.putStrLn s!"CLASS {pn} {id} 절차오류"
        | some P =>
          let (s, trs) := run P.cfg (init P.cfg) (outcomesOf seq)
          let r := classify P s trs
          let pAll := match r.pAll with | some (a, b) => s!"{a}/{b}" | none => "-"
          h.putStrLn (s!"CLASS {pn} {id} {aStStr r.status} {aRsStr r.reason} " ++
            s!"{b01 r.nearCeil}{b01 r.nearFloor}{b01 r.earlyCeil}{b01 r.ruleChance}{b01 r.notAboveChance} " ++
            s!"{pairStr r.thr} {pairStr r.thrRaw} {boundStr r.bound} " ++
            s!"{b01 r.sigCeilWorse}{b01 r.ceilBelow}{b01 r.floorAbove}{b01 r.winBelow} {pAll} " ++
            s!"{r.nValid} {r.nCorrect} {r.nAttempts} {r.nTech} {r.nBlocked} {optN r.maxI} {optN r.minI}")
      | ["SUM", pn, id, kinds] =>
        match protoOf pn with
        | none => h.putStrLn s!"SUM {pn} {id} 절차오류"
        | some P =>
          let r := protoSummary P ((kinds.splitOn ",").map (tokKind P))
          let v := match r.value with | some q => ratStr q | none => "-"
          h.putStrLn s!"SUM {pn} {id} {sStStr r.state} {v} {r.needMore} {r.used} {r.det} {r.nInvalid} {ruleStr r.rule}"
      | ["BTAB", qs, nn] =>
        let q := qs.toNat!
        for n in [1:nn.toNat! + 1] do
          let row := (pascalRow n).toArray
          let den := geDen q n
          for k in [0:n + 1] do
            let num := geNumW row q n k
            h.putStrLn s!"B {q} {n} {k} {num} {den} {b01 (decide (20 * num < den))}"
      | ["FONE", a, b, c, d] =>
        let a := a.toNat!
        let b := b.toNat!
        let c := c.toNat!
        let d := d.toNat!
        let num := fgNumW (rows.getD (a + b) #[]) (rows.getD (c + d) #[]) a b c d
        let den := fgDenW (rows.getD (a + b + (c + d)) #[]) a b c d
        h.putStrLn s!"F {a} {b} {c} {d} {num} {den} {b01 (decide (20 * num < den))}"
      | ["FTAB", nn] =>
        let N := nn.toNat!
        for n in [0:N + 1] do
          for a in [0:n + 1] do
            for b in [0:n + 1 - a] do
              for c in [0:n + 1 - a - b] do
                let d := n - a - b - c
                let num := fgNumW (rows.getD (a + b) #[]) (rows.getD (c + d) #[]) a b c d
                let den := fgDenW (rows.getD n #[]) a b c d
                h.putStrLn s!"F {a} {b} {c} {d} {num} {den} {b01 (decide (20 * num < den))}"
      | ["TTAB", nn] =>
        for n in [1:nn.toNat! + 1] do
          let R := rowArr n
          let SP := spArr n
          let TP := tpArr n
          for k in [0:n + 1] do
            let L := tailLeWith R SP TP n k
            let G := tailGeWith R SP TP n k
            h.putStrLn s!"T {n} {k} {b01 (negZ2 (20 * L.a - 2 ^ n) (20 * L.b))} {b01 (negZ2 (20 * G.a - 2 ^ n) (20 * G.b))}"
      | ["HTAB", nn] =>
        for n in [1:nn.toNat! + 1] do
          let row := (pascalRow n).toArray
          for k in [0:n + 1] do
            let le := decide (20 * halfLeNumW row n k < 2 ^ n)
            let ge := decide (20 * geNumW row 2 n k < geDen 2 n)
            h.putStrLn s!"H {n} {k} {b01 le} {b01 ge}"
      | ["TSUM", nn] =>
        for n in [0:nn.toNat! + 1] do
          let S := tailLe n n
          h.putStrLn s!"TSUM {n} {S.a} {S.b}"
      | _ => h.putStrLn s!"? {ln}"

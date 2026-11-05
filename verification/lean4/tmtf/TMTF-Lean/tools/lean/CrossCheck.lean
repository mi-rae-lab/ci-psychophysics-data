import TMTF

/-!
JS ↔ Lean 대조의 Lean 쪽 (Claude, 2026-10-24 — 와우TMTF 3.2, 와우SRD tools/lean/CrossCheck.lean 과 같은 방식)
  lake build crosscheck && .lake/build/bin/crosscheck.exe <입력> <출력>
증명한 모듈(TMTF.*)의 정의를 그대로 불러 줄마다 씀. tools/lean/cross_check.js 가 같은 입력으로 앱의 js(stim · track · protocols)를
불러 같은 꼴의 줄을 만들고 한 줄씩 비교함 (PV · GAIN 은 부동소수와 정확한 유리수를 허용 오차로).
입력 줄 → 출력 줄:
  RNG 씨앗 개수               → RNG 씨앗 u32들                         (js `makeRng(seed).uniform() × 2³²`)
  RAMP fs 경사ms N            → RAMP fs 경사ms N R 1                   (`rampLen`; js 는 make() 출력의 경사 이득에서 R 을 읽고 (2i+1)/(2R) · 앞뒤 대칭인지)
  BINS 종류 fs N              → BINS 종류 fs N gauss호출수             (js noise() 가 부르는 gauss 수 = 2 × 칸 수)
  SPEC 종류 fs N kref k들     → SPEC 종류 fs N k시작 k끝 · FLAT … 1 (wide · brick) · GAIN 종류 fs N k G2(k)/G2(kref) (bp)
                                                                       (N 이 2 의 거듭제곱일 때 js 출력의 DFT 로 칸 범위 · 모양을 잼)
  DUR fs 분자 분모            → DUR fs 분자 분모 N                     (`jsRound`)
  GRID                        → GRID … · CHOICES uw|deruiter|custom … · PAPER uw|deruiter …
  TRACK 번호 절차 응답        → TRACK 번호 절차 끝 천장 미완 깊이 run 방향 n0 k0 천장틀림 반전들 반전시행 시행깊이들 역치 우연
                                 · PV 번호 p(정확한 분수)            (`runTrack` · `thrQ` · `atChanceQ`, 응답 글자 C 맞힘 · W 틀림)
-/

open TMTF

def b01 (b : Bool) : String := if b then "1" else "0"
def csvN (l : List Nat) : String := if l.isEmpty then "-" else ",".intercalate (l.map toString)
def csvI (l : List Int) : String := if l.isEmpty then "-" else ",".intercalate (l.map toString)
def ratStr (q : Rat) : String := s!"{q.num}/{q.den}"

/-- js `nextPow2` -/
def nextPow2 (N : Nat) : Nat := go 1 64
where go (p fuel : Nat) : Nat := match fuel with
  | 0 => p
  | f + 1 => if p < N then go (2 * p) f else p

def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- js `noise()` 의 칸 범위 (kStart, kEnd) — wide: 20 Hz … fs/2, brick: 188 … 7938 Hz, bp: 1 … n/2 − 1 -/
def binRange (ty : String) (fs N : Nat) : Nat × Nat :=
  let n := nextPow2 N
  if ty = "bp" then (1, n / 2 - 1)
  else if ty = "brick" then (max 1 (ceilDiv (188 * n) fs), min (n / 2 - 1) (7938 * n / fs))
  else (max 1 (ceilDiv (20 * n) fs), min (n / 2 - 1) (fs * n / (2 * fs)))

def gaussCalls (ty : String) (fs N : Nat) : Nat :=
  let (a, b) := binRange ty fs N
  if a ≤ b then 2 * (b - a + 1) else 0

/-- 칸 k 의 주파수 k·fs/n 에서 G2 -/
def g2At (fs N k : Nat) : Rat := G2 (((k * fs : Nat) : Rat) / ((nextPow2 N : Nat) : Rat))

def customFms : List Nat := [2, 4, 5, 8, 10, 16, 32, 50, 56, 57, 58, 59, 61, 62, 63, 64, 66, 67, 68, 69, 75, 100, 128, 150, 200, 256, 300, 512]   -- 3.3.1: 66–69 Hz · 3.3.2: 61–63 Hz · 3.3.3: 56–59 Hz
def customPrFms : List Nat := [4, 8, 16, 32, 64, 128, 256]
def sortDedup (l : List Nat) : List Nat := (l.mergeSort (fun a b => decide (a ≤ b))).eraseDups

def protoOf (s : String) : Option TrackP :=
  match s with
  | "uw" => some uwP
  | "deruiter" => some drP
  | "std2" => some { uwP with nAFC := 2, stop4 := true }
  | "std3" => some { uwP with nAFC := 3, stop4 := true }
  | "short2" => some { drP with nAFC := 2, startDb := 0 }
  | "short3" => some { drP with nAFC := 3, startDb := 0 }
  | _ => none

/-- q·100 을 0 에서 먼 쪽으로 반올림 (js toFixed(2)) -/
def roundHund (q : Rat) : Int :=
  let a := q * 100
  if 0 ≤ a then (a + 1 / 2).floor else -((-a + 1 / 2).floor)

/-- js `String(+x.toFixed(2))` 꼴 -/
def fmtHund (r : Int) : String :=
  let s := if r < 0 then "-" else ""
  let a := r.natAbs
  let ip := a / 100
  let fp := a % 100
  if fp = 0 then s ++ toString ip
  else if fp % 10 = 0 then s ++ toString ip ++ "." ++ toString (fp / 10)
  else s ++ toString ip ++ "." ++ (if fp < 10 then "0" else "") ++ toString fp

def main (args : List String) : IO Unit := do
  let inPath := args.getD 0 "cross_in.txt"
  let outPath := args.getD 1 "cross_lean.txt"
  let lines ← IO.FS.lines inPath
  IO.FS.withFile outPath .write fun h => do
    for ln in lines do
      match ln.trimRight.splitOn " " with
      | ["RNG", seed, cnt] =>
        let s : UInt32 := UInt32.ofNat seed.toNat!
        let out := (mbOutputs s cnt.toNat!).map (·.toNat)
        h.putStrLn s!"RNG {seed} {csvN out}"
      | ["RAMP", fs, rms, n] =>
        h.putStrLn s!"RAMP {fs} {rms} {n} {rampLen fs.toNat! rms.toNat! n.toNat!} 1"
      | ["BINS", ty, fs, n] =>
        h.putStrLn s!"BINS {ty} {fs} {n} {gaussCalls ty fs.toNat! n.toNat!}"
      | ["SPEC", ty, fs, n, kref, ks] =>
        let fsN := fs.toNat!
        let nN := n.toNat!
        let (a, b) := binRange ty fsN nN
        h.putStrLn s!"SPEC {ty} {fs} {n} {a} {b}"
        if ty = "bp" then
          let r := g2At fsN nN kref.toNat!
          for k in (ks.splitOn ",").map String.toNat! do
            h.putStrLn s!"GAIN {ty} {fs} {n} {k} {ratStr (g2At fsN nN k / r)}"
        else
          h.putStrLn s!"FLAT {ty} {fs} {n} 1"
      | ["DUR", fs, a, b] =>
        let q : Rat := ((fs.toNat! : Nat) : Rat) * (((a.toNat! : Nat) : Rat) / ((b.toNat! : Nat) : Rat))
        h.putStrLn s!"DUR {fs} {a} {b} {jsRound q}"
      | ["GRID"] =>
        h.putStrLn s!"GRID {csvN fineFms}"
        h.putStrLn s!"CHOICES uw {csvN (sortDedup (fineFms ++ wonFms))}"
        h.putStrLn s!"CHOICES deruiter {csvN (sortDedup (fineFms ++ drFms))}"
        h.putStrLn s!"CHOICES custom {csvN (sortDedup (customFms ++ fineFms ++ customPrFms))}"
        h.putStrLn s!"PAPER uw {csvN (fineFms.filter (fun f => f ∈ wonFms))}"
        h.putStrLn s!"PAPER deruiter {csvN (fineFms.filter (fun f => f ∈ drFms))}"
      | ["TRACK", id, pr, seq] =>
        match protoOf pr with
        | none => h.putStrLn s!"TRACK {id} 절차오류"
        | some P =>
          let S := runTrack P (seq.toList.map (· == 'C'))
          let thr := match thrQ P S with
            | some q => fmtHund (roundHund q)
            | none => "-"
          let ch := match atChanceQ S.k0 S.n0 P.nAFC with
            | some b => b01 b
            | none => "-"
          h.putStrLn s!"TRACK {id} {pr} {b01 S.done} {b01 S.ceiling} {b01 S.incomplete} {S.depth} {S.run} {S.dir} {S.n0} {S.k0} {S.ceilMiss} {csvI S.reversals} {csvN S.revAt} {csvI (S.trials.map (·.1))} {thr} {ch}"
          if 6 ≤ S.n0 then
            h.putStrLn s!"PV {id} {ratStr (tailQ S.k0 S.n0 (1 / (P.nAFC : Rat)))}"
      | _ => h.putStrLn s!"? {ln}"

import SMRT

/-!
JS ↔ Lean 전수 대조의 Lean 쪽 (Claude, 2026-10-22 — 와우SMRT 1.1)
  lake build crosscheck && .lake/build/bin/crosscheck.exe <입력> <출력>
증명된 정의(SMRT.*)를 그대로 불러 줄마다 씀. 파스칼 행은 0 … 1000 을 한 번 만들어 씀 — 그 값 = `pascalRow`
(`rowsArr_getD`), 이항 · Fisher 분자/분모 = 증명된 `geThirdNum` · `f2Num` · `f2Den` (`geThirdNum_fast` · `f2Num_fast` · `f2Den_fast`).
tools/lean/cross_check.js 가 같은 입력으로 앱의 js 함수를 불러 같은 꼴의 줄을 만들고 한 줄씩 비교함.

입력 줄 → 출력 줄 (응답 글자 C 맞힘 · W 틀림, 빈 순서는 -)
  TRACK id 응답      → TRACK id 끝 천장 미완 칸 cRun wRun 방향 시행 맞힘 바닥시행 반전들 반전시행들 제시칸들 역치(합/개수) thr4 sd4 확인안됨 p가수 p지수
  RUN id 응답 같은파일 → RUN …(TRACK 과 같은 칸)          — 실제 기록 (js 쪽은 db.json 에 저장된 값을 씀)
  BTAB N             → B n k 확인안됨 p가수 p지수      (1 ≤ n ≤ N, 0 ≤ k ≤ n)
  F2TAB N            → F2 a b c d 판정 ~분자/분모      (a+b+c+d ≤ N — 양측 Fisher)
  F2ONE a b c d      → F2 …                            (표 하나)
  R4 S               → R4 S thr4                        (thr = S/60 의 넷째 자리, S = 0 … 1200)
  SDR 반전6개        → SDR 반전6개 thr4 sd4
  DIN k1 k2          → DIN k1 k2 판정 판정              (k = thr·10⁴ — js 쪽은 앱 finishTrack · 기록 점검 completeness 두 곳)
  CD ks1 ks2         → CD ks1 ks2 범위밖 cd2 diff2 T:cd2갈림,diff2갈림
  ZONE ks            → ZONE ks 2아래 2위 1.1위 0.3이하 mean2 sd2 T:mean2갈림,sd2갈림
  CLAIM 키 종류 …     → CLAIM 키 종류 보고값 계산값 OK|DIFF (+갈림)   — 앞의 RUN 줄로 계산 (보고서 대조)
  ── 1.2 (2026-11-02) 크기 로빙 실험 · 크기 구별 확인 ──
  LT id 응답          → LT id 끝 미완 db cRun 방향 시행 맞힘 바닥시행 천장시행 반전들 반전시행들 제시ΔL들 역치(합/개수) thr4 확인안됨 p가수 p지수 T:동점
  LRUN id 응답        → LRUN …(LT 와 같은 칸)                 — 실제 크기 구별 기록 (js 쪽은 저장 값)
  LBTAB N             → LB n k 확인안됨 p가수 p지수 T:동점     (2구간 우연 1/2, 1 ≤ n ≤ N)
  LZ S들              → LZ S들 thr4들 (구역 B% C% m2) ×2 T:m2동점,B동점,C동점   — S = 측정마다 마지막 6 반전 합, 평균 m = ΣS/(6·측정 수)
  RV 조건             → RV 조건 값들(반 dB)
  RS                  → RS 순서 연습수 본수            — 1.3 로빙 단독 회기 순서 (js ROVE_SEQ · ROVE_PLAN)
  RU n 값들           → RU n 값들 뽑은값 받은수 (또는 - -)    — js randUnbiased(n), 32비트 값을 차례로 줌
  PR 집합 규칙 Δh     → PR 집합 규칙 Δh 점수×6 분모(6n³)      — 보호 범위 (파이썬 tools/rove_protect.py 와 대조)
  RULE est se t90 t95 → RULE … 판정번호                         — 1차 판정 (파이썬 tools/rove_analysis.py verdict_t 와 대조, 소수 문자열 = 정확한 유리수)
-/

open SMRT

def b01 (b : Bool) : String := if b then "1" else "0"
def csvN (l : List Nat) : String := if l.isEmpty then "-" else ",".intercalate (l.map toString)
def parseCsv (s : String) : List Nat := if s == "-" then [] else (s.splitOn ",").map String.toNat!
def boolsOf (s : String) : List Bool := if s == "-" then [] else s.toList.map (· == 'C')

def maxRow : Nat := 1000

/-- 행 0 … 1000 (한 번만) -/
def rows : Array (Array Nat) := rowsArr maxRow

def gNum (n k : Nat) : Nat := geThirdNumWith (rows.getD n #[]) n k

def pStr (n k : Nat) : String :=
  if n = 0 then "- -" else
    let (m, e) := sig4 (gNum n k) (geThirdDen n)
    s!"{m} {e}"

def unvFast (n k : Nat) : Bool := n == 0 || decide (geThirdDen n < 20 * gNum n k)

structure RunRes where
  id : String
  st : St
  pres : List Nat
  resp : List Bool
  same : String
  thr4v : Option Nat

def runRes (id seqStr same : String) : RunRes :=
  let bs := boolsOf seqStr
  let (s, pres) := run smrtCfg (init smrtCfg) bs
  let t4 := match thrSum smrtCfg s with | some (S, c) => some (thr4 S c) | none => none
  { id := id, st := s, pres := pres, resp := bs.take pres.length, same := same, thr4v := t4 }

def trackLine (tag : String) (r : RunRes) : String :=
  let s := r.st
  let thr := thrSum smrtCfg s
  let thrS := match thr with | some (S, c) => s!"{S}/{c}" | none => "-"
  let t4 := match thr with | some (S, c) => toString (thr4 S c) | none => "-"
  let s4 := match thr with | some _ => toString (sd4 (usedRevs smrtCfg s)) | none => "-"
  s!"{tag} {r.id} {b01 s.done} {b01 s.ceiling} {b01 (resIncomplete smrtCfg s)} {s.idx} {s.cRun} {s.wRun} {s.dir} {s.nTrials} {s.nCorrect} {s.floorHits} {csvN s.revs} {csvN s.revAt} {csvN r.pres} {thrS} {t4} {s4} {b01 (unvFast s.nTrials s.nCorrect)} {pStr s.nTrials s.nCorrect}"

def f2Line (a b c d : Nat) : String :=
  let num := f2NumWith (rows.getD (a + b) #[]) (rows.getD (c + d) #[]) a c
  let den := (rows.getD (a + b + (c + d)) #[]).getD (a + c) 0
  s!"F2 {a} {b} {c} {d} {b01 (decide (20 * num < den))} ~{num}/{den}"

def intStr (i : Int) : String := toString i

/-! ## 보고서 대조 (CLAIM) -/

def findRun (rs : List RunRes) (id : String) : Option RunRes := rs.find? (·.id == id)

def thrsOf (rs : List RunRes) (ids : String) : Option (List Nat) :=
  ((ids.splitOn ",").map (fun i => (findRun rs i).bind (·.thr4v))).foldr
    (fun o acc => match o, acc with | some v, some l => some (v :: l) | _, _ => none) (some [])

/-- 제시 칸이 [lo, hi] 인 시행의 (맞힘, 시행) -/
def accOf (rs : List RunRes) (ids : String) (lo hi : Nat) : Nat × Nat :=
  (ids.splitOn ",").foldl (fun (acc : Nat × Nat) i =>
    match findRun rs i with
    | none => acc
    | some r =>
      (r.pres.zip r.resp).foldl (fun (a : Nat × Nat) (p : Nat × Bool) =>
        if lo ≤ p.1 ∧ p.1 ≤ hi then (a.1 + (if p.2 then 1 else 0), a.2 + 1) else a) acc) (0, 0)

/-- 같은 파일 기준음 표 (a 같은·맞음, b 같은·틀림, c 다른·맞음, d 다른·틀림) — 모르겠음은 js 처럼 같은파일 칸에서 'u' 로 빠짐 -/
def sameRefOf (rs : List RunRes) (ids : String) : Nat × Nat × Nat × Nat :=
  (ids.splitOn ",").foldl (fun (acc : Nat × Nat × Nat × Nat) i =>
    match findRun rs i with
    | none => acc
    | some r =>
      (r.same.toList.zip r.resp).foldl (fun (t : Nat × Nat × Nat × Nat) (p : Char × Bool) =>
        let (a, b, c, d) := t
        if p.1 == '1' then (if p.2 then (a + 1, b, c, d) else (a, b + 1, c, d))
        else if p.1 == '0' then (if p.2 then (a, b, c + 1, d) else (a, b, c, d + 1))
        else t) acc) (0, 0, 0, 0)

/-- 시행 수 (Lean 계단 재생의 시행 수) -/
def ntOf (rs : List RunRes) (ids : String) : Nat :=
  (ids.splitOn ",").foldl (fun n i => match findRun rs i with | some r => n + r.st.nTrials | none => n) 0

/-- ‘모르겠음’ 시행 수 (같은파일 칸의 'u') -/
def nuOf (rs : List RunRes) (ids : String) : Nat :=
  (ids.splitOn ",").foldl (fun n i => match findRun rs i with
    | some r => n + (r.same.toList.filter (· == 'u')).length | none => n) 0

def verdict (rep : String) (comp : String) (tie : Bool) : String :=
  (if rep == comp then "OK" else "DIFF") ++ (if tie then " 갈림" else "")

def claimLine (rs : List RunRes) (parts : List String) : String :=
  match parts with
  | ["CLAIM", key, "MEAN2", ids, rep] =>
    match thrsOf rs ids with
    | some ks => s!"CLAIM {key} MEAN2 {rep} {mean2 ks} {verdict rep (toString (mean2 ks)) (mean2Tie ks)}"
    | none => s!"CLAIM {key} MEAN2 {rep} ? 역치없음"
  | ["CLAIM", key, "SD2", ids, rep] =>
    match thrsOf rs ids with
    | some ks => s!"CLAIM {key} SD2 {rep} {sd2 ks} {verdict rep (toString (sd2 ks)) (sd2Tie ks)}"
    | none => s!"CLAIM {key} SD2 {rep} ? 역치없음"
  | ["CLAIM", key, "DIFF2", idsA, idsB, rep] =>
    match thrsOf rs idsA, thrsOf rs idsB with
    | some a, some b => s!"CLAIM {key} DIFF2 {rep} {intStr (diff2 a b)} {verdict rep (intStr (diff2 a b)) (diff2Tie a b)}"
    | _, _ => s!"CLAIM {key} DIFF2 {rep} ? 역치없음"
  | ["CLAIM", key, "CD2", na, nb, rep] =>
    let c := cd2 na.toNat! nb.toNat!
    s!"CLAIM {key} CD2 {rep} {c} {verdict rep (toString c) (cd2Tie na.toNat! nb.toNat!)}"
  | ["CLAIM", key, "BEYOND", idsA, idsB, rep] =>
    match thrsOf rs idsA, thrsOf rs idsB with
    | some a, some b => s!"CLAIM {key} BEYOND {rep} {b01 (beyondB a b)} {verdict rep (b01 (beyondB a b)) false}"
    | _, _ => s!"CLAIM {key} BEYOND {rep} ? 역치없음"
  | ["CLAIM", key, "THR2", id, rep] =>
    match (findRun rs id).bind (·.thr4v) with
    | some t => s!"CLAIM {key} THR2 {rep} {roundDiv t 100} {verdict rep (toString (roundDiv t 100)) (isTie t 100)}"
    | none => s!"CLAIM {key} THR2 {rep} ? 역치없음"
  | ["CLAIM", key, "THR4", id, rep] =>
    match (findRun rs id).bind (·.thr4v) with
    | some t => s!"CLAIM {key} THR4 {rep} {t} {verdict rep (toString t) false}"
    | none => s!"CLAIM {key} THR4 {rep} ? 역치없음"
  | ["CLAIM", key, "NT", ids, rep] =>
    let n := ntOf rs ids
    s!"CLAIM {key} NT {rep} {n} {verdict rep (toString n) false}"
  | ["CLAIM", key, "NU", ids, rep] =>
    let comp := s!"{nuOf rs ids}/{ntOf rs ids}"
    s!"CLAIM {key} NU {rep} {comp} {verdict rep comp false}"
  | ["CLAIM", key, "ACC", ids, lo, hi, rep] =>
    let (k, n) := accOf rs ids lo.toNat! hi.toNat!
    s!"CLAIM {key} ACC {rep} {k}/{n} {verdict rep s!"{k}/{n}" false}"
  | ["CLAIM", key, "PCT", ids, lo, hi, rep] =>
    let (k, n) := accOf rs ids lo.toNat! hi.toNat!
    let pc := if n = 0 then 0 else roundDiv (100 * k) n
    s!"CLAIM {key} PCT {rep} {pc} {verdict rep (toString pc) (n != 0 && isTie (100 * k) n)}"
  | ["CLAIM", key, "PCTMIN", ids, lo, hi, mn] =>
    let (k, n) := accOf rs ids lo.toNat! hi.toNat!
    let pc := if n = 0 then 0 else roundDiv (100 * k) n
    s!"CLAIM {key} PCTMIN ≥{mn} {pc}({k}/{n}) {if mn.toNat! ≤ pc then "OK" else "DIFF"}"
  | ["CLAIM", key, "VERIFIED", ids, rep] =>
    let all := (ids.splitOn ",").all (fun i => match findRun rs i with
      | some r => !unvFast r.st.nTrials r.st.nCorrect | none => false)
    s!"CLAIM {key} VERIFIED {rep} {b01 all} {verdict rep (b01 all) false}"
  | ["CLAIM", key, "PALL", id, rep] =>
    match findRun rs id with
    | some r =>
      let p := (pStr r.st.nTrials r.st.nCorrect).replace " " "e"
      s!"CLAIM {key} PALL {rep} {p} {verdict rep p false}"
    | none => s!"CLAIM {key} PALL {rep} ? 측정없음"
  | ["CLAIM", key, "SAMEREF", ids, rep] =>
    let (a, b, c, d) := sameRefOf rs ids
    let ps := if a + b = 0 then 0 else roundDiv (100 * a) (a + b)
    let pd := if c + d = 0 then 0 else roundDiv (100 * c) (c + d)
    let comp := s!"{ps}/{pd}"
    s!"CLAIM {key} SAMEREF {rep} {comp} {verdict rep comp false} 표 {a},{b},{c},{d} 피셔유의 {b01 (decide (20 * f2NumWith (rows.getD (a + b) #[]) (rows.getD (c + d) #[]) a c < (rows.getD (a + b + (c + d)) #[]).getD (a + c) 0))}"
  | _ => s!"? {" ".intercalate parts}"

/-! ## 1.2 크기 구별 확인 · 로빙 -/

def gHalf (n k : Nat) : Nat := geHalfNumWith (rows.getD n #[]) n k

def unvHalf (n k : Nat) : Bool := n == 0 || decide (geHalfDen n < 20 * gHalf n k)

def pStrHalf (n k : Nat) : String :=
  if n = 0 then "- -" else
    let (m, e) := sig4 (gHalf n k) (geHalfDen n)
    s!"{m} {e}"

def tieHalf (n k : Nat) : Bool := n != 0 && sig4Tie (gHalf n k) (geHalfDen n)

def loudLine (tag id : String) (bs : List Bool) : String :=
  let (s, pres) := lrun loudCfg (linit loudCfg) bs
  let thr := lthrSum loudCfg s
  let thrS := match thr with | some (S, c) => s!"{S}/{c}" | none => "-"
  let t4 := match thr with | some (S, c) => toString (lthr4 S c) | none => "-"
  let n := s.nTrials
  let k := s.nCorrect
  s!"{tag} {id} {b01 s.done} {b01 (lresIncomplete loudCfg s)} {s.db} {s.cRun} {s.dir} {n} {k} {s.floorHits} {s.ceilHits} {csvN s.revs} {csvN s.revAt} {csvN pres} {thrS} {t4} {b01 (unvHalf n k)} {pStrHalf n k} T:{b01 (tieHalf n k)}"

def csvI (l : List Int) : String := if l.isEmpty then "-" else ",".intercalate (l.map toString)

def lzLine (l : String) : String :=
  let Ss := parseCsv l
  let cnt := 6 * Ss.length
  let sumS := Ss.sum
  let kB := pairCnt (roveH 'B') sumS cnt
  let kC := pairCnt (roveH 'C') sumS cnt
  let one := s!"{lzone sumS cnt} {roundDiv (100 * kB) 81} {roundDiv (100 * kC) 256} {lmean2 sumS cnt}"
  s!"LZ {l} {csvN (Ss.map (fun S => lthr4 S 6))} {one} {one} T:{b01 (isTie (sumS * 100) cnt)},{b01 (isTie (100 * kB) 81)},{b01 (isTie (100 * kC) 256)}"

def setOf (nm : String) : List Int :=
  if nm == "B" then roveH 'B' else if nm == "C" then roveH 'C' else if nm == "W7" then won7H else if nm == "W15" then won15H else []

/-- 소수 문자열(부호 · 정수부 · 소수부) → 정확한 유리수 -/
def parseDec (s : String) : Rat :=
  let neg := s.startsWith "-"
  let body := if neg then s.drop 1 else s
  let v : Rat := match body.splitOn "." with
    | [i] => (i.toNat! : Rat)
    | [i, f] => (i.toNat! : Rat) + (f.toNat! : Rat) / ((10 ^ f.length : Nat) : Rat)
    | _ => 0
  if neg then -v else v

def main (args : List String) : IO Unit := do
  let inPath := args.getD 0 "cross_in.txt"
  let outPath := args.getD 1 "cross_lean.txt"
  let lines ← IO.FS.lines inPath
  let mut runs : List RunRes := []
  let h ← IO.FS.Handle.mk outPath .write
  for ln in lines do
    let parts := (ln.trimRight.splitOn " ").filter (· ≠ "")
    match parts with
    | ["TRACK", id, seq] => h.putStrLn (trackLine "TRACK" (runRes id seq "-"))
    | ["RUN", id, seq, same] =>
      let r := runRes id seq same
      runs := runs ++ [r]
      h.putStrLn (trackLine "RUN" r)
    | ["BTAB", nn] =>
      for n in [1:nn.toNat! + 1] do
        for k in [0:n + 1] do
          h.putStrLn s!"B {n} {k} {b01 (unvFast n k)} {pStr n k}"
    | ["F2TAB", nn] =>
      let N := nn.toNat!
      for n in [0:N + 1] do
        for a in [0:n + 1] do
          for b in [0:n + 1 - a] do
            for c in [0:n + 1 - a - b] do
              h.putStrLn (f2Line a b c (n - a - b - c))
    | ["F2ONE", a, b, c, d] => h.putStrLn (f2Line a.toNat! b.toNat! c.toNat! d.toNat!)
    | ["R4", S] => h.putStrLn s!"R4 {S} {thr4 S.toNat! 6}"
    | ["SDR", l] =>
      let rv := parseCsv l
      h.putStrLn s!"SDR {l} {thr4 rv.sum rv.length} {sd4 rv}"
    | ["DIN", k1, k2] =>
      let d := b01 (dininoB k1.toNat! k2.toNat!)
      h.putStrLn s!"DIN {k1} {k2} {d} {d}"
    | ["CD", l1, l2] =>
      let a := parseCsv l1
      let b := parseCsv l2
      h.putStrLn s!"CD {l1} {l2} {b01 (beyondB a b)} {cd2 a.length b.length} {intStr (diff2 a b)} T:{b01 (cd2Tie a.length b.length)},{b01 (diff2Tie a b)}"
    | ["ZONE", l] =>
      let ks := parseCsv l
      let s2 := if ks.length < 2 then "-" else toString (sd2 ks)
      let s2t := if ks.length < 2 then "0" else b01 (sd2Tie ks)
      h.putStrLn s!"ZONE {l} {b01 (amZoneB ks)} {b01 (limitZoneB ks 20000)} {b01 (limitZoneB ks 11000)} {b01 (floorZoneB ks)} {mean2 ks} {s2} T:{b01 (mean2Tie ks)},{s2t}"
    | "CLAIM" :: _ => h.putStrLn (claimLine runs parts)
    | ["LT", id, seq] => h.putStrLn (loudLine "LT" id (boolsOf seq))
    | ["LRUN", id, seq] => h.putStrLn (loudLine "LRUN" id (boolsOf seq))
    | ["LBTAB", nn] =>
      for n in [1:nn.toNat! + 1] do
        for k in [0:n + 1] do
          h.putStrLn s!"LB {n} {k} {b01 (unvHalf n k)} {pStrHalf n k} T:{b01 (tieHalf n k)}"
    | ["LZ", l] => h.putStrLn (lzLine l)
    | ["RV", c] => h.putStrLn s!"RV {c} {csvI (roveH (c.toList.headD ' '))}"
    | ["RS"] => h.putStrLn s!"RS {String.mk roveSeq} {rovePlan.1} {rovePlan.2}"
    | ["RU", n, xs] =>
      match ruDraw n.toNat! (parseCsv xs) with
      | some (r, k) => h.putStrLn s!"RU {n} {xs} {r} {k}"
      | none => h.putStrLn s!"RU {n} {xs} - -"
    | ["PR", nm, rule, dh] =>
      let V := setOf nm
      let sc := if rule == "L" then protL V dh.toInt! else protD V dh.toInt!
      h.putStrLn s!"PR {nm} {rule} {dh} {sc} {6 * V.length ^ 3}"
    | ["RULE", e, se, a, b] =>
      h.putStrLn s!"RULE {e} {se} {a} {b} {ruleV (parseDec e) (parseDec se) (parseDec a) (parseDec b)}"
    | [] => pure ()
    | _ => h.putStrLn s!"? {ln}"
  h.flush

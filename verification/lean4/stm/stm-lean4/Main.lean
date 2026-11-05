import Lean
import Stm

/- JSON adapter for executable differential tests. Not part of the theorem TCB. -/
open Lean
namespace Stm.Check

def field (j : Json) (k : String) : Except String Json := j.getObjVal? k
def bool (j : Json) (k : String) : Except String Bool := do (← field j k).getBool?
def nat (j : Json) (k : String) : Except String Nat := do (← field j k).getNat?
def intAt (j : Json) (k : Nat) : Except String Int := do (← j.getArrVal? k).getInt?
def natAt (j : Json) (k : Nat) : Except String Nat := do (← j.getArrVal? k).getNat?

def dirOf (v : Int) : Except String (Option Staircase.Dir) :=
  if v = -1 then .ok (some .harder)
  else if v = 1 then .ok (some .easier)
  else if v = 0 then .ok none else .error "direction must be -1, 0 or 1"

def dirCode : Option Staircase.Dir → Int
  | none => 0 | some d => d.sign

def statusCode : Staircase.Status → Nat
  | .running => 0 | .technicalFailure => 1
  | .reversalTargetReached => 2 | .trialCapBeforeReversalTarget => 3

def revJson (r : Staircase.Reversal) : Json :=
  toJson ([toJson r.db, toJson r.validNo, toJson r.attemptNo, toJson r.dirAfter.sign] : List Json)

def stateJson (s : Staircase.State) : Json :=
  toJson ([toJson s.levelDb, toJson s.correctStreak, toJson (dirCode s.lastDir),
    toJson s.reversals.length, toJson s.validCount, toJson s.technicalCount,
    toJson (statusCode s.status), toJson s.attemptCount, toJson s.moves,
    toJson (s.reversals.map revJson)] : List Json)

def projected (j : Json) : Except String Json := do
  let b ← field j "before"
  let db ← intAt b 0
  let streak ← natAt b 1
  let dir ← dirOf (← intAt b 2)
  let revs ← natAt b 3
  let v ← natAt b 4
  let tech ← natAt b 5
  let valid ← bool j "valid"
  let correct ← bool j "correct"
  let dummy : Staircase.Reversal := ⟨0, 0, 0, "", .harder, none⟩
  let s : Staircase.State := {
    levelDb := db
    correctStreak := streak
    lastDir := dir
    reversals := List.replicate revs dummy
    validCount := v
    technicalCount := tech
    attemptCount := v + tech }
  match Staircase.step s ⟨"fresh", db, valid, correct⟩ with
  | .advanced n t =>
      return toJson ([toJson n.levelDb, toJson n.correctStreak,
        toJson (dirCode n.lastDir), toJson n.reversals.length,
        toJson n.validCount, toJson n.technicalCount,
        toJson (statusCode n.status), toJson t.requestedDir,
        toJson t.reversal, toJson t.requestedStepDb] : List Json)
  | _ => throw "projected step rejected"

def trace (responses : String) (allSteps : Bool) : Except String Json := do
  let mut s := Staircase.init
  let mut states : Array Json := #[]
  for c in responses.toList do
    unless c = 'C' || c = 'E' || c = 'I' do throw "invalid response character"
    let id := s!"t{s.attemptCount + 1}"
    match Staircase.step s ⟨id, s.levelDb, c != 'I', c == 'C'⟩ with
    | .advanced n _ =>
        s := n
        if allSteps then states := states.push (stateJson s)
    | _ => throw "trace contains input after termination"
  return if allSteps then toJson states else stateJson s

def run (j : Json) : Except String Json := do
  let op ← (← field j "op").getStr?
  match op with
  | "classify" =>
      return toJson (Analysis.classifyCode
        (← bool j "aborted") (← bool j "hasState") (← nat j "stateCode")
        (← bool j "hasThreshold") (← bool j "winFloor")
        (← nat j "blocked") (← nat j "ceilingAllowance") (← nat j "zeroN")
        (← bool j "zeroWorse") (← bool j "belowTarget"))
  | "summary" =>
      let six ← bool j "sixRule"
      let tracks ← (← field j "tracks").getArr?
      let ts ← tracks.toList.mapM fun t => do
        return (← natAt t 0, ← intAt t 1)
      let r := Analysis.summaryCode six ts
      return toJson ([toJson r.1, toJson r.2.1, toJson r.2.2.1, toJson r.2.2.2] : List Json)
  | "stair" => projected j
  | "trace" => trace (← (← field j "responses").getStr?) false
  | "traceAll" => trace (← (← field j "responses").getStr?) true
  | _ => throw s!"unknown operation: {op}"

end Stm.Check

def main : IO UInt32 := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  let err ← IO.getStderr
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    match Json.parse line >>= Stm.Check.run with
    | .ok result =>
        output.putStrLn result.compress
        output.flush
    | .error message =>
        err.putStrLn s!"stmCheck: {message}"
        return 1
  return 0

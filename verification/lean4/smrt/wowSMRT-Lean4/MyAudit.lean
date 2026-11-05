import SMRT
import Lean
open Lean

/-!
환경 전체 감사 (Claude, 2026-10-22 — 와우SRD tools/lean/MyAudit.lean 과 같은 방식)
빌드된 환경에서 `SMRT.*` 의 모든 상수를 직접 훑어
  · 정리(theorem) · axiom 선언 · 그 밖의 상수 수
  · 정리마다 `collectAxioms` (= #print axioms 와 같은 함수) — sorryAx · 표준 밖 공리가 있는지
  · 정의(def 등)까지 포함한 모든 SMRT 상수의 공리 합집합
을 출력함. `lake build` · `lake env lean` 은 sorry · axiom 이 있어도 종료 코드 0 이라, 판정은 이 출력으로 함:
  SUMMARY axiomDecls=0 · UNION ⊆ {propext, Classical.choice, Quot.sound} · NONSTANDARD 0
-/

def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def audit : CoreM Unit := do
  let env ← getEnv
  let consts : Array (Name × ConstantInfo) :=
    env.constants.fold (fun acc n ci => if n.getRoot == `SMRT then acc.push (n, ci) else acc) #[]
  let mut thms : Array Name := #[]
  let mut axDecls : Array Name := #[]
  let mut nOther := 0
  for (n, ci) in consts do
    match ci with
    | .thmInfo _ => thms := thms.push n
    | .axiomInfo _ => axDecls := axDecls.push n
    | _ => nOther := nOther + 1
  IO.println s!"SUMMARY consts={consts.size} theorems={thms.size} axiomDecls={axDecls.size} others={nOther}"
  for a in axDecls do IO.println s!"AXIOMDECL {a}"
  let mut bad : Array Name := #[]
  let mut union : Array Name := #[]
  for n in thms.qsort (fun a b => a.toString < b.toString) do
    let axs ← collectAxioms n
    let sorted := axs.qsort (fun a b => a.toString < b.toString)
    IO.println s!"THM {n} {",".intercalate (sorted.toList.map toString)} internal={n.isInternal}"
    for a in axs do
      unless union.contains a do union := union.push a
      unless stdAxioms.contains a do
        unless bad.contains n do bad := bad.push n
  -- 정의 등 나머지 상수도 공리 합집합에 넣음 (정리가 쓰는 정의에 sorry 가 숨어 있지 않은지)
  for (n, ci) in consts do
    match ci with
    | .thmInfo _ => pure ()
    | _ =>
      let axs ← collectAxioms n
      for a in axs do
        unless union.contains a do union := union.push a
        unless stdAxioms.contains a do
          unless bad.contains n do bad := bad.push n
  IO.println s!"UNION {",".intercalate ((union.qsort (fun a b => a.toString < b.toString)).toList.map toString)}"
  IO.println s!"NONSTANDARD {bad.size}"
  for b in bad do IO.println s!"BAD {b}"

#eval audit

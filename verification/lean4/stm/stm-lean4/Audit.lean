import Lean
import Stm

open Lean

/- Fail-closed transitive axiom audit of every Stm theorem.
   The only admitted logical foundations are Lean's standard three axioms.
   Compiler-generated executable auxiliaries are not proof declarations;
   every axiom transitively reachable FROM a theorem is nevertheless checked. -/
#eval show CoreM Unit from do
  let env ← getEnv
  let mut declarations := 0
  let mut theorems := 0
  for (name, info) in env.constants.toList do
    if "Stm.".isPrefixOf name.toString then
      declarations := declarations + 1
      match info with
      | .axiomInfo _ => throwError "Custom axiom declaration: {name}"
      | _ => pure ()
      match info with
      | .thmInfo _ =>
          theorems := theorems + 1
          let axioms ← collectAxioms name
          for ax in axioms do
            unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
              throwError "Forbidden axiom {ax} used by theorem {name}"
          IO.println s!"{name}: {axioms}"
      | _ => pure ()
  if theorems = 0 then throwError "No theorems audited"
  IO.println s!"PASS: {theorems} theorem declarations audited; {declarations} total Stm declarations scanned; no nonstandard theorem axioms."

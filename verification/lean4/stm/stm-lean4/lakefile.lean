import Lake
open Lake DSL

package stmVerified where
  version := v!"0.1.0"

@[default_target]
lean_lib Stm where
  roots := #[`Stm]

lean_exe stmCheck where
  root := `Main

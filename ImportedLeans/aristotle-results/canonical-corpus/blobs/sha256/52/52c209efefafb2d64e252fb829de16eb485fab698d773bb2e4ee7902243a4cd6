import Lake
open Lake DSL

package «RequestProject» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

@[default_target]
lean_lib «Wave1Foundations» where
  srcDir := "lean-baseline"
  roots := #[`AgdaMirror, `DashiPerf, `Main, `Main11, `Q]

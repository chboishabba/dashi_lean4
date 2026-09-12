import Lake
open Lake DSL

package «RequestProject» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

@[default_target]
lean_lib «Wave1Mirror» where
  srcDir := "lean-baseline"
  roots := #[`AgdaMirror, `AgdaMirror1, `ClosureEndToEnd, `DASHI, `DashiPerf, `Main, `Main11, `MoonshineFractran, `NavierStokesClosure, `SpectralClosure, `YangMillsClosure, `YangMillsContinuumGap]

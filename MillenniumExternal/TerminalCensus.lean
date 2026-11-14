import Synthesis.RiemannSelectedRHMaxCutFrontier
import Synthesis.MillenniumBSDUniversalRankWeld
import NSBControl.CombinedCurrentEndgame
import Synthesis.MillenniumHodgeRealAlgebraicCycleMultiplicityExact
import YangMills.ContinuumWilsonCovariance

/-!
# DASHI Millennium terminal-constructor census

This module deliberately does not restate any Clay problem. It imports stable
theorem-bearing surfaces already present in the root DASHI Lean package and
records the strongest external-facing producer found across the Lean/Agda
repositories.

The census is same-object first. A lane may therefore name a stronger producer
that lives in a separate Lean/Agda kernel even when the root package can only
`#check` an earlier theorem-bearing donor. Kernel separation is not mathematical
closure and is not promoted to a GREEN external receipt.
-/

namespace MillenniumExternal

inductive Problem where
  | pVersusNP
  | riemann
  | navierStokes
  | hodge
  | birchSwinnertonDyer
  | yangMills
  | poincare
  deriving DecidableEq, BEq, Repr

inductive UpstreamStatus where
  | openProblem
  | solvedProblem
  | statementIncomplete
  deriving DecidableEq, BEq, Repr

inductive DashiOwner where
  | leanKernel
  | agdaSource
  | leanAndAgda
  | upstreamOnly
  deriving DecidableEq, BEq, Repr

structure TerminalLane where
  problem : Problem
  upstreamDeclaration : String
  upstreamStatus : UpstreamStatus
  dashiOwner : DashiOwner
  dashiTerminalModule : String
  directCrossVersionAdapterKernelChecked : Bool
  deriving DecidableEq, Repr

/-- Exact declaration names from LeanDojo commit
`603053dc267cf3efe422f438eb78098c0ececd6f`. -/
def pVersusNPLane : TerminalLane :=
  { problem := .pVersusNP
    upstreamDeclaration := "Millennium.ClayPVersusNP.Formulations.NegativeBranch"
    upstreamStatus := .openProblem
    dashiOwner := .agdaSource
    dashiTerminalModule :=
      "DASHI/Mathematics/Complexity/PNotEqualsNPClayCoreExact.agda + PNotEqualsNPDirectSATLowerBoundExact.agda"
    directCrossVersionAdapterKernelChecked := false }

def riemannLane : TerminalLane :=
  { problem := .riemann
    upstreamDeclaration := "Millennium.ClayRiemannHypothesis"
    upstreamStatus := .openProblem
    dashiOwner := .leanAndAgda
    dashiTerminalModule :=
      "Synthesis.RiemannSelectedRHMaxCutFrontier + Agda RH status/provenance mirror"
    directCrossVersionAdapterKernelChecked := false }

def navierStokesLane : TerminalLane :=
  { problem := .navierStokes
    upstreamDeclaration := "MillenniumNavierStokes.FeffermanA|B|C|D"
    upstreamStatus := .openProblem
    dashiOwner := .leanAndAgda
    dashiTerminalModule :=
      "ExternalClayNS/LiteralABCD.lean (literal independent C/D terminal, separate Lean kernel) + NSBControl.CombinedCurrentEndgame"
    directCrossVersionAdapterKernelChecked := false }

def hodgeLane : TerminalLane :=
  { problem := .hodge
    upstreamDeclaration := "MillenniumHodge.ClayHodge"
    upstreamStatus := .statementIncomplete
    dashiOwner := .leanAndAgda
    dashiTerminalModule :=
      "Synthesis.MillenniumHodgeRealAlgebraicCycleMultiplicityExact + Agda HodgeAlgebraicCycleClayCoreExact"
    directCrossVersionAdapterKernelChecked := false }

def bsdLane : TerminalLane :=
  { problem := .birchSwinnertonDyer
    upstreamDeclaration := "MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer"
    upstreamStatus := .openProblem
    dashiOwner := .leanAndAgda
    dashiTerminalModule :=
      "Synthesis.MillenniumBSDUniversalRankWeld (literal L-series / Mordell-Weil same-curve rank weld; upstream Taylor-data packaging still separate)"
    directCrossVersionAdapterKernelChecked := false }

def yangMillsLane : TerminalLane :=
  { problem := .yangMills
    upstreamDeclaration := "MillenniumYangMills.ClayYangMills"
    upstreamStatus := .statementIncomplete
    dashiOwner := .leanAndAgda
    dashiTerminalModule :=
      "YangMills.ContinuumWilsonCovariance + Agda OS/QFT/mass-gap physical same-object stack"
    directCrossVersionAdapterKernelChecked := false }

def poincareLane : TerminalLane :=
  { problem := .poincare
    upstreamDeclaration := "MillenniumPoincare.ClayPoincareConjecture"
    upstreamStatus := .solvedProblem
    dashiOwner := .upstreamOnly
    dashiTerminalModule := "Perelman / upstream solved target (regression only)"
    directCrossVersionAdapterKernelChecked := false }

def terminalLanes : List TerminalLane :=
  [pVersusNPLane, riemannLane, navierStokesLane, hodgeLane,
    bsdLane, yangMillsLane, poincareLane]

theorem terminalLanes_length : terminalLanes.length = 7 := by decide

/-- Known-incomplete upstream targets can never count as a GREEN prize target
in this integration layer. -/
def isValidPrizeAcceptanceTarget (lane : TerminalLane) : Bool :=
  match lane.upstreamStatus with
  | .statementIncomplete => false
  | .openProblem | .solvedProblem => true

theorem hodge_upstream_not_prize_target :
    isValidPrizeAcceptanceTarget hodgeLane = false := by decide

theorem yangMills_upstream_not_prize_target :
    isValidPrizeAcceptanceTarget yangMillsLane = false := by decide

/-! ## Existing root-package theorem-bearing surfaces

These checks intentionally name declarations available to the root DASHI Lean
package. Stronger terminals in nested projects are named above but are not
silently imported across their independent package graphs.
-/

#check Synthesis.QuarticFourSignedPolePair.RHMaxCutRoute.signedFifth_terminalPositive
#check Synthesis.Millennium.BSD.universalBSDRankTheorem_of_background
#check Synthesis.Millennium.BSD.universalBSDRankTheorem_of_producers
#check NSBControl.CombinedCurrentEndgame.current_three_coordinate_endgame
#check Synthesis.Millennium.Hodge.doublePointCycle_isWeilDivisor
#check RequestProject.YangMills.probabilityCovariance_exponential_bound_of_weak_limit

end MillenniumExternal

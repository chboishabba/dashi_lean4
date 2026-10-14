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
that lives in a separate Lean/Agda kernel or an open producer branch even when
the root package can only `#check` an earlier theorem-bearing donor. Such names
are routing/provenance metadata only: kernel separation and open-branch status
are not mathematical closure and are never promoted to a GREEN external receipt.
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
      "Agda PR #1129: PNotEqualsNPCodedLiteralSelfQuotationPositiveBudgetNoGoExact retires positive-budget literal own-Cook materialisation; PNotEqualsNPFixedDescriptionVirtualGeneratorExact + PNotEqualsNPFaithfulVirtualSimulationExact define the active fixed-description virtual/streaming route. Exact streamed semantics and linear fixed-description work are paid; finite coded machine execution, faithful same-target simulation and same-Cook-budget closure remain the live producer before the existing SATNotInP -> PNotEqualsNP terminal compiler."
    directCrossVersionAdapterKernelChecked := false }

def riemannLane : TerminalLane :=
  { problem := .riemann
    upstreamDeclaration := "Millennium.ClayRiemannHypothesis"
    upstreamStatus := .openProblem
    dashiOwner := .leanAndAgda
    dashiTerminalModule :=
      "Lean PR #50 Synthesis.RiemannSelectedRHMaxCutFrontier + Agda RH mirror; exact LeanDojo/Mathlib statement weld lives in MillenniumExternal, while A1 shell partition, A2 selected allowance/curvature/compensation and Route-B boundary-gap-limit analytic producers remain explicit"
    directCrossVersionAdapterKernelChecked := false }

def navierStokesLane : TerminalLane :=
  { problem := .navierStokes
    upstreamDeclaration := "MillenniumNavierStokes.FeffermanA|B|C|D"
    upstreamStatus := .openProblem
    dashiOwner := .leanAndAgda
    dashiTerminalModule :=
      "PR #53 DASHILiteralClayNS.dashiExactFeffermanC/D in ExternalClayNS/LeanDojoExactTerminal.lean + NSBControl.CombinedCurrentEndgame; exact pinned external C/D terms source-written, kernel receipt pending"
    directCrossVersionAdapterKernelChecked := false }

def hodgeLane : TerminalLane :=
  { problem := .hodge
    upstreamDeclaration := "MillenniumHodge.ClayHodge"
    upstreamStatus := .statementIncomplete
    dashiOwner := .leanAndAgda
    dashiTerminalModule :=
      "Merged Lean #40 Synthesis.MillenniumHodgeRulingCycleSwapMaxCutExact over genuine Mathlib AlgebraicCycle / actual P1_Q x P1_Q factor swap, plus Agda HodgeAlgebraicCycleClayCoreExact; cycle-class/naturality and universal primitive algebraic lift remain beyond the regression geometry"
    directCrossVersionAdapterKernelChecked := false }

def bsdLane : TerminalLane :=
  { problem := .birchSwinnertonDyer
    upstreamDeclaration := "MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer"
    upstreamStatus := .openProblem
    dashiOwner := .leanAndAgda
    dashiTerminalModule :=
      "Synthesis.MillenniumBSDUniversalRankWeld + MillenniumBSDSelmerDefectClayEquivalence (under same-curve analytic bridge, Clay core iff universal zero Selmer defect); merged MillenniumBSDActualE2ShaSameObjectMaxCut fixes the genuine E[2]/Sha[2] comparison boundary for the selected CM curve only. Agda #1145 j=0/Eisenstein C3 symmetry is a local selected-curve algebra donor and is not a universal analytic-rank/zero-defect inhabitant."
    directCrossVersionAdapterKernelChecked := false }

def yangMillsLane : TerminalLane :=
  { problem := .yangMills
    upstreamDeclaration := "MillenniumYangMills.ClayYangMills"
    upstreamStatus := .statementIncomplete
    dashiOwner := .leanAndAgda
    dashiTerminalModule :=
      "Open Lean #7 conditional Welds.YMClayAssembly.massGapOfSourceCovariance / Welds.YMClayAssembly.massGapOfEnergyForms over retained bounded-form/BIDI assembly, plus YangMills.ContinuumWilsonCovariance and Agda OS/RP/QFT physical stack; actual physical cutoff/OS same-object inhabitants remain explicit"
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
package. Stronger terminals in separate/open producer branches are named above
but are not silently imported across their independent package graphs.
-/

#check Synthesis.QuarticFourSignedPolePair.RHMaxCutRoute.signedFifth_terminalPositive
#check Synthesis.Millennium.BSD.universalBSDRankTheorem_of_background
#check Synthesis.Millennium.BSD.universalBSDRankTheorem_of_producers
#check NSBControl.CombinedCurrentEndgame.current_three_coordinate_endgame
#check Synthesis.Millennium.Hodge.doublePointCycle_isWeilDivisor
#check RequestProject.YangMills.probabilityCovariance_exponential_bound_of_weak_limit

end MillenniumExternal

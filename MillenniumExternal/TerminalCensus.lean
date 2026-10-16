import Synthesis.RiemannSelectedRHMaxCutFrontier
import Synthesis.MillenniumBSDUniversalRankWeld
import NSBControl.CombinedCurrentEndgame
import Synthesis.MillenniumHodgeRealAlgebraicCycleMultiplicityExact
import YangMills.ContinuumWilsonCovariance

/-!
# DASHI Millennium terminal-constructor census
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
      "Live Agda PR #1129 has normalized semantic execution away from Cook padding: CodedStandardCanonicalInputExact / CodedStandardHaltingPolynomialDeciderExact give one canonical input, actual quiescent runtime and only a polynomial upper bound, while GuardedExecutionReceipt is downstream representation transport. Literal table-baked/raw syntactic self-fix routes are theorem-level no-go results, so PNotEqualsNPKleeneSpecializationFixedPointExact is the surviving behavioural route. CodedFiniteStandardSelfDelimitingCodeExact now gives the actual CodedFiniteStandardTM a self-framing quote with parser round-trip, and CodedFiniteStandardRawInterpreterExact supplies first-order parse/dispatch/tape-update/bounded-iteration semantics with runActualCodeReducesToRawView on actual quotes. Recent XOR-grid work is consumed only through locally reproved complexity facts: PNotEqualsNPXORCountdownMicrocodeExact separates recoverable XOR data update from borrow; PNotEqualsNPBinaryCountdownExactRunExact gives a literal three-rule compact timer with arbitrary-word exact runs and quiescent endpoints; PNotEqualsNPBinaryCountdownCostExact pays decrement work <= bit-width+1 (tight on all-zero words); PNotEqualsNPPhaseCounterParetoExact compares that compact runtime timer against the exact phase lift whose states=|Q|*(T+1), rules=T*|R|. IIT phi remains explicitly non-authoritative for complexity hardness. The live residual is therefore a quoted-code-consuming coded behavioural specializer/diagonal compiler, typed fidelity/resource accounting for that specialization, and one final same-object program-size/runtime/Cook resource fixed point before the existing SATDecisionFailure -> SATNotInP -> PNotEqualsNP terminal chain."
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
      "PR #53 DASHILiteralClayNS.dashiExactFeffermanC/D in ExternalClayNS/LeanDojoExactTerminal.lean + NSBControl.CombinedCurrentEndgame; exact pinned external C/D terms source-written. External scientific/credit status is kept separate from DASHI reconstruction/provenance."
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

def isValidPrizeAcceptanceTarget (lane : TerminalLane) : Bool :=
  match lane.upstreamStatus with
  | .statementIncomplete => false
  | .openProblem | .solvedProblem => true

theorem hodge_upstream_not_prize_target :
    isValidPrizeAcceptanceTarget hodgeLane = false := by decide

theorem yangMills_upstream_not_prize_target :
    isValidPrizeAcceptanceTarget yangMillsLane = false := by decide

#check Synthesis.QuarticFourSignedPolePair.RHMaxCutRoute.signedFifth_terminalPositive
#check Synthesis.Millennium.BSD.universalBSDRankTheorem_of_background
#check Synthesis.Millennium.BSD.universalBSDRankTheorem_of_producers
#check NSBControl.CombinedCurrentEndgame.current_three_coordinate_endgame
#check Synthesis.Millennium.Hodge.doublePointCycle_isWeilDivisor
#check RequestProject.YangMills.probabilityCovariance_exponential_bound_of_weak_limit

end MillenniumExternal

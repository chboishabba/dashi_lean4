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
      "Live Agda PR #1129: costed streamed Cook access + finite local tables + linked candidate execution are paid. Runtime is now normalized by CodedStandardCanonicalInputExact / CodedStandardHaltingPolynomialDeciderExact: one canonical semantic input independent of T, actual quiescent halting runtime, polynomial upper bound only, and Cook padding downstream via GuardedExecutionReceipt; PNotEqualsNPHaltingCodedCandidateBridgeExact reuses the existing candidate/clock stack without identifying runtime with its upper bound. CodedFiniteUnaryCursorExact + CodedFiniteBitStreamLookupExact + GuardedCookFiniteBitTableGeneratorExact make fixed-description Cook-bit lookup literal machine syntax, while ConcreteTapeCookLevinStateWidthLowerExact + GuardedCookFiniteBitTableSelfCodeNoGoExact prove that full-table-baked own-Cook lookup code cannot be the same machine it describes. Thus raw/materialized self-fixity is formally closed. Existing PNotEqualsNPKleeneSpecializationFixedPointExact gives the surviving behavioural fixed-point shape, but CandidateActualSelfInstantiationBoundaryExact shows the old Q2 primitive erases quoted code. The first live residual is candidate-aware behavioural specialization/diagonalization on the actual CodedFiniteStandardTM program-code carrier plus GuardedExecutionReceipt transport and final same-object resource closure. XOR-grid work remains an attribution-safe compact-control donor only: XOR gives recoverable local data update, borrow is separate, and IIT phi is not hardness evidence."
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

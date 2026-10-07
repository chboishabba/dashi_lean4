import MillenniumExternal.TerminalCensus

namespace MillenniumExternal

inductive AdapterState where
  | greenExact
  | redType
  | redMath
  | upstreamIncomplete
  | upstreamSolvedUnformalized
  deriving DecidableEq, BEq, Repr

inductive FrontierClass where
  | proved
  | typeWeld
  | analytic
  | upstreamDefect
  | solvedUnformalized
  deriving DecidableEq, BEq, Repr

structure ExternalTargetReceipt where
  problem : Problem
  upstreamDeclaration : String
  state : AdapterState
  frontier : FrontierClass
  firstUnpaid : String
  note : String
  deriving DecidableEq, Repr

/-- Fail-closed current receipts.  `frontier = proved` means the mathematical
and same-object dependency cone is source-written down to the literal external
proposition; `state = greenExact` is deliberately stronger and is reserved for
a recorded exact-kernel acceptance receipt. -/
def externalTargetReceipts : List ExternalTargetReceipt :=
  [ { problem := .pVersusNP
      upstreamDeclaration := "Millennium.ClayPVersusNP.Formulations.NegativeBranch"
      state := .redMath
      frontier := .analytic
      firstUnpaid := "Agda UniversalAnchoredPolynomialSATDecisionCollision on the literal PolynomialCostModel/SAT carrier"
      note := "Agda already proves UniversalAnchoredPolynomialSATDecisionCollision -> SATNotInP -> SATLowerBoundProducer -> PNotEqualsNP, including the anchor-or-already-fails reduction. The universal anchored collision theorem is the first unpaid mathematical edge." }
  , { problem := .riemann
      upstreamDeclaration := "Millennium.ClayRiemannHypothesis"
      state := .redMath
      frontier := .analytic
      firstUnpaid := "selected-witness A2 leading comparison postSixthTerminalEighthLeadingAllowance < postSixthTerminalDominantHeadroom"
      note := "Exact LeanDojo <-> Mathlib RiemannHypothesis statement weld is source-written. A2 is compressed to the selected eighth-leading allowance versus sixth headroom; failure should retire this A2 branch rather than create another terminal certificate. A1 and Route B remain independent fallbacks." }
  , { problem := .navierStokes
      upstreamDeclaration := "MillenniumNavierStokes.FeffermanC|D"
      state := .redType
      frontier := .proved
      firstUnpaid := "exact-kernel acceptance of DASHILiteralClayNS.dashiExactFeffermanC and DASHILiteralClayNS.dashiExactFeffermanD against the pinned LeanDojo targets"
      note := "LeanDojoForceDecayQuantitative pays both previously isolated force-decay transports; momentum, divergence, energy, boundary and carrier transports are already paid; LeanDojoExactTerminal constructs literal theorem terms dashiExactFeffermanC : MillenniumNavierStokes.FeffermanC and dashiExactFeffermanD : MillenniumNavierStokes.FeffermanD. No mathematical or same-object theorem remains on this branch. The receipt stays redType only because GREEN is reserved for a recorded exact-kernel run/axiom audit." }
  , { problem := .hodge
      upstreamDeclaration := "MillenniumHodge.ClayHodge"
      state := .upstreamIncomplete
      frontier := .upstreamDefect
      firstUnpaid := "faithful official Clay Hodge statement; internal general algebraic-cycle theorem remains separate"
      note := "LeanDojo marks this statement incomplete and not a valid prize target. DASHI retains the stronger rational-Hodge/algebraic-cycle programme; the general algebraic reopening remains the research wall." }
  , { problem := .birchSwinnertonDyer
      upstreamDeclaration := "MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer"
      state := .redMath
      frontier := .analytic
      firstUnpaid := "Synthesis.Millennium.BSD.BSDClayCoreObligation bg"
      note := "The Clay-facing source isolates the novel theorem exactly: equality of canonical analytic rank and Mordell-Weil free rank on the same rational elliptic curve after established background. LeanDojo carrier transport is downstream certification, not the first mathematical debt." }
  , { problem := .yangMills
      upstreamDeclaration := "MillenniumYangMills.ClayYangMills"
      state := .upstreamIncomplete
      frontier := .upstreamDefect
      firstUnpaid := "faithful official Jaffe-Witten target; internal continuum construction and positive mass gap remain separate"
      note := "LeanDojo marks this interface incomplete. DASHI's OS/reflection-positivity, continuum-QFT, Hamiltonian and mass-gap physical-object programme remains authoritative until a faithful external statement exists." }
  , { problem := .poincare
      upstreamDeclaration := "MillenniumPoincare.ClayPoincareConjecture"
      state := .upstreamSolvedUnformalized
      frontier := .solvedUnformalized
      firstUnpaid := "upstream does not include Perelman's proof term"
      note := "Historically solved, but the pinned upstream repository does not contain Perelman's Lean proof. This is not a DASHI research lane or a type-adapter failure." }
  ]

theorem externalTargetReceipts_length : externalTargetReceipts.length = 7 := by decide

def hasGreenExact (p : Problem) : Bool :=
  externalTargetReceipts.any fun r => r.problem == p && r.state == .greenExact

theorem riemann_frontier_is_analytic :
    (externalTargetReceipts.find? (fun r => r.problem == .riemann)).map
        (fun r => r.frontier) = some .analytic := by
  decide

/-- NS has no unpaid proof edge after the literal C/D theorem terms are
constructed; only the fail-closed kernel acceptance gate remains. -/
theorem navierStokes_frontier_is_proved :
    (externalTargetReceipts.find? (fun r => r.problem == .navierStokes)).map
        (fun r => r.frontier) = some .proved := by
  decide

theorem navierStokes_not_green_before_kernel_receipt :
    hasGreenExact .navierStokes = false := by decide

theorem birchSwinnertonDyer_frontier_is_analytic :
    (externalTargetReceipts.find? (fun r => r.problem == .birchSwinnertonDyer)).map
        (fun r => r.frontier) = some .analytic := by
  decide

theorem hodge_not_green_exact : hasGreenExact .hodge = false := by decide

theorem yangMills_not_green_exact : hasGreenExact .yangMills = false := by decide

theorem poincare_not_green_exact : hasGreenExact .poincare = false := by decide

end MillenniumExternal

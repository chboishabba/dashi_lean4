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

/-- Fail-closed current receipts. `frontier = proved` means the mathematical
and same-object dependency cone is source-written down to the literal external
proposition; `state = greenExact` is deliberately stronger and is reserved for
a recorded exact-kernel acceptance receipt.

The proof-resolution-only policy used by the stacked submission pass lives in
`ProofResolutionMaxCut`: it forbids inventing new mathematics while searching
for already-proved donors, but it does not falsify these acceptance receipts. -/
def externalTargetReceipts : List ExternalTargetReceipt :=
  [ { problem := .pVersusNP
      upstreamDeclaration := "Millennium.ClayPVersusNP.Formulations.NegativeBranch"
      state := .redMath
      frontier := .analytic
      firstUnpaid := "Agda UniversalPolynomialSATDecisionFailure on the literal PolynomialCostModel/SAT candidate carrier"
      note := "PNotEqualsNPAnchoredCollisionEquivalenceExact proves constructively that UniversalPolynomialSATDecisionFailure and UniversalAnchoredPolynomialSATDecisionCollision are interderivable. ExactTargetSurface additionally reduces LeanDojo's negative branch to one finite-alphabet language in NP but not P. The submission pass must resolve an existing concrete SAT-failure donor and transport it; it may not replace that donor with a new lower-bound hypothesis." }
  , { problem := .riemann
      upstreamDeclaration := "Millennium.ClayRiemannHypothesis"
      state := .redMath
      frontier := .analytic
      firstUnpaid := "selected A2 witness fourthLipschitz < quarticSignedPoleFloorFourthLipschitzThreshold"
      note := "Exact LeanDojo <-> Mathlib RiemannHypothesis statement weld is source-written. The underlying RH programme currently exposes the selected A2 witness G1 bound as its shortest recorded positive-eighth-cap leaf, with A1 and Route B retained as alternatives. The submission pass treats the mathematics as already proved somewhere in the graph and therefore performs discovery/composition only; this receipt remains fail-closed until such a donor is actually resolved into Mathlib.RiemannHypothesis." }
  , { problem := .navierStokes
      upstreamDeclaration := "MillenniumNavierStokes.FeffermanC|D"
      state := .redType
      frontier := .proved
      firstUnpaid := "exact-kernel acceptance of DASHILiteralClayNS.dashiExactFeffermanC and DASHILiteralClayNS.dashiExactFeffermanD against the pinned LeanDojo targets"
      note := "LeanDojoForceDecayQuantitative pays both force-decay transports; momentum, divergence, energy, boundary and carrier transports are paid; LeanDojoExactTerminal constructs literal dashiExactFeffermanC : MillenniumNavierStokes.FeffermanC and dashiExactFeffermanD : MillenniumNavierStokes.FeffermanD. No mathematical or same-object theorem remains on this branch. GREEN is reserved for a recorded exact-kernel run and axiom audit." }
  , { problem := .hodge
      upstreamDeclaration := "MillenniumHodge.ClayHodge"
      state := .upstreamIncomplete
      frontier := .upstreamDefect
      firstUnpaid := "faithful official Clay Hodge statement; internal general algebraic-cycle theorem remains separate"
      note := "LeanDojo marks this statement incomplete and not a valid prize target. DASHI retains the stronger rational-Hodge/algebraic-cycle programme; the external acceptance seam is specification, not permission to weaken that programme." }
  , { problem := .birchSwinnertonDyer
      upstreamDeclaration := "MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer"
      state := .redMath
      frontier := .analytic
      firstUnpaid := "Synthesis.Millennium.BSD.BSDClayCoreObligation bg"
      note := "The Clay-facing source isolates equality of canonical analytic rank and Mordell-Weil free rank on the same rational elliptic curve after established background. The affine/projective point-group seam is now explicitly paid by MillenniumBSDProjectiveRankWeld. The submission pass must discover/compose existing continuation, finite-rank and universal-rank donors into the LeanDojo compiler; it may not reopen Taylor or rank mathematics with replacement hypotheses." }
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

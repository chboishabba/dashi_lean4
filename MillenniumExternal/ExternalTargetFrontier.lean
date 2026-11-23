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
      note := "ExactTargetSurface now proves that one concrete finite-alphabet LeanDojo language L with L∈NP and L∉P yields the exact NegativeBranch. Thus the external adapter does not require a second class hierarchy or NP-completeness wrapper. DASHI already reduces its Clay core to an actual SAT lower-bound producer; the surviving mathematical wall is that universal polynomial SAT lower bound, followed by same-object transport of the SAT language/machine model into the LeanDojo witness." }
  , { problem := .riemann
      upstreamDeclaration := "Millennium.ClayRiemannHypothesis"
      state := .redMath
      frontier := .analytic
      firstUnpaid := "selected A2 witness fourthLipschitz < quarticSignedPoleFloorFourthLipschitzThreshold"
      note := "Exact LeanDojo <-> Mathlib RiemannHypothesis statement weld is source-written. RiemannProjectiveQuarticFourWindowSignedPoleA2SelectedWitnessCut reduces the leading sixth/eighth comparison for every strength-floor witness to one exact selected-witness G1 bound; the floor threshold is approximately 737.365. The old generic support/L1 K0 is far too coarse and does not constitute an A2 no-go. If the selected witness cannot meet the exact threshold, retire this positive-eighth-cap A2 branch and continue A1/Route B rather than introducing a stronger terminal certificate." }
  , { problem := .navierStokes
      upstreamDeclaration := "MillenniumNavierStokes.FeffermanC|D"
      state := .redType
      note := "Fefferman C is the shortest external route. The released comparator theorem, comparator-data -> ClaySpec weld, ClaySpec-solution -> comparator weld, literal spatial carrier, pair-spacetime packing round-trip, domain membership, generic smooth pullback, initial divergence and solution initial condition are already paid. The exact-target compiler exposes exactly five remaining transport leaves: condition-(4) derivative packaging; condition-(5) pair-spacetime -> LeanDojo time-first Fin4 derivative packaging; positive-time momentum -> closed-half-space Clay equation with smooth boundary extension; positive-time incompressibility -> closed-half-space Clay equation with smooth boundary extension; and LeanDojo coordinate-square finite energy -> ClaySpec vector L2/norm-square energy. No new fluid estimate belongs in this seam." }
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
      note := "The Clay-facing source isolates the novel theorem exactly: equality of canonical analytic rank and Mordell-Weil free rank on the same rational elliptic curve after established background. The Selmer audit proves arbitrary mediators merely rename BSD. The literal two-descent donor has already reached |Sel_2(E)| = |E(Q)/2E(Q)| * |R_2(E)|; the arithmetic route now needs same-curve residual/Sha identification and 2^n or 2^infinity tower control to stable rank, while the analytic comparison remains independently necessary. LeanDojo carrier transport is downstream certification, not the first mathematical debt." }
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

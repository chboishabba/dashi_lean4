import MillenniumExternal.SameObjectMaxCut

/-!
# Proof-resolution-only completion board

This is the operational interpretation of the project completion assumption for
the external Millennium pass.  For P≠NP, RH, Navier--Stokes and BSD, adapter
work is restricted to theorem discovery/import, definitional reduction,
existing equivalences, same-object transport, theorem composition and kernel
checking.  A failed lookup is a reason to search the graph, not to manufacture a
replacement Millennium hypothesis.

The producer lists below are ordered by the latest cross-prover archaeology.
They deliberately include exact equivalence/terminal constructors that tell us
where *not* to reopen mathematics: when an existing package is equivalent to the
final hard witness, resolution must find its inhabitant elsewhere rather than
prove a duplicate formulation.
-/

namespace MillenniumExternal

inductive ResolutionOperation where
  | locateExistingTheorem
  | importExistingTheorem
  | definitionalEquality
  | simplifyExistingEquality
  | applyExistingEquivalence
  | sameObjectTransport
  | composeExistingTheorems
  | kernelCheck
  deriving DecidableEq, BEq, Repr

structure ProofResolutionLane where
  problem : Problem
  producerSearch : List String
  preferredOperations : List ResolutionOperation
  externalCompiler : String
  /-- A literal source-written exact target theorem already found on the graph,
  if one has been resolved.  This is not a GREEN kernel receipt. -/
  resolvedSourceTerm : Option String
  newMathematicsPermitted : Bool
  deriving DecidableEq, Repr

private def standardResolutionOps : List ResolutionOperation :=
  [ .locateExistingTheorem
  , .importExistingTheorem
  , .definitionalEquality
  , .simplifyExistingEquality
  , .applyExistingEquivalence
  , .sameObjectTransport
  , .composeExistingTheorems
  , .kernelCheck
  ]

def pVersusNPResolution : ProofResolutionLane :=
  { problem := .pVersusNP
    producerSearch :=
      [ "PNotEqualsNPQ1TerminalSemanticsDecisionFailureExact.universalQ1TerminalPackageGivesUniversalDecisionFailure"
      , "PNotEqualsNPQ1TerminalSemanticsDecisionFailureExact.universalDecisionFailureGivesUniversalQ1TerminalPackage"
      , "PNotEqualsNPQ1TerminalSemanticsDecisionFailureExact.universalQ1TerminalPackageClosesPNotEqualsNP"
      , "PNotEqualsNPGeneratedClosedQ1DiscoveryExact.GeneratedExecutedQ1StateConstructor"
      , "PNotEqualsNPQ1FiniteCodeClayClosureExact.q1FiniteCodeContradictsSATInP"
      , "PNotEqualsNPDirectSATLowerBoundExact.universalDecisionFailureClosesPNotEqualsNP"
      , "PNotEqualsNPClayCoreExact.satLowerBoundProducerClosesClayCore"
      , "UniversalPolynomialSATDecisionFailure"
      , "ConcreteTapeCookLevinCookFormulaExact"
      , "LeanDojo finite-alphabet SAT language/machine transport" ]
    preferredOperations := standardResolutionOps
    externalCompiler := "MillenniumExternal.clayPNotEqualsNP_of_language_outside_p"
    resolvedSourceTerm := none
    newMathematicsPermitted := false }

def rhResolution : ProofResolutionLane :=
  { problem := .riemann
    producerSearch :=
      [ "_root_.RiemannHypothesis"
      , "QuarticFourSignedPolePair.threeTap_globalize_near_and_mid"
      , "QuarticFourSignedPolePair.threeTap_globalize_of_pair_tsum_lt"
      , "QuarticFourSignedPolePair.RHMaxCutRoute.signedFifth_terminalPositive"
      , "RiemannSelectedPrimeSensitiveThreeTapMaxCutComplete"
      , "CanonicalTerminalPositive"
      , "high-zero/global RH terminal constructor"
      , "selected-zero/globalization same-object weld" ]
    preferredOperations := standardResolutionOps
    externalCompiler := "MillenniumExternal.clayRiemannHypothesis_of_mathlib"
    resolvedSourceTerm := none
    newMathematicsPermitted := false }

def navierStokesResolution : ProofResolutionLane :=
  { problem := .navierStokes
    producerSearch :=
      [ "DASHILiteralClayNS.dashiExactFeffermanC"
      , "DASHILiteralClayNS.dashiExactFeffermanD"
      , "LeanDojoForceDecayQuantitative"
      , "LeanDojoMomentumTransport"
      , "LeanDojoDivergenceTransport"
      , "LeanDojoEnergyTransport" ]
    preferredOperations := standardResolutionOps
    externalCompiler := "DASHILiteralClayNS.dashiExactFeffermanC / dashiExactFeffermanD"
    resolvedSourceTerm := some "DASHILiteralClayNS.dashiExactFeffermanC|D"
    newMathematicsPermitted := false }

def bsdResolution : ProofResolutionLane :=
  { problem := .birchSwinnertonDyer
    producerSearch :=
      [ "Synthesis.Millennium.BSD.universalBSDRankTheorem_of_background"
      , "Synthesis.Millennium.BSD.universalBSDRankTheorem_of_producers"
      , "Synthesis.Millennium.BSD.universalBSDRankTheorem_of_bound"
      , "Synthesis.Millennium.BSD.BSDClayCoreObligation"
      , "Synthesis.Millennium.BSD.BSDEllipticLContinuation"
      , "Synthesis.Millennium.BSD.universalBSDEstablishedBackgroundProducer_iff"
      , "Synthesis.Millennium.BSD.universalBSDMordellWeilBindingProducer_iff"
      , "MillenniumBSDProjectiveRankWeld.projective_rank_carrier_paid"
      , "Mathlib WeierstrassCurve.Projective.Point ≃+ WeierstrassCurve.Affine.Point"
      , "Hasse-Weil/LSeries bad-prime-correction same-object donor" ]
    preferredOperations := standardResolutionOps
    externalCompiler := "MillenniumExternal.clayBirchSwinnertonDyer_of_dashi"
    resolvedSourceTerm := none
    newMathematicsPermitted := false }

def faithfulResolutionLanes : List ProofResolutionLane :=
  [pVersusNPResolution, rhResolution, navierStokesResolution, bsdResolution]

theorem faithfulResolutionLanes_length : faithfulResolutionLanes.length = 4 := by
  decide

theorem no_faithful_resolution_lane_permits_new_mathematics :
    faithfulResolutionLanes.all (fun lane => !lane.newMathematicsPermitted) = true := by
  decide

theorem navierStokes_source_term_is_resolved :
    navierStokesResolution.resolvedSourceTerm =
      some "DASHILiteralClayNS.dashiExactFeffermanC|D" := by
  decide

/-- These three lanes are search/composition obligations only.  `none` means
"the unconditional exact source term has not yet been located by this adapter
branch"; it does not mean the mathematics is reopened. -/
theorem pnp_rh_bsd_still_require_donor_resolution :
    pVersusNPResolution.resolvedSourceTerm = none ∧
    rhResolution.resolvedSourceTerm = none ∧
    bsdResolution.resolvedSourceTerm = none := by
  decide

theorem resolution_board_agrees_with_same_object_cut :
    pVersusNPSameObjectCut.remaining = .transportOnly ∧
    riemannSameObjectCut.remaining = .transportOnly ∧
    navierStokesSameObjectCut.remaining = .transportOnly ∧
    bsdSameObjectCut.remaining = .transportOnly := by
  decide

end MillenniumExternal

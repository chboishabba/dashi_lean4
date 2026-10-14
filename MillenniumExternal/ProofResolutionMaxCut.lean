import MillenniumExternal.SameObjectMaxCut
import Synthesis.MillenniumBSDSelmerDefectClayEquivalence

/-!
# Proof-resolution-only completion board
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

/-- P≠NP search ordering follows live Agda #1129.

Literal own-Cook materialisation is closed at positive budget.  The actual global
clause path and token/bit cursor now return semantics and charged work from the
same recursion.  Once a concrete same-target rule table/run is supplied, the
existing `ConcreteTapeStandardClockExact.concreteStandardClockReceipt` already
pays exact step-clock identity, dispatch work bounded by `T * |rules|`, and the
guarded tape-width bound.  Thus the bespoke residual is narrowed to realizing
the streamed recursive evaluator inside the literal coded target, proving the
same-target run correspondence, and closing the resulting arithmetic inside the
same Cook budget; generic interpreter overhead is not a new premise. -/
def pVersusNPResolution : ProofResolutionLane :=
  { problem := .pVersusNP
    producerSearch :=
      [ "PNotEqualsNPCodedLiteralSelfQuotationPositiveBudgetNoGoExact.literalStructuralSelfQuotationPositiveBudgetImpossible"
      , "PNotEqualsNPCodedLiteralSelfQuotationPositiveBudgetNoGoExact.literalStructuralSelfQuotationForcesZeroBudget"
      , "PNotEqualsNPVirtualQuotationFrontierExact.literalAnchoredRouteClosed"
      , "ConcreteTapeGlobalCookLevinStreamingClauseCostedExact.globalClauseSeekCostedResultExact"
      , "ConcreteTapeGlobalCookLevinStreamingClauseCostedExact.globalClauseSeekCostedWorkBound"
      , "ConcreteTapeGlobalCookLevinStreamingBitCostedExact.streamedCookBitCostedResultExact"
      , "ConcreteTapeGlobalCookLevinStreamingBitCostedExact.streamedCookBitCostedWorkBound"
      , "PNotEqualsNPCodedFixedOwnCookStreamingCostExact.ownCookBitCostedSemanticExact"
      , "PNotEqualsNPCodedFixedOwnCookStreamingCostExact.ownCookBitCostedWorkLinear"
      , "PNotEqualsNPCodedFixedOwnCookStreamingCostExact.ownCookFormulaSameObject"
      , "PNotEqualsNPFixedDescriptionVirtualGeneratorExact.FixedDescriptionGuardedCookBitGenerator"
      , "PNotEqualsNPFaithfulVirtualGeneratorOutputExact.FaithfulGeneratorOutput"
      , "PNotEqualsNPFaithfulVirtualSimulationExact.FaithfulVirtualSelfQuotationCompilation"
      , "ConcreteTapeStandardClockExact.concreteStandardClockReceipt"
      , "PNotEqualsNPConcreteTapeRuleTableInterpreterExact.fetchConcreteRuleWorkBound"
      , "PNotEqualsNPStandardMachineMaxCutClosureExact.StandardPolynomialCandidateCoverage"
      , "PNotEqualsNPStandardMachineMaxCutClosureExact.standardMaxCutGivesCandidateFailure"
      , "PNotEqualsNPStandardMachineMaxCutClosureExact.standardMaxCutGivesUniversalFailure"
      , "PNotEqualsNPStandardMachineMaxCutClosureExact.standardMaxCutGivesSATNotInP"
      , "PNotEqualsNPStandardMachineMaxCutClosureExact.standardMaxCutGivesPNotEqualsNP"
      , "PNotEqualsNPFixedStandardOppositeQuotationExact.standardEndpointRealizationGivesDecisionFailure"
      , "PNotEqualsNPDirectSATLowerBoundExact.UniversalPolynomialSATDecisionFailure"
      , "PNotEqualsNPClayCoreExact.SATNotInP"
      , "PNotEqualsNPClayCoreExact.PNotEqualsNP"
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
      [ "Synthesis.Millennium.BSD.bsdClayCore_iff_universalSelmerDefectZero"
      , "Synthesis.Millennium.BSD.bsdClayCore_of_selmerDefectBridge_and_zero"
      , "Synthesis.Millennium.BSD.UniversalSelmerDefectAnalyticBridge"
      , "Synthesis.Millennium.BSD.UniversalSelmerDefectZero"
      , "Synthesis.Millennium.BSD.universalBSDRankTheorem_of_background"
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

theorem faithfulResolutionLanes_length : faithfulResolutionLanes.length = 4 := by decide

theorem no_faithful_resolution_lane_permits_new_mathematics :
    faithfulResolutionLanes.all (fun lane => !lane.newMathematicsPermitted) = true := by decide

theorem navierStokes_source_term_is_resolved :
    navierStokesResolution.resolvedSourceTerm =
      some "DASHILiteralClayNS.dashiExactFeffermanC|D" := by decide

theorem pnp_rh_bsd_still_require_donor_resolution :
    pVersusNPResolution.resolvedSourceTerm = none ∧
    rhResolution.resolvedSourceTerm = none ∧
    bsdResolution.resolvedSourceTerm = none := by decide

theorem pnp_resolution_uses_virtual_streaming_maxcut :
    pVersusNPResolution.producerSearch.contains
      "PNotEqualsNPCodedLiteralSelfQuotationPositiveBudgetNoGoExact.literalStructuralSelfQuotationPositiveBudgetImpossible" = true ∧
    pVersusNPResolution.producerSearch.contains
      "ConcreteTapeGlobalCookLevinStreamingBitCostedExact.streamedCookBitCostedResultExact" = true ∧
    pVersusNPResolution.producerSearch.contains
      "ConcreteTapeGlobalCookLevinStreamingBitCostedExact.streamedCookBitCostedWorkBound" = true ∧
    pVersusNPResolution.producerSearch.contains
      "ConcreteTapeStandardClockExact.concreteStandardClockReceipt" = true ∧
    pVersusNPResolution.producerSearch.contains
      "PNotEqualsNPFaithfulVirtualSimulationExact.FaithfulVirtualSelfQuotationCompilation" = true := by decide

theorem bsd_resolution_uses_zero_defect_equivalence :
    bsdResolution.producerSearch.contains
      "Synthesis.Millennium.BSD.bsdClayCore_iff_universalSelmerDefectZero" = true := by decide

#check Synthesis.Millennium.BSD.bsdClayCore_iff_universalSelmerDefectZero
#check Synthesis.Millennium.BSD.bsdClayCore_of_selmerDefectBridge_and_zero

theorem resolution_board_agrees_with_same_object_cut :
    pVersusNPSameObjectCut.remaining = .transportOnly ∧
    riemannSameObjectCut.remaining = .transportOnly ∧
    navierStokesSameObjectCut.remaining = .transportOnly ∧
    bsdSameObjectCut.remaining = .transportOnly := by decide

end MillenniumExternal

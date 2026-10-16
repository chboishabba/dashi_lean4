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

/-- P≠NP follows the live Agda #1129 compiler recut.

The streamed evaluator is index-only at runtime, its local Boolean kernels are
frozen finite tables, actual candidate rules embed into a summed/linked coded
target, and exact candidate runs lift edge-for-edge with identical step count.
Three-phase run composition is paid.  The return-freshness theorem shows that a
declared T-step `finish` is not automatically a legal return point when its
resident dispatch key is still occupied.

Recent XOR-grid work contributes one bounded compiler insight only.  The
complexity branch reproves locally that a binary countdown data bit updates by
XOR with the incoming borrow and that the XOR coordinate is recoverable, while
the outgoing borrow is a separate nonlinear coordinate.  Equal XOR output can
carry different borrow output, so parity alone is neither an exact-T clock nor
complexity hardness evidence.  The next machine payment is therefore a literal
bit+borrow tape counter which emits one exact handoff pulse, followed by a final
self-consistent Cook budget T* charging generator + timer + candidate + suffix. -/
def pVersusNPResolution : ProofResolutionLane :=
  { problem := .pVersusNP
    producerSearch :=
      [ "PNotEqualsNPCodedLiteralSelfQuotationPositiveBudgetNoGoExact.literalStructuralSelfQuotationPositiveBudgetImpossible"
      , "PNotEqualsNPVirtualQuotationFrontierExact.literalAnchoredRouteClosed"
      , "ConcreteTapeGlobalCookLevinStreamingClauseCostedExact.globalClauseSeekCostedResultExact"
      , "ConcreteTapeGlobalCookLevinStreamingBitCostedExact.streamedCookBitCostedResultExact"
      , "ConcreteTapeGlobalCookLevinStreamingBitCostedExact.streamedCookBitCostedWorkBound"
      , "PNotEqualsNPCodedFixedOwnCookStreamingCostExact.ownCookFormulaSameObject"
      , "GuardedCookFixedDescriptionIndexABIExact.indexABIWorkBound"
      , "ConcreteTapeFixedLocalKernelTablesExact.transitionKernelFrozenSeekExact"
      , "ConcreteTapeFixedLocalKernelTablesExact.acceptanceKernelFrozenSeekExact"
      , "CodedFiniteStandardModeSumExact.sumFragments"
      , "CodedFiniteStandardLinkedStructuralSimulationExact.linkedStructuralSimulation"
      , "CodedFiniteStandardLinkedRunSimulationExact.simulateCodedCandidateExecution"
      , "CodedFiniteStandardLinkedRunSimulationExact.appendLinkedCandidatePhase"
      , "CodedFiniteStandardReturnLinkFreshnessExact.residentCandidateRuleBlocksReturnLink"
      , "PNotEqualsNPXORCountdownMicrocodeExact.xorRecoverLeft"
      , "PNotEqualsNPXORCountdownMicrocodeExact.xorRecoverRight"
      , "PNotEqualsNPXORCountdownMicrocodeExact.sameXorOutputDifferentBorrow"
      , "PNotEqualsNPXORCountdownMicrocodeExact.counterCompilationRemains"
      , "ConcreteTapeStandardClockExact.concreteStandardClockReceipt"
      , "PNotEqualsNPFaithfulVirtualSimulationExact.FaithfulVirtualSelfQuotationCompilation"
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
      , "Synthesis.Millennium.BSD.BSDClayCoreObligation"
      , "MillenniumBSDProjectiveRankWeld.projective_rank_carrier_paid"
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
      "GuardedCookFixedDescriptionIndexABIExact.indexABIWorkBound" = true ∧
    pVersusNPResolution.producerSearch.contains
      "CodedFiniteStandardLinkedRunSimulationExact.simulateCodedCandidateExecution" = true ∧
    pVersusNPResolution.producerSearch.contains
      "CodedFiniteStandardLinkedRunSimulationExact.appendLinkedCandidatePhase" = true ∧
    pVersusNPResolution.producerSearch.contains
      "CodedFiniteStandardReturnLinkFreshnessExact.residentCandidateRuleBlocksReturnLink" = true ∧
    pVersusNPResolution.producerSearch.contains
      "PNotEqualsNPXORCountdownMicrocodeExact.sameXorOutputDifferentBorrow" = true ∧
    pVersusNPResolution.producerSearch.contains
      "ConcreteTapeStandardClockExact.concreteStandardClockReceipt" = true := by decide

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

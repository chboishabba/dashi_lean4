import Integration.JInvariantSheafDescent

/-!
# Agda mirror receipt: J/369 sheaf/descent integration

Cross-prover mirror for the Agda owner
DASHI/Moonshine/JInvariantSheafHyperformAdmissibleDescentExact.agda.

The theorem proofs live in Integration.JInvariantSheafDescent; this module
provides the repository's conventional AgdaMirror discovery surface and a
fail-closed provenance receipt. File/path correspondence is not itself a
proof that two formal terms are definitionally identical across provers.
-/

namespace AgdaMirror.JInvariantSheafDescent

open Integration.JInvariantSheafDescent

def agdaRepository : String := "chboishabba/dashi_agda"

def agdaOwner : String :=
  "DASHI/Moonshine/JInvariantSheafHyperformAdmissibleDescentExact.agda"

def leanIntegrationOwner : String :=
  "Integration/JInvariantSheafDescent.lean"

structure CrossProverReceipt where
  agdaRepository : String
  agdaOwner : String
  leanOwner : String
  localObserverSectionMirrored : Bool
  hiddenFineNonDescentMirrored : Bool
  consumerGatedRepairMirrored : Bool
  pantsFiniteRechartMirrored : Bool
  arithmetic369Mirrored : Bool
  pathCorrespondenceIsProofEquivalence : Bool
  deriving Repr

def crossProverReceipt : CrossProverReceipt where
  agdaRepository := agdaRepository
  agdaOwner := agdaOwner
  leanOwner := leanIntegrationOwner
  localObserverSectionMirrored := true
  hiddenFineNonDescentMirrored := true
  consumerGatedRepairMirrored := true
  pantsFiniteRechartMirrored := true
  arithmetic369Mirrored := true
  pathCorrespondenceIsProofEquivalence := false

theorem localObserver_section_parity (v : Local27) :
    localObserver (localSection v) = v :=
  localObserver_section v

theorem q11_nonDescent_parity :
    ¬ ConsumerSufficient localObserver (fineFieldAt q11) :=
  local27_not_sufficient_for_q11

theorem fullFineRepair_parity :
    JObserverEligible .fullField :=
  fullField_eligible

theorem localShortObserverRejected_parity :
    ¬ JObserverEligible .local27 :=
  local27_not_eligible

theorem ninePantsRoundTrip_parity (q : JCoarse) :
    pants2ToNine (nineToPants2 q) = q :=
  pants2_nine_roundtrip q

theorem local27PantsRoundTrip_parity (v : Local27) :
    pants3ToLocal27 (local27ToPants3 v) = v :=
  pants3_local27_roundtrip v

theorem bulk196830_parity :
    3^11 + 3^9 = 196830 :=
  bulk196830

theorem monster196883_parity :
    3^11 + 3^9 + 53 = 196883 :=
  monster196883

theorem moonshine196884_parity :
    3^11 + 3^9 + 54 = 196884 :=
  moonshine196884

theorem weight12Square144_not_promoted :
    arithmeticAnalyticLinks.square144IsAutomaticModularInvariant = false := rfl

theorem literalAnalyticSite_not_claimed :
    frontier.literalAnalyticGrothendieckSiteConstructed = false := rfl

theorem literalMonsterIntertwiner_not_claimed :
    frontier.literalMonsterModuleIntertwinerConstructed = false := rfl

end AgdaMirror.JInvariantSheafDescent

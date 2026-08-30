import Cuisine.SurfaceInterpretation
import Cuisine.SafetyFabric
import Cuisine.KnotWeave
import Cuisine.NonaryAction

/-!
# The Sweetgrass carrier spine, audited and realised

`Agda/DASHI/Interop/SweetgrassCarrierSpine.agda` is the module the cuisine
record reaches through `sweetgrassAttribution : String`.  It enumerates
thirty-five *carrier motifs* — among them `base_369`, `dialectical_depth`,
`supervoxel_admissibility`, `fifteen_ssp`, `monster_moonshine`,
`j_invariant_moonshine_anchor`, `p_adic_metric`, `hecke_eigen_motif`,
`high_dimensional_hyperfabric` — and threads them into named lanes
(`dialecticTiesTo369`, `heckeEigenJInvariantThread`, ...).

That module is a *vocabulary*: every motif is a nullary constructor, its content
is a `String` key, a role, an anchor and a fabric order, and its outputs are
role-vectors and evidence-only PNF atoms.  Nothing in it is a value of the
repository's `TriTruth`, `SSP`, `Fabric`, `MaskSSP` or `Stage6`.  This file does
two things.

## 1. The audit (negatives, all proved)

* `canonicalCarrierMotifs_nodup`, `_length` — the thirty-five motifs are
  distinct, and the canonical list is complete (`motifs_complete`).
* `motifAnchor_not_injective` — the anchor map identifies motifs
  (`motifBTTree` and `motifBTBraid` share `anchorBTBraidKP`), so anchors do not
  separate the vocabulary.
* `anchors_not_surjective`, `unreachedAnchors_eq` — two of the thirty-three
  declared anchors, `anchorLocalDocs369` and `anchorMonsterMoonshineSSPQuotient`,
  are never the anchor of any motif: they are declared and unused.
* `heckeOperatorRole_unused` — likewise the role named for the Hecke *operator*
  is declared and never assigned; `motifHeckeEigen` is given `eigenProfileRole`.
* `projectionTarget_image`, `motifProjectionTarget_not_injective` — the
  role-vector projection collapses the thirty-nine roles onto five of the eight
  projection targets, so the PNF surface retains almost none of the
  distinctions the motif vocabulary draws.

## 2. The realisation (positives, all proved)

`realise : CarrierMotif → SpineCarrier` is the typed table saying, for each
motif, *which implementation type in this repository it names* — with an
explicit `unrealised` value for the motifs that name nothing here.  Its
cardinalities are checked against the real `Fintype.card`s
(`carrierCard_eq`), and the honesty clauses are proved:
`sweetgrass_itself_unrealised`, `card_realised`.

Beyond the naming table, `SweetgrassRealisation` bundles the *structural*
statements — the thing that was genuinely missing.  For the two threads the
Agda module singles out, `dialecticTiesTo369` and `heckeEigenJInvariantThread`,
each of the realised motifs is not merely matched with a type but with a
theorem about that type, and all of the theorems are about the *same* object:
the hyperfabric of ternary sections over the fifteen supersingular primes, and
the cuisine umami transport onto it.

Boundary: this realises the *carriers*.  It does not prove any Hecke
eigenvalue statement, any modular-form statement, or anything about the Monster
group; `motifGaugeYangMills` and `motifNavierStokesFlow` are mirrored as bare
enumeration labels with no content whatsoever, exactly as in the source, and no
statement in this file mentions either subject again.
-/

namespace Cuisine.SweetgrassSpine

open AgdaMirror.DASHIAlgebra (Trit Stage6)
open AgdaMirror.Base369 (TriTruth)
open AgdaMirror.MonsterOntos (SSP)
open Synthesis.MonsterFibre
open Synthesis.Hyperfabric
open Synthesis.MoonshineBase
open Cuisine.SensoryCore (TasteDimension)
open Cuisine.UmamiTransport
open Cuisine.NineSheet
open Cuisine.SafetyFabric
open Cuisine.KnotWeave (KnotWeaveField knotWeaveFabric)
open Cuisine.NonaryAction

/-! ## Mirrors of the vocabulary -/

/-- Mirror of `CarrierMotif`.  Thirty-five nullary constructors. -/
inductive CarrierMotif
  | motifSweetgrassBraidFabric | motif369 | motifCarry | motifDialectic | motifBraid
  | motifBTTree | motifBTBraid | motifPAdic | motifDecimalArchimedean | motifSupervoxel
  | motifThreadBraid | motifLowOrderRegularFabric | motifHighDimensionalHyperfabric
  | motifFascisticContraction | motifAntifascistInvertibility | motifWaveTransport
  | motifWeave | motifKnot | motifFifteenSSP | motifHeckeEigen | motifJInvariant
  | motifMonsterMoonshine | motifHighNPrimeCarrier | motifTlureyTriadicNonary
  | motifUltrametricAdelic | motifCliffordBottSpinor | motifGaugeYangMills
  | motifNavierStokesFlow | motifSemanticPNFResidual | motifClaimWikidataLattice
  | motifDNAGenomeChemistry | motifBrainConnectomeSemantic | motifBiologySensorimotor
  | motifCategoryFunctorOperator | motifLatticeQuotient
  deriving DecidableEq, Fintype, Repr

/-- Mirror of `CarrierAnchor`.  Thirty-three nullary constructors. -/
inductive CarrierAnchor
  | anchorBase369 | anchorLocalDocs369 | anchorCarryMemory | anchorDialecticalDepth
  | anchorUnifiedCarryBraid | anchorBTBraidKP | anchorCarrierBraid | anchorPAdicMetric
  | anchorDecimalArchimedeanLane | anchorSupervoxelAdmissibility
  | anchorPrimeHeckeEigenMotif | anchorHeckeScan15 | anchorModularJInvariant
  | anchorMonsterMoonshineJDistribution | anchorMonsterMoonshineSSPQuotient
  | anchorFascisticSystem | anchorAntifascistSystem | anchorWaveTransport
  | anchorKnotWeaveCulture | anchorCarrierWeaveDefect | anchorMonsterSSP15
  | anchorTlureyLogic | anchorUltrametricAdelicTransport | anchorCliffordBottSpinor
  | anchorGaugeYangMills | anchorNavierStokesFlow | anchorSemanticPNFResidual
  | anchorClaimWikidataLattice | anchorDNAGenomeChemistry | anchorBrainConnectomeSemantic
  | anchorBiologySensorimotor | anchorCategoryFunctorOperator | anchorLatticeQuotient
  deriving DecidableEq, Fintype, Repr

/-- Mirror of `CarrierRole`.  Thirty-nine nullary constructors. -/
inductive CarrierRole
  | localStateRole | orientationRole | memoryRole | defectRole | pressureRole
  | admissibilityRole | transportRole | bindingRole | braidRole | threadRole
  | btBraidRole | fabricRole | hyperfabricRole | dialecticalInclusionRole
  | contractionRole | invertibilityRole | primeLaneRole | highNPrimeCarrierRole
  | heckeOperatorRole | eigenProfileRole | jInvariantRole | moonshineGroupRole
  | categorySurfaceRole | latticeRole | quotientRole | functorRole | operatorRole
  | semanticTransportRole | residualComparisonRole | claimReviewRole | genomeRole
  | connectomeRole | sensorimotorRole | chemistryChannelRole | gaugeRole | spinorRole
  | flowRole | sourceAttributionRole | nonPromotionBoundaryRole
  deriving DecidableEq, Fintype, Repr

/-- Mirror of `Role.ProjectionTarget` of `PNFRoleVectorAlgebra`. -/
inductive ProjectionTarget
  | predicateTarget | subjectTarget | actionTarget | objectTarget | qualifierTarget
  | modifierDiagnosticTarget | provenanceTarget | droppedTarget
  deriving DecidableEq, Fintype, Repr

/-- Mirror of `FabricOrder`. -/
inductive FabricOrder
  | lowOrderRegularFabric | highDimensionalBTBraidHyperfabric
  deriving DecidableEq, Fintype, Repr

open CarrierMotif CarrierAnchor CarrierRole ProjectionTarget FabricOrder

/-- Mirror of `motifAnchor`. -/
def motifAnchor : CarrierMotif → CarrierAnchor
  | motifSweetgrassBraidFabric => anchorKnotWeaveCulture
  | motif369 => anchorBase369
  | motifCarry => anchorCarryMemory
  | motifDialectic => anchorDialecticalDepth
  | motifBraid => anchorUnifiedCarryBraid
  | motifBTTree => anchorBTBraidKP
  | motifBTBraid => anchorBTBraidKP
  | motifPAdic => anchorPAdicMetric
  | motifDecimalArchimedean => anchorDecimalArchimedeanLane
  | motifSupervoxel => anchorSupervoxelAdmissibility
  | motifThreadBraid => anchorCarrierBraid
  | motifLowOrderRegularFabric => anchorCarrierWeaveDefect
  | motifHighDimensionalHyperfabric => anchorBTBraidKP
  | motifFascisticContraction => anchorFascisticSystem
  | motifAntifascistInvertibility => anchorAntifascistSystem
  | motifWaveTransport => anchorWaveTransport
  | motifWeave => anchorCarrierWeaveDefect
  | motifKnot => anchorKnotWeaveCulture
  | motifFifteenSSP => anchorMonsterSSP15
  | motifHeckeEigen => anchorPrimeHeckeEigenMotif
  | motifJInvariant => anchorModularJInvariant
  | motifMonsterMoonshine => anchorMonsterMoonshineJDistribution
  | motifHighNPrimeCarrier => anchorHeckeScan15
  | motifTlureyTriadicNonary => anchorTlureyLogic
  | motifUltrametricAdelic => anchorUltrametricAdelicTransport
  | motifCliffordBottSpinor => anchorCliffordBottSpinor
  | motifGaugeYangMills => anchorGaugeYangMills
  | motifNavierStokesFlow => anchorNavierStokesFlow
  | motifSemanticPNFResidual => anchorSemanticPNFResidual
  | motifClaimWikidataLattice => anchorClaimWikidataLattice
  | motifDNAGenomeChemistry => anchorDNAGenomeChemistry
  | motifBrainConnectomeSemantic => anchorBrainConnectomeSemantic
  | motifBiologySensorimotor => anchorBiologySensorimotor
  | motifCategoryFunctorOperator => anchorCategoryFunctorOperator
  | motifLatticeQuotient => anchorLatticeQuotient

/-- Mirror of `motifPrimaryRole`. -/
def motifPrimaryRole : CarrierMotif → CarrierRole
  | motifSweetgrassBraidFabric => fabricRole
  | motif369 => localStateRole
  | motifCarry => memoryRole
  | motifDialectic => dialecticalInclusionRole
  | motifBraid => braidRole
  | motifBTTree => primeLaneRole
  | motifBTBraid => btBraidRole
  | motifPAdic => transportRole
  | motifDecimalArchimedean => transportRole
  | motifSupervoxel => admissibilityRole
  | motifThreadBraid => threadRole
  | motifLowOrderRegularFabric => fabricRole
  | motifHighDimensionalHyperfabric => hyperfabricRole
  | motifFascisticContraction => contractionRole
  | motifAntifascistInvertibility => invertibilityRole
  | motifWaveTransport => transportRole
  | motifWeave => bindingRole
  | motifKnot => bindingRole
  | motifFifteenSSP => primeLaneRole
  | motifHeckeEigen => eigenProfileRole
  | motifJInvariant => jInvariantRole
  | motifMonsterMoonshine => moonshineGroupRole
  | motifHighNPrimeCarrier => highNPrimeCarrierRole
  | motifTlureyTriadicNonary => localStateRole
  | motifUltrametricAdelic => transportRole
  | motifCliffordBottSpinor => spinorRole
  | motifGaugeYangMills => gaugeRole
  | motifNavierStokesFlow => flowRole
  | motifSemanticPNFResidual => residualComparisonRole
  | motifClaimWikidataLattice => claimReviewRole
  | motifDNAGenomeChemistry => genomeRole
  | motifBrainConnectomeSemantic => connectomeRole
  | motifBiologySensorimotor => sensorimotorRole
  | motifCategoryFunctorOperator => categorySurfaceRole
  | motifLatticeQuotient => latticeRole

/-- Mirror of `roleProjectionTarget`. -/
def roleProjectionTarget : CarrierRole → ProjectionTarget
  | localStateRole => objectTarget
  | orientationRole => modifierDiagnosticTarget
  | memoryRole => provenanceTarget
  | defectRole => objectTarget
  | pressureRole => qualifierTarget
  | admissibilityRole => qualifierTarget
  | transportRole => actionTarget
  | bindingRole => objectTarget
  | braidRole => modifierDiagnosticTarget
  | threadRole => provenanceTarget
  | btBraidRole => modifierDiagnosticTarget
  | fabricRole => modifierDiagnosticTarget
  | hyperfabricRole => modifierDiagnosticTarget
  | dialecticalInclusionRole => qualifierTarget
  | contractionRole => actionTarget
  | invertibilityRole => qualifierTarget
  | primeLaneRole => objectTarget
  | highNPrimeCarrierRole => objectTarget
  | heckeOperatorRole => actionTarget
  | eigenProfileRole => qualifierTarget
  | jInvariantRole => objectTarget
  | moonshineGroupRole => objectTarget
  | categorySurfaceRole => modifierDiagnosticTarget
  | latticeRole => modifierDiagnosticTarget
  | quotientRole => actionTarget
  | functorRole => actionTarget
  | operatorRole => actionTarget
  | semanticTransportRole => actionTarget
  | residualComparisonRole => qualifierTarget
  | claimReviewRole => objectTarget
  | genomeRole => objectTarget
  | connectomeRole => objectTarget
  | sensorimotorRole => qualifierTarget
  | chemistryChannelRole => objectTarget
  | gaugeRole => qualifierTarget
  | spinorRole => objectTarget
  | flowRole => actionTarget
  | sourceAttributionRole => provenanceTarget
  | nonPromotionBoundaryRole => provenanceTarget

/-- Mirror of `motifProjectionTarget`. -/
def motifProjectionTarget (m : CarrierMotif) : ProjectionTarget :=
  roleProjectionTarget (motifPrimaryRole m)

/-- Mirror of `motifFabricOrder`. -/
def motifFabricOrder : CarrierMotif → FabricOrder
  | motifHighDimensionalHyperfabric | motifBTBraid | motifHighNPrimeCarrier
  | motifHeckeEigen | motifJInvariant | motifMonsterMoonshine
  | motifCliffordBottSpinor | motifGaugeYangMills | motifUltrametricAdelic
  | motifCategoryFunctorOperator | motifLatticeQuotient =>
      highDimensionalBTBraidHyperfabric
  | _ => lowOrderRegularFabric

/-! ## The canonical lists and the threads -/

def canonicalCarrierMotifs : List CarrierMotif :=
  [motifSweetgrassBraidFabric, motif369, motifCarry, motifDialectic, motifBraid,
    motifBTTree, motifBTBraid, motifPAdic, motifDecimalArchimedean, motifSupervoxel,
    motifThreadBraid, motifLowOrderRegularFabric, motifHighDimensionalHyperfabric,
    motifFascisticContraction, motifAntifascistInvertibility, motifWaveTransport,
    motifWeave, motifKnot, motifFifteenSSP, motifHeckeEigen, motifJInvariant,
    motifMonsterMoonshine, motifHighNPrimeCarrier, motifTlureyTriadicNonary,
    motifUltrametricAdelic, motifCliffordBottSpinor, motifGaugeYangMills,
    motifNavierStokesFlow, motifSemanticPNFResidual, motifClaimWikidataLattice,
    motifDNAGenomeChemistry, motifBrainConnectomeSemantic, motifBiologySensorimotor,
    motifCategoryFunctorOperator, motifLatticeQuotient]

def canonicalCarrierAnchors : List CarrierAnchor :=
  [anchorBase369, anchorLocalDocs369, anchorCarryMemory, anchorDialecticalDepth,
    anchorUnifiedCarryBraid, anchorBTBraidKP, anchorCarrierBraid, anchorPAdicMetric,
    anchorDecimalArchimedeanLane, anchorSupervoxelAdmissibility,
    anchorPrimeHeckeEigenMotif, anchorHeckeScan15, anchorModularJInvariant,
    anchorMonsterMoonshineJDistribution, anchorMonsterMoonshineSSPQuotient,
    anchorFascisticSystem, anchorAntifascistSystem, anchorWaveTransport,
    anchorKnotWeaveCulture, anchorCarrierWeaveDefect, anchorMonsterSSP15,
    anchorTlureyLogic, anchorUltrametricAdelicTransport, anchorCliffordBottSpinor,
    anchorGaugeYangMills, anchorNavierStokesFlow, anchorSemanticPNFResidual,
    anchorClaimWikidataLattice, anchorDNAGenomeChemistry, anchorBrainConnectomeSemantic,
    anchorBiologySensorimotor, anchorCategoryFunctorOperator, anchorLatticeQuotient]

/-- Mirror of `dialecticTiesTo369`. -/
def dialecticTiesTo369 : List CarrierMotif :=
  [motif369, motifCarry, motifDialectic, motifTlureyTriadicNonary,
    motifSweetgrassBraidFabric]

/-- Mirror of `heckeEigenJInvariantThread`. -/
def heckeEigenJInvariantThread : List CarrierMotif :=
  [motifHeckeEigen, motifJInvariant, motifMonsterMoonshine, motifFifteenSSP,
    motifHighNPrimeCarrier]

/-- Mirror of `btBraidFabricThread`. -/
def btBraidFabricThread : List CarrierMotif :=
  [motifThreadBraid, motifBraid, motifBTTree, motifBTBraid,
    motifLowOrderRegularFabric, motifHighDimensionalHyperfabric,
    motifHighNPrimeCarrier]

/-! ## The audit -/

theorem canonicalCarrierMotifs_length : canonicalCarrierMotifs.length = 35 := rfl

theorem canonicalCarrierMotifs_nodup : canonicalCarrierMotifs.Nodup := by decide

theorem motifs_complete (m : CarrierMotif) : m ∈ canonicalCarrierMotifs := by
  cases m <;> decide

theorem canonicalCarrierAnchors_length : canonicalCarrierAnchors.length = 33 := rfl

theorem canonicalCarrierAnchors_nodup : canonicalCarrierAnchors.Nodup := by decide

theorem card_carrierMotif : Fintype.card CarrierMotif = 35 := rfl

theorem card_carrierAnchor : Fintype.card CarrierAnchor = 33 := rfl

theorem card_carrierRole : Fintype.card CarrierRole = 39 := rfl

/-- **Anchors do not separate motifs.**  The Bruhat–Tits tree motif, the
BT-braid motif and the hyperfabric motif all carry the same anchor. -/
theorem motifAnchor_not_injective : ¬ Function.Injective motifAnchor := by
  intro h
  exact absurd (h (a₁ := motifBTTree) (a₂ := motifBTBraid) rfl) (by decide)

theorem motifAnchor_collision :
    motifAnchor motifBTTree = motifAnchor motifBTBraid ∧
      motifAnchor motifBTBraid = motifAnchor motifHighDimensionalHyperfabric ∧
      motifAnchor motifWeave = motifAnchor motifLowOrderRegularFabric ∧
      motifAnchor motifKnot = motifAnchor motifSweetgrassBraidFabric := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- The declared anchors that no motif reaches. -/
def unreachedAnchors : List CarrierAnchor :=
  [anchorLocalDocs369, anchorMonsterMoonshineSSPQuotient]

/-- **Two declared anchors are unused.**  In particular the anchor named for the
Monster/moonshine *`SSP` quotient* — the one place where the vocabulary would
have met the fifteen-prime base — is never assigned to any motif. -/
theorem unreachedAnchors_eq (a : CarrierAnchor) :
    (∀ m, motifAnchor m ≠ a) ↔ a ∈ unreachedAnchors := by
  revert a
  decide

theorem anchors_not_surjective : ¬ Function.Surjective motifAnchor := by
  intro h
  obtain ⟨m, hm⟩ := h anchorLocalDocs369
  exact absurd hm (by revert m; decide)

/-- **The role named for the Hecke operator is never used**: the Hecke motif is
assigned the *eigen-profile* role instead. -/
theorem heckeOperatorRole_unused (m : CarrierMotif) :
    motifPrimaryRole m ≠ heckeOperatorRole := by
  revert m; decide

theorem heckeEigen_role : motifPrimaryRole motifHeckeEigen = eigenProfileRole := rfl

/-- The five projection targets the role table actually uses. -/
def usedProjectionTargets : List ProjectionTarget :=
  [actionTarget, objectTarget, qualifierTarget, modifierDiagnosticTarget,
    provenanceTarget]

/-- **The PNF projection collapses the vocabulary.**  Thirty-nine roles land in
five of the eight projection targets; `predicateTarget`, `subjectTarget` and
`droppedTarget` are never produced. -/
theorem projectionTarget_image (r : CarrierRole) :
    roleProjectionTarget r ∈ usedProjectionTargets := by
  revert r; decide

theorem projectionTarget_missing (t : ProjectionTarget) :
    (∀ r, roleProjectionTarget r ≠ t) ↔
      t = predicateTarget ∨ t = subjectTarget ∨ t = droppedTarget := by
  revert t; decide

theorem motifProjectionTarget_not_injective : ¬ Function.Injective motifProjectionTarget := by
  intro h
  exact absurd (h (a₁ := motif369) (a₂ := motifWeave) rfl) (by decide)

/-! ## The realisation table -/

/-- The implementation carriers of this repository that Sweetgrass motifs name,
plus an explicit `unrealised` marker for the ones that name nothing here. -/
inductive SpineCarrier
  | tone3Carrier | knot3Carrier | stage4Carrier | stage6Carrier | nonary9Carrier
  | prime15Carrier | sheet9Carrier | mask15Carrier | fabric15Carrier | jGradedCarrier
  | unrealised
  deriving DecidableEq, Fintype, Repr

open SpineCarrier

/-- **The realisation table.**  Each Sweetgrass motif is sent to the type in this
repository that it names, or to `unrealised`. -/
def realise : CarrierMotif → SpineCarrier
  | motif369 => tone3Carrier
  | motifDialectic => stage6Carrier
  | motifTlureyTriadicNonary => nonary9Carrier
  | motifKnot => knot3Carrier
  | motifWeave => knot3Carrier
  | motifFifteenSSP => prime15Carrier
  | motifHighNPrimeCarrier => prime15Carrier
  | motifLowOrderRegularFabric => sheet9Carrier
  | motifHighDimensionalHyperfabric => fabric15Carrier
  | motifMonsterMoonshine => mask15Carrier
  | motifPAdic => mask15Carrier
  | motifUltrametricAdelic => mask15Carrier
  | motifJInvariant => jGradedCarrier
  | _ => unrealised

/-- The size of each carrier. -/
def carrierCard : SpineCarrier → Option ℕ
  | tone3Carrier => some 3
  | knot3Carrier => some 3
  | stage4Carrier => some 4
  | stage6Carrier => some 6
  | nonary9Carrier => some 9
  | prime15Carrier => some 15
  | sheet9Carrier => some 19683
  | mask15Carrier => some 32768
  | fabric15Carrier => some 14348907
  | jGradedCarrier => some 196884
  | unrealised => none

/-- **The carriers are the real implementation types.**  Every stated size is
the `Fintype.card` of the type the motif names, and the graded carrier is the
supplied moonshine numeral. -/
theorem carrierCard_eq :
    carrierCard tone3Carrier = some (Fintype.card TriTruth) ∧
      carrierCard knot3Carrier = some (Fintype.card Cuisine.KnotWeave.KnotWeaveCarrier) ∧
      carrierCard stage4Carrier = some (Fintype.card AgdaMirror.LogicTlurey.Stage) ∧
      carrierCard stage6Carrier = some (Fintype.card Stage6) ∧
      carrierCard nonary9Carrier = some (Fintype.card (TriTruth × TriTruth)) ∧
      carrierCard prime15Carrier = some (Fintype.card SSP) ∧
      carrierCard mask15Carrier = some (Fintype.card MaskSSP) ∧
      carrierCard fabric15Carrier = some (Fintype.card Fabric) ∧
      carrierCard jGradedCarrier = some AgdaMirror.Moonshine.jCoefficient := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · rw [card_maskSSP]; norm_num [carrierCard]
  · rw [card_fabric]; norm_num [carrierCard]

/-- The depth-nine sheet carrier is the three-taste sheet of `Cuisine.NineSheet`. -/
theorem carrierCard_sheet9 (T : Finset TasteDimension) (hT : T.card = 3) :
    carrierCard sheet9Carrier = some (Fintype.card (Supported (tasteBlock T))) := by
  rw [card_taste_sheet T hT]
  rfl

/-- **Honesty clause.**  The Sweetgrass braid/fabric motif itself — the one the
cuisine record actually reaches, and only through a `String` — names no
implementation type in this repository. -/
theorem sweetgrass_itself_unrealised : realise motifSweetgrassBraidFabric = unrealised := rfl

/-- The motifs that do name an implementation type. -/
def realisedMotifs : List CarrierMotif :=
  [motif369, motifDialectic, motifTlureyTriadicNonary, motifKnot, motifWeave,
    motifFifteenSSP, motifHighNPrimeCarrier, motifLowOrderRegularFabric,
    motifHighDimensionalHyperfabric, motifMonsterMoonshine, motifPAdic,
    motifUltrametricAdelic, motifJInvariant]

theorem realised_iff (m : CarrierMotif) : realise m ≠ unrealised ↔ m ∈ realisedMotifs := by
  revert m; decide

/-- **Thirteen of the thirty-five motifs are realised**; the other twenty-two
name nothing this repository defines. -/
theorem card_realised : realisedMotifs.length = 13 := rfl

theorem realisedMotifs_nodup : realisedMotifs.Nodup := by decide

/-- Every motif on the `heckeEigenJInvariantThread` except the Hecke motif
itself is realised, and the Hecke motif is not. -/
theorem hecke_thread_realisation :
    realise motifHeckeEigen = unrealised ∧
      realise motifJInvariant = jGradedCarrier ∧
      realise motifMonsterMoonshine = mask15Carrier ∧
      realise motifFifteenSSP = prime15Carrier ∧
      realise motifHighNPrimeCarrier = prime15Carrier := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- On the `dialecticTiesTo369` thread, the `369`, dialectic and Tlurey motifs
are realised and the carry and Sweetgrass motifs are not. -/
theorem dialectic_thread_realisation :
    realise motif369 = tone3Carrier ∧
      realise motifDialectic = stage6Carrier ∧
      realise motifTlureyTriadicNonary = nonary9Carrier ∧
      realise motifCarry = unrealised ∧
      realise motifSweetgrassBraidFabric = unrealised := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The structural realisation

The naming table above says *which* type each motif denotes.  The record below
says what those types **do**, and that they all do it to one another: the
`369` fibre sits over the fifteen-prime base, the dialectic acts on the
resulting hyperfabric, the Monster mask is the support of a section, the
depth-nine sheet of the `3 · 5` grid carries the moonshine numerals, the p-adic
carrier is the Monster ultrametric on those masks, and the cuisine umami law is
a surjective homomorphism onto the whole thing. -/

/-- The Sweetgrass motifs that this repository realises, together with the
theorem each one realises. -/
structure SweetgrassRealisation where
  /-- `base_369`: the fibre is the three-element tone carrier. -/
  base369 : realise motif369 = tone3Carrier ∧ Fintype.card TriTruth = 3
  /-- `fifteen_ssp`: the base is the fifteen supersingular primes, in the
  shape `3 · 5`. -/
  fifteenSSP : Fintype.card SSP = 15 ∧ Nonempty (SSP ≃ TriTruth × TasteDimension)
  /-- `high_dimensional_hyperfabric`: the sections over that base. -/
  hyperfabric : Fintype.card Fabric = 3 ^ 15
  /-- `carrier_weave` / `knot_binding`: the knot-weave culture carrier is the
  tone carrier, and its fields over the base are hyperfabric sections. -/
  knotWeave : KnotWeaveField ≃ Fabric
  /-- `dialectical_depth`: the six dialectical stages act on the hyperfabric,
  and cuisine-side that action is seasoning with the radical. -/
  dialecticAction : ∀ (s : Stage6) (u : ℕ),
    fabricAct s (umamiFabric u) =
      umamiFabric (Nat.rec u (fun _ v => umamiCompose v radicalIntensity) (stageIndex s))
  /-- The cuisine umami law is a surjective homomorphism onto the hyperfabric,
  so the whole picture is reachable from the cuisine side. -/
  umamiTransport : (∀ a b, umamiFabric (umamiCompose a b) =
      fabricXor (umamiFabric a) (umamiFabric b)) ∧ Function.Surjective umamiFabric
  /-- `monster_moonshine`: the Monster mask carrier is the support of a
  section, and every mask is the support of a transported cuisine intensity. -/
  monsterMask : ∀ m : MaskSSP, supportMask (umamiFabric (maskIntensity m)) = m
  /-- `low_order_regular_fabric`: three of the five taste columns of the
  `3 · 5` grid carry `3 ^ 9 = 19683` sections. -/
  nineSheet : ∀ T : Finset TasteDimension, T.card = 3 →
    Fintype.card (Supported (tasteBlock T)) = 19683
  /-- `j_invariant_moonshine_anchor`: the supplied numerals are affine in that
  sheet count. -/
  jAnchor : AgdaMirror.Moonshine.jCoefficient = 10 * 19683 + 54 ∧
    AgdaMirror.Moonshine.repDim = 10 * 19683 + 53
  /-- `p_adic_metric` / `ultrametric_adelic_transport`: the mask carrier bears
  the Monster ultrametric, and projection onto a target is strictly
  contracting — pulled back here to cuisine safety fields. -/
  pAdicTransport : ∀ (target : MaskSSP) (x y : SafetyField), doubtMask x ≠ doubtMask y →
    dSSP (projectSSP target (doubtMask x)) (projectSSP target (doubtMask y)) < dSafety x y
  /-- `tlurey_triadic_nonary`: the nonary group `ℤ/3 × ℤ/3` acts faithfully on
  the hyperfabric — the base rotation of the `3 · 5` grid commuting with the
  `369` rotation of the fibre — and the base-invariant sections number
  `3 ^ 5 = 243`. -/
  nonary : (∀ F : Fabric, fabricPull (fabricRot F) = fabricRot (fabricPull F)) ∧
    (∀ i j i' j' : Fin 3, nonaryAct i j = nonaryAct i' j' → i = i' ∧ j = j') ∧
    Fintype.card BaseInvariant = 243
  /-- A base symmetry that *does* preserve the moonshine data: the three-cycle
  of the trivector primes commutes with the `369` fibre rotation and fixes the
  trivector mask. -/
  moonshineSymmetry :
    (∀ F : Fabric, pullBy moonshineRot (fabricRot F) = fabricRot (pullBy moonshineRot F)) ∧
      (fun p => trivectorMask (moonshineRot p)) = trivectorMask
  /-- Honesty clause: the `369` base rotation of the `3 · 5` grid is *not* a
  symmetry of the moonshine data.  It moves the trivector mask, and the mask
  product with it. -/
  baseRotationMovesMoonshine :
    maskProduct (maskPull trivectorMask) ≠ maskProduct trivectorMask
  /-- Honesty clause: the motif the cuisine record actually names is itself
  unrealised. -/
  sweetgrassUnrealised : realise motifSweetgrassBraidFabric = unrealised

/-- The canonical realisation: each field is a theorem already proved in this
library. -/
noncomputable def sweetgrassRealisation : SweetgrassRealisation where
  base369 := ⟨rfl, rfl⟩
  fifteenSSP := ⟨rfl, ⟨sspToneTaste⟩⟩
  hyperfabric := card_fabric
  knotWeave := knotWeaveFabric
  dialecticAction := dialectic_stage_is_seasoning
  umamiTransport := ⟨umamiFabric_compose, umamiFabric_surjective⟩
  monsterMask := supportMask_umamiFabric_maskIntensity
  nineSheet := fun T hT => card_taste_sheet T hT
  jAnchor := ⟨by decide, by decide⟩
  pAdicTransport := fun target _ _ hxy => safety_projection_contractive target hxy
  nonary := ⟨fabricPull_fabricRot, nonary_faithful, card_baseInvariant⟩
  moonshineSymmetry := ⟨moonshine_preserving_symmetry.1, moonshine_preserving_symmetry.2.2.1⟩
  baseRotationMovesMoonshine := base_rotation_moves_moonshine.2.2
  sweetgrassUnrealised := rfl

/-- **The Sweetgrass carrier spine is realised.**  Thirteen of its thirty-five
motifs name types this repository defines; those types are the ternary fibre,
the fifteen-prime base, the hyperfabric of sections over it, the Monster mask
lattice with its ultrametric, the depth-nine sheet of the `3 · 5` grid and the
graded moonshine numeral; and they are tied to one another, and to the cuisine
umami transport, by the theorems collected in `SweetgrassRealisation`.  The
Sweetgrass motif itself is not among them. -/
theorem sweetgrass_spine_realised :
    ∃ R : SweetgrassRealisation, R.knotWeave = knotWeaveFabric ∧
      realisedMotifs.length = 13 ∧
      realise motifSweetgrassBraidFabric = unrealised :=
  ⟨sweetgrassRealisation, rfl, rfl, rfl⟩

end Cuisine.SweetgrassSpine

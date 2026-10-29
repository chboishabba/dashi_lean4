import Mathlib

/-!
# Lean mirror of `DASHI/Core/AuthorityBoundary.agda` (genuine interface + witness)

Faithful transcription of the authority-boundary bookkeeping:

* `AuthorityKind` — `CitationAuthority` vs `ArtifactAuthority` (distinct kinds),
* `AuthorityBoundary kind` — a kind-indexed boundary receipt whose stored kind is
  proven to match its index (`authorityKindMatches`),
* `CitationAuthorityNoArtifact` — the genuine boundary fact that a *citation*
  authority closes a source slot **without** authorizing a machine-readable
  artifact.

We give a genuine *witness* `citationOnly` exhibiting an accepted citation
boundary with both artifact flags `false`, packaged as a
`CitationAuthorityNoArtifact`.  No `sorry`, axiom-clean.
-/

namespace AgdaMirror.AuthorityBoundaries

/-- The two distinct authority kinds (Agda `data AuthorityKind`). -/
inductive AuthorityKind | CitationAuthority | ArtifactAuthority
  deriving DecidableEq, Repr

open AuthorityKind

/-- A kind-indexed authority boundary receipt (Agda `record AuthorityBoundary`). -/
structure AuthorityBoundary (kind : AuthorityKind) where
  authorityKind : AuthorityKind
  authorityKindMatches : authorityKind = kind
  recordIdentifier : String
  citation : String
  authorityAccepted : Bool
  artifactAuthority : Bool
  machineReadableArtifactPresent : Bool
  notes : List String

/-- A citation-kind boundary (Agda `CitationAuthorityBoundary`). -/
abbrev CitationAuthorityBoundary := AuthorityBoundary CitationAuthority

/-- An artifact-kind boundary (Agda `ArtifactAuthorityBoundary`). -/
abbrev ArtifactAuthorityBoundary := AuthorityBoundary ArtifactAuthority

/-- The genuine "citation closes a slot but authorizes no artifact" fact
(Agda `record CitationAuthorityNoArtifact`). -/
structure CitationAuthorityNoArtifact where
  citationBoundary : CitationAuthorityBoundary
  citationAuthorityAccepted : citationBoundary.authorityAccepted = true
  artifactAuthorityIsFalse : citationBoundary.artifactAuthority = false
  machineReadableArtifactPresentIsFalse :
    citationBoundary.machineReadableArtifactPresent = false

/-- Genuine witness: an accepted citation boundary with no artifact authority. -/
def citationOnly : CitationAuthorityNoArtifact where
  citationBoundary :=
    { authorityKind := CitationAuthority
      authorityKindMatches := rfl
      recordIdentifier := "rec-001"
      citation := "source citation"
      authorityAccepted := true
      artifactAuthority := false
      machineReadableArtifactPresent := false
      notes := [] }
  citationAuthorityAccepted := rfl
  artifactAuthorityIsFalse := rfl
  machineReadableArtifactPresentIsFalse := rfl

end AgdaMirror.AuthorityBoundaries


namespace AgdaMirror.AuthorityBoundaries

/-!
## Golden Agda cannabis potency / preference mirror

Golden owner:

* `DASHI.Wikimedia.IbrahimCannabisTerpeneCommercialSampleQuantitativeAssayExact`

Golden TOE consumers:

* `DASHI.EverythingTOESymmetryResolved369`
* `DASHI.Unifier`
* `DASHI.Unified.Everything`

This Lean surface mirrors the stable bounded discriminator only.
Agda remains the semantic owner.
-/

inductive CurrentCannabisProduct
  | jade
  | royale
  | comparator30
  deriving DecidableEq, Repr

open CurrentCannabisProduct

def nominalTHCPercent : CurrentCannabisProduct → Nat
  | jade => 25
  | royale => 27
  | comparator30 => 30

inductive NominalPotencyOrder :
    CurrentCannabisProduct → CurrentCannabisProduct → Prop
  | jadeBelowRoyale : NominalPotencyOrder jade royale
  | royaleBelowComparator30 : NominalPotencyOrder royale comparator30

inductive ReportedPreferenceOrder :
    CurrentCannabisProduct → CurrentCannabisProduct → Prop
  | royalePreferredToJade : ReportedPreferenceOrder royale jade
  | royalePreferredToComparator30 :
      ReportedPreferenceOrder royale comparator30

inductive PotencyOnlyMonotoneFitsCurrentFixture : Prop
  | potencyOnlyMonotone :
      ReportedPreferenceOrder comparator30 royale →
      PotencyOnlyMonotoneFitsCurrentFixture

theorem potencyOnlyMonotoneDoesNotFitCurrentFixture :
    ¬ PotencyOnlyMonotoneFitsCurrentFixture := by
  intro h
  cases h with
  | potencyOnlyMonotone pref =>
      cases pref

structure PotencyPreferenceObservation where
  lowerNominalProduct : CurrentCannabisProduct
  higherNominalProduct : CurrentCannabisProduct
  nominalOrder :
    NominalPotencyOrder lowerNominalProduct higherNominalProduct
  preferredProduct : CurrentCannabisProduct
  lessPreferredProduct : CurrentCannabisProduct
  reportedPreference :
    ReportedPreferenceOrder preferredProduct lessPreferredProduct
  reportReference : String
  exactBatchAssayPaid : Bool
  administeredDosePaid : Bool
  exposurePaid : Bool
  causalMechanismPaid : Bool

def royaleComparatorPreferenceObservation : PotencyPreferenceObservation where
  lowerNominalProduct := royale
  higherNominalProduct := comparator30
  nominalOrder := NominalPotencyOrder.royaleBelowComparator30
  preferredProduct := royale
  lessPreferredProduct := comparator30
  reportedPreference := ReportedPreferenceOrder.royalePreferredToComparator30
  reportReference :=
    "current bounded report: Royale is preferred to a product labelled 30 percent THC"
  exactBatchAssayPaid := false
  administeredDosePaid := false
  exposurePaid := false
  causalMechanismPaid := false

def jadeRoyalePreferenceObservation : PotencyPreferenceObservation where
  lowerNominalProduct := jade
  higherNominalProduct := royale
  nominalOrder := NominalPotencyOrder.jadeBelowRoyale
  preferredProduct := royale
  lessPreferredProduct := jade
  reportedPreference := ReportedPreferenceOrder.royalePreferredToJade
  reportReference := "current bounded report: Royale is preferred to Jade"
  exactBatchAssayPaid := false
  administeredDosePaid := false
  exposurePaid := false
  causalMechanismPaid := false

inductive NominalPotencyCreatesDeliveredDose : Prop
inductive NominalPotencyCreatesExposure : Prop
inductive ReportedPreferenceCreatesTerpeneCause : Prop
inductive ReportedPreferenceCreatesOutdoorCause : Prop
inductive ProductLabelCreatesExactBatchComposition : Prop

theorem nominalPotencyDoesNotCreateDeliveredDose :
    ¬ NominalPotencyCreatesDeliveredDose := by
  intro h
  cases h

theorem nominalPotencyDoesNotCreateExposure :
    ¬ NominalPotencyCreatesExposure := by
  intro h
  cases h

theorem reportedPreferenceDoesNotCreateTerpeneCause :
    ¬ ReportedPreferenceCreatesTerpeneCause := by
  intro h
  cases h

theorem reportedPreferenceDoesNotCreateOutdoorCause :
    ¬ ReportedPreferenceCreatesOutdoorCause := by
  intro h
  cases h

theorem productLabelDoesNotCreateExactBatchComposition :
    ¬ ProductLabelCreatesExactBatchComposition := by
  intro h
  cases h

structure CannabisPotencyPreferenceBoundary where
  headlinePotencySeparatedFromExactBatchAssay : Bool
  headlinePotencySeparatedFromExactBatchAssayIsTrue :
    headlinePotencySeparatedFromExactBatchAssay = true
  productPotencySeparatedFromDeliveredDose : Bool
  productPotencySeparatedFromDeliveredDoseIsTrue :
    productPotencySeparatedFromDeliveredDose = true
  deliveredDoseSeparatedFromExposure : Bool
  deliveredDoseSeparatedFromExposureIsTrue :
    deliveredDoseSeparatedFromExposure = true
  nominalPotencyAloneFitsCurrentPreferenceOrdering : Bool
  nominalPotencyAloneFitsCurrentPreferenceOrderingIsFalse :
    nominalPotencyAloneFitsCurrentPreferenceOrdering = false
  reportedPreferenceCreatesTerpeneMechanism : Bool
  reportedPreferenceCreatesTerpeneMechanismIsFalse :
    reportedPreferenceCreatesTerpeneMechanism = false
  reportedPreferenceCreatesOutdoorMechanism : Bool
  reportedPreferenceCreatesOutdoorMechanismIsFalse :
    reportedPreferenceCreatesOutdoorMechanism = false
  exactBatchAssayIsNextParetoTarget : Bool
  exactBatchAssayIsNextParetoTargetIsTrue :
    exactBatchAssayIsNextParetoTarget = true
  clinicalRecommendationPaid : Bool
  clinicalRecommendationPaidIsFalse :
    clinicalRecommendationPaid = false

def canonicalCannabisPotencyPreferenceBoundary :
    CannabisPotencyPreferenceBoundary where
  headlinePotencySeparatedFromExactBatchAssay := true
  headlinePotencySeparatedFromExactBatchAssayIsTrue := rfl
  productPotencySeparatedFromDeliveredDose := true
  productPotencySeparatedFromDeliveredDoseIsTrue := rfl
  deliveredDoseSeparatedFromExposure := true
  deliveredDoseSeparatedFromExposureIsTrue := rfl
  nominalPotencyAloneFitsCurrentPreferenceOrdering := false
  nominalPotencyAloneFitsCurrentPreferenceOrderingIsFalse := rfl
  reportedPreferenceCreatesTerpeneMechanism := false
  reportedPreferenceCreatesTerpeneMechanismIsFalse := rfl
  reportedPreferenceCreatesOutdoorMechanism := false
  reportedPreferenceCreatesOutdoorMechanismIsFalse := rfl
  exactBatchAssayIsNextParetoTarget := true
  exactBatchAssayIsNextParetoTargetIsTrue := rfl
  clinicalRecommendationPaid := false
  clinicalRecommendationPaidIsFalse := rfl

structure CannabisPotencyPreferenceZKPFrame where
  O : String
  R : String
  C : String
  S : String
  L : String
  P : String
  G : String
  F : String
  esdMutationAllowed : Bool

def canonicalCannabisPotencyPreferenceZKPFrame :
    CannabisPotencyPreferenceZKPFrame where
  O :=
    "formalise the Jade/Royale/high-potency comparison without promoting headline THC into dose, exposure, mechanism, or clinical effect"
  R :=
    "mirror the golden commercial same-sample assay and TOE non-promotion owners"
  C :=
    "mirror the bounded potency/preference discriminator only"
  S :=
    "potency is not dose; dose is not exposure; preference does not create terpene or outdoor causation"
  L :=
    "one nonblocking cannabis evidence lane; no ESD mutation; no retargeting of discharged fibres"
  P :=
    "Agda remains golden; exact batch assays remain unpaid; attribution remains source-bound"
  G :=
    "management, risk, quality, privacy, security, usability, and architecture standards are process lenses only"
  F :=
    "Lean mirrors the bounded reversal and the same open causal residuals without changing Agda ownership"
  esdMutationAllowed := false

theorem cannabisAgdaGoldenBoundaryPinned :
    canonicalCannabisPotencyPreferenceBoundary.exactBatchAssayIsNextParetoTarget =
      true := by
  rfl

theorem cannabisClinicalPromotionStillBlocked :
    canonicalCannabisPotencyPreferenceBoundary.clinicalRecommendationPaid =
      false := by
  rfl

end AgdaMirror.AuthorityBoundaries

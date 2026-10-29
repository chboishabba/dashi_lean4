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


/-!
## Safe-and-just paper-chain mirror

This section mirrors the finite non-promotion surface exposed by the golden Agda
owners for the O'Neill 2018 -> Fanning 2022 -> Kallis 2025 chain.

The Agda owners remain authoritative.  This Lean section is an independent
finite consistency mirror.  It does not ingest the empirical workbooks.  It
does not promote a review statement, forecast, count summary, or GDP association
into causal or policy authority.
-/

namespace AgdaMirror.SafeJustPaperChain

def boolToNat : Bool → Nat
  | false => 0
  | true => 1

structure BioShadow where
  co2Over : Bool
  phosphorusOver : Bool
  deriving DecidableEq, Repr

def bioCount (p : BioShadow) : Nat :=
  boolToNat p.co2Over + boolToNat p.phosphorusOver

def bioA : BioShadow := ⟨true, false⟩
def bioB : BioShadow := ⟨false, true⟩

theorem sameBioCount : bioCount bioA = bioCount bioB := rfl

theorem sameBioCountDoesNotRecoverCO2 :
    bioA.co2Over ≠ bioB.co2Over := by
  decide

abbrev UniversalSafeJustImpossibilityPromotion : Prop := False

theorem observedSampleDoesNotCreateUniversalImpossibility :
    ¬ UniversalSafeJustImpossibilityPromotion := by
  intro h
  cases h

abbrev IdentifiedProvisioningTreatmentEffectPromotion : Prop := False

theorem observedProvisioningGapDoesNotIdentifyTreatmentEffect :
    ¬ IdentifiedProvisioningTreatmentEffectPromotion := by
  intro h
  cases h

abbrev BAUProjectionAsObservedFuturePromotion : Prop := False

theorem bauProjectionDoesNotBecomeObservedFuture :
    ¬ BAUProjectionAsObservedFuturePromotion := by
  intro h
  cases h

abbrev GDP15000CausalThresholdPromotion : Prop := False

theorem gdp15000PatternDoesNotBecomeCausalThreshold :
    ¬ GDP15000CausalThresholdPromotion := by
  intro h
  cases h

structure PaperChainBoundary where
  agdaIsGoldenFormalAuthority : Bool
  agdaIsGoldenFormalAuthorityIsTrue :
    agdaIsGoldenFormalAuthority = true
  countProjectionRecoversIndicatorCoordinates : Bool
  countProjectionRecoversIndicatorCoordinatesIsFalse :
    countProjectionRecoversIndicatorCoordinates = false
  observedCountryResultCreatesUniversalImpossibility : Bool
  observedCountryResultCreatesUniversalImpossibilityIsFalse :
    observedCountryResultCreatesUniversalImpossibility = false
  resourceQuantityAloneDeterminesNeedOutcome : Bool
  resourceQuantityAloneDeterminesNeedOutcomeIsFalse :
    resourceQuantityAloneDeterminesNeedOutcome = false
  observedProvisioningGapIdentifiesCausalTreatmentEffect : Bool
  observedProvisioningGapIdentifiesCausalTreatmentEffectIsFalse :
    observedProvisioningGapIdentifiesCausalTreatmentEffect = false
  fanningAggregateExtentRecoversIndicatorVector : Bool
  fanningAggregateExtentRecoversIndicatorVectorIsFalse :
    fanningAggregateExtentRecoversIndicatorVector = false
  fanningBAUProjectionIsObservedFutureOutcome : Bool
  fanningBAUProjectionIsObservedFutureOutcomeIsFalse :
    fanningBAUProjectionIsObservedFutureOutcome = false
  gdp15000PatternIsUniversalCausalThreshold : Bool
  gdp15000PatternIsUniversalCausalThresholdIsFalse :
    gdp15000PatternIsUniversalCausalThreshold = false
  descriptiveEvidenceCreatesPolicyMandate : Bool
  descriptiveEvidenceCreatesPolicyMandateIsFalse :
    descriptiveEvidenceCreatesPolicyMandate = false
  leanMirrorCreatesAgdaAuthority : Bool
  leanMirrorCreatesAgdaAuthorityIsFalse :
    leanMirrorCreatesAgdaAuthority = false

def canonicalPaperChainBoundary : PaperChainBoundary where
  agdaIsGoldenFormalAuthority := true
  agdaIsGoldenFormalAuthorityIsTrue := rfl
  countProjectionRecoversIndicatorCoordinates := false
  countProjectionRecoversIndicatorCoordinatesIsFalse := rfl
  observedCountryResultCreatesUniversalImpossibility := false
  observedCountryResultCreatesUniversalImpossibilityIsFalse := rfl
  resourceQuantityAloneDeterminesNeedOutcome := false
  resourceQuantityAloneDeterminesNeedOutcomeIsFalse := rfl
  observedProvisioningGapIdentifiesCausalTreatmentEffect := false
  observedProvisioningGapIdentifiesCausalTreatmentEffectIsFalse := rfl
  fanningAggregateExtentRecoversIndicatorVector := false
  fanningAggregateExtentRecoversIndicatorVectorIsFalse := rfl
  fanningBAUProjectionIsObservedFutureOutcome := false
  fanningBAUProjectionIsObservedFutureOutcomeIsFalse := rfl
  gdp15000PatternIsUniversalCausalThreshold := false
  gdp15000PatternIsUniversalCausalThresholdIsFalse := rfl
  descriptiveEvidenceCreatesPolicyMandate := false
  descriptiveEvidenceCreatesPolicyMandateIsFalse := rfl
  leanMirrorCreatesAgdaAuthority := false
  leanMirrorCreatesAgdaAuthorityIsFalse := rfl

theorem leanMirrorDoesNotCreateAgdaAuthority :
    canonicalPaperChainBoundary.leanMirrorCreatesAgdaAuthority = false :=
  rfl

end AgdaMirror.SafeJustPaperChain

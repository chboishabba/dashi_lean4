import Integration.BishopRound11MachinBindingManifest
import Integration.BishopRound11MachinCanonicalBinding
import Integration.MoonshineEisensteinRound11RouteB

/-!
# Typed recognition boundary for the Round11/Machin route-B replay

Cross-pollination rule used here:

* source provenance is not formal reconstruction;
* formal reconstruction is not cross-module inference;
* manifest recognition is not cross-prover proof transport;
* an imported source binding must preserve the actual convergence structure,
  not merely agree on names, hashes, or cardinalities.

The mathematical target is already unique up to the Bishop setoid. Therefore a
future genuine Agda replay/importer only needs to provide an inhabitant of the
exact `Round11MachinSourceBinding` fields. Existing uniqueness then forces that
binding into the canonical Lean equivalence class and all route-B transport
theorems compile automatically.

This file deliberately does not manufacture such a replay witness.
-/

namespace Integration.BishopRound11MachinRecognition

open Integration.BishopRound11MachinBindingManifest
open Integration.BishopRound11MachinSourceBinding
open Integration.BishopRound11MachinCanonicalBinding
open Integration.MoonshineEisensteinRound11RouteB

noncomputable section

/-- Typed origin tags. They prevent a source citation or manifest match from
being silently promoted into a cross-prover proof claim. -/
inductive ClaimOrigin
  | vendoredExternalDependency
  | agdaFormalReconstruction
  | leanFormalReconstruction
  | repositoryCrossModuleInference
  | crossProverReplayObservation
  | repositoryNewExtension
  deriving Repr, DecidableEq

def bishopRepresentationOrigin : ClaimOrigin :=
  .vendoredExternalDependency

def round11MachinSourceReceiptOrigin : ClaimOrigin :=
  .agdaFormalReconstruction

def canonicalLeanBindingOrigin : ClaimOrigin :=
  .leanFormalReconstruction

def sourceToTargetBindingTableOrigin : ClaimOrigin :=
  .repositoryCrossModuleInference

def genuineReplayObservationOrigin : ClaimOrigin :=
  .crossProverReplayObservation

/-- What the current manifest/replay machinery can establish without claiming
that an Agda proof object has been imported into Lean. -/
structure ManifestRecognition where
  agdaCommitPinned : Bool
  bishopSubmodulePinned : Bool
  loadBearingBlobsMatched : Bool
  sourceDeclarationsObserved : Bool
  theoremBindingTableKernelMatched : Bool
  canonicalLeanBindingInhabitedIndependently : Bool
  everyAdmissibleLeanBindingSetoidEquivalent : Bool

  agdaElaborationObserved : Bool
  sourceProofObjectsImported : Bool
  importedBindingInhabitedFromSourceTerms : Bool

def currentManifestRecognition : ManifestRecognition where
  agdaCommitPinned := true
  bishopSubmodulePinned := true
  loadBearingBlobsMatched := true
  sourceDeclarationsObserved := true
  theoremBindingTableKernelMatched := true
  canonicalLeanBindingInhabitedIndependently := true
  everyAdmissibleLeanBindingSetoidEquivalent := true

  agdaElaborationObserved := false
  sourceProofObjectsImported := false
  importedBindingInhabitedFromSourceTerms := false

theorem current_manifest_is_not_cross_prover_replay :
    currentManifestRecognition.importedBindingInhabitedFromSourceTerms = false := rfl

/-- A future importer chooses its own concrete proposition saying what counts
as a genuine replay observation. This module never invents that proposition's
inhabitant. -/
structure CrossProverBindingRecognition
    (ReplayObserved : Round11MachinSourceBinding Arithmetic → Prop) where
  binding : Round11MachinSourceBinding Arithmetic
  replayObserved : ReplayObserved binding

/-- Recognition compiler: once a genuine imported binding exists, no further
same-object theorem is required. The existing convergence-uniqueness theorem
forces it into the canonical Bishop-setoid class. -/
def recognize
    {ReplayObserved : Round11MachinSourceBinding Arithmetic → Prop}
    (B : Round11MachinSourceBinding Arithmetic)
    (hReplay : ReplayObserved B) :
    CrossProverBindingRecognition ReplayObserved where
  binding := B
  replayObserved := hReplay

def canonicalAgreement
    {ReplayObserved : Round11MachinSourceBinding Arithmetic → Prop}
    (R : CrossProverBindingRecognition ReplayObserved) :
    BindingSetoidAgreement R.binding :=
  everyBinding_agrees_setoid R.binding

/-- Structural preservation theorem for the recognition map. This is stronger
than name/hash agreement: each imported convergence-selected value is forced
to the canonical value up to Bishop equivalence. -/
theorem recognized_exp_preserves_setoid_class
    {ReplayObserved : Round11MachinSourceBinding Arithmetic → Prop}
    (R : CrossProverBindingRecognition ReplayObserved)
    (x : Integration.BishopVendoredRealEvaluation.RegularRatReal) :
    Integration.BishopVendoredRealEvaluation.Equiv
      (R.binding.expB x)
      (canonicalBinding.expB x) :=
  (canonicalAgreement R).exp x

theorem recognized_sin_preserves_setoid_class
    {ReplayObserved : Round11MachinSourceBinding Arithmetic → Prop}
    (R : CrossProverBindingRecognition ReplayObserved)
    (x : Integration.BishopVendoredRealEvaluation.RegularRatReal) :
    Integration.BishopVendoredRealEvaluation.Equiv
      (R.binding.sinB x)
      (canonicalBinding.sinB x) :=
  (canonicalAgreement R).sin x

theorem recognized_cos_preserves_setoid_class
    {ReplayObserved : Round11MachinSourceBinding Arithmetic → Prop}
    (R : CrossProverBindingRecognition ReplayObserved)
    (x : Integration.BishopVendoredRealEvaluation.RegularRatReal) :
    Integration.BishopVendoredRealEvaluation.Equiv
      (R.binding.cosB x)
      (canonicalBinding.cosB x) :=
  (canonicalAgreement R).cos x

theorem recognized_atan_fifth_preserves_setoid_class
    {ReplayObserved : Round11MachinSourceBinding Arithmetic → Prop}
    (R : CrossProverBindingRecognition ReplayObserved) :
    Integration.BishopVendoredRealEvaluation.Equiv
      R.binding.atanOneFifth
      canonicalBinding.atanOneFifth :=
  (canonicalAgreement R).atanOneFifth

theorem recognized_atan_239_preserves_setoid_class
    {ReplayObserved : Round11MachinSourceBinding Arithmetic → Prop}
    (R : CrossProverBindingRecognition ReplayObserved) :
    Integration.BishopVendoredRealEvaluation.Equiv
      R.binding.atanOneTwoHundredThirtyNinth
      canonicalBinding.atanOneTwoHundredThirtyNinth :=
  (canonicalAgreement R).atan239

/-- A genuinely recognized source binding immediately produces the already
proved primitive real extraction. -/
def recognizedPrimitiveExtraction
    {ReplayObserved : Round11MachinSourceBinding Arithmetic → Prop}
    (R : CrossProverBindingRecognition ReplayObserved) :=
  Integration.BishopRound11MachinSourceBinding.primitiveExtractionDirect
    Arithmetic R.binding

/-- Likewise the complete source q/E4/E6/Delta compiler is available for the
recognized binding without any new analytic hypothesis. -/
theorem recognized_mapped_normalized_delta_tendsto
    {ReplayObserved : Round11MachinSourceBinding Arithmetic → Prop}
    (R : CrossProverBindingRecognition ReplayObserved)
    (τs : RouteComplex Arithmetic R.binding)
    (τ : ℍ)
    (hτ : mapRouteComplex τs = (τ : ℂ)) :
    Filter.Tendsto
      (fun N => mapRouteComplex (sourceNormalizedDelta N τs))
      Filter.atTop
      (nhds (Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaLimit τ)) :=
  mapped_sourceNormalizedDelta_tendsto τs τ hτ

structure RecognitionBoundary where
  typedClaimOriginsOwned : Bool
  manifestRecognitionSeparatedFromReplay : Bool
  recognitionCompilerOwned : Bool
  importedBindingForcedToCanonicalSetoidClass : Bool
  recognizedBindingBuildsPrimitiveExtraction : Bool
  recognizedBindingBuildsNormalizedDeltaLimit : Bool
  actualCrossProverReplayObserved : Bool

def recognitionBoundary : RecognitionBoundary where
  typedClaimOriginsOwned := true
  manifestRecognitionSeparatedFromReplay := true
  recognitionCompilerOwned := true
  importedBindingForcedToCanonicalSetoidClass := true
  recognizedBindingBuildsPrimitiveExtraction := true
  recognizedBindingBuildsNormalizedDeltaLimit := true
  actualCrossProverReplayObserved := false

end

end Integration.BishopRound11MachinRecognition

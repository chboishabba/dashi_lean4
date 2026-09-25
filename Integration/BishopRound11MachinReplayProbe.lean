import Integration.BishopRound11MachinBindingManifest
import Integration.BishopRound11MachinCanonicalBinding
import Integration.MoonshineEisensteinRound11CanonicalRouteB
import Integration.MoonshineDeltaFinalMinCut

/-!
# Focused Round11/Machin route-B replay probe

This module is intentionally small enough to elaborate in a focused CI job.

It checks that:
* the content-addressed Agda/Lean manifest is present;
* the canonical Bishop completion binding is inhabited;
* the hypothesis-free source q/E4/E6/Delta route is available;
* the eta^24 same-object theorem is available at the pinned Mathlib version;
* the inverse-conjugation and sixfold-phase targets are available.

This is a Lean kernel probe of the checked-in route-B development.  It is not,
by itself, evidence that the named Agda source declarations were generated into
Lean; that provenance evidence is supplied separately by the manifest verifier.
-/

namespace Integration.BishopRound11MachinReplayProbe

open Integration.BishopRound11MachinBindingManifest
open Integration.BishopRound11MachinCanonicalBinding
open Integration.MoonshineEisensteinRound11CanonicalRouteB
open Integration.MoonshineDeltaFinalMinCut

/-- The currently pinned Agda source blob IDs are definitionally the ones the
route-B manifest declares. -/
theorem source_manifest_literal_receipt :
    agdaSourceCommit =
      "c72ea464663a02333319f2254967c94bd188f5f5" ∧
    sourceInstanceBlob.gitBlob =
      "ec132e001eeb7836078561e88fe2b3f54438facb" ∧
    machinConstructionBlob.gitBlob =
      "be11dee1db4eb6856346267134dcd85fed96fc2a" ∧
    exponentialConvergenceBlob.gitBlob =
      "b62d767e74c6473e31bdf86458d93445656f6978" ∧
    trigConvergenceBlob.gitBlob =
      "75b8b72ea4e240bfde706272beb5ff5e5fba9af5" ∧
    setoidComplexBlob.gitBlob =
      "739af368ced4b730225db4177529b281f4e8c493" ∧
    finiteQSeriesBlob.gitBlob =
      "4787feafbd9630dc439556543c42c6b75bf7fdbd" ∧
    extractionBlob.gitBlob =
      "baee86e7085c9193227142eb9713df9d2e4a546e" := by
  native_decide

/-- The manifest names the concrete verification artifacts used by this PR. -/
theorem verification_artifacts_literal_receipt :
    replayVerifierScript =
      "scripts/verify_round11_machin_route_b.py" ∧
    generatedReplayCertificatePath =
      "Generated/BishopRound11MachinReplayCertificate.lean" ∧
    focusedReplayProbeModule =
      "Integration/BishopRound11MachinReplayProbe.lean" ∧
    focusedAxiomAuditModule =
      "Integration/AxiomAuditMoonshineRound11RouteB.lean" ∧
    focusedReplayWorkflow =
      ".github/workflows/moonshine-round11-route-b.yml" := by
  native_decide

/-- Mathematical inhabitance of the exact Lean-facing Round11/Machin binding
shape is no longer conditional. -/
theorem canonical_binding_inhabited :
    Nonempty
      (Integration.BishopRound11MachinSourceBinding.Round11MachinSourceBinding
        Arithmetic) :=
  ⟨canonicalBinding⟩

/-- The canonical source route reaches the normalized classical Delta target. -/
theorem canonical_route_delta_same_object :
    ∀ τ : ℍ,
      Integration.MoonshineEta24Pinned.eta24 τ =
        Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaLimit τ :=
  eta24_eq_canonical_route_delta

/-- The final sixfold phase theorem is hypothesis-free apart from the geometric
unit-circle condition itself. -/
theorem canonical_sixfold_phase_available
    (τ : ℍ)
    (hunit : Complex.normSq (τ : ℂ) = 1) :
    ∃ k : ℤ,
      Complex.arg
          (Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaLimit τ)
        + 6 * Complex.arg (τ : ℂ)
      =
        (k : ℝ) * Real.pi :=
  normalizedDelta_sixfold_phase_canonical τ hunit

structure ReplayProbeBoundary where
  contentAddressedManifestKernelVisible : Bool
  verificationArtifactManifestKernelVisible : Bool
  canonicalBindingKernelVisible : Bool
  canonicalRouteDeltaKernelVisible : Bool
  eta24SameObjectKernelVisible : Bool
  sixfoldPhaseKernelVisible : Bool
  generatedAgdaProvenanceReplayObserved : Bool

def replayProbeBoundary : ReplayProbeBoundary where
  contentAddressedManifestKernelVisible := true
  verificationArtifactManifestKernelVisible := true
  canonicalBindingKernelVisible := true
  canonicalRouteDeltaKernelVisible := true
  eta24SameObjectKernelVisible := true
  sixfoldPhaseKernelVisible := true
  generatedAgdaProvenanceReplayObserved := false

end Integration.BishopRound11MachinReplayProbe

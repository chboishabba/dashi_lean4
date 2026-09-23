import Integration.MoonshineEta24SixfoldPhase
import Integration.MoonshineEisensteinWeld

/-!
# Final Delta same-object min-cut at the pinned Mathlib dependency

All standard analysis, Bishop semantics, Eisenstein convergence, modular
reflection, and phase readout are already compiler-owned on this branch.

The remaining mathematical seam between the two independently constructed
classical Delta targets is exactly the pointwise proposition

  eta(tau)^24 = (E4(tau)^3 - E6(tau)^2) / 1728.

This file makes that proposition the single load-bearing input and compiles all
remaining consequences from it.  It does not prove the proposition itself.

At Mathlib v4.28.0 the later level-one dimension/discriminant package that proves
this identity is absent, so keeping this min-cut explicit prevents downstream
results from being misreported as separate open leaves.
-/

namespace Integration.MoonshineDeltaFinalMinCut

open Complex Real
open UpperHalfPlane hiding I
open scoped Real Topology

noncomputable section

namespace Target
open Integration.MoonshineEisensteinAgdaTarget
end Target

namespace Eta
open Integration.MoonshineEta24Pinned
end Eta

namespace Phase
open Integration.MoonshineEta24SixfoldPhase
end Phase

/-- The sole remaining classical same-object proposition at the current pin. -/
def Eta24NormalizedDeltaSameObject : Prop :=
  ∀ τ : ℍ,
    Eta.eta24 τ = Target.normalizedDeltaLimit τ

/-- Symmetric orientation of the same min-cut. -/
theorem normalizedDelta_eq_eta24
    (W : Eta24NormalizedDeltaSameObject)
    (τ : ℍ) :
    Target.normalizedDeltaLimit τ = Eta.eta24 τ :=
  (W τ).symm

/-- The normalized E4/E6 Delta target becomes nonzero immediately from the
same-object weld and eta nonvanishing. -/
theorem normalizedDelta_ne_zero
    (W : Eta24NormalizedDeltaSameObject)
    (τ : ℍ) :
    Target.normalizedDeltaLimit τ ≠ 0 := by
  rw [← W τ]
  exact pow_ne_zero 24 (ModularForm.eta_ne_zero τ.2)

/-- The conditional normalized-Delta phase compiler becomes unconditional once
the sole same-object weld is supplied. -/
theorem normalizedDelta_sixfold_phase
    (W : Eta24NormalizedDeltaSameObject)
    (τ : ℍ)
    (hunit : Complex.normSq (τ : ℂ) = 1) :
    ∃ k : ℤ,
      Complex.arg (Target.normalizedDeltaLimit τ)
        + 6 * Complex.arg (τ : ℂ)
      =
        (k : ℝ) * Real.pi :=
  Phase.normalizedDelta_sixfold_phase_of_ne
    τ hunit (normalizedDelta_ne_zero W τ)

/-- Equivalent modulo-pi presentation for normalized E4/E6 Delta. -/
theorem normalizedDelta_arg_congruent_neg_six
    (W : Eta24NormalizedDeltaSameObject)
    (τ : ℍ)
    (hunit : Complex.normSq (τ : ℂ) = 1) :
    ∃ k : ℤ,
      Complex.arg (Target.normalizedDeltaLimit τ)
      =
        -6 * Complex.arg (τ : ℂ) +
          (k : ℝ) * Real.pi :=
  Phase.normalizedDelta_arg_congruent_neg_six_of_ne
    τ hunit (normalizedDelta_ne_zero W τ)

/-- The two independently proved inverse-conjugation owners agree pointwise
after the same-object weld. -/
theorem inverseConjugation_targets_same
    (W : Eta24NormalizedDeltaSameObject)
    (τ : ℍ) :
    Eta.eta24 (ModularGroup.S • Target.negConj τ) =
      Target.normalizedDeltaLimit (ModularGroup.S • Target.negConj τ) := by
  exact W _

/-- The two fixed-locus value identities are now statements about one and the
same value, rather than merely parallel theorems. -/
theorem unitCircle_values_same
    (W : Eta24NormalizedDeltaSameObject)
    (τ : ℍ)
    (_hunit : Complex.normSq (τ : ℂ) = 1) :
    Eta.eta24 τ = Target.normalizedDeltaLimit τ :=
  W τ

/-- Package the min-cut as the existing typed Delta weld. -/
def extractedNormalizedDeltaSurface :
    Integration.MoonshineEisensteinWeld.ExtractedDeltaSurface where
  delta := Target.normalizedDeltaLimit

def eta24WeldOfMinCut
    (W : Eta24NormalizedDeltaSameObject) :
    Integration.MoonshineEisensteinWeld.DeltaEta24SameObjectWeld
      extractedNormalizedDeltaSurface where
  delta_same τ := normalizedDelta_eq_eta24 W τ

/-- Conversely, the existing typed eta weld on the canonical normalized target
is exactly the min-cut proposition. -/
theorem minCutOfEta24Weld
    (W :
      Integration.MoonshineEisensteinWeld.DeltaEta24SameObjectWeld
        extractedNormalizedDeltaSurface) :
    Eta24NormalizedDeltaSameObject := by
  intro τ
  exact (W.delta_same τ).symm

/-- Hence the final proposition is equivalent to inhabiting the typed eta24 weld
on the canonical normalized E4/E6 target. -/
theorem minCut_iff_typedWeld :
    Eta24NormalizedDeltaSameObject ↔
      Nonempty
        (Integration.MoonshineEisensteinWeld.DeltaEta24SameObjectWeld
          extractedNormalizedDeltaSurface) := by
  constructor
  · intro W
    exact ⟨eta24WeldOfMinCut W⟩
  · rintro ⟨W⟩
    exact minCutOfEta24Weld W

structure FinalDeltaMinCutBoundary where
  soleClassicalSameObjectInputIsEta24NormalizedDelta : Bool
  normalizedDeltaNonvanishingCompilerOwned : Bool
  unconditionalNormalizedDeltaSixfoldCompilerOwned : Bool
  normalizedDeltaArgCongruenceCompilerOwned : Bool
  parallelReflectionOwnersCollapseAfterWeld : Bool
  typedEta24WeldEquivalentToMinCut : Bool

  eta24NormalizedDeltaSameObjectProvedAtPinnedMathlib : Bool
  dependencyBumpUsed : Bool

def finalDeltaMinCutBoundary : FinalDeltaMinCutBoundary where
  soleClassicalSameObjectInputIsEta24NormalizedDelta := true
  normalizedDeltaNonvanishingCompilerOwned := true
  unconditionalNormalizedDeltaSixfoldCompilerOwned := true
  normalizedDeltaArgCongruenceCompilerOwned := true
  parallelReflectionOwnersCollapseAfterWeld := true
  typedEta24WeldEquivalentToMinCut := true

  eta24NormalizedDeltaSameObjectProvedAtPinnedMathlib := false
  dependencyBumpUsed := false

end

end Integration.MoonshineDeltaFinalMinCut

import Integration.MoonshineEisensteinAnalytic
import Integration.MoonshineEisensteinAgdaTarget
import Integration.PromotionDiscipline

/-!
# Typed Moonshine/Eisenstein same-object weld

The Mathlib-backed analytic bridge proves the standard q-disk and Eisenstein
facts on Lean's ordinary complex upper-half-plane carrier.  The Agda lane uses
its own constructed-real / concrete-complex representation.

This module does not identify those carriers by resemblance.  Instead it states
the exact pointwise identifications a future extraction / quotient / mirror
witness must provide.  Once those fields are inhabited, all standard analytic
facts transport by rewriting.

The Delta seam is deliberately separate: at Mathlib v4.28.0 we have eta and its
nonvanishing theorem, but not the later packaged theorem identifying
eta^24 with (E4^3-E6^2)/1728.
-/

namespace Integration.MoonshineEisensteinWeld

open Complex Real
open UpperHalfPlane hiding I
open ArithmeticFunction
open scoped Real Nat ArithmeticFunction.sigma

noncomputable section

namespace Analytic
open Integration.MoonshineEisensteinAnalytic
end Analytic

/-- An Agda-facing semantic surface after extraction into Lean.

No assertion is made that any current Agda object already inhabits this record;
it is simply the minimum function-level carrier needed to state the weld. -/
structure ExtractedEisensteinSurface where
  q : ℍ → ℂ
  e4 : ℍ → ℂ
  e6 : ℍ → ℂ

/-- Exact same-object identification with the Mathlib analytic functions.

This is the load-bearing representation seam.  Shared formulas or equal
cardinality do not construct it. -/
structure EisensteinSameObjectWeld (S : ExtractedEisensteinSurface) : Prop where
  q_same : ∀ τ, S.q τ = Analytic.qParam τ
  e4_same : ∀ τ, S.e4 τ = Analytic.E4 τ
  e6_same : ∀ τ, S.e6 τ = Analytic.E6 τ

/-- The q-disk theorem transports immediately once q is identified. -/
theorem q_norm_lt_one_of_weld
    {S : ExtractedEisensteinSurface}
    (W : EisensteinSameObjectWeld S)
    (τ : ℍ) :
    ‖S.q τ‖ < 1 := by
  rw [W.q_same τ]
  exact Analytic.norm_qParam_lt_one τ

/-- The exact q norm formula transports through the same weld. -/
theorem q_norm_formula_of_weld
    {S : ExtractedEisensteinSurface}
    (W : EisensteinSameObjectWeld S)
    (τ : ℍ) :
    ‖S.q τ‖ = Real.exp (-2 * π * τ.im) := by
  rw [W.q_same τ]
  exact Analytic.norm_qParam τ

/-- Quartic polynomial-geometric summability transports after q identification. -/
theorem summable_quartic_of_weld
    {S : ExtractedEisensteinSurface}
    (W : EisensteinSameObjectWeld S)
    (τ : ℍ) :
    Summable (fun n : ℕ => (n : ℂ) ^ 4 * S.q τ ^ n) := by
  simpa [W.q_same τ] using Analytic.summable_quartic_geometric τ

/-- Sextic polynomial-geometric summability transports after q identification. -/
theorem summable_sextic_of_weld
    {S : ExtractedEisensteinSurface}
    (W : EisensteinSameObjectWeld S)
    (τ : ℍ) :
    Summable (fun n : ℕ => (n : ℂ) ^ 6 * S.q τ ^ n) := by
  simpa [W.q_same τ] using Analytic.summable_sextic_geometric τ

/-- Literal sigma_3 q-series summability transports through q identification. -/
theorem summable_sigma3_q_of_weld
    {S : ExtractedEisensteinSurface}
    (W : EisensteinSameObjectWeld S)
    (τ : ℍ) :
    Summable (fun n : ℕ => (σ 3 n : ℂ) * S.q τ ^ n) := by
  simpa [W.q_same τ] using Analytic.summable_sigma3_q τ

/-- Literal sigma_5 q-series summability transports through q identification. -/
theorem summable_sigma5_q_of_weld
    {S : ExtractedEisensteinSurface}
    (W : EisensteinSameObjectWeld S)
    (τ : ℍ) :
    Summable (fun n : ℕ => (σ 5 n : ℂ) * S.q τ ^ n) := by
  simpa [W.q_same τ] using Analytic.summable_sigma5_q τ

/-- The literal Agda E4 coefficient scale preserves summability after the weld. -/
theorem summable_240_sigma3_q_of_weld
    {S : ExtractedEisensteinSurface}
    (W : EisensteinSameObjectWeld S)
    (τ : ℍ) :
    Summable (fun n : ℕ =>
      (240 : ℂ) * ((σ 3 n : ℂ) * S.q τ ^ n)) := by
  simpa [W.q_same τ] using Analytic.summable_240_sigma3_q τ

/-- The literal Agda E6 coefficient scale preserves summability after the weld. -/
theorem summable_504_sigma5_q_of_weld
    {S : ExtractedEisensteinSurface}
    (W : EisensteinSameObjectWeld S)
    (τ : ℍ) :
    Summable (fun n : ℕ =>
      (504 : ℂ) * ((σ 5 n : ℂ) * S.q τ ^ n)) := by
  simpa [W.q_same τ] using Analytic.summable_504_sigma5_q τ

/-- The converged normalized E4 q-expansion transports through the exact weld. -/
theorem e4_qExpansion_of_weld
    {S : ExtractedEisensteinSurface}
    (W : EisensteinSameObjectWeld S)
    (τ : ℍ) :
    S.e4 τ =
      1 - (2 * (4 : ℂ) / bernoulli 4) *
        ∑' n : ℕ+, (σ 3 n : ℂ) * S.q τ ^ (n : ℤ) := by
  rw [W.e4_same τ]
  simpa [W.q_same τ] using Analytic.E4_qExpansion τ

/-- The converged normalized E6 q-expansion transports through the exact weld. -/
theorem e6_qExpansion_of_weld
    {S : ExtractedEisensteinSurface}
    (W : EisensteinSameObjectWeld S)
    (τ : ℍ) :
    S.e6 τ =
      1 - (2 * (6 : ℂ) / bernoulli 6) *
        ∑' n : ℕ+, (σ 5 n : ℂ) * S.q τ ^ (n : ℤ) := by
  rw [W.e6_same τ]
  simpa [W.q_same τ] using Analytic.E6_qExpansion τ

/-- Delta is kept as a separate extracted coordinate so that eta^24 identity
cannot be smuggled in through the E4/E6 weld. -/
structure ExtractedDeltaSurface where
  delta : ℍ → ℂ

/-- Exact identification of one extracted Delta candidate with eta^24. -/
structure DeltaEta24SameObjectWeld (D : ExtractedDeltaSurface) : Prop where
  delta_same : ∀ τ, D.delta τ = Analytic.deltaEta24 τ

/-- Nonvanishing of eta^24 transports once and only once the Delta weld exists. -/
theorem delta_ne_zero_of_eta24_weld
    {D : ExtractedDeltaSurface}
    (W : DeltaEta24SameObjectWeld D)
    (τ : ℍ) :
    D.delta τ ≠ 0 := by
  rw [W.delta_same τ]
  exact Analytic.deltaEta24_ne_zero τ

/-- The still-open algebraic normalization seam.

At the repository's current Mathlib pin this is intentionally a proposition to
be supplied/proved, rather than a theorem claimed by this module. -/
def DeltaE4E6Normalization
    (S : ExtractedEisensteinSurface)
    (D : ExtractedDeltaSurface) : Prop :=
  ∀ τ : ℍ, D.delta τ = (S.e4 τ ^ 3 - S.e6 τ ^ 2) / 1728

/-- Full analytic transport requires the function welds and the normalization
identity as separate evidence. -/
structure FullEisensteinDeltaWeld
    (S : ExtractedEisensteinSurface)
    (D : ExtractedDeltaSurface) : Prop where
  eisenstein : EisensteinSameObjectWeld S
  deltaEta24 : DeltaEta24SameObjectWeld D
  deltaNormalization : DeltaE4E6Normalization S D

/-- The normalization equation becomes available only from the explicit full weld. -/
theorem delta_eq_e4_cube_sub_e6_sq_of_full_weld
    {S : ExtractedEisensteinSurface}
    {D : ExtractedDeltaSurface}
    (W : FullEisensteinDeltaWeld S D)
    (τ : ℍ) :
    D.delta τ = (S.e4 τ ^ 3 - S.e6 τ ^ 2) / 1728 :=
  W.deltaNormalization τ

/-- Exact same-object weld to the route-B normalized E4/E6 Delta target.

This is deliberately distinct from the eta^24 weld: the reflection theorem is
already proved for the normalized E4/E6 target at the pinned dependency, so it
can be transported before eta^24 itself is identified. -/
structure DeltaNormalizedE4E6SameObjectWeld
    (D : ExtractedDeltaSurface) : Prop where
  delta_same :
    ∀ τ, D.delta τ =
      Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaLimit τ

/-- The concrete inverse-conjugation reflection identity transports through the
same-object weld with no additional analytic assumptions. -/
theorem delta_inv_conj_of_normalized_weld
    {D : ExtractedDeltaSurface}
    (W : DeltaNormalizedE4E6SameObjectWeld D)
    (τ : ℍ) :
    D.delta (ModularGroup.S •
      Integration.MoonshineEisensteinAgdaTarget.negConj τ) =
      conj ((τ : ℂ) ^ 12 * D.delta τ) := by
  rw [W.delta_same, W.delta_same]
  exact Integration.MoonshineEisensteinAgdaTarget.normalizedDelta_inv_conj τ

/-- Unit norm gives the exact fixed-locus value equation required by the Agda
phase compiler, transported to any extracted Delta surface. -/
theorem delta_unitCircle_fixed_of_normalized_weld
    {D : ExtractedDeltaSurface}
    (W : DeltaNormalizedE4E6SameObjectWeld D)
    (τ : ℍ)
    (hunit : Complex.normSq (τ : ℂ) = 1) :
    D.delta τ = conj ((τ : ℂ) ^ 12 * D.delta τ) := by
  rw [W.delta_same, W.delta_same]
  exact
    Integration.MoonshineEisensteinAgdaTarget.normalizedDelta_unitCircle_fixed
      τ hunit

/-- Once both normalizations are known, the normalized E4/E6 target and eta^24
are definitionally the same extracted Delta surface pointwise. -/
theorem normalized_target_eq_eta24_of_two_welds
    {D : ExtractedDeltaSurface}
    (WE : DeltaNormalizedE4E6SameObjectWeld D)
    (Wη : DeltaEta24SameObjectWeld D)
    (τ : ℍ) :
    Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaLimit τ =
      Analytic.deltaEta24 τ := by
  rw [← WE.delta_same τ, Wη.delta_same τ]

/-- Machine-readable promotion boundary. -/
structure WeldBoundary where
  mathlibAnalyticTargetOwned : Bool
  qE4E6TransportCompilerOwned : Bool
  literalSigma3Sigma5TransportCompilerOwned : Bool
  literal240And504TransportCompilerOwned : Bool
  eta24NonvanishingTransportCompilerOwned : Bool
  normalizedDeltaReflectionTransportCompilerOwned : Bool
  normalizedDeltaFixedLocusTransportCompilerOwned : Bool
  extractedAgdaSurfaceInhabited : Bool
  exactAgdaLeanSameObjectWeldInhabited : Bool
  deltaE4E6NormalizationOwnedAtPinnedMathlib : Bool

def weldBoundary : WeldBoundary where
  mathlibAnalyticTargetOwned := true
  qE4E6TransportCompilerOwned := true
  literalSigma3Sigma5TransportCompilerOwned := true
  literal240And504TransportCompilerOwned := true
  eta24NonvanishingTransportCompilerOwned := true
  normalizedDeltaReflectionTransportCompilerOwned := true
  normalizedDeltaFixedLocusTransportCompilerOwned := true
  extractedAgdaSurfaceInhabited := false
  exactAgdaLeanSameObjectWeldInhabited := false
  deltaE4E6NormalizationOwnedAtPinnedMathlib := false

end

end Integration.MoonshineEisensteinWeld

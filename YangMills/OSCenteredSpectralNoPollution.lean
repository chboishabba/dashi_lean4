import Mathlib
import YangMills.OSCenteredExcitationHalfRate
import YangMills.HalfRateSpectralNoPollution

open Filter MeasureTheory

/-!
# Same-carrier centered OS no-pollution theorem

The centered same-family weld now supplies, on the literal excitation Hilbert
space `Ω⊥`, both ingredients needed by the abstract spectral compiler:

* a dense real span of centered Wilson/OS vectors;
* a vector-dependent `2^{-n}` matrix-coefficient bound on every pair in that
  span.

Therefore every strict-above-half spectral window operator satisfying the
standard spectral lower bound for the SAME restricted transfer family is zero.
No additional F2 density or uniform operator norm estimate is assumed.
-/

namespace RequestProject.YangMills

namespace SameHOSCenteredMixedHalfRateWeld

/-- The half-rate controlled dense set used by the same-H spectral argument. -/
def controlledExcitationSpan
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V) :
    Set (vacuumOrthogonalSubmodule weld.vacuum) :=
  (Submodule.span ℝ (Set.range weld.centeredExcitationVector) :
    Set (vacuumOrthogonalSubmodule weld.vacuum))

/-- The controlled excitation span is dense. -/
theorem controlled_excitation_span_dense
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V) :
    Dense weld.controlledExcitationSpan :=
  weld.dense_centered_excitation_span

/-- Every controlled excitation vector has a self half-rate bound. -/
theorem controlled_excitation_self_half_rate
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V)
    (x : vacuumOrthogonalSubmodule weld.vacuum)
    (hx : x ∈ weld.controlledExcitationSpan) :
    HalfRateMatrixBound weld.excitationTransfer x x :=
  weld.centered_excitation_span_half_rate hx hx

/--
No nonzero strict-above-half spectral window survives on the same excitation
sector once functional calculus supplies its standard quadratic lower bound.
-/
theorem strict_above_half_spectral_window_zero
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V)
    (P : vacuumOrthogonalSubmodule weld.vacuum →L[ℝ]
      vacuumOrthogonalSubmodule weld.vacuum)
    (λ : ℝ)
    (hλ : (1 / 2 : ℝ) < λ)
    (hLower : SpectralWindowLowerBound weld.excitationTransfer P λ) :
    P = 0 :=
  dense_half_rate_forces_spectral_window_zero
    weld.excitationTransfer weld.controlledExcitationSpan
    weld.controlled_excitation_span_dense
    weld.controlled_excitation_self_half_rate
    P λ hλ hLower

end SameHOSCenteredMixedHalfRateWeld

end RequestProject.YangMills

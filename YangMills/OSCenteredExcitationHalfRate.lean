import Mathlib
import YangMills.OSCenteredSameFamilyWeld

open Filter MeasureTheory

/-!
# Half-rate directly on the vacuum-orthogonal OS sector

The centered same-family source already gives exponential covariance bounds on
ambient centered vectors and proves their centered image is dense in `Ω⊥`.
For spectral analysis it is cleaner to place both facts on the actual excitation
Hilbert space itself.  This file restricts every discrete OS transfer to `Ω⊥`
and transports the source half-rate to the resulting dense real span.
-/

namespace RequestProject.YangMills

namespace SameHOSCenteredMixedHalfRateWeld

/-- The same discrete OS transfer, restricted to the vacuum-orthogonal sector. -/
noncomputable def excitationTransfer
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V) :
    ℕ → vacuumOrthogonalSubmodule weld.vacuum →L[ℝ]
      vacuumOrthogonalSubmodule weld.vacuum :=
  fun time =>
    ((weld.transfer time).domRestrict
      (vacuumOrthogonalSubmodule weld.vacuum)).codRestrict
      (vacuumOrthogonalSubmodule weld.vacuum)
      (fun x => weld.transfer_preserves_excitation time x.property)

/-- A selected centered Wilson/OS vector, now living literally in `Ω⊥`. -/
noncomputable def centeredExcitationVector
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V) :
    V → vacuumOrthogonalSubmodule weld.vacuum :=
  weld.data.centeredRawVector weld.vacuum weld.vacuumNormalized

/-- The exact source half-rate survives restriction to the same excitation sector. -/
theorem centered_excitation_pair_half_rate
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V)
    (left right : V) :
    HalfRateMatrixBound weld.excitationTransfer
      (weld.centeredExcitationVector left)
      (weld.centeredExcitationVector right) := by
  rcases weld.centered_pair_half_rate left right with ⟨C, hC, hRate⟩
  refine ⟨C, hC, ?_⟩
  intro time
  simpa [excitationTransfer, centeredExcitationVector,
    OSGramData.centeredRawVector,
    SameHOSCenteredMixedHalfRateWeld.centeredVector] using hRate time

/-- Mixed half-rate extends by linearity to the full real span of centered generators. -/
theorem centered_excitation_span_half_rate
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V)
    {left right : vacuumOrthogonalSubmodule weld.vacuum}
    (hleft : left ∈ Submodule.span ℝ (Set.range weld.centeredExcitationVector))
    (hright : right ∈ Submodule.span ℝ (Set.range weld.centeredExcitationVector)) :
    HalfRateMatrixBound weld.excitationTransfer left right :=
  halfRateMatrixBound_of_mem_span
    weld.excitationTransfer weld.centeredExcitationVector
    weld.centered_excitation_pair_half_rate hleft hright

/-- The half-rate-controlled excitation span is dense by the centered OS construction. -/
theorem dense_centered_excitation_span
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V) :
    Dense
      (Submodule.span ℝ (Set.range weld.centeredExcitationVector) :
        Set (vacuumOrthogonalSubmodule weld.vacuum)) := by
  simpa [centeredExcitationVector] using weld.dense_centered_span

end SameHOSCenteredMixedHalfRateWeld

end RequestProject.YangMills

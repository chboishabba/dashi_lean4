import Mathlib
import YangMills.CMP116WilsonMixedHalfRateClustering
import YangMills.OSCenteredExcitationSector
import YangMills.OSGramHilbertSemigroup
import YangMills.SameHWilsonMixedHalfRateWeld

open Filter MeasureTheory

/-!
# Centered same-family Wilson/OS weld

The physical mixed covariance is centered.  Therefore the preferred same-H
package must identify it with matrix coefficients of centered OS vectors in the
vacuum-orthogonal sector, not with raw vectors in a Hilbert space that still
contains the invariant vacuum.

Density of the centered vectors is construction-owned by
`OSCenteredExcitationSector`; the source-facing content is the physical
same-object identification of the Wilson carrier, its covariance and the same
OS transfer family.
-/

namespace RequestProject.YangMills

structure SameHOSCenteredMixedHalfRateWeld
    (State V : Type*)
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V] where
  data : OSGramData V
  source : CMP116WilsonMixedHalfRateClusteringSource State V
  cutoffConverges : Tendsto source.cutoffLaw atTop (𝓝 source.continuumLaw)
  rawTransfer : ℕ → V →ₗ[ℝ] V
  rawContractive :
    ∀ time v,
      data.gram (rawTransfer time v) (rawTransfer time v) ≤ data.gram v v
  rawZero : ∀ v, rawTransfer 0 v = v
  rawAdd : ∀ s t v, rawTransfer (s + t) v = rawTransfer s (rawTransfer t v)
  vacuum : data.Hilbert
  vacuumNormalized : ⟪vacuum, vacuum⟫_ℝ = 1
  vacuumFixed :
    ∀ time,
      data.hilbertTranslation
          (rawTransfer time) (rawContractive time) vacuum = vacuum
  transferSymmetric :
    ∀ time left right,
      ⟪left,
          data.hilbertTranslation
            (rawTransfer time) (rawContractive time) right⟫_ℝ =
        ⟪data.hilbertTranslation
            (rawTransfer time) (rawContractive time) left,
          right⟫_ℝ
  sameCenteredCorrelation :
    ∀ left right time,
      |probabilityCovariance source.continuumLaw
          (source.wilson left) (source.timeTranslate right time)| =
        |⟪osCenteredWilsonVector vacuum (data.rawVector left),
            data.hilbertTranslation
              (rawTransfer time) (rawContractive time)
              (osCenteredWilsonVector vacuum (data.rawVector right))⟫_ℝ|

namespace SameHOSCenteredMixedHalfRateWeld

/-- The completed OS transfer selected by the same raw carrier. -/
noncomputable def transfer
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V) :
    ℕ → weld.data.Hilbert →L[ℝ] weld.data.Hilbert :=
  fun time =>
    weld.data.hilbertTranslation
      (weld.rawTransfer time) (weld.rawContractive time)

/-- Ambient centered OS vector associated to a selected Wilson observable. -/
noncomputable def centeredVector
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V) :
    V → weld.data.Hilbert :=
  fun v => osCenteredWilsonVector weld.vacuum (weld.data.rawVector v)

/-- The exact source mixed half-rate is a bound on centered vectors of the same OS transfer. -/
theorem centered_pair_half_rate
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V)
    (left right : V) :
    HalfRateMatrixBound weld.transfer
      (weld.centeredVector left) (weld.centeredVector right) := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro time
  rw [← weld.sameCenteredCorrelation left right time]
  exact weld.source.continuum_mixed_half_rate
    weld.cutoffConverges left right time

/-- Centered selected Wilson vectors have dense span in the excitation sector by construction. -/
theorem dense_centered_span
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V) :
    Dense
      (Submodule.span ℝ
        (Set.range (weld.data.centeredRawVector
          weld.vacuum weld.vacuumNormalized)) :
        Set (vacuumOrthogonalSubmodule weld.vacuum)) :=
  weld.data.dense_centeredRawVector_span
    weld.vacuum weld.vacuumNormalized

/-- The same discrete OS transfer preserves the vacuum-orthogonal excitation sector. -/
theorem transfer_preserves_excitation
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V)
    (time : ℕ) {x : weld.data.Hilbert}
    (hx : x ∈ vacuumOrthogonalSubmodule weld.vacuum) :
    weld.transfer time x ∈ vacuumOrthogonalSubmodule weld.vacuum := by
  apply os_transfer_preserves_vacuumOrthogonal
    weld.vacuum (weld.transfer time).toLinearMap
  · exact weld.vacuumFixed time
  · intro left right
    exact weld.transferSymmetric time left right
  · exact hx

/-- The completed centered OS translations obey the discrete semigroup identity. -/
theorem transfer_zero
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V) :
    weld.transfer 0 = ContinuousLinearMap.id ℝ weld.data.Hilbert := by
  simpa [transfer] using
    weld.data.hilbertTranslation_zero
      weld.rawTransfer weld.rawContractive weld.rawZero

/-- The completed centered OS translations obey additive-time composition. -/
theorem transfer_add
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V)
    (s t : ℕ) :
    weld.transfer (s + t) =
      (weld.transfer s).comp (weld.transfer t) := by
  simpa [transfer] using
    weld.data.hilbertTranslation_add
      weld.rawTransfer weld.rawContractive weld.rawAdd s t

end SameHOSCenteredMixedHalfRateWeld

/-- Exact preferred centered same-family producer. -/
def SameHOSCenteredMixedHalfRateWeldExists
    (State V : Type*)
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V] : Prop :=
  Nonempty (SameHOSCenteredMixedHalfRateWeld State V)

end RequestProject.YangMills

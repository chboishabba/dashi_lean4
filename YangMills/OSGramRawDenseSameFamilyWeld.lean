import Mathlib
import YangMills.OSGramHilbertTranslation
import YangMills.OSGramHilbertSemigroup
import YangMills.SameHWilsonMixedHalfRateWeld

open Filter MeasureTheory

/-!
# Same-family OS carrier makes F2 density canonical

If the positive-time OS pre-Hilbert carrier `V` is chosen to be exactly the
observable family controlled by the mixed R551 estimate, then the corresponding
OS vectors are dense by construction: every quotient class comes from some
`v : V`, and the quotient embeds densely into its Hilbert completion.

This removes a separate density/cyclicity hypothesis from F2 on the preferred
same-carrier route.  The genuine physical receipt is instead the same-object
choice that the R551 observable carrier really is the OS positive-time test
carrier and that its continuum covariance is the matrix coefficient of the
completed translation built from that carrier.
-/

namespace RequestProject.YangMills

namespace OSGramData

/-- Canonical OS vector associated to a raw positive-time test observable. -/
noncomputable def rawVector
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V) :
    V → data.Hilbert :=
  fun v => data.toHilbert (Submodule.Quotient.mk v)

/--
Raw positive-time test observables have dense image in the reconstructed OS
Hilbert space.  This is purely the quotient-plus-completion construction.
-/
theorem denseRange_rawVector
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V) :
    DenseRange data.rawVector := by
  change DenseRange
    ((fun q : data.PreHilbert => UniformSpace.Completion.coe q) ∘
      (Submodule.Quotient.mk : V → data.PreHilbert))
  exact UniformSpace.Completion.denseRange_coe.comp
    (Submodule.Quotient.mk_surjective data.gram.ker).denseRange
    UniformSpace.Completion.continuous_coe

/-- The real linear span of all raw OS vectors is dense as well. -/
theorem dense_rawVector_span
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V) :
    Dense (Submodule.span ℝ (Set.range data.rawVector) : Set data.Hilbert) :=
  data.denseRange_rawVector.mono (fun _ hx => Submodule.subset_span hx)

end OSGramData

/--
Preferred discrete same-family F1/F2 package.  R551 acts directly on the SAME
raw carrier `V` from which the OS Hilbert space is reconstructed, and the
transfer family is literally the completed OS translation of the raw
positive-time maps.
-/
structure SameHOSRawMixedHalfRateWeld
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
  sameCorrelation :
    ∀ left right time,
      |probabilityCovariance source.continuumLaw
          (source.wilson left) (source.timeTranslate right time)| =
        |⟪data.rawVector left,
            data.hilbertTranslation
              (rawTransfer time) (rawContractive time)
              (data.rawVector right)⟫_ℝ|

namespace SameHOSRawMixedHalfRateWeld

/-- The completed OS transfer family selected by the same raw carrier. -/
noncomputable def transfer
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSRawMixedHalfRateWeld State V) :
    ℕ → weld.data.Hilbert →L[ℝ] weld.data.Hilbert :=
  fun time =>
    weld.data.hilbertTranslation
      (weld.rawTransfer time) (weld.rawContractive time)

/-- Forget to the generic mixed same-H R551 weld. -/
noncomputable def toMixedHalfRateWeld
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSRawMixedHalfRateWeld State V) :
    SameHWilsonMixedHalfRateWeld State V weld.data.Hilbert where
  source := weld.source
  cutoffConverges := weld.cutoffConverges
  transfer := weld.transfer
  vector := weld.data.rawVector
  sameCorrelation := by
    intro left right time
    exact weld.sameCorrelation left right time

/--
The SAME R551-controlled carrier has dense OS-vector span automatically.  No
separate F2 density producer is needed on this preferred construction.
-/
noncomputable def toDenseSameFamilyWeld
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSRawMixedHalfRateWeld State V) :
    SameHDenseWilsonMixedHalfRateWeld State V weld.data.Hilbert where
  toSameHWilsonMixedHalfRateWeld := weld.toMixedHalfRateWeld
  denseWilsonSpan := weld.data.dense_rawVector_span

/-- Every pair of raw OS vectors has the source half-rate on the same transfer family. -/
theorem raw_pair_half_rate
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSRawMixedHalfRateWeld State V)
    (left right : V) :
    HalfRateMatrixBound weld.transfer
      (weld.data.rawVector left) (weld.data.rawVector right) :=
  weld.toMixedHalfRateWeld.generator_half_rate left right

/-- The completed OS translations obey the discrete semigroup law. -/
theorem transfer_zero
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSRawMixedHalfRateWeld State V) :
    weld.transfer 0 = ContinuousLinearMap.id ℝ weld.data.Hilbert := by
  simpa [transfer] using
    weld.data.hilbertTranslation_zero
      weld.rawTransfer weld.rawContractive weld.rawZero

/-- The completed OS translations obey exact additive-time composition. -/
theorem transfer_add
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSRawMixedHalfRateWeld State V)
    (s t : ℕ) :
    weld.transfer (s + t) =
      (weld.transfer s).comp (weld.transfer t) := by
  simpa [transfer] using
    weld.data.hilbertTranslation_add
      weld.rawTransfer weld.rawContractive weld.rawAdd s t

end SameHOSRawMixedHalfRateWeld

/--
Exact preferred F1/F2 source producer after the construction-level density cut.
Its missing content is now same-carrier/same-correlation physics, not density.
-/
def SameHOSRawMixedHalfRateWeldExists
    (State V : Type*)
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V] : Prop :=
  Nonempty (SameHOSRawMixedHalfRateWeld State V)

end RequestProject.YangMills

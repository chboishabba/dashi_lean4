import Mathlib
import YangMills.YMClayMaxCut20261003D3ExtensionClosed
import YangMills.ProjectiveFinIicBridge
import YangMills.CountableObservableMarginals
import YangMills.CountableObservableNormMomentContinuum
import YangMills.CountableObservableCoordinateMoment
import YangMills.LiteralSU2PositiveHalfBoundaryIndependence
import YangMills.LiteralSU2CrossingPositiveIndexCoincidence
import YangMills.LiteralSU2BoundaryHaarTranslation
import YangMills.LiteralSU2BoundaryHaarDoubleAverage
import YangMills.LiteralSU2BoundaryGaugeRelative
import YangMills.LiteralSU2CrossingDoubleGaugeRelative
import YangMills.LiteralSU2CrossingDoubleGaugeAverage
import YangMills.LiteralSU2BoundaryProjectedKernelPlaneSplit

/-!
# YM physical-frontier max cut, 2026-10-03

This integration surface records the current literal frontier without upgrading
source hypotheses into proofs.

A / finite Wilson:
* the positive Wilson half is theorem-bearingly independent of both temporal
  boundary Haar planes and of the reflected-right field;
* upper/lower crossing half paths are read back to boundary gauge transforms on
  the same literal positive spatial edges;
* the reflected positive edge and explicit positive edge are identified;
* the selected one-link and boundary Haar laws have genuine left/right
  translation invariance;
* two independently endpoint-gauged SU(2) edges depend only on the exact
  relative gauge `b * c⁻¹`;
* that local identity is lifted through the complete upper+lower crossing sum;
* two independent full temporal-boundary Haar copies collapse exactly to one
  relative Haar boundary;
* therefore the complete double-gauged augmented crossing exponential average
  is exactly the single-boundary literal Wilson crossing-kernel average.

So the crossing/Fubini same-object seam is now paid.  The remaining pure-Wilson
leaf is narrower: prove the reflected positive noncrossing half reads only the
right positive field, then absorb the left/right noncrossing half factors into
the already-positive augmented crossing quadratic form.  The final consumer is
still `LiteralSU2BoundaryGaugeProjectionRPExact`.

B / complete action:
The generic Wilson × residual compiler and crossing falsifier are ready, but no
literal selected CMP119 crossing-polymer dictionary has been found.  B remains
a source audit: construct the actual E/R/B crossing kernels and prove PSD or
supply a negative quadratic witness.

C / source weld:
The source-native CMP119 record owns E_k/R_k/B_k/vacuum under equation (2.23),
but the source repository explicitly marks the literal complete-density
instantiation conditional.  Therefore the Lean selected-source dictionary is
correctly left uninhabited rather than filled by a surrogate scalar projection.

D3:
* the Fin (n+1) <-> Iic n indexing seam is closed;
* one countable selected scalar observable sequence canonically generates every
  finite marginal and prefix consistency is definitional;
* the canonical finite-dimensional cost is ENNReal.ofReal of the sup norm, with
  compact sublevels automatically;
* scalar coordinate first moments imply every finite-prefix norm moment;
* if the selected coordinates are pointwise cutoff-uniformly bounded, even
  those scalar moments are automatic under every cutoff probability law;
* either route yields tightness, one simultaneous subsequence, consistent
  limits, canonical regular conditional kernels and an actual probability law
  on ℕ -> ℝ.

Thus there is no remaining D3 quantitative moment theorem for a bounded selected
coordinate family.  The physical choice is now sharper: either exhibit a
bounded countable determining/scaling-relevant observable family, or use the
literal CMP119 insertion/exponential-moment producer only for coordinates that
are genuinely unbounded.  The Agda R559 lane already has the correct same-measure
interface for the latter, while its literal exponential-moment producer remains
explicitly conditional.  No generic probability-theory obligation is being
counted as physical debt here.
-/

open Set MeasureTheory Preorder

namespace RequestProject.YangMills

/-- Block A locality: the positive half reads only `left`. -/
theorem ym_20261003_block_a_positive_half_boundary_independent
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left : SU2PositiveInteriorLinks n)
    (boundary₁ boundary₂ : SU2BoundaryTemporalLinks n)
    (right₁ right₂ : SU2PositiveInteriorLinks n) :
    su2EvenTimePositiveWilsonHalf n
        (su2AssembleReflectedPair n left boundary₁ right₁) β =
      su2EvenTimePositiveWilsonHalf n
        (su2AssembleReflectedPair n left boundary₂ right₂) β :=
  su2_positive_half_assembled_pair_boundary_independent
    n β left boundary₁ boundary₂ right₁ right₂

/-- Upper crossing really uses one common positive spatial-link index. -/
theorem ym_20261003_block_a_upper_common_positive_edge
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2UpperCrossingPlaquettes n) :
    su2UpperCrossingRightPositiveIndex n p hp =
      su2UpperCrossingLeftPositiveIndex n p hp :=
  su2_upper_crossing_positive_index_coincides n p hp

/-- Lower crossing really uses one common positive spatial-link index. -/
theorem ym_20261003_block_a_lower_common_positive_edge
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2LowerCrossingPlaquettes n) :
    su2LowerCrossingRightPositiveIndex n p hp =
      su2LowerCrossingLeftPositiveIndex n p hp :=
  su2_lower_crossing_positive_index_coincides n p hp

/-- Local Block-A noncommutative weld: two boundary gauges reduce to one relative gauge. -/
theorem ym_20261003_block_a_two_gauges_relative
    (bs bt cs ct left right : SU2PlaquetteHolonomy) :
    su2RelativeFundamentalTrace
        (su2BoundaryGaugeTransformEdge bs bt left)
        (su2BoundaryGaugeTransformEdge cs ct right) =
      su2RelativeFundamentalTrace right
        (su2BoundaryGaugeTransformEdge
          (bs * cs⁻¹) (bt * ct⁻¹) left) :=
  su2_relative_trace_two_boundary_gauges_relative_swapped
    bs bt cs ct left right

/-- Complete crossing sum with two boundary copies depends only on the relative boundary. -/
theorem ym_20261003_block_a_double_crossing_relative
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (b c : SU2BoundaryTemporalLinks n) :
    su2DoubleGaugedCrossingTraceSum n left right b c =
      su2UpperGaugedCrossingTraceSum n left right
        (su2RelativeBoundaryField b c) +
      su2LowerGaugedCrossingTraceSum n left right
        (su2RelativeBoundaryField b c) :=
  su2_double_gauged_crossing_trace_sum_relative n left right b c

/-- The entire augmented crossing average is the exact literal Wilson crossing average. -/
theorem ym_20261003_block_a_crossing_average_same_object
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n) :
    (∫ b, ∫ c,
      su2DoubleGaugedCrossingKernel n β left right b c
      ∂(literalSU2BoundaryTemporalHaar n)
      ∂(literalSU2BoundaryTemporalHaar n)) =
      ∫ u,
        su2WilsonCrossingPlaneKernel
          (su2EvenTimeCrossingPlaquettes n) β
          (su2LiteralCrossingFirstBoundary
            (su2AssembleReflectedPair n left u right))
          (su2LiteralCrossingSecondBoundary
            (su2AssembleReflectedPair n left u right))
        ∂(literalSU2BoundaryTemporalHaar n) :=
  su2_double_gauged_crossing_average_eq_literal n β left right

/-- The final pure-Wilson Block-A statement. -/
def YM20261003BlockAFinalGaugeProjectionPositivity : Prop :=
  LiteralSU2BoundaryGaugeProjectionRPExact

/-- D3 indexing bridge: every simultaneous Fin-limit family is a sequential Iic family. -/
noncomputable def ym_20261003_d3_sequential_family
    {Ω : Type*} [MeasurableSpace Ω]
    {family : RealCanonicalProjectiveMarginalFamily Ω}
    (diag : RealSimultaneousMarginalSubsequence family) :
    RealSequentialProjectiveFamily :=
  diag.toSequentialProjectiveFamily

/-- Selected-observable norm moments construct the actual countable continuum law. -/
noncomputable def ym_20261003_selected_observable_continuum
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableNormMomentSource Ω) :
    Measure (ℕ → ℝ) :=
  source.globalMeasure

instance ym_20261003_selected_observable_continuum_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableNormMomentSource Ω) :
    IsProbabilityMeasure (ym_20261003_selected_observable_continuum source) := by
  unfold ym_20261003_selected_observable_continuum
  infer_instance

/-- Exact selected prefix recovery for the constructed continuum law. -/
theorem ym_20261003_selected_observable_continuum_prefix
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableNormMomentSource Ω)
    (n : ℕ) :
    (ym_20261003_selected_observable_continuum source).map (frestrictLe n) =
      (realFinSuccLawToIic n (source.diagonal.limit (n + 1)) :
        Measure ((i : Set.Iic n) → ℝ)) :=
  source.globalMeasure_prefix n

/-- Bounded selected coordinates construct the same actual countable continuum law for free. -/
noncomputable def ym_20261003_bounded_selected_observable_continuum
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableUniformBoundSource Ω) :
    Measure (ℕ → ℝ) :=
  source.globalMeasure

instance ym_20261003_bounded_selected_observable_continuum_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableUniformBoundSource Ω) :
    IsProbabilityMeasure
      (ym_20261003_bounded_selected_observable_continuum source) := by
  unfold ym_20261003_bounded_selected_observable_continuum
  infer_instance

/--
Exact physical D3 leaf after all generic compactness/extension machinery:
the producer must live on the SAME selected cutoff law and scalar observable
sequence supplied here.
-/
def YM20261003D3SelectedPrefixNormMomentProducerExists
    {Ω : Type*} [MeasurableSpace Ω]
    (cutoffLaw : ℕ → ProbabilityMeasure Ω)
    (observable : ℕ → Ω → ℝ) : Prop :=
  ∃ source : RealCountableObservableNormMomentSource Ω,
    source.cutoffLaw = cutoffLaw ∧
    source.observable = observable

/--
For bounded selected coordinates the old quantitative D3 moment leaf is already
closed: the pointwise bound manufactures the exact same-law norm-moment source.
-/
theorem ym_20261003_d3_bounded_source_closes_moment_leaf
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableUniformBoundSource Ω) :
    YM20261003D3SelectedPrefixNormMomentProducerExists
      source.cutoffLaw source.observable := by
  refine ⟨source.toNormMomentSource, ?_, ?_⟩
  · rfl
  · rfl

/--
The genuinely remaining bounded-coordinate physical question: produce the
chosen same-law bounded observable source.  Whether that family is sufficiently
determining for the intended continuum Yang--Mills configuration space is a
separate source/topology theorem and is deliberately not hidden here.
-/
def YM20261003D3SelectedUniformBoundProducerExists
    {Ω : Type*} [MeasurableSpace Ω]
    (cutoffLaw : ℕ → ProbabilityMeasure Ω)
    (observable : ℕ → Ω → ℝ) : Prop :=
  ∃ source : RealCountableObservableUniformBoundSource Ω,
    source.cutoffLaw = cutoffLaw ∧
    source.observable = observable

end RequestProject.YangMills

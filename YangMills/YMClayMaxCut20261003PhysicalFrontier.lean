import Mathlib
import YangMills.YMClayMaxCut20261003D3ExtensionClosed
import YangMills.ProjectiveFinIicBridge
import YangMills.CountableObservableMarginals
import YangMills.CountableObservableNormMomentContinuum
import YangMills.LiteralSU2PositiveHalfBoundaryIndependence
import YangMills.LiteralSU2CrossingPositiveIndexCoincidence
import YangMills.LiteralSU2BoundaryHaarTranslation
import YangMills.LiteralSU2BoundaryProjectedKernelPlaneSplit

/-!
# YM physical-frontier max cut, 2026-10-03

This integration surface records the current literal frontier without upgrading
source hypotheses into proofs.

A / finite Wilson:
* the positive Wilson half is now theorem-bearingly independent of both temporal
  boundary Haar planes and of the reflected-right field;
* upper/lower crossing half paths have already been read back to boundary gauge
  transforms on the same literal positive spatial edges;
* the reflected positive edge and the explicit positive edge are identified;
* the selected one-link and boundary-plane Haar laws have genuine right
  translation invariance;
* the projected kernel is already the exact two-plane Haar integral.
The remaining pure-Wilson leaf is therefore only the final gauge-projector
positivity/Fubini theorem.  No lattice representation seam remains below it.

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
* a source-native uniform finite-prefix norm moment therefore yields tightness,
  one simultaneous subsequence, consistent limits, canonical regular
  conditional kernels and an actual probability law on ℕ -> ℝ.

The remaining D3 physical theorem is exactly the quantitative source estimate.
The Agda CMP119 moment lane already has the correct same-measure interface:
uniform exponential moments imply its polynomial insertion moments, while the
literal CMP119 exponential-moment producer itself remains explicitly
conditional.  No generic probability-theory obligation is being counted as
physical debt here.
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

/-- The final pure-Wilson Block-A statement; only its final projector proof remains. -/
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

end RequestProject.YangMills

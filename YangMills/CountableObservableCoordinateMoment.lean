import Mathlib
import YangMills.CountableObservableNormMomentContinuum

/-!
# Coordinate moments -> selected finite-prefix norm moments

The source RG/moment lane naturally gives scalar insertion bounds.  For the
countable selected observable family, the finite-product sup norm is bounded by
the sum of the absolute values of its coordinates.  Hence uniform scalar first
moments automatically give the finite-prefix coercive moment required by D3.

This is the exact adapter from source single-insertion moments to the projective
compactness compiler; it does not assume a separate m-dimensional estimate.
-/

open Set MeasureTheory

namespace RequestProject.YangMills

/-- Sum of the first `m` scalar moment budgets. -/
def finitePrefixCoordinateMomentBound
    (coordinateMomentBound : ℕ → ENNReal)
    (m : ℕ) : ENNReal :=
  ∑ i : Fin m, coordinateMomentBound i.1

/-- Sup norm of a finite real vector is bounded by the sum of coordinate absolute values. -/
theorem real_pi_norm_le_sum_abs
    {m : ℕ} (x : Fin m → ℝ) :
    ‖x‖ ≤ ∑ i : Fin m, |x i| := by
  have hsum : 0 ≤ ∑ i : Fin m, |x i| := by positivity
  rw [pi_norm_le_iff_of_nonneg hsum]
  intro i
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum
    (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)

/-- The ENNReal prefix norm cost is bounded by the sum of coordinate costs. -/
theorem real_finite_prefix_norm_cost_le_coordinate_sum
    {m : ℕ} (x : Fin m → ℝ) :
    realFinitePrefixNormCost m x ≤
      ∑ i : Fin m, ENNReal.ofReal |x i| := by
  unfold realFinitePrefixNormCost
  calc
    ENNReal.ofReal ‖x‖ ≤
        ENNReal.ofReal (∑ i : Fin m, |x i|) :=
      ENNReal.ofReal_le_ofReal (real_pi_norm_le_sum_abs x)
    _ = ∑ i : Fin m, ENNReal.ofReal |x i| := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i hi
      exact abs_nonneg _

/--
Source-facing scalar moment producer.  `coordinateUniformAbsMoment` is the
physical input supplied by a CMP119 insertion/exponential-moment theorem.
-/
structure RealCountableObservableCoordinateMomentSource
    (Ω : Type*) [MeasurableSpace Ω] where
  cutoffLaw : ℕ → ProbabilityMeasure Ω
  observable : ℕ → Ω → ℝ
  observableMeasurable : ∀ i, Measurable (observable i)
  coordinateMomentBound : ℕ → ENNReal
  coordinateUniformAbsMoment :
    ∀ (i k : ℕ),
      (∫⁻ x : Ω, ENNReal.ofReal |observable i x|
        ∂((cutoffLaw k : ProbabilityMeasure Ω) : Measure Ω)) ≤
      coordinateMomentBound i
  threshold :
    ∀ (m : ℕ) (ε : ENNReal), 0 < ε →
      ∃ R : ENNReal,
        R ≠ 0 ∧ R ≠ ⊤ ∧
          finitePrefixCoordinateMomentBound coordinateMomentBound m / R ≤ ε

namespace RealCountableObservableCoordinateMomentSource

/-- The automatically assembled m-dimensional moment budget. -/
def prefixMomentBound
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableCoordinateMomentSource Ω)
    (m : ℕ) : ENNReal :=
  finitePrefixCoordinateMomentBound source.coordinateMomentBound m

/-- Scalar source moments imply the source-native finite-prefix norm moment. -/
theorem uniform_prefix_norm_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableCoordinateMomentSource Ω)
    (m k : ℕ) :
    (∫⁻ x : Ω,
      realFinitePrefixNormCost m
        (countableObservablePrefix source.observable m x)
      ∂((source.cutoffLaw k : ProbabilityMeasure Ω) : Measure Ω)) ≤
      source.prefixMomentBound m := by
  calc
    (∫⁻ x : Ω,
      realFinitePrefixNormCost m
        (countableObservablePrefix source.observable m x)
      ∂((source.cutoffLaw k : ProbabilityMeasure Ω) : Measure Ω))
      ≤ ∫⁻ x : Ω,
          ∑ i : Fin m,
            ENNReal.ofReal |source.observable i.1 x|
          ∂((source.cutoffLaw k : ProbabilityMeasure Ω) : Measure Ω) := by
        apply lintegral_mono
        intro x
        exact real_finite_prefix_norm_cost_le_coordinate_sum
          (countableObservablePrefix source.observable m x)
    _ = ∑ i : Fin m,
          ∫⁻ x : Ω, ENNReal.ofReal |source.observable i.1 x|
            ∂((source.cutoffLaw k : ProbabilityMeasure Ω) : Measure Ω) := by
        rw [lintegral_finsetSum]
        intro i hi
        exact ((source.observableMeasurable i.1).abs.ennreal_ofReal).aemeasurable
    _ ≤ ∑ i : Fin m, source.coordinateMomentBound i.1 := by
        exact Finset.sum_le_sum fun i hi =>
          source.coordinateUniformAbsMoment i.1 k
    _ = source.prefixMomentBound m := rfl

/-- Compile scalar insertion moments directly to the full D3 norm-moment source. -/
noncomputable def toNormMomentSource
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableCoordinateMomentSource Ω) :
    RealCountableObservableNormMomentSource Ω where
  cutoffLaw := source.cutoffLaw
  observable := source.observable
  observableMeasurable := source.observableMeasurable
  momentBound := source.prefixMomentBound
  sourceUniformNormMoment := source.uniform_prefix_norm_moment
  threshold := by
    intro m ε hε
    exact source.threshold m ε hε

/-- Scalar insertion moments therefore construct the selected continuum law. -/
noncomputable def globalMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableCoordinateMomentSource Ω) :
    Measure (ℕ → ℝ) :=
  source.toNormMomentSource.globalMeasure

instance globalMeasureIsProbability
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableCoordinateMomentSource Ω) :
    IsProbabilityMeasure source.globalMeasure := by
  unfold globalMeasure
  infer_instance

end RealCountableObservableCoordinateMomentSource

end RequestProject.YangMills

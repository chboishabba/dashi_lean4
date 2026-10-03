import Mathlib
import YangMills.CountableObservableNormMomentContinuum

/-!
# Coordinate moments -> selected finite-prefix norm moments

The source RG/moment lane naturally gives scalar insertion bounds.  For the
countable selected observable family, the finite-product sup norm is bounded by
the sum of the absolute values of its coordinates.  Hence uniform scalar first
moments automatically give the finite-prefix coercive moment required by D3.

This is the exact adapter from source single-insertion moments to the projective
compactness compiler; it does not assume a separate m-dimensional estimate or
an independently supplied compactness threshold.
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

/-- Elementary Markov threshold for any finite ENNReal moment budget. -/
theorem finite_ennreal_moment_threshold
    (M : ENNReal) (hM : M ≠ ⊤)
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ R : ENNReal, R ≠ 0 ∧ R ≠ ⊤ ∧ M / R ≤ ε := by
  let R : ENNReal := M / ε + 1
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have hDivTop : M / ε ≠ ⊤ := ENNReal.div_ne_top hM hε0
  have hR0 : R ≠ 0 := by simp [R]
  have hRTop : R ≠ ⊤ := by
    simp [R, hDivTop]
  refine ⟨R, hR0, hRTop, ?_⟩
  by_cases hεTop : ε = ⊤
  · simp [hεTop]
  · apply (ENNReal.div_le_iff hR0 hRTop).2
    rw [show R = M / ε + 1 by rfl, mul_add,
      ENNReal.mul_div_cancel hε0 hεTop]
    exact le_add_right (le_refl M) ε

/--
Source-facing scalar moment producer.  `coordinateUniformAbsMoment` is the
physical input supplied by a CMP119 insertion/exponential-moment theorem.
Finiteness of each scalar budget is the only quantitative side condition.
-/
structure RealCountableObservableCoordinateMomentSource
    (Ω : Type*) [MeasurableSpace Ω] where
  cutoffLaw : ℕ → ProbabilityMeasure Ω
  observable : ℕ → Ω → ℝ
  observableMeasurable : ∀ i, Measurable (observable i)
  coordinateMomentBound : ℕ → ENNReal
  coordinateMomentBoundFinite : ∀ i, coordinateMomentBound i ≠ ⊤
  coordinateUniformAbsMoment :
    ∀ (i k : ℕ),
      (∫⁻ x : Ω, ENNReal.ofReal |observable i x|
        ∂((cutoffLaw k : ProbabilityMeasure Ω) : Measure Ω)) ≤
      coordinateMomentBound i

namespace RealCountableObservableCoordinateMomentSource

/-- The automatically assembled m-dimensional moment budget. -/
def prefixMomentBound
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableCoordinateMomentSource Ω)
    (m : ℕ) : ENNReal :=
  finitePrefixCoordinateMomentBound source.coordinateMomentBound m

/-- Every finite prefix budget is finite. -/
theorem prefixMomentBound_ne_top
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableCoordinateMomentSource Ω)
    (m : ℕ) : source.prefixMomentBound m ≠ ⊤ := by
  unfold prefixMomentBound finitePrefixCoordinateMomentBound
  exact ENNReal.sum_ne_top.2 fun i hi =>
    source.coordinateMomentBoundFinite i.1

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
        fun_prop
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
    exact finite_ennreal_moment_threshold
      (source.prefixMomentBound m)
      (source.prefixMomentBound_ne_top m) ε hε

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

/--
A stronger but often cheaper source interface: every selected scalar observable
has a cutoff-uniform pointwise bound.  This is enough to manufacture the scalar
first moments required above under *any* cutoff probability law, so bounded
Wilson/cylinder coordinates do not need a separate RG moment estimate merely to
obtain projective tightness.
-/
structure RealCountableObservableUniformBoundSource
    (Ω : Type*) [MeasurableSpace Ω] where
  cutoffLaw : ℕ → ProbabilityMeasure Ω
  observable : ℕ → Ω → ℝ
  observableMeasurable : ∀ i, Measurable (observable i)
  coordinateBound : ℕ → ℝ
  coordinateBoundNonneg : ∀ i, 0 ≤ coordinateBound i
  observableAbsLe : ∀ (i : ℕ) (x : Ω), |observable i x| ≤ coordinateBound i

namespace RealCountableObservableUniformBoundSource

/-- Pointwise bounded coordinates have the corresponding cutoff-uniform L1 budget. -/
theorem uniform_abs_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableUniformBoundSource Ω)
    (i k : ℕ) :
    (∫⁻ x : Ω, ENNReal.ofReal |source.observable i x|
      ∂((source.cutoffLaw k : ProbabilityMeasure Ω) : Measure Ω)) ≤
      ENNReal.ofReal (source.coordinateBound i) := by
  calc
    (∫⁻ x : Ω, ENNReal.ofReal |source.observable i x|
      ∂((source.cutoffLaw k : ProbabilityMeasure Ω) : Measure Ω))
      ≤ ∫⁻ _x : Ω, ENNReal.ofReal (source.coordinateBound i)
          ∂((source.cutoffLaw k : ProbabilityMeasure Ω) : Measure Ω) := by
        apply lintegral_mono
        intro x
        exact ENNReal.ofReal_le_ofReal (source.observableAbsLe i x)
    _ = ENNReal.ofReal (source.coordinateBound i) := by simp

/-- Bounded selected observables compile to the scalar-moment D3 source. -/
noncomputable def toCoordinateMomentSource
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableUniformBoundSource Ω) :
    RealCountableObservableCoordinateMomentSource Ω where
  cutoffLaw := source.cutoffLaw
  observable := source.observable
  observableMeasurable := source.observableMeasurable
  coordinateMomentBound := fun i => ENNReal.ofReal (source.coordinateBound i)
  coordinateMomentBoundFinite := by
    intro i
    simp
  coordinateUniformAbsMoment := source.uniform_abs_moment

/-- Hence bounded selected observables compile directly to the full norm-moment source. -/
noncomputable def toNormMomentSource
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableUniformBoundSource Ω) :
    RealCountableObservableNormMomentSource Ω :=
  source.toCoordinateMomentSource.toNormMomentSource

/-- And therefore to an actual probability law on the countable selected coordinates. -/
noncomputable def globalMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableUniformBoundSource Ω) :
    Measure (ℕ → ℝ) :=
  source.toCoordinateMomentSource.globalMeasure

instance globalMeasureIsProbability
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableUniformBoundSource Ω) :
    IsProbabilityMeasure source.globalMeasure := by
  unfold globalMeasure
  infer_instance

end RealCountableObservableUniformBoundSource

end RequestProject.YangMills

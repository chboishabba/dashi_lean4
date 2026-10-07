import Mathlib
import YangMills.CMP116WilsonMixedHalfRateClustering

open Filter MeasureTheory

/-!
# Mixed same-H Wilson half-rate and dense-span extension

R551 is mixed in the selected left/right Wilson observables.  Once those SAME
continuum covariances are identified with matrix coefficients of the SAME OS
transfer family, the half-rate holds on every generator pair.  Elementary
linearity then extends the rate to the real linear span of those Wilson vectors.

This is the exact algebraic bridge needed before a density/cyclicity receipt can
exclude hidden subgap spectral modes.  Density itself remains a physical
same-family theorem and is never inferred merely from clustering of a sparse
family.
-/

namespace RequestProject.YangMills

structure SameHWilsonMixedHalfRateWeld
    (State Obs H : Type*)
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  source : CMP116WilsonMixedHalfRateClusteringSource State Obs
  cutoffConverges : Tendsto source.cutoffLaw atTop (𝓝 source.continuumLaw)
  transfer : ℕ → H →L[ℝ] H
  vector : Obs → H
  sameCorrelation :
    ∀ left right time,
      |probabilityCovariance source.continuumLaw
          (source.wilson left) (source.timeTranslate right time)| =
        |⟪vector left, transfer time (vector right)⟫_ℝ|

namespace SameHWilsonMixedHalfRateWeld

/-- The literal mixed R551 half-rate is a bound on the SAME reconstructed transfer family. -/
theorem semigroup_mixed_half_rate
    {State Obs H : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (weld : SameHWilsonMixedHalfRateWeld State Obs H)
    (left right : Obs) (time : ℕ) :
    |⟪weld.vector left, weld.transfer time (weld.vector right)⟫_ℝ| ≤
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ time := by
  rw [← weld.sameCorrelation left right time]
  exact weld.source.continuum_mixed_half_rate
    weld.cutoffConverges left right time

end SameHWilsonMixedHalfRateWeld

/--
A pair of Hilbert vectors has the source half-rate when its matrix coefficient
is bounded by a vector-dependent nonnegative constant times `2^{-time}`.
Allowing the constant to depend on the pair is exactly what is needed for
closure under finite linear combinations.
-/
def HalfRateMatrixBound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : ℕ → H →L[ℝ] H) (left right : H) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ time : ℕ,
      |⟪left, T time right⟫_ℝ| ≤ C * (1 / 2 : ℝ) ^ time

/-- Zero in the left slot has the half-rate. -/
theorem halfRateMatrixBound_zero_left
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : ℕ → H →L[ℝ] H) (right : H) :
    HalfRateMatrixBound T 0 right := by
  refine ⟨0, le_rfl, ?_⟩
  intro time
  simp

/-- Zero in the right slot has the half-rate. -/
theorem halfRateMatrixBound_zero_right
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : ℕ → H →L[ℝ] H) (left : H) :
    HalfRateMatrixBound T left 0 := by
  refine ⟨0, le_rfl, ?_⟩
  intro time
  simp

/-- Half-rate bounds are closed under addition in the left slot. -/
theorem HalfRateMatrixBound.add_left
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : ℕ → H →L[ℝ] H} {left₁ left₂ right : H}
    (h₁ : HalfRateMatrixBound T left₁ right)
    (h₂ : HalfRateMatrixBound T left₂ right) :
    HalfRateMatrixBound T (left₁ + left₂) right := by
  rcases h₁ with ⟨C₁, hC₁, h₁⟩
  rcases h₂ with ⟨C₂, hC₂, h₂⟩
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, ?_⟩
  intro time
  calc
    |⟪left₁ + left₂, T time right⟫_ℝ|
        = |⟪left₁, T time right⟫_ℝ + ⟪left₂, T time right⟫_ℝ| := by
            rw [inner_add_left]
    _ ≤ |⟪left₁, T time right⟫_ℝ| + |⟪left₂, T time right⟫_ℝ| :=
          abs_add_le _ _
    _ ≤ C₁ * (1 / 2 : ℝ) ^ time + C₂ * (1 / 2 : ℝ) ^ time :=
          add_le_add (h₁ time) (h₂ time)
    _ = (C₁ + C₂) * (1 / 2 : ℝ) ^ time := by ring

/-- Half-rate bounds are closed under addition in the right slot. -/
theorem HalfRateMatrixBound.add_right
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : ℕ → H →L[ℝ] H} {left right₁ right₂ : H}
    (h₁ : HalfRateMatrixBound T left right₁)
    (h₂ : HalfRateMatrixBound T left right₂) :
    HalfRateMatrixBound T left (right₁ + right₂) := by
  rcases h₁ with ⟨C₁, hC₁, h₁⟩
  rcases h₂ with ⟨C₂, hC₂, h₂⟩
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, ?_⟩
  intro time
  calc
    |⟪left, T time (right₁ + right₂)⟫_ℝ|
        = |⟪left, T time right₁⟫_ℝ + ⟪left, T time right₂⟫_ℝ| := by
            rw [map_add, inner_add_right]
    _ ≤ |⟪left, T time right₁⟫_ℝ| + |⟪left, T time right₂⟫_ℝ| :=
          abs_add_le _ _
    _ ≤ C₁ * (1 / 2 : ℝ) ^ time + C₂ * (1 / 2 : ℝ) ^ time :=
          add_le_add (h₁ time) (h₂ time)
    _ = (C₁ + C₂) * (1 / 2 : ℝ) ^ time := by ring

/-- Half-rate bounds are closed under real scaling in the left slot. -/
theorem HalfRateMatrixBound.smul_left
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : ℕ → H →L[ℝ] H} {left right : H}
    (a : ℝ) (h : HalfRateMatrixBound T left right) :
    HalfRateMatrixBound T (a • left) right := by
  rcases h with ⟨C, hC, h⟩
  refine ⟨|a| * C, mul_nonneg (abs_nonneg a) hC, ?_⟩
  intro time
  calc
    |⟪a • left, T time right⟫_ℝ|
        = |a| * |⟪left, T time right⟫_ℝ| := by
            rw [real_inner_smul_left, abs_mul]
    _ ≤ |a| * (C * (1 / 2 : ℝ) ^ time) :=
          mul_le_mul_of_nonneg_left (h time) (abs_nonneg a)
    _ = (|a| * C) * (1 / 2 : ℝ) ^ time := by ring

/-- Half-rate bounds are closed under real scaling in the right slot. -/
theorem HalfRateMatrixBound.smul_right
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : ℕ → H →L[ℝ] H} {left right : H}
    (a : ℝ) (h : HalfRateMatrixBound T left right) :
    HalfRateMatrixBound T left (a • right) := by
  rcases h with ⟨C, hC, h⟩
  refine ⟨|a| * C, mul_nonneg (abs_nonneg a) hC, ?_⟩
  intro time
  calc
    |⟪left, T time (a • right)⟫_ℝ|
        = |a| * |⟪left, T time right⟫_ℝ| := by
            rw [map_smul, real_inner_smul_right, abs_mul]
    _ ≤ |a| * (C * (1 / 2 : ℝ) ^ time) :=
          mul_le_mul_of_nonneg_left (h time) (abs_nonneg a)
    _ = (|a| * C) * (1 / 2 : ℝ) ^ time := by ring

/--
Mixed half-rate bounds on every selected Wilson-generator pair extend to every
pair in the real linear span.  This uses mathlib's binary span induction, so
both variables stay tied to the SAME generator family throughout the proof.
-/
theorem halfRateMatrixBound_of_mem_span
    {Obs H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : ℕ → H →L[ℝ] H) (vector : Obs → H)
    (hgen : ∀ i j, HalfRateMatrixBound T (vector i) (vector j))
    {left right : H}
    (hleft : left ∈ Submodule.span ℝ (Set.range vector))
    (hright : right ∈ Submodule.span ℝ (Set.range vector)) :
    HalfRateMatrixBound T left right := by
  refine Submodule.span_induction₂
    (s := Set.range vector) (t := Set.range vector)
    ?mem_mem ?zero_left ?zero_right ?add_left ?add_right ?smul_left ?smul_right
    hleft hright
  · intro x y hx hy
    rcases hx with ⟨i, rfl⟩
    rcases hy with ⟨j, rfl⟩
    exact hgen i j
  · intro y _
    exact halfRateMatrixBound_zero_left T y
  · intro x _
    exact halfRateMatrixBound_zero_right T x
  · intro x y z _ _ _ hx hy
    exact hx.add_left hy
  · intro x y z _ _ _ hy hz
    exact hy.add_right hz
  · intro a x y _ _ hx
    exact hx.smul_left a
  · intro a x y _ _ hx
    exact hx.smul_right a

/-- Every mixed same-H R551 weld supplies generator-pair half-rate bounds. -/
theorem SameHWilsonMixedHalfRateWeld.generator_half_rate
    {State Obs H : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (weld : SameHWilsonMixedHalfRateWeld State Obs H)
    (left right : Obs) :
    HalfRateMatrixBound weld.transfer (weld.vector left) (weld.vector right) := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro time
  exact weld.semigroup_mixed_half_rate left right time

/--
The exact strengthened F1/F2 producer: mixed R551 clustering is welded to the
same transfer family and the span of those SAME Wilson vectors is dense.
-/
structure SameHDenseWilsonMixedHalfRateWeld
    (State Obs H : Type*)
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    extends SameHWilsonMixedHalfRateWeld State Obs H where
  denseWilsonSpan : Dense (Submodule.span ℝ (Set.range vector) : Set H)

namespace SameHDenseWilsonMixedHalfRateWeld

/-- Every pair in the dense Wilson span obeys the same exponential rate. -/
theorem span_half_rate
    {State Obs H : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (weld : SameHDenseWilsonMixedHalfRateWeld State Obs H)
    {left right : H}
    (hleft : left ∈ Submodule.span ℝ (Set.range weld.vector))
    (hright : right ∈ Submodule.span ℝ (Set.range weld.vector)) :
    HalfRateMatrixBound weld.transfer left right :=
  halfRateMatrixBound_of_mem_span
    weld.transfer weld.vector weld.toSameHWilsonMixedHalfRateWeld.generator_half_rate
    hleft hright

/-- The half-rate-controlled Wilson span is genuinely dense in the same Hilbert sector. -/
theorem dense_span
    {State Obs H : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (weld : SameHDenseWilsonMixedHalfRateWeld State Obs H) :
    Dense (Submodule.span ℝ (Set.range weld.vector) : Set H) :=
  weld.denseWilsonSpan

end SameHDenseWilsonMixedHalfRateWeld

end RequestProject.YangMills

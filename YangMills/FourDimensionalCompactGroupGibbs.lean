import Mathlib
import Mathlib.MeasureTheory.Measure.Tilted
import YangMills.FourDimensionalCompactGroupHaar

/-!
# Genuine finite 4D compact-group Wilson Gibbs probability

This consumes the actual native normalized Haar probability on the 4D
link-configuration GROUP from FourDimensionalCompactGroupHaar, not
an independently selected abstract Haar integration functional.

For any compact Hausdorff topological group G and any nonnegative
conjugacy-class plaquette cost in [0,2], the pure Wilson Boltzmann
weight is in (0,1].  Thus its density is automatically integrable
under the normalized link Haar law whenever the selected action is
measurable, and the exponential tilt is a genuine probability measure.

The complete E/R/boundary/vacuum model is included separately, with
each sector visible.  It requires a finite lower estimate for all
four sectors; there is no assumption that they vanish or are negligible.

These are finite SU(N)/other-group mathematical results, not a proof
of cutoff-uniform compactness, continuum OS positivity, Clay H5
quantitative estimates, or correspondence with CMP119's published
renormalized action.
-/

namespace RequestProject.YangMills

def fourDimensionalCompleteGroupAction
    {G : Type*} [Group G] (L : ℕ) [NeZero L]
    (classCost : G → ℝ)
    (β : ℝ)
    (regular rOperation boundary vacuum :
      FourDimensionalGroupLinks G L → ℝ)
    (links : FourDimensionalGroupLinks G L) : ℝ :=
  fourDimensionalClassAction L classCost links β +
    regular links + rOperation links + boundary links + vacuum links

def fourDimensionalGroupCompleteWeight
    {G : Type*} [Group G] (L : ℕ) [NeZero L]
    (classCost : G → ℝ)
    (β : ℝ)
    (regular rOperation boundary vacuum :
      FourDimensionalGroupLinks G L → ℝ)
    (links : FourDimensionalGroupLinks G L) : ℝ :=
  Real.exp (-(fourDimensionalCompleteGroupAction L
    classCost β regular rOperation boundary vacuum links))

theorem finite_compact_group_wilson_weight_bounded
    {G : Type*} [Group G]
    (L : ℕ) [NeZero L]
    (classCost : G → ℝ)
    (hCost : ∀ U : G, 0 ≤ classCost U ∧ classCost U ≤ 2)
    (β : ℝ) (hβ : 0 ≤ β)
    (links : FourDimensionalGroupLinks G L) :
    0 < Real.exp (-(fourDimensionalClassAction
        L classCost links β)) ∧
    Real.exp (-(fourDimensionalClassAction
        L classCost links β)) ≤ 1 := by
  constructor
  · exact Real.exp_pos _
  · rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr
      (neg_nonpos.mpr
        (four_dimensional_class_action_bounds
          L classCost hCost links β hβ).1)

/--
From Haar existence and a positive finite Wilson cost, construct the
native finite probability measure directly, without an external
partition function or probability normalization field.
-/
noncomputable def finiteFourDimensionalWilsonProbability
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L]
    (classCost : G → ℝ)
    (hCost : ∀ U : G, 0 ≤ classCost U ∧ classCost U ≤ 2)
    (β : ℝ) (hβ : 0 ≤ β)
    (hMeasurable :
      Measurable (fun links : FourDimensionalGroupLinks G L =>
        Real.exp (-(fourDimensionalClassAction
          L classCost links β)))) :
    MeasureTheory.ProbabilityMeasure (FourDimensionalGroupLinks G L) := by
  let haar := fourDimensionalNativeLinkHaar G L
  have hIntegrable :
      MeasureTheory.Integrable
        (fun links : FourDimensionalGroupLinks G L =>
          Real.exp (-(fourDimensionalClassAction
            L classCost links β)))
        ((haar : MeasureTheory.ProbabilityMeasure
            (FourDimensionalGroupLinks G L)) :
          MeasureTheory.Measure (FourDimensionalGroupLinks G L)) := by
    apply MeasureTheory.Integrable.of_bound
      hMeasurable.aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro links
    rw [Real.norm_eq_abs, abs_of_pos
      (finite_compact_group_wilson_weight_bounded
        L classCost hCost β hβ links).1]
    exact (finite_compact_group_wilson_weight_bounded
      L classCost hCost β hβ links).2
  haveI : NeZero
      ((haar : MeasureTheory.ProbabilityMeasure
          (FourDimensionalGroupLinks G L)) :
        MeasureTheory.Measure (FourDimensionalGroupLinks G L)) :=
    inferInstance
  exact ⟨(((haar : MeasureTheory.ProbabilityMeasure
      (FourDimensionalGroupLinks G L)) :
      MeasureTheory.Measure (FourDimensionalGroupLinks G L)).tilted
      (fun links => -(fourDimensionalClassAction
        L classCost links β))),
    MeasureTheory.isProbabilityMeasure_tilted hIntegrable⟩

/--
Full CMP119-style five-sector finite probability on a genuine compact
group link Haar carrier. The condition is integrability of the ENTIRE
selected action, rather than of the Wilson term alone.
-/
noncomputable def finiteFourDimensionalCompleteProbability
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L]
    (classCost : G → ℝ)
    (β : ℝ)
    (regular rOperation boundary vacuum :
      FourDimensionalGroupLinks G L → ℝ)
    (hIntegrable :
      MeasureTheory.Integrable
        (fourDimensionalGroupCompleteWeight L classCost β
          regular rOperation boundary vacuum)
        (((fourDimensionalNativeLinkHaar G L) :
            MeasureTheory.ProbabilityMeasure
              (FourDimensionalGroupLinks G L)) :
          MeasureTheory.Measure (FourDimensionalGroupLinks G L))) :
    MeasureTheory.ProbabilityMeasure (FourDimensionalGroupLinks G L) := by
  let haar := fourDimensionalNativeLinkHaar G L
  haveI : NeZero
      ((haar : MeasureTheory.ProbabilityMeasure
          (FourDimensionalGroupLinks G L)) :
        MeasureTheory.Measure (FourDimensionalGroupLinks G L)) :=
    inferInstance
  exact ⟨(((haar : MeasureTheory.ProbabilityMeasure
      (FourDimensionalGroupLinks G L)) :
      MeasureTheory.Measure (FourDimensionalGroupLinks G L)).tilted
      (fun links =>
        -(fourDimensionalCompleteGroupAction L classCost β
          regular rOperation boundary vacuum links))),
    MeasureTheory.isProbabilityMeasure_tilted hIntegrable⟩

end RequestProject.YangMills

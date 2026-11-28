import Mathlib
import Mathlib.MeasureTheory.Measure.Tilted
import YangMills.LiteralSU2FourDimensionalLattice
import YangMills.LiteralSU2FiniteWilson

/-!
# Native finite Gibbs probability on the actual four-dimensional SU(2) link field

Unlike the earlier real expectation-only carrier, this module constructs
a genuine Mathlib `ProbabilityMeasure` on the finite four-dimensional
link configuration type, from exp(-S_complete) and ONE supplied normalized
reference probability measure.  The exponential tilt automatically uses
the same normalization denominator as the complete source action.

This removes a type-level obstruction to applying the native Prokhorov
theorems: finite lattice Gibbs distributions are now actual
`ProbabilityMeasure` values, not merely opaque normalized expectation
functionals.

The reference must still be identified with the LINK PRODUCT HAAR law
on a topological SU(2) group, and the action with the actual published
CMP119 finite functional.  Cutoff-uniform coercive estimates, weak
compactness and finite OS positivity are NOT established here.
-/

namespace RequestProject.YangMills

/-- Literal four-dimensional exponential weight including all sectors. -/
def su2FourDimensionalCompleteWeight (L : ℕ) [NeZero L]
    (links : SU2TorusLinks L) (β : ℝ)
    (regular rOperation boundary vacuum : SU2TorusLinks L → ℝ) : ℝ :=
  Real.exp (-(su2FourDimensionalCompleteAction L links β
    regular rOperation boundary vacuum))

theorem su2_four_dimensional_complete_weight_positive
    (L : ℕ) [NeZero L] (links : SU2TorusLinks L) (β : ℝ)
    (regular rOperation boundary vacuum : SU2TorusLinks L → ℝ) :
    0 < su2FourDimensionalCompleteWeight L links β
      regular rOperation boundary vacuum := by
  unfold su2FourDimensionalCompleteWeight
  exact Real.exp_pos _

/--
The actual finite SU(2) normalized Gibbs measure, in Mathlib's native
probability-measure representation, via exponential tilting of the
selected reference measure by the FULL five-sector lattice action.

This is a construction, not a postulated probability.  Integrability
is required explicitly; the next theorem proves it whenever the
four additional sectors have finite lower bounds.
-/
noncomputable def su2NativeFiniteGibbsProbability
    (L : ℕ) [NeZero L]
    (haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L))
    (β : ℝ)
    (regular rOperation boundary vacuum : SU2TorusLinks L → ℝ)
    (hWeightIntegrable :
      MeasureTheory.Integrable
        (su2FourDimensionalCompleteWeight L · β
          regular rOperation boundary vacuum)
        ((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L))) :
    MeasureTheory.ProbabilityMeasure (SU2TorusLinks L) :=
  ⟨((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
        MeasureTheory.Measure (SU2TorusLinks L)).tilted
      (fun links =>
        -(su2FourDimensionalCompleteAction L links β
          regular rOperation boundary vacuum)),
    by
      haveI : NeZero
          ((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
            MeasureTheory.Measure (SU2TorusLinks L)) := inferInstance
      exact MeasureTheory.isProbabilityMeasure_tilted hWeightIntegrable⟩

/--
Pointwise lower bounds on the actual four additional sectors prove
integrability of the full exponential Gibbs weight on each finite
four-dimensional torus, for ANY normalized reference probability law.

This is explicitly cutoff-dependent: the sector lower bounds may grow
without limit along the CMP119 ultraviolet/volume trajectory.
-/
theorem su2_native_complete_weight_integrable
    (L : ℕ) [NeZero L]
    (haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L))
    (β : ℝ) (hβ : 0 ≤ β)
    (regular rOperation boundary vacuum : SU2TorusLinks L → ℝ)
    (Kregular Kr Kboundary Kv : ℝ)
    (hRegular : ∀ links, -Kregular ≤ regular links)
    (hR : ∀ links, -Kr ≤ rOperation links)
    (hBoundary : ∀ links, -Kboundary ≤ boundary links)
    (hVacuum : ∀ links, -Kv ≤ vacuum links)
    (hMeasurable :
      Measurable (su2FourDimensionalCompleteWeight L · β
        regular rOperation boundary vacuum)) :
    MeasureTheory.Integrable
      (su2FourDimensionalCompleteWeight L · β
        regular rOperation boundary vacuum)
      ((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
        MeasureTheory.Measure (SU2TorusLinks L)) := by
  apply MeasureTheory.Integrable.of_bound
    hMeasurable.aestronglyMeasurable
    (Real.exp (Kregular + Kr + Kboundary + Kv))
  apply Filter.Eventually.of_forall
  intro links
  have hUpper :
      su2FourDimensionalCompleteWeight L links β
        regular rOperation boundary vacuum ≤
        Real.exp (Kregular + Kr + Kboundary + Kv) := by
    unfold su2FourDimensionalCompleteWeight
    apply Real.exp_le_exp.mpr
    have hWilson :=
      (su2_four_dimensional_wilson_action_bounds
        L links β hβ).1
    have hSource :
      -(Kregular + Kr + Kboundary + Kv) ≤
      su2FourDimensionalCompleteAction L links β
        regular rOperation boundary vacuum := by
      dsimp [su2FourDimensionalCompleteAction]
      linarith [hRegular links, hR links,
        hBoundary links, hVacuum links]
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg
    (su2_four_dimensional_complete_weight_positive
      L links β regular rOperation boundary vacuum).le]
  exact hUpper

/--
The native finite `ProbabilityMeasure` integrates the SAME Gibbs
weight and action used in the real finite partition/expectation lane.

This equality is based on Mathlib's exponential-tilt integration lemma.
It is not a new independently normalized probability measure.
-/
theorem su2_native_complete_expectation_is_gibbs_ratio
    (L : ℕ) [NeZero L]
    (haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L))
    (β : ℝ)
    (regular rOperation boundary vacuum : SU2TorusLinks L → ℝ)
    (hWeightIntegrable :
      MeasureTheory.Integrable
        (su2FourDimensionalCompleteWeight L · β
          regular rOperation boundary vacuum)
        ((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L)))
    (observable : SU2TorusLinks L → ℝ) :
    (∫ links : SU2TorusLinks L, observable links
        ∂((su2NativeFiniteGibbsProbability L haar β
          regular rOperation boundary vacuum hWeightIntegrable :
          MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L))) =
    (∫ links : SU2TorusLinks L,
        su2FourDimensionalCompleteWeight L links β
          regular rOperation boundary vacuum * observable links
        ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L))) /
    (∫ links : SU2TorusLinks L,
        su2FourDimensionalCompleteWeight L links β
          regular rOperation boundary vacuum
        ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L))) := by
  change
    (∫ links : SU2TorusLinks L, observable links
      ∂(((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L)).tilted
            (fun links => -(su2FourDimensionalCompleteAction L
              links β regular rOperation boundary vacuum)))) = _
  rw [MeasureTheory.integral_tilted]
  simp only [smul_eq_mul]
  simp_rw [div_mul_eq_mul_div]
  rw [MeasureTheory.integral_div]
  rfl

end RequestProject.YangMills

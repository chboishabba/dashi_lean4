import Mathlib
import YangMills.CMP119SelectedSourceInstantiation
import YangMills.LiteralSU2NativeGibbsProbability

/-!
# Selected CMP119 complete action and native Gibbs probability

The native finite Gibbs constructor already uses the literal four-dimensional
Wilson action plus four supplied residual sectors.  On a selected CMP119 source
instantiation, choose those four sectors to be the SAME literal E/R/B/V
functions carried by the source dictionary.  The existing dictionary theorem
then identifies their sum with the selected source residual.

Thus the complete literal action, exponential density and native tilted
probability all use one source object.  This pays the C-level representation
debt; it does not construct the missing source instantiation or the remaining
BC reflection certificates.
-/

namespace RequestProject.YangMills

/-- Complete selected CMP119 action on the literal `2*n` SU(2) link carrier. -/
def selectedCMP119CompleteAction
    {n : ℕ} [NeZero n]
    (source : CMP119SelectedSourceInstantiation n)
    (β : ℝ) (links : SU2TorusLinks (2 * n)) : ℝ :=
  su2FourDimensionalCompleteAction (2 * n) links β
    source.residual.literalRegular
    source.residual.literalROperation
    source.residual.literalBoundary
    source.residual.literalVacuum

/-- The selected complete action is literally Wilson plus the selected source residual. -/
theorem selected_cmp119_complete_action_eq_wilson_add_source_residual
    {n : ℕ} [NeZero n]
    (source : CMP119SelectedSourceInstantiation n)
    (β : ℝ) (links : SU2TorusLinks (2 * n)) :
    selectedCMP119CompleteAction source β links =
      su2FourDimensionalWilsonAction (2 * n) links β +
        source.residual.sourceResidual links := by
  unfold selectedCMP119CompleteAction su2FourDimensionalCompleteAction
  have hResidual := source.literal_residual_eq_source links
  dsimp [su2FullResidual] at hResidual
  linarith

/-- Exponential weight of the exact selected complete action. -/
def selectedCMP119CompleteWeight
    {n : ℕ} [NeZero n]
    (source : CMP119SelectedSourceInstantiation n)
    (β : ℝ) (links : SU2TorusLinks (2 * n)) : ℝ :=
  Real.exp (-(selectedCMP119CompleteAction source β links))

/-- The literal selected Gibbs weight is the exponential of Wilson plus the same source residual. -/
theorem selected_cmp119_complete_weight_eq_source_density
    {n : ℕ} [NeZero n]
    (source : CMP119SelectedSourceInstantiation n)
    (β : ℝ) (links : SU2TorusLinks (2 * n)) :
    selectedCMP119CompleteWeight source β links =
      Real.exp (-(su2FourDimensionalWilsonAction (2 * n) links β +
        source.residual.sourceResidual links)) := by
  simp only [selectedCMP119CompleteWeight]
  rw [selected_cmp119_complete_action_eq_wilson_add_source_residual]

/--
The selected source law as Mathlib's native exponential tilt of one supplied
normalized reference law.  Supplying the reference is intentional: identifying
it with the source product-Haar convention is a separate same-object theorem.
-/
noncomputable def selectedCMP119NativeGibbsProbability
    {n : ℕ} [NeZero n]
    (source : CMP119SelectedSourceInstantiation n)
    (haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks (2 * n)))
    (β : ℝ)
    (hWeightIntegrable :
      MeasureTheory.Integrable
        (selectedCMP119CompleteWeight source β)
        ((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks (2 * n))) :
          MeasureTheory.Measure (SU2TorusLinks (2 * n)))) :
    MeasureTheory.ProbabilityMeasure (SU2TorusLinks (2 * n)) := by
  have hLiteralIntegrable :
      MeasureTheory.Integrable
        (su2FourDimensionalCompleteWeight (2 * n) · β
          source.residual.literalRegular
          source.residual.literalROperation
          source.residual.literalBoundary
          source.residual.literalVacuum)
        ((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks (2 * n))) :
          MeasureTheory.Measure (SU2TorusLinks (2 * n))) := by
    simpa [selectedCMP119CompleteWeight, selectedCMP119CompleteAction,
      su2FourDimensionalCompleteWeight] using hWeightIntegrable
  exact su2NativeFiniteGibbsProbability (2 * n) haar β
    source.residual.literalRegular
    source.residual.literalROperation
    source.residual.literalBoundary
    source.residual.literalVacuum
    hLiteralIntegrable

/--
The selected native probability has exactly the existing complete-action Gibbs
ratio.  There is no second action or normalization denominator.
-/
theorem selected_cmp119_native_expectation_is_source_gibbs_ratio
    {n : ℕ} [NeZero n]
    (source : CMP119SelectedSourceInstantiation n)
    (haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks (2 * n)))
    (β : ℝ)
    (hWeightIntegrable :
      MeasureTheory.Integrable
        (selectedCMP119CompleteWeight source β)
        ((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks (2 * n))) :
          MeasureTheory.Measure (SU2TorusLinks (2 * n))))
    (observable : SU2TorusLinks (2 * n) → ℝ) :
    (∫ links, observable links
      ∂((selectedCMP119NativeGibbsProbability source haar β hWeightIntegrable :
        MeasureTheory.ProbabilityMeasure (SU2TorusLinks (2 * n))) :
        MeasureTheory.Measure (SU2TorusLinks (2 * n)))) =
      (∫ links,
          selectedCMP119CompleteWeight source β links * observable links
        ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks (2 * n))) :
          MeasureTheory.Measure (SU2TorusLinks (2 * n)))) /
      (∫ links,
          selectedCMP119CompleteWeight source β links
        ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks (2 * n))) :
          MeasureTheory.Measure (SU2TorusLinks (2 * n))) := by
  have hLiteralIntegrable :
      MeasureTheory.Integrable
        (su2FourDimensionalCompleteWeight (2 * n) · β
          source.residual.literalRegular
          source.residual.literalROperation
          source.residual.literalBoundary
          source.residual.literalVacuum)
        ((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks (2 * n))) :
          MeasureTheory.Measure (SU2TorusLinks (2 * n))) := by
    simpa [selectedCMP119CompleteWeight, selectedCMP119CompleteAction,
      su2FourDimensionalCompleteWeight] using hWeightIntegrable
  simpa [selectedCMP119NativeGibbsProbability,
    selectedCMP119CompleteWeight, selectedCMP119CompleteAction,
    su2FourDimensionalCompleteWeight] using
    su2_native_complete_expectation_is_gibbs_ratio
      (2 * n) haar β
      source.residual.literalRegular
      source.residual.literalROperation
      source.residual.literalBoundary
      source.residual.literalVacuum
      hLiteralIntegrable observable

end RequestProject.YangMills

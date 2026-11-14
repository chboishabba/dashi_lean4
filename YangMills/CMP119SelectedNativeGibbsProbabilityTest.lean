import Mathlib
import YangMills.CMP119SelectedNativeGibbsProbability

namespace RequestProject.YangMills

example
    {n : ℕ} [NeZero n]
    (source : CMP119SelectedSourceInstantiation n)
    (β : ℝ) (links : SU2TorusLinks (2 * n)) :
    selectedCMP119CompleteAction source β links =
      su2FourDimensionalWilsonAction (2 * n) links β +
        source.residual.sourceResidual links :=
  selected_cmp119_complete_action_eq_wilson_add_source_residual source β links

example
    {n : ℕ} [NeZero n]
    (source : CMP119SelectedSourceInstantiation n)
    (β : ℝ) (links : SU2TorusLinks (2 * n)) :
    selectedCMP119CompleteWeight source β links =
      Real.exp (-(su2FourDimensionalWilsonAction (2 * n) links β +
        source.residual.sourceResidual links)) :=
  selected_cmp119_complete_weight_eq_source_density source β links

end RequestProject.YangMills

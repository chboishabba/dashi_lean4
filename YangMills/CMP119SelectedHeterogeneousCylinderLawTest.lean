import Mathlib
import YangMills.CMP119SelectedHeterogeneousCylinderLaw

open MeasureTheory

namespace RequestProject.YangMills

example
    (cutoff : ∀ k : ℕ, CMP119SelectedPhysicalCutoff (k + 1))
    (raw : ∀ k : ℕ, ℕ → SU2TorusLinks (2 * (k + 1)) → ℝ)
    (hMeas : ∀ k i, Measurable (raw k i)) :
    ℕ → ProbabilityMeasure HeterogeneousWilsonCylinderState :=
  selectedCMP119HeterogeneousCylinderCutoffLaw cutoff raw hMeas

end RequestProject.YangMills

import Mathlib
import YangMills.CMP119SelectedCanonicalGibbsProbability

open MeasureTheory

namespace RequestProject.YangMills

example
    {n : ℕ} [NeZero n]
    (source : CMP119SelectedSourceInstantiation n)
    (β : ℝ)
    (hWeightIntegrable :
      Integrable (selectedCMP119CompleteWeight source β)
        (((literalSU2ProductLinkHaar (2 * n) :
          ProbabilityMeasure (SU2TorusLinks (2 * n))) :
          Measure (SU2TorusLinks (2 * n))))) :
    ProbabilityMeasure (SU2TorusLinks (2 * n)) :=
  selectedCMP119CanonicalGibbsProbability source β hWeightIntegrable

end RequestProject.YangMills

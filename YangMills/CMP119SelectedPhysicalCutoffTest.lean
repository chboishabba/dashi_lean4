import Mathlib
import YangMills.CMP119SelectedPhysicalCutoff

open MeasureTheory

namespace RequestProject.YangMills

example
    {n : ℕ} [NeZero n]
    (cutoff : CMP119SelectedPhysicalCutoff n) :
    cutoff.beta = 4 * cutoff.sourceInverseCoupling :=
  cutoff.beta_eq_four_mul_sourceInverseCoupling

example
    {n : ℕ} [NeZero n]
    (cutoff : CMP119SelectedPhysicalCutoff n) :
    ProbabilityMeasure (SU2TorusLinks (2 * n)) :=
  cutoff.gibbsLaw

end RequestProject.YangMills

import YangMills.LiteralSU2PositiveHalfAnalytic

open MeasureTheory

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n]
    (β : ℝ) :
    Measurable (fun links : SU2TorusLinks (2 * n) =>
      su2EvenTimePositiveWilsonHalf n links β) :=
  su2_positive_half_measurable n β

example
    (n : ℕ) [NeZero n]
    (β : ℝ) (hβ : 0 ≤ β)
    (links : SU2TorusLinks (2 * n)) :
    0 < su2EvenTimePositiveWilsonHalf n links β ∧
      su2EvenTimePositiveWilsonHalf n links β ≤ 1 :=
  su2_positive_half_pos_le_one n β hβ links

end RequestProject.YangMills

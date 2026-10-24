import Synthesis.RiemannG21PositivePlateauMoment

/-! RED-first regression contract for the literal positive-plateau odd compiler. -/

open MeasureTheory Set

namespace Synthesis

example {w : ℝ → ℝ} {a p R l m r : ℝ}
    (ha : 0 < a) (hap : a < p)
    (hl : 0 < l) (hlm : l < m) (hmr : m < r) (hrR : r < R)
    (hwNonneg : ∀ x ∈ Icc (0:ℝ) R, 0 <= w x)
    (hwPos : ∀ x ∈ Ioo l r, 0 < w x)
    (hA : Integrable (g21OddMomentWeight R w a) volume)
    (hP : Integrable (g21OddMomentWeight R w p) volume)
    (hqA : Integrable (fun x => x^2 * g21OddMomentWeight R w a x) volume)
    (hqP : Integrable (fun x => x^2 * g21OddMomentWeight R w p x) volume) :
    0 < moment0 (g21OddMomentWeight R w a) volume
          * momentQ (fun x => x^2) (g21OddMomentWeight R w p) volume
        - momentQ (fun x => x^2) (g21OddMomentWeight R w a) volume
          * moment0 (g21OddMomentWeight R w p) volume := by
  exact oddMomentCrossProduct_pos_of_positivePlateau
    ha hap hl hlm hmr hrR hwNonneg hwPos hA hP hqA hqP

end Synthesis

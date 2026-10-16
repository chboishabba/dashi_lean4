import Synthesis.RiemannG21PositivePlateauMoment

/-! RED-first regression contract for the positive-plateau continuum compiler. -/

open MeasureTheory Set

namespace Synthesis

example {w : ℝ → ℝ} {a p R l m r : ℝ}
    (ha : 0 < a) (hap : a < p)
    (hl : 0 < l) (hlm : l < m) (hmr : m < r) (hrR : r < R)
    (hwNonneg : ∀ x ∈ Icc (0:ℝ) R, 0 <= w x)
    (hwPos : ∀ x ∈ Ioo l r, 0 < w x)
    (hA : Integrable (fun x => g21ClippedWeight R w x * Real.sinh (a*x)) volume)
    (hP : Integrable (fun x => g21ClippedWeight R w x * Real.sinh (p*x)) volume)
    (hqA : Integrable (fun x => x^2 * (g21ClippedWeight R w x * Real.sinh (a*x))) volume)
    (hqP : Integrable (fun x => x^2 * (g21ClippedWeight R w x * Real.sinh (p*x))) volume) :
    0 < moment0 (fun x => g21ClippedWeight R w x * Real.sinh (a*x)) volume
          * momentQ (fun x => x^2) (fun x => g21ClippedWeight R w x * Real.sinh (p*x)) volume
        - momentQ (fun x => x^2) (fun x => g21ClippedWeight R w x * Real.sinh (a*x)) volume
          * moment0 (fun x => g21ClippedWeight R w x * Real.sinh (p*x)) volume := by
  exact oddMomentCrossProduct_pos_of_positivePlateau
    ha hap hl hlm hmr hrR hwNonneg hwPos hA hP hqA hqP

end Synthesis

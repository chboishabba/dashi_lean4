import Synthesis.RiemannG21OddContinuumToRadius

/-! RED-first regression for continuum odd sign -> explicit admissible radius. -/

open MeasureTheory Set

namespace Synthesis

example {w : ℝ → ℝ} {a p R l m r : ℝ}
    (ha : 0 < a) (hap : a < p)
    (hl : 0 < l) (hlm : l < m) (hmr : m < r) (hrR : r < R)
    (hwNonneg : ∀ x ∈ Icc (0:ℝ) R, 0 <= w x)
    (hwPos : ∀ x ∈ Ioo l r, 0 < w x)
    (hAa : Integrable (oddHeightWeight R w a) volume)
    (hAp : Integrable (oddHeightWeight R w p) volume)
    (hQa : Integrable (fun x => x^2 * oddHeightWeight R w a x) volume)
    (hQp : Integrable (fun x => x^2 * oddHeightWeight R w p x) volume) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ <= 1 ∧
      g21OddSupportPolynomial R * ρ^2 <
        900 * (oddRatio R w p - oddRatio R w a) := by
  exact exists_unit_oddRadiusGate_of_positivePlateau
    ha hap hl hlm hmr hrR hwNonneg hwPos hAa hAp hQa hQp

end Synthesis

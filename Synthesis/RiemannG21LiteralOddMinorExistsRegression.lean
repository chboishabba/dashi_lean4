import Synthesis.RiemannG21LiteralOddMinorExists

open MeasureTheory Set

namespace Synthesis

example {w : ℝ → ℝ} {a p R l m r0 : ℝ}
    (ha : 0 < a) (hap : a < p)
    (hl : 0 < l) (hlm : l < m) (hmr : m < r0) (hrR : r0 < R)
    (hwNonneg : ∀ x ∈ Icc (0:ℝ) R, 0 <= w x)
    (hwPos : ∀ x ∈ Ioo l r0, 0 < w x)
    (h1a : Integrable (oddHeightWeight R w a) volume)
    (h3a : Integrable (fun x => x^2 * oddHeightWeight R w a x) volume)
    (h5a : Integrable (fun x => x^4 * oddHeightWeight R w a x) volume)
    (h1p : Integrable (oddHeightWeight R w p) volume)
    (h3p : Integrable (fun x => x^2 * oddHeightWeight R w p x) volume)
    (h5p : Integrable (fun x => x^4 * oddHeightWeight R w p x) volume) :
    ∃ r : ℝ, 0 < r ∧ r <= 1 ∧ literalOddFiniteDeterminant R w a p r < 0 := by
  exact exists_literalOddFiniteDeterminant_neg_of_positivePlateau
    ha hap hl hlm hmr hrR hwNonneg hwPos h1a h3a h5a h1p h3p h5p

end Synthesis

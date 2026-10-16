import Synthesis.RiemannG21EvenFiniteMinorExists

open MeasureTheory Set

namespace Synthesis

example {w : ℝ → ℝ} {a p R l m r0 : ℝ}
    (ha : 0 < a) (hap : a < p)
    (hl : 0 < l) (hlm : l < m) (hmr : m < r0) (hrR : r0 < R)
    (hwNonneg : ∀ x ∈ Icc (0:ℝ) R, 0 <= w x)
    (hwPos : ∀ x ∈ Ioo l r0, 0 < w x)
    (h0a : Integrable (evenHeightWeight R w a) volume)
    (h2a : Integrable (fun x => x^2 * evenHeightWeight R w a x) volume)
    (h4a : Integrable (fun x => x^4 * evenHeightWeight R w a x) volume)
    (h0p : Integrable (evenHeightWeight R w p) volume)
    (h2p : Integrable (fun x => x^2 * evenHeightWeight R w p x) volume)
    (h4p : Integrable (fun x => x^4 * evenHeightWeight R w p x) volume) :
    ∃ r : ℝ, 0 < r ∧ r <= 1 ∧ literalEvenFiniteDeterminant R w a p r < 0 := by
  exact exists_literalEvenFiniteDeterminant_neg_of_positivePlateau
    ha hap hl hlm hmr hrR hwNonneg hwPos h0a h2a h4a h0p h2p h4p

end Synthesis

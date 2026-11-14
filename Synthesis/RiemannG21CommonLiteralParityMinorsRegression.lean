import Synthesis.RiemannG21CommonLiteralParityMinors

open MeasureTheory Set

namespace Synthesis

example {w : ℝ → ℝ} {a p R l m r0 : ℝ}
    (ha : 0 < a) (hap : a < p)
    (hl : 0 < l) (hlm : l < m) (hmr : m < r0) (hrR : r0 < R)
    (hwNonneg : ∀ x ∈ Icc (0:ℝ) R, 0 <= w x)
    (hwPos : ∀ x ∈ Ioo l r0, 0 < w x)
    (ho1a : Integrable (oddHeightWeight R w a) volume)
    (ho3a : Integrable (fun x => x^2 * oddHeightWeight R w a x) volume)
    (ho5a : Integrable (fun x => x^4 * oddHeightWeight R w a x) volume)
    (ho1p : Integrable (oddHeightWeight R w p) volume)
    (ho3p : Integrable (fun x => x^2 * oddHeightWeight R w p x) volume)
    (ho5p : Integrable (fun x => x^4 * oddHeightWeight R w p x) volume)
    (he0a : Integrable (evenHeightWeight R w a) volume)
    (he2a : Integrable (fun x => x^2 * evenHeightWeight R w a x) volume)
    (he4a : Integrable (fun x => x^4 * evenHeightWeight R w a x) volume)
    (he0p : Integrable (evenHeightWeight R w p) volume)
    (he2p : Integrable (fun x => x^2 * evenHeightWeight R w p x) volume)
    (he4p : Integrable (fun x => x^4 * evenHeightWeight R w p x) volume) :
    ∃ r : ℝ, 0 < r ∧ r <= 1 ∧
      literalOddFiniteDeterminant R w a p r < 0 ∧
      literalEvenFiniteDeterminant R w a p r < 0 := by
  exact exists_commonRadius_literalParityMinors_neg
    ha hap hl hlm hmr hrR hwNonneg hwPos
    ho1a ho3a ho5a ho1p ho3p ho5p
    he0a he2a he4a he0p he2p he4p

end Synthesis

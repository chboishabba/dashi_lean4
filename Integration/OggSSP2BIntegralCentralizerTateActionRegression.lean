import Integration.OggSSP2BIntegralCentralizerTateAction

/-! Regression surface for automatic centralizer descent to the Tate quotient. -/

namespace Integration.OggSSP2BIntegralCentralizerTateActionRegression

open Integration.OggSSP2BIntegralCentralizerTateAction

variable {K G V : Type*}
  [Semiring K] [Group G]
  [AddCommMonoid V] [Module K V]

example (d : IntegralCentralizerActionData K G V) :
    Representation K G (V ⧸ d.normRange) :=
  d.tateQuotientRepresentation

example (d : IntegralCentralizerActionData K G V) (g : G) :
    d.normRange ≤ d.normRange.comap (d.rho g) :=
  d.normRange_stable g

end Integration.OggSSP2BIntegralCentralizerTateActionRegression

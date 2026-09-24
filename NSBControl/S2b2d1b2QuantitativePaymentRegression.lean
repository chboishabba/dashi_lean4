import NSBControl

namespace NSBControl

open RequestProject.NavierStokes

-- RED-first integration contract.  The production namespace intentionally
-- does not exist yet; the next commit must provide it without weakening the
-- hypotheses of the quantitative same-object payment.
example : S2b2d1b2QuantitativePayment.quantitativePaymentClosed = true := by
  exact S2b2d1b2QuantitativePayment.quantitativePaymentClosed_eq_true

example : S2b2d1b2QuantitativePayment.literalFourSignResidualConsumed = true := by
  exact S2b2d1b2QuantitativePayment.literalFourSignResidualConsumed_eq_true

example : S2b2d1b2QuantitativePayment.r571EnvelopeConsumed = true := by
  exact S2b2d1b2QuantitativePayment.r571EnvelopeConsumed_eq_true

example : S2b2d1b2QuantitativePayment.r568AdapterConstructed = true := by
  exact S2b2d1b2QuantitativePayment.r568AdapterConstructed_eq_true

end NSBControl

/-!
# Lean mirror of the golden DASHI residual-budget margin compiler

Golden Agda owners:

* `DASHI/Analysis/ResidualBudgetMarginCompilerExact.agda`
* `DASHI/Analysis/RiemannG2PoleQuotientProducerAllowanceTargetExact.agda`
* `DASHI/Analysis/RiemannG2FinalSplitComplementOrderTransportCompilerExact.agda`
* `DASHI/Unified/RiemannRHMaxCutTOEExact.agda`

This file mirrors the domain-neutral ordered arithmetic only.
It does not choose an RH route.
It does not import a Lean donor theorem into Agda.
It does not prove RH.

Internal provenance:
`chboishabba/dashi_agda` is the golden contract.
Existing Aristotle and meta-introspector repositories keep their own authorship.
-/

namespace AgdaMirror.ResidualBudgetMarginCompilerExact

/-- A residual may have either sign.  The proof only needs an upper budget
strictly below the signal margin. -/
structure ResidualBudgetMargin where
  residual : ℚ
  budget : ℚ
  strictSignalMargin : ℚ
  residualBound : residual ≤ budget
  budgetBelowStrictMargin : budget < strictSignalMargin

/-- Golden compiler:
`residual ≤ budget < margin` implies `residual < margin`. -/
theorem residualStrictlyBelowSignalMargin (d : ResidualBudgetMargin) :
    d.residual < d.strictSignalMargin :=
  lt_of_le_of_lt d.residualBound d.budgetBelowStrictMargin

/-- Two separately controlled residual groups. -/
structure SplitResidualBudgetMargin where
  structuredResidual : ℚ
  farResidual : ℚ
  structuredBudget : ℚ
  farBudget : ℚ
  strictSignalMargin : ℚ
  structuredBound : structuredResidual ≤ structuredBudget
  farBound : farResidual ≤ farBudget
  combinedBudgetBelowStrictMargin :
    structuredBudget + farBudget < strictSignalMargin

/-- Sum the two paid residual budgets before comparing with the strict margin. -/
theorem splitResidualStrictlyBelowSignalMargin (d : SplitResidualBudgetMargin) :
    d.structuredResidual + d.farResidual < d.strictSignalMargin :=
  lt_of_le_of_lt
    (add_le_add d.structuredBound d.farBound)
    d.combinedBudgetBelowStrictMargin

/-- Consumer-assigned two-channel allowance contract.

The analytic producers do not choose the allowances.
The final consumer assigns them.
This mirrors the golden Off/Gamma allowance interface. -/
structure TwoChannelAllowanceMargin where
  offResponse : ℚ
  gammaResponse : ℚ
  offBudget : ℚ
  gammaBudget : ℚ
  offAllowance : ℚ
  gammaAllowance : ℚ
  strictSignalMargin : ℚ

  offResponseBound : offResponse ≤ offBudget
  gammaResponseBound : gammaResponse ≤ gammaBudget
  offBudgetFitsAllowance : offBudget ≤ offAllowance
  gammaBudgetFitsAllowance : gammaBudget ≤ gammaAllowance
  allowancesBelowMargin :
    offAllowance + gammaAllowance < strictSignalMargin

/-- Paid Off and Gamma allowances imply the combined response is below the
strict signal margin. -/
theorem twoChannelResponseStrictlyBelowMargin (d : TwoChannelAllowanceMargin) :
    d.offResponse + d.gammaResponse < d.strictSignalMargin := by
  have hBudget :
      d.offResponse + d.gammaResponse ≤ d.offBudget + d.gammaBudget :=
    add_le_add d.offResponseBound d.gammaResponseBound
  have hAllowance :
      d.offBudget + d.gammaBudget ≤ d.offAllowance + d.gammaAllowance :=
    add_le_add d.offBudgetFitsAllowance d.gammaBudgetFitsAllowance
  exact lt_of_le_of_lt (hBudget.trans hAllowance) d.allowancesBelowMargin

end AgdaMirror.ResidualBudgetMarginCompilerExact

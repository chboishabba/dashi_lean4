import Mathlib

/-
# Generic residual-budget / strict-margin compiler

Agda return from `DASHI.Analysis.ResidualBudgetMarginCompilerExact`.

The residual does not need a favourable sign.  The stable interface is

    residual ≤ budget < strictSignalMargin

and, for split estimates,

    structuredResidual ≤ structuredBudget
    farResidual        ≤ farBudget
    structuredBudget + farBudget < strictSignalMargin.

No domain theorem follows from this file alone.
-/

namespace Zeta23Bridge

structure ResidualBudgetMargin where
  residual : ℝ
  budget : ℝ
  strictSignalMargin : ℝ
  residualBound : residual ≤ budget
  budgetBelowStrictMargin : budget < strictSignalMargin

theorem ResidualBudgetMargin.residual_lt_margin (d : ResidualBudgetMargin) :
    d.residual < d.strictSignalMargin :=
  lt_of_le_of_lt d.residualBound d.budgetBelowStrictMargin

structure SplitResidualBudgetMargin where
  structuredResidual : ℝ
  farResidual : ℝ
  structuredBudget : ℝ
  farBudget : ℝ
  strictSignalMargin : ℝ
  structuredBound : structuredResidual ≤ structuredBudget
  farBound : farResidual ≤ farBudget
  combinedBudgetBelowStrictMargin :
    structuredBudget + farBudget < strictSignalMargin

theorem SplitResidualBudgetMargin.residual_lt_margin (d : SplitResidualBudgetMargin) :
    d.structuredResidual + d.farResidual < d.strictSignalMargin :=
  lt_of_le_of_lt (add_le_add d.structuredBound d.farBound)
    d.combinedBudgetBelowStrictMargin

end Zeta23Bridge

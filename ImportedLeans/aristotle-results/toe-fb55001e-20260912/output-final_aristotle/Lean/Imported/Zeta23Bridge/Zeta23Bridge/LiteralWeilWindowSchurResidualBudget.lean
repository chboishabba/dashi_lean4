/-
# Stable residual-budget interface for literal window Schur admission

This is the Lean consumer corresponding to DASHI's generic residual-budget owner.
It wraps the already-proved

    |detRest| ≤ detRestBound

and deliberately keeps the endpoint/geometric budget separate from the Schur
admission theorem.

The next analytic layer only has to construct `WindowSchurResidualBudgetData`.
-/
import Zeta23Bridge.ResidualBudgetMarginCompiler
import Zeta23Bridge.LiteralWeilWindowRatioSeparation

noncomputable section

namespace Zeta23Bridge
namespace LiteralWeilWindowSchurResidualBudget

open Zeta23Bridge.LiteralWeilLeadingCoefficientCovariance
open Zeta23Bridge.LiteralWeilWindowRatioSeparation

/-- A stable carrier for the one-nuisance window-Schur quantitative payment. -/
structure WindowSchurResidualBudgetData
    (p q0 q1 : ℝ → ℝ) (lam a b : ℝ) where
  budget : ℝ
  detRestBound_le_budget :
    detRestBound p q0 q1 lam a b ≤ budget
  budget_lt_crossMargin :
    budget <
      4 * lam ^ 2 *
        (covForm p q0 a * covForm p q1 b -
          covForm p q1 a * covForm p q0 b)

/-- A budget object immediately implies the old `hdom` hypothesis. -/
theorem hdom_of_budget {p q0 q1 : ℝ → ℝ} {lam a b : ℝ}
    (hp : Continuous p) (hpc : HasCompactSupport p)
    (hq0 : Continuous q0) (hq0c : HasCompactSupport q0)
    (hq1 : Continuous q1) (hq1c : HasCompactSupport q1)
    (hpn : ∀ u, 0 ≤ p u) (hq0n : ∀ u, 0 ≤ q0 u) (hq1n : ∀ u, 0 ≤ q1 u)
    (d : WindowSchurResidualBudgetData p q0 q1 lam a b) :
    |detRest p q0 q1 lam a b| <
      4 * lam ^ 2 *
        (covForm p q0 a * covForm p q1 b -
          covForm p q1 a * covForm p q0 b) := by
  exact lt_of_le_of_lt
    ((abs_detRest_le hp hpc hq0 hq0c hq1 hq1c hpn hq0n hq1n lam a b).trans
      d.detRestBound_le_budget)
    d.budget_lt_crossMargin

/-- The same fact packaged through the domain-neutral compiler. -/
def toResidualBudgetMargin {p q0 q1 : ℝ → ℝ} {lam a b : ℝ}
    (hp : Continuous p) (hpc : HasCompactSupport p)
    (hq0 : Continuous q0) (hq0c : HasCompactSupport q0)
    (hq1 : Continuous q1) (hq1c : HasCompactSupport q1)
    (hpn : ∀ u, 0 ≤ p u) (hq0n : ∀ u, 0 ≤ q0 u) (hq1n : ∀ u, 0 ≤ q1 u)
    (d : WindowSchurResidualBudgetData p q0 q1 lam a b) :
    ResidualBudgetMargin :=
  { residual := |detRest p q0 q1 lam a b|
    budget := d.budget
    strictSignalMargin :=
      4 * lam ^ 2 *
        (covForm p q0 a * covForm p q1 b -
          covForm p q1 a * covForm p q0 b)
    residualBound :=
      (abs_detRest_le hp hpc hq0 hq0c hq1 hq1c hpn hq0n hq1n lam a b).trans
        d.detRestBound_le_budget
    budgetBelowStrictMargin := d.budget_lt_crossMargin }

end LiteralWeilWindowSchurResidualBudget
end Zeta23Bridge

import Mathlib.Tactic
import NSBControl.Rational345R831ReserveDecision
import NSBControl.Rational345R830DecisionCompiler

/-!
# Real R745--R760 total nonlinear normal form

This owner records only the scalar total carried by the exact Agda
R745 -> R749 -> R760 chain:

  R745 nonlinear fold      = 3 * (12 * coherent - production),
  R749 difference fold     = R745 fold,
  R760 swap-paired fold    = 2 * R749 fold.

Hence on the public real radius-four normalization

  R760 total = 6 * (12 * coherent - production)
             = selectedNonlinear.

This is deliberately NOT yet a theorem that the concrete real cellwise R760 or
R822 fold has been identified.  The remaining same-object leaf is precisely
that carrier weld.
-/

namespace NSBControl
namespace Rational345R823TouchedNormalForm

open Rational345RealRadius4
open Rational345R831ReserveDecision

/-- Real scalar normal form mirroring the R745 orbit-aligned nonlinear fold. -/
def r745OrbitAlignedNonlinear (u : State) : ℝ :=
  3 * (12 * globalCoherentWork u - criticalProduction u)

/-- R749 preserves the complete nonlinear fold exactly. -/
def r749DifferenceAlignedTotal (u : State) : ℝ :=
  r745OrbitAlignedNonlinear u

/-- R760 swap-pairs the complete residual and therefore doubles the R749 fold. -/
def r760SwapPairedResidualTotal (u : State) : ℝ :=
  2 * r749DifferenceAlignedTotal u

/-- The R745--R760 total normal form is exactly the public Lean nonlinear
selected rate. -/
theorem r760SwapPairedResidualTotal_eq_selectedNonlinear (u : State) :
    r760SwapPairedResidualTotal u = selectedNonlinear u := by
  unfold r760SwapPairedResidualTotal r749DifferenceAlignedTotal
    r745OrbitAlignedNonlinear selectedNonlinear
  ring

/-- The public nonlinear selected-rate polynomial is continuous. -/
theorem selectedNonlinear_continuous_real : Continuous selectedNonlinear := by
  have hsel := Rational345R830DecisionCompiler.selectedRate_continuous
  have hdiss := criticalDissipation_continuous_real
  have hdiff :
      Continuous (fun x : State => selectedRate x - 6 * criticalDissipation x) :=
    hsel.sub (continuous_const.mul hdiss)
  have heq :
      (fun x : State => selectedRate x - 6 * criticalDissipation x) =
        selectedNonlinear := by
    funext x
    rw [selectedRate_eq_selectedNonlinear_add_dissipation]
    ring
  exact heq ▸ hdiff

/-- The real R760 total scalar normal form is continuous as well. -/
theorem r760SwapPairedResidualTotal_continuous :
    Continuous r760SwapPairedResidualTotal := by
  have heq : r760SwapPairedResidualTotal = selectedNonlinear := by
    funext u
    exact r760SwapPairedResidualTotal_eq_selectedNonlinear u
  exact heq.symm ▸ selectedNonlinear_continuous_real

/-- Algebraic total normalization is complete; cellwise R760/R822 same-object
identification remains separate. -/
def r823RealR760TotalNormalFormClosed : Bool := true

def r823RealR760CellwiseCarrierSameObjectClosed : Bool := false

end Rational345R823TouchedNormalForm
end NSBControl

import Mathlib.Tactic
import NSBControl.Rational345BPClosed

/-!
# R831 reserve decision transport

R830 is already closed by `Rational345BPClosed`: there exists a literal
radius-four Galerkin trajectory whose integrated selected payment is strictly
negative on a nonzero interval.

R823's Agda owner proves the exact integrated algebra

  integratedCompleteRate = integratedReserve - integratedDemand.

This file mirrors only that semantic transport.  It deliberately does **not**
fabricate the still-missing real-time R823 instantiation.  Instead it isolates
that one remaining same-object leaf as `R823WeldForR830Witness`.

Once such a weld is supplied for the R830 trajectory, the reserve inequality
is refuted immediately.  Thus R831 contains no new Navier--Stokes estimate.
-/

open Set

namespace NSBControl
namespace Rational345R831ReserveDecision

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345R830ResidenceInterval
open Rational345BPClosed

/-- Pure algebraic R831 transport. -/
theorem negative_payment_refutes_reserve
    {payment reserve demand : ℝ}
    (hneg : payment < 0)
    (hweld : payment = reserve - demand) :
    ¬ demand ≤ reserve := by
  intro hreserve
  linarith

/-- Exact equivalence behind the R823 decision gate. -/
theorem reserve_iff_nonnegative_payment
    {payment reserve demand : ℝ}
    (hweld : payment = reserve - demand) :
    demand ≤ reserve ↔ 0 ≤ payment := by
  constructor <;> intro h <;> linarith

/-- The literal selected payment integrated on a terminal interval. -/
def selectedPayment (u : ℝ → State) (terminal : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..terminal, selectedRate (u t)

/-- Exact real-time counterpart of Agda R823's
`integratedReserveMinusDemand`.  The fields are the *actual* R823 integrated
reserve and demand once that same-object instantiation is constructed. -/
structure R823IntegratedWeld (u : ℝ → State) (terminal : ℝ) where
  integratedReserve : ℝ
  integratedDemand : ℝ
  selectedPayment_eq_reserve_sub_demand :
    selectedPayment u terminal = integratedReserve - integratedDemand

/-- A negative selected payment refutes the reserve inequality for any exact
R823 integrated weld of that same trajectory and terminal time. -/
theorem welded_negative_payment_refutes_reserve
    {u : ℝ → State} {terminal : ℝ}
    (weld : R823IntegratedWeld u terminal)
    (hneg : selectedPayment u terminal < 0) :
    ¬ weld.integratedDemand ≤ weld.integratedReserve := by
  exact negative_payment_refutes_reserve
    hneg weld.selectedPayment_eq_reserve_sub_demand

/-- The one remaining semantic leaf after R830: instantiate Agda R823's exact
reserve/demand decomposition on any local R830 witness.  No sign or estimate is
part of this interface. -/
def R823WeldForR830Witness : Prop :=
  ∀ (u : ℝ → State) (ε δ : ℝ),
    0 < ε →
    0 < δ →
    u 0 = u₀ →
    (∀ t ∈ Ioo (-ε) ε,
      HasDerivAt u (galerkinField (u t)) t) →
    R823IntegratedWeld u (residenceUsableTime ε δ)

/-- R830 + the exact R823 same-object weld produce an explicit integrated
reserve counterexample. -/
theorem r830_refutes_r823_reserve
    (hWeld : R823WeldForR830Witness) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve := by
  obtain ⟨u, ε, δ, hε, hδ, hu0, hderiv, hneg⟩ :=
    r830_negative_integrated_payment
  let weld := hWeld u ε δ hε hδ hu0 hderiv
  refine ⟨weld.integratedReserve, weld.integratedDemand, ?_⟩
  apply welded_negative_payment_refutes_reserve weld
  simpa [selectedPayment] using hneg

/-- The universal reserve proposition on the produced R830 witness is false as
soon as the semantic weld exists.  Kept separate from the stronger repository
claim until `R823WeldForR830Witness` itself is inhabited. -/
theorem not_all_welded_r830_reserves
    (hWeld : R823WeldForR830Witness) :
    ¬ (∀ reserve demand : ℝ,
        reserve = reserve → demand = demand → demand ≤ reserve) := by
  obtain ⟨reserve, demand, hfail⟩ := r830_refutes_r823_reserve hWeld
  intro hall
  exact hfail (hall reserve demand rfl rfl)

/-- R831's logical transport is closed. -/
def r831TransportClosed : Bool := true

/-- The actual real-time R823 integrated same-object weld remains the only
semantic leaf before the repository-level universal reserve route may be
frozen. -/
def r823RealIntegratedWeldClosed : Bool := false

end Rational345R831ReserveDecision
end NSBControl

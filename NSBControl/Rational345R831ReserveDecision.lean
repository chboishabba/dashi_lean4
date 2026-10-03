import Mathlib.Tactic
import NSBControl.Rational345BPClosed

/-!
# R831 reserve decision transport

R830 is already closed by `Rational345BPClosed`: there exists a literal
radius-four Galerkin trajectory whose integrated selected payment is strictly
negative on a nonzero interval.

Agda R820 proves the actual R815 signed payment equals the full four-helicity
payment rate pointwise.  Agda R823 then proves that full rate is exactly

  signedReserve - cubicQuinticDemand.

This file mirrors that semantic transport without fabricating the still-open
real-time same-object identification.  The remaining pointwise leaf is cut
into the exact R815/R813/R822 identities that the Agda chain already owns.
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
`integratedReserveMinusDemand`. -/
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

------------------------------------------------------------------------
-- Max-cut the semantic leaf from integrated equality to pointwise equality.
------------------------------------------------------------------------

/-- Real pointwise counterpart of the Agda R820+R823 chain. -/
structure R823PointwiseWeld where
  reserveRate : State → ℝ
  demandRate : State → ℝ
  selectedRate_eq_reserve_sub_demand :
    ∀ x, selectedRate x = reserveRate x - demandRate x
  reserveRate_continuous : Continuous reserveRate
  demandRate_continuous : Continuous demandRate

------------------------------------------------------------------------
-- Cut the pointwise leaf into the exact R815 / R813 / R822 same-object rows.
------------------------------------------------------------------------

/-- Non-viscous part of the real R815-normalized selected rate. -/
def selectedNonlinear (x : State) : ℝ :=
  6 * (12 * globalCoherentWork x - criticalProduction x)

theorem selectedRate_eq_selectedNonlinear_add_dissipation (x : State) :
    selectedRate x = selectedNonlinear x + 6 * criticalDissipation x := by
  unfold selectedRate selectedNonlinear
  ring

/-- The critical dissipation fold is a continuous finite polynomial on the
radius-four state carrier. -/
theorem criticalDissipation_continuous_real :
    Continuous criticalDissipation := by
  unfold criticalDissipation modalDissipation hermitianDot
  fun_prop

/-- Exact real-time data needed to mirror Agda R820/R813/R822.

* `r815SeparatedTouched` is the real R815 nonlinear split;
* `r813SeparatedNormalForm` is Dsep = 2*(9*Nsep-Qsep);
* `r822TouchedComparable` identifies the touched fold with the actual signed
  comparable-CC rows.

No sign or analytic estimate is included. -/
structure R823NonlinearPointwiseData where
  separatedRate : State → ℝ
  touchedRate : State → ℝ
  nestedFourHelicityWork : State → ℝ
  qsep : State → ℝ
  signedComparableCC : State → ℝ

  nestedFourHelicityWork_continuous : Continuous nestedFourHelicityWork
  qsep_continuous : Continuous qsep
  signedComparableCC_continuous : Continuous signedComparableCC

  r815SeparatedTouched :
    ∀ x, selectedNonlinear x = separatedRate x + touchedRate x
  r813SeparatedNormalForm :
    ∀ x,
      separatedRate x =
        2 * (9 * nestedFourHelicityWork x - qsep x)
  r822TouchedComparable :
    ∀ x, touchedRate x = signedComparableCC x

/-- The three Agda same-object identities imply the literal pointwise R823
reserve-minus-demand identity on the real radius-four carrier. -/
theorem r823_pointwise_identity_of_nonlinearData
    (data : R823NonlinearPointwiseData) :
    ∀ x : State,
      selectedRate x =
        (data.signedComparableCC x + 6 * criticalDissipation x) -
        (2 * (data.qsep x - 9 * data.nestedFourHelicityWork x)) := by
  intro x
  calc
    selectedRate x
        = selectedNonlinear x + 6 * criticalDissipation x :=
          selectedRate_eq_selectedNonlinear_add_dissipation x
    _ = (data.separatedRate x + data.touchedRate x)
          + 6 * criticalDissipation x := by
          rw [data.r815SeparatedTouched x]
    _ = (2 * (9 * data.nestedFourHelicityWork x - data.qsep x)
          + data.signedComparableCC x)
          + 6 * criticalDissipation x := by
          rw [data.r813SeparatedNormalForm x, data.r822TouchedComparable x]
    _ = (data.signedComparableCC x + 6 * criticalDissipation x) -
          (2 * (data.qsep x - 9 * data.nestedFourHelicityWork x)) := by
          ring

/-- Construct the actual pointwise reserve/demand weld from the three exact
nonlinear same-object leaves. -/
def r823PointwiseWeld_of_nonlinearData
    (data : R823NonlinearPointwiseData) : R823PointwiseWeld where
  reserveRate := fun x =>
    data.signedComparableCC x + 6 * criticalDissipation x
  demandRate := fun x =>
    2 * (data.qsep x - 9 * data.nestedFourHelicityWork x)
  selectedRate_eq_reserve_sub_demand :=
    r823_pointwise_identity_of_nonlinearData data
  reserveRate_continuous := by
    exact data.signedComparableCC_continuous.add
      (continuous_const.mul criticalDissipation_continuous_real)
  demandRate_continuous := by
    exact continuous_const.mul
      (data.qsep_continuous.sub
        (continuous_const.mul data.nestedFourHelicityWork_continuous))

/-- Integrated actual reserve attached to a pointwise weld. -/
def integratedReserve
    (weld : R823PointwiseWeld) (u : ℝ → State) (terminal : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..terminal, weld.reserveRate (u t)

/-- Integrated actual demand attached to a pointwise weld. -/
def integratedDemand
    (weld : R823PointwiseWeld) (u : ℝ → State) (terminal : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..terminal, weld.demandRate (u t)

/-- Pointwise R820+R823 equality plus continuity implies the exact integrated
R823 weld; no new PDE estimate enters here. -/
theorem integrated_weld_of_pointwise
    (weld : R823PointwiseWeld)
    (u : ℝ → State) (terminal : ℝ)
    (hu : ContinuousOn u (uIcc (0 : ℝ) terminal)) :
    selectedPayment u terminal =
      integratedReserve weld u terminal - integratedDemand weld u terminal := by
  have hreserveCont :
      ContinuousOn (fun t => weld.reserveRate (u t))
        (uIcc (0 : ℝ) terminal) :=
    weld.reserveRate_continuous.continuousOn.comp hu (fun _ ht => ht)
  have hdemandCont :
      ContinuousOn (fun t => weld.demandRate (u t))
        (uIcc (0 : ℝ) terminal) :=
    weld.demandRate_continuous.continuousOn.comp hu (fun _ ht => ht)
  have hreserveInt := hreserveCont.intervalIntegrable
  have hdemandInt := hdemandCont.intervalIntegrable
  unfold selectedPayment integratedReserve integratedDemand
  simp_rw [weld.selectedRate_eq_reserve_sub_demand]
  exact intervalIntegral.integral_sub hreserveInt hdemandInt

/-- Build the integrated R823 object on any continuous trajectory. -/
def integratedWeldOfPointwise
    (weld : R823PointwiseWeld)
    (u : ℝ → State) (terminal : ℝ)
    (hu : ContinuousOn u (uIcc (0 : ℝ) terminal)) :
    R823IntegratedWeld u terminal where
  integratedReserve := integratedReserve weld u terminal
  integratedDemand := integratedDemand weld u terminal
  selectedPayment_eq_reserve_sub_demand :=
    integrated_weld_of_pointwise weld u terminal hu

/-- The older integrated interface retained as the exact consumer shape of
R830. -/
def R823WeldForR830Witness : Prop :=
  ∀ (u : ℝ → State) (ε δ : ℝ),
    0 < ε →
    0 < δ →
    u 0 = u₀ →
    (∀ t ∈ Ioo (-ε) ε,
      HasDerivAt u (galerkinField (u t)) t) →
    R823IntegratedWeld u (residenceUsableTime ε δ)

/-- A global pointwise real R820+R823 weld automatically supplies the exact
integrated weld on every R830 witness. -/
theorem r823WitnessWeld_of_pointwise
    (weld : R823PointwiseWeld) :
    R823WeldForR830Witness := by
  intro u ε δ hε hδ hu0 hderiv
  let terminal := residenceUsableTime ε δ
  have hterminal : 0 ≤ terminal :=
    le_of_lt (residenceUsableTime_pos hε hδ)
  have huIcc : ContinuousOn u (uIcc (0 : ℝ) terminal) := by
    rw [uIcc_of_le hterminal]
    exact solution_continuousOn_residence hε hderiv
  exact integratedWeldOfPointwise weld u terminal huIcc

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

/-- Direct pointwise version of the decision gate. -/
theorem r830_refutes_r823_reserve_of_pointwise
    (weld : R823PointwiseWeld) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve :=
  r830_refutes_r823_reserve (r823WitnessWeld_of_pointwise weld)

/-- R831's logical and integration transport is closed. -/
def r831TransportClosed : Bool := true

/-- Interval linearity is no longer an open leaf. -/
def r831IntegratedWeldReducedToPointwise : Bool := true

/-- Pointwise reserve transport is reduced to the three exact Agda mirror
identities in `R823NonlinearPointwiseData`. -/
def r831PointwiseWeldReducedToThreeSameObjectLeaves : Bool := true

/-- No real radius-four owner has yet instantiated all three leaves. -/
def r823RealNonlinearSameObjectClosed : Bool := false

end Rational345R831ReserveDecision
end NSBControl

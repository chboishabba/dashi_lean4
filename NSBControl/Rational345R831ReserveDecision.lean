import Mathlib.Tactic
import NSBControl.Rational345BPClosed

/-!
# R831 reserve decision transport

R830 is already closed by `Rational345BPClosed`: there exists a literal
radius-four Galerkin trajectory whose integrated selected payment is strictly
negative on a nonzero interval.

Agda R853 gives the decisive general normal form on every live packet:

  R815 selected rate(delta)
    = 6 * (12 * coherent - production + (2*nu-delta) * dissipation).

At the decision normalization `nu = delta = 1`, this is exactly the public
Lean `selectedRate`.  Agda R823 independently gives the exact same-packet
identity

  completePhysicalRate = signedReserve - cubicQuinticDemand.

Therefore the remaining R831 semantic problem is not R813/R822 arithmetic.
It is the narrow real-carrier/live-packet weld that identifies the Lean
radius-four state operators with the R853/R823 live packet operators.
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
-- Pointwise-to-integrated compiler.
------------------------------------------------------------------------

structure R823PointwiseWeld where
  reserveRate : State → ℝ
  demandRate : State → ℝ
  selectedRate_eq_reserve_sub_demand :
    ∀ x, selectedRate x = reserveRate x - demandRate x
  reserveRate_continuous : Continuous reserveRate
  demandRate_continuous : Continuous demandRate

def integratedReserve
    (weld : R823PointwiseWeld) (u : ℝ → State) (terminal : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..terminal, weld.reserveRate (u t)

def integratedDemand
    (weld : R823PointwiseWeld) (u : ℝ → State) (terminal : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..terminal, weld.demandRate (u t)

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

def integratedWeldOfPointwise
    (weld : R823PointwiseWeld)
    (u : ℝ → State) (terminal : ℝ)
    (hu : ContinuousOn u (uIcc (0 : ℝ) terminal)) :
    R823IntegratedWeld u terminal where
  integratedReserve := integratedReserve weld u terminal
  integratedDemand := integratedDemand weld u terminal
  selectedPayment_eq_reserve_sub_demand :=
    integrated_weld_of_pointwise weld u terminal hu

def R823WeldForR830Witness : Prop :=
  ∀ (u : ℝ → State) (ε δ : ℝ),
    0 < ε →
    0 < δ →
    u 0 = u₀ →
    (∀ t ∈ Ioo (-ε) ε,
      HasDerivAt u (galerkinField (u t)) t) →
    R823IntegratedWeld u (residenceUsableTime ε δ)

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

------------------------------------------------------------------------
-- Round853 max-cut: the actual remaining semantic leaf.
------------------------------------------------------------------------

/-- Minimal real-carrier mirror of Agda R853 + R823.

`completePhysicalRate` is the actual R815/R853 selected rate on the decoded
live packet.  The three scalar same-object fields are deliberately explicit:
they are exactly the R853 carrier weld between the Lean finite real state and
Agda's live packet owners R741/R815.  At nu=delta=1 R853 then gives
`selectedRateSameObject`.

The R823 fields are the actual signed reserve and cubic/quintic demand on the
same decoded packet.  Their exact subtraction identity is already theorem
content in Agda R823; Lean only requires the same-object real-carrier mirror.
-/
structure R853RealCarrierWeld where
  coherent : State → ℝ
  production : State → ℝ
  dissipation : State → ℝ
  completePhysicalRate : State → ℝ
  reserveRate : State → ℝ
  demandRate : State → ℝ

  coherent_sameObject : ∀ x, coherent x = globalCoherentWork x
  production_sameObject : ∀ x, production x = criticalProduction x
  dissipation_sameObject : ∀ x, dissipation x = criticalDissipation x

  r853DecisionNormalForm :
    ∀ x,
      completePhysicalRate x =
        6 * (12 * coherent x - production x + dissipation x)

  r823ReserveMinusDemand :
    ∀ x, completePhysicalRate x = reserveRate x - demandRate x

  reserveRate_continuous : Continuous reserveRate
  demandRate_continuous : Continuous demandRate

/-- Round853 plus the three scalar carrier identifications prove that the
actual packet selected rate is literally the public Lean `selectedRate`. -/
theorem r853_selectedRate_sameObject
    (weld : R853RealCarrierWeld) (x : State) :
    selectedRate x = weld.completePhysicalRate x := by
  rw [selectedRate_public_definition]
  rw [← weld.coherent_sameObject x,
      ← weld.production_sameObject x,
      ← weld.dissipation_sameObject x]
  exact (weld.r853DecisionNormalForm x).symm

/-- The R853 real-carrier weld is enough to construct the exact pointwise
R823 reserve/demand weld; no R813/R822 re-expansion is needed in Lean. -/
def r823PointwiseWeld_of_r853
    (weld : R853RealCarrierWeld) : R823PointwiseWeld where
  reserveRate := weld.reserveRate
  demandRate := weld.demandRate
  selectedRate_eq_reserve_sub_demand := by
    intro x
    exact (r853_selectedRate_sameObject weld x).trans
      (weld.r823ReserveMinusDemand x)
  reserveRate_continuous := weld.reserveRate_continuous
  demandRate_continuous := weld.demandRate_continuous

------------------------------------------------------------------------
-- Legacy/fallback expansion through R813/R822.
-- Kept for cross-checking only; Round853 is the preferred decision route.
------------------------------------------------------------------------

def selectedNonlinear (x : State) : ℝ :=
  6 * (12 * globalCoherentWork x - criticalProduction x)

theorem selectedRate_eq_selectedNonlinear_add_dissipation (x : State) :
    selectedRate x = selectedNonlinear x + 6 * criticalDissipation x := by
  unfold selectedRate selectedNonlinear
  ring

theorem criticalDissipation_continuous_real :
    Continuous criticalDissipation := by
  unfold criticalDissipation modalDissipation hermitianDot
  fun_prop

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

------------------------------------------------------------------------
-- Terminal decision compilers.
------------------------------------------------------------------------

theorem r830_refutes_r823_reserve
    (hWeld : R823WeldForR830Witness) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve := by
  obtain ⟨u, ε, δ, hε, hδ, hu0, hderiv, hneg⟩ :=
    r830_negative_integrated_payment
  let weld := hWeld u ε δ hε hδ hu0 hderiv
  refine ⟨weld.integratedReserve, weld.integratedDemand, ?_⟩
  apply welded_negative_payment_refutes_reserve weld
  simpa [selectedPayment] using hneg

theorem r830_refutes_r823_reserve_of_pointwise
    (weld : R823PointwiseWeld) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve :=
  r830_refutes_r823_reserve (r823WitnessWeld_of_pointwise weld)

/-- Preferred terminal route: Round853 real carrier weld -> R823 refutation. -/
theorem r830_refutes_r823_reserve_of_r853
    (weld : R853RealCarrierWeld) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve :=
  r830_refutes_r823_reserve_of_pointwise (r823PointwiseWeld_of_r853 weld)

def r831TransportClosed : Bool := true

def r831IntegratedWeldReducedToPointwise : Bool := true

/-- Round853 supersedes the older R813/R822 expansion in the decision lane. -/
def r831DecisionReducedToR853RealCarrierWeld : Bool := true

/-- Exact remaining semantic leaf before R823/B-RESERVE may be frozen. -/
def r853RealTrajectoryCarrierWeldClosed : Bool := false

end Rational345R831ReserveDecision
end NSBControl

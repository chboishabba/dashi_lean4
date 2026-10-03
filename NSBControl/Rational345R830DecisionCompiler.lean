import Mathlib.Tactic
import NSBControl.Rational345RealRadius4Quadratic
import NSBControl.Rational345RealSnapshotW2
import NSBControl.Rational345BQFieldBound
import NSBControl.Rational345BPBudget
import NSBControl.Rational345R830ResidenceInterval

/-!
# R830 decision compiler after W2 and B_Q

W2 supplies the exact negative initial value of the genuine real evolving
observable.  B_Q supplies the certified field bound on any smaller bootstrap
ball.  The residence-aware interval compiler supplies a positive terminal
interval inside Picard, the R828 horizon, and the chosen ball.

The sole quantitative R830 leaf exposed here is therefore B_P:

  selectedRate x - selectedRate u0
    <= rateLipschitzBound * ||x-u0||

on the radius-1/100 ball.
-/

open Set

namespace NSBControl
namespace Rational345R830DecisionCompiler

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345RealRadius4Quadratic
open Rational345RealSnapshotW2
open Rational345BQGeometry
open Rational345BQFieldBound
open Rational345BPBudget
open Rational345ShortTime
open Rational345R830LocalInterval
open Rational345R830ResidenceInterval

/-- W2 has much more than the integer margin needed by R828. -/
theorem initial_rate_has_integer_margin :
    selectedRate u₀ ≤ -integerMargin := by
  rw [selectedRate_u₀_exact]
  norm_num [expectedInitialRate, integerMargin]

/-- B_Q was proved on the radius-one ball, hence automatically holds on the
smaller B_P ball of radius 1/100. -/
theorem field_bound_on_bp_ball
    {x : State}
    (hx : x ∈ Metric.closedBall u₀ bpBootstrapRadius) :
    ‖galerkinField x‖ ≤ odeComponentBound := by
  apply galerkinField_norm_le_certified
  have hr : bpBootstrapRadius ≤ bootstrapRadius := by
    norm_num [bpBootstrapRadius, bootstrapRadius]
  exact Metric.closedBall_subset_closedBall hr hx

/-- Explicit B_P leaf in exactly the shape consumed by R830. -/
def BPLeaf : Prop :=
  ∀ x ∈ Metric.closedBall u₀ bpBootstrapRadius,
    selectedRate x - selectedRate u₀
      ≤ rateLipschitzBound * ‖x - u₀‖

/-- Continuity of the literal finite selected-rate polynomial.  This is a
standard finite algebra fact; the proof is isolated here so B_P itself remains
only the explicit quantitative difference inequality. -/
theorem selectedRate_continuous : Continuous selectedRate := by
  unfold selectedRate globalCoherentWork criticalProduction criticalDissipation
  fun_prop

/-- R830 endpoint.  Once B_P is supplied, the actual literal radius-four
Galerkin solution has strictly negative integrated selected payment on a
nonzero interval. -/
theorem exists_local_solution_with_negative_integral
    (hBP : BPLeaf) :
    ∃ (u : ℝ → State) (ε δ : ℝ),
      0 < ε ∧ 0 < δ ∧
      u 0 = u₀ ∧
      (∀ t ∈ Ioo (-ε) ε,
        HasDerivAt u (galerkinField (u t)) t) ∧
      (∫ t in (0 : ℝ)..residenceUsableTime ε δ,
        selectedRate (u t)) < 0 := by
  obtain ⟨u, hu0, ε, hε, hderiv⟩ := exists_local_solution u₀
  obtain ⟨δ, hδ, hres⟩ :=
    exists_positive_ball_residence
      galerkinField u u₀ hε bpBootstrapRadius_pos hu0 hderiv
  refine ⟨u, ε, δ, hε, hδ, hu0, hderiv, ?_⟩
  exact negativeIntegral_from_residence_ball_lipschitz
    galerkinField u u₀ selectedRate
    hε hδ bpBootstrapRadius_pos hu0 hderiv hres
    (fun x hx => field_bound_on_bp_ball hx)
    hBP selectedRate_continuous
    initial_rate_has_integer_margin

end Rational345R830DecisionCompiler
end NSBControl

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.MeanValue
import NSBControl.Rational345LocalODE
import NSBControl.Rational345ShortTime
import NSBControl.Rational345RateLipschitz

/-!
# R830 local-interval compiler

Picard--Lindelöf supplies an unspecified positive radius `ε`.  The R828
certificate supplies a fixed positive horizon `certifiedTime`.  There is no
reason to prove one is larger than the other: use

  usableTime ε = min (ε / 2) certifiedTime.

For every `ε > 0`, this is a strictly positive interval, lies strictly inside
the Picard interval, and is no longer than the R828 certified horizon.  Hence
all remaining R830 estimates may be proved only on this canonical local
subinterval.
-/

open Set

namespace NSBControl
namespace Rational345R830LocalInterval

open Rational345ShortTime

def usableTime (ε : ℝ) : ℝ :=
  min (ε / 2) certifiedTime

theorem usableTime_pos {ε : ℝ} (hε : 0 < ε) :
    0 < usableTime ε := by
  rw [usableTime]
  exact lt_min (by linarith) certifiedTime_pos

theorem usableTime_le_certifiedTime (ε : ℝ) :
    usableTime ε ≤ certifiedTime := by
  exact min_le_right _ _

theorem usableTime_le_half {ε : ℝ} :
    usableTime ε ≤ ε / 2 := by
  exact min_le_left _ _

theorem usableTime_lt_eps {ε : ℝ} (hε : 0 < ε) :
    usableTime ε < ε := by
  calc
    usableTime ε ≤ ε / 2 := usableTime_le_half
    _ < ε := by linarith

theorem usable_Icc_inside_picard_Ioo
    {ε t : ℝ} (hε : 0 < ε)
    (ht : t ∈ Icc (0 : ℝ) (usableTime ε)) :
    t ∈ Ioo (-ε) ε := by
  constructor
  · linarith [ht.1]
  · exact lt_of_le_of_lt ht.2 (usableTime_lt_eps hε)

/-- Derivative authority on the Picard interval automatically gives
continuity on the canonical usable interval. -/
theorem solution_continuousOn_usable
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {field : E → E} {u : ℝ → E} {ε : ℝ}
    (hε : 0 < ε)
    (hderiv :
      ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt u (field (u t)) t) :
    ContinuousOn u (Icc (0 : ℝ) (usableTime ε)) := by
  intro t ht
  exact
    (hderiv t (usable_Icc_inside_picard_Ioo hε ht)).continuousAt.continuousWithinAt

/-- If the selected rate observable is continuous, no separate trajectory-rate
continuity proof is required on the usable interval. -/
theorem rate_comp_continuousOn_usable
    {E : Type*}
    [TopologicalSpace E]
    {u : ℝ → E} {rate : E → ℝ} {ε : ℝ}
    (hu : ContinuousOn u (Icc (0 : ℝ) (usableTime ε)))
    (hrate : Continuous rate) :
    ContinuousOn (fun t => rate (u t)) (Icc (0 : ℝ) (usableTime ε)) := by
  exact hrate.continuousOn.comp hu (fun _ ht => ht)

/-- Final generic local-interval transport.  Once a concrete Galerkin solution
supplies the R828 displacement and one-sided rate-Lipschitz bounds on the
usable interval, strict negative integrated payment follows. -/
theorem negativeIntegral_on_usableTime
    {E : Type*}
    [NormedAddCommGroup E]
    (u : ℝ → E) (u₀ : E) (rate : E → ℝ)
    {ε : ℝ}
    (hε : 0 < ε)
    (hinitial : rate u₀ ≤ -integerMargin)
    (hdisp :
      ∀ t ∈ Icc (0 : ℝ) (usableTime ε),
        ‖u t - u₀‖ ≤ odeComponentBound * t)
    (hrate :
      ∀ x,
        rate x - rate u₀ ≤ rateLipschitzBound * ‖x - u₀‖)
    (hcont :
      ContinuousOn (fun t => rate (u t))
        (Icc (0 : ℝ) (usableTime ε))) :
    (∫ t in (0 : ℝ)..usableTime ε, rate (u t)) < 0 := by
  exact
    ConcreteConstants.negativeIntegral_from_R828_bounds_up_to
      u u₀ rate (usableTime ε)
      (usableTime_pos hε)
      (usableTime_le_certifiedTime ε)
      hinitial hdisp hrate hcont



/-- O2 compiler: a uniform norm bound on the actual vector field along the
usable solution segment gives the required linear displacement estimate in one
mean-value step.  No coordinatewise integration is needed. -/
theorem displacement_le_of_field_norm_le
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : E → E)
    (u : ℝ → E) (u₀ : E)
    {ε K : ℝ}
    (hε : 0 < ε)
    (hu0 : u 0 = u₀)
    (hderiv :
      ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt u (field (u t)) t)
    (hfield :
      ∀ t ∈ Icc (0 : ℝ) (usableTime ε),
        ‖field (u t)‖ ≤ K) :
    ∀ t ∈ Icc (0 : ℝ) (usableTime ε),
      ‖u t - u₀‖ ≤ K * t := by
  intro t ht
  have hT : 0 ≤ usableTime ε := le_of_lt (usableTime_pos hε)
  have hwithin :
      ∀ x ∈ Icc (0 : ℝ) (usableTime ε),
        HasDerivWithinAt u (field (u x))
          (Icc (0 : ℝ) (usableTime ε)) x := by
    intro x hx
    exact
      (hderiv x (usable_Icc_inside_picard_Ioo hε hx)).hasDerivWithinAt
  have hbound :
      ∀ x ∈ Ico (0 : ℝ) (usableTime ε),
        ‖field (u x)‖ ≤ K := by
    intro x hx
    exact hfield x ⟨hx.1, le_of_lt hx.2⟩
  have hmv :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      (a := (0 : ℝ)) (b := usableTime ε)
      (f := u) (f' := fun x => field (u x))
      hwithin hbound t ht
  simpa [hu0] using hmv

/-- Stronger terminal compiler: derivative authority plus continuity of the
finite selected-rate observable discharges the continuity hypothesis
automatically.  The concrete NS residue is therefore just initial-rate
identification and the two quantitative R828 bounds. -/
theorem negativeIntegral_on_usableTime_of_continuousRate
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : E → E)
    (u : ℝ → E) (u₀ : E) (rate : E → ℝ)
    {ε : ℝ}
    (hε : 0 < ε)
    (hderiv :
      ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt u (field (u t)) t)
    (hrateContinuous : Continuous rate)
    (hinitial : rate u₀ ≤ -integerMargin)
    (hdisp :
      ∀ t ∈ Icc (0 : ℝ) (usableTime ε),
        ‖u t - u₀‖ ≤ odeComponentBound * t)
    (hrate :
      ∀ x,
        rate x - rate u₀ ≤ rateLipschitzBound * ‖x - u₀‖) :
    (∫ t in (0 : ℝ)..usableTime ε, rate (u t)) < 0 := by
  apply negativeIntegral_on_usableTime
    u u₀ rate hε hinitial hdisp hrate
  exact rate_comp_continuousOn_usable
    (solution_continuousOn_usable hε hderiv)
    hrateContinuous


/-- Ball-local terminal compiler for R830.

The concrete proof no longer needs global bounds.  It is enough that the local
solution segment stays in one closed bootstrap ball, the literal Galerkin field
has the certified norm bound on that ball, and the literal selected-rate
polynomial has the certified derivative bound there. -/
theorem negativeIntegral_from_ball_bounds
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : E → E)
    (u : ℝ → E) (u₀ : E) (rate : E → ℝ)
    {ε radius : ℝ}
    (hε : 0 < ε)
    (hradius : 0 ≤ radius)
    (hu0 : u 0 = u₀)
    (hderiv :
      ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt u (field (u t)) t)
    (hstay :
      ∀ t ∈ Icc (0 : ℝ) (usableTime ε),
        u t ∈ Metric.closedBall u₀ radius)
    (hfieldBall :
      ∀ x ∈ Metric.closedBall u₀ radius,
        ‖field x‖ ≤ odeComponentBound)
    (hrateDiff :
      ∀ x ∈ Metric.closedBall u₀ radius,
        DifferentiableAt ℝ rate x)
    (hrateDerivBound :
      ∀ x ∈ Metric.closedBall u₀ radius,
        ‖fderiv ℝ rate x‖ ≤ rateLipschitzBound)
    (hrateContinuous : Continuous rate)
    (hinitial : rate u₀ ≤ -integerMargin) :
    (∫ t in (0 : ℝ)..usableTime ε, rate (u t)) < 0 := by
  have hdisp :
      ∀ t ∈ Icc (0 : ℝ) (usableTime ε),
        ‖u t - u₀‖ ≤ odeComponentBound * t := by
    apply displacement_le_of_field_norm_le
      field u u₀ hε hu0 hderiv
    intro t ht
    exact hfieldBall (u t) (hstay t ht)

  have hneg :
      ∀ t ∈ Icc (0 : ℝ) (usableTime ε),
        rate (u t) < 0 := by
    intro t ht
    have hrateStep :
        rate (u t) - rate u₀
          ≤ rateLipschitzBound * ‖u t - u₀‖ :=
      Rational345RateLipschitz.rate_sub_le_of_fderiv_bound
        rate u₀ radius rateLipschitzBound
        hradius hrateDiff hrateDerivBound (hstay t ht)
    have hdispStep := hdisp t ht
    have htime :
        rateLipschitzBound * odeComponentBound * t
          ≤ integerMargin / 2 := by
      calc
        rateLipschitzBound * odeComponentBound * t
            ≤ rateLipschitzBound * odeComponentBound * usableTime ε := by
              gcongr
        _ ≤ integerMargin / 2 :=
          ConcreteConstants.certifiedBudget_le_of_le_certifiedTime
            (le_of_lt (usableTime_pos hε))
            (usableTime_le_certifiedTime ε)
    have hgrowth :
        rate (u t) - rate u₀ ≤ integerMargin / 2 := by
      calc
        rate (u t) - rate u₀
            ≤ rateLipschitzBound * ‖u t - u₀‖ := hrateStep
        _ ≤ rateLipschitzBound * (odeComponentBound * t) := by
              gcongr
        _ = rateLipschitzBound * odeComponentBound * t := by ring
        _ ≤ integerMargin / 2 := htime
    have hm : 0 < integerMargin := by norm_num [integerMargin]
    linarith

  apply intervalIntegral_strictlyNegative
    (usableTime_pos hε)
  · exact rate_comp_continuousOn_usable
      (solution_continuousOn_usable hε hderiv)
      hrateContinuous
  · exact hneg

end Rational345R830LocalInterval
end NSBControl

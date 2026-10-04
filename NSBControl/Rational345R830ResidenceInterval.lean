import Mathlib.Tactic
import Mathlib.Analysis.Calculus.MeanValue
import NSBControl.Rational345R830LocalInterval

/-!
# R830 residence-aware terminal interval

The local Picard interval, the R828 certified horizon, and the bootstrap-ball
residence interval are independent positive scales.  The actual terminal time
used by the decision experiment is their positive minimum.
-/

open Set
open scoped Interval

namespace NSBControl
namespace Rational345R830ResidenceInterval

open Rational345ShortTime
open Rational345R830LocalInterval

/-- `usableTime ε` already combines Picard and the R828 horizon.  Intersect it
with half of the positive ball-residence radius. -/
def residenceUsableTime (ε δ : ℝ) : ℝ :=
  min (usableTime ε) (δ / 2)

theorem residenceUsableTime_pos
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    0 < residenceUsableTime ε δ := by
  rw [residenceUsableTime]
  exact lt_min (usableTime_pos hε) (by linarith)

theorem residenceUsableTime_le_usable (ε δ : ℝ) :
    residenceUsableTime ε δ ≤ usableTime ε :=
  min_le_left _ _

theorem residenceUsableTime_le_certified (ε δ : ℝ) :
    residenceUsableTime ε δ ≤ certifiedTime := by
  exact (residenceUsableTime_le_usable ε δ).trans
    (usableTime_le_certifiedTime ε)

theorem residenceUsableTime_lt_eps
    {ε δ : ℝ} (hε : 0 < ε) :
    residenceUsableTime ε δ < ε := by
  exact (residenceUsableTime_le_usable ε δ).trans_lt
    (usableTime_lt_eps hε)

theorem residenceUsableTime_lt_residence
    {ε δ : ℝ} (hδ : 0 < δ) :
    residenceUsableTime ε δ < δ := by
  calc
    residenceUsableTime ε δ ≤ δ / 2 := min_le_right _ _
    _ < δ := by linarith

theorem residence_Icc_inside_picard
    {ε δ t : ℝ} (hε : 0 < ε)
    (ht : t ∈ Icc (0 : ℝ) (residenceUsableTime ε δ)) :
    t ∈ Ioo (-ε) ε := by
  constructor
  · linarith [ht.1]
  · exact lt_of_le_of_lt ht.2 (residenceUsableTime_lt_eps hε)

theorem residence_Icc_abs_lt
    {ε δ t : ℝ} (hδ : 0 < δ)
    (ht : t ∈ Icc (0 : ℝ) (residenceUsableTime ε δ)) :
    |t| < δ := by
  have ht0 : 0 ≤ t := ht.1
  rw [abs_of_nonneg ht0]
  exact lt_of_le_of_lt ht.2 (residenceUsableTime_lt_residence hδ)

/-- A derivative bound on the whole Picard interval gives continuity on the
residence-aware terminal interval. -/
theorem solution_continuousOn_residence
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {field : E → E} {u : ℝ → E} {ε δ : ℝ}
    (hε : 0 < ε)
    (hderiv :
      ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt u (field (u t)) t) :
    ContinuousOn u (Icc (0 : ℝ) (residenceUsableTime ε δ)) := by
  intro t ht
  exact (hderiv t (residence_Icc_inside_picard hε ht)).continuousAt.continuousWithinAt

/-- O2 on the final interval: a ballwise field bound gives the linear
displacement estimate with no coordinatewise integration. -/
theorem displacement_le_on_residence
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : E → E)
    (u : ℝ → E) (u₀ : E)
    {ε δ K : ℝ}
    (hε : 0 < ε)
    (hu0 : u 0 = u₀)
    (hderiv :
      ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt u (field (u t)) t)
    (hfield :
      ∀ t ∈ Icc (0 : ℝ) (residenceUsableTime ε δ),
        ‖field (u t)‖ ≤ K) :
    ∀ t ∈ Icc (0 : ℝ) (residenceUsableTime ε δ),
      ‖u t - u₀‖ ≤ K * t := by
  intro t ht
  have hwithin :
      ∀ x ∈ Icc (0 : ℝ) (residenceUsableTime ε δ),
        HasDerivWithinAt u (field (u x))
          (Icc (0 : ℝ) (residenceUsableTime ε δ)) x := by
    intro x hx
    exact (hderiv x (residence_Icc_inside_picard hε hx)).hasDerivWithinAt
  have hbound :
      ∀ x ∈ Ico (0 : ℝ) (residenceUsableTime ε δ),
        ‖field (u x)‖ ≤ K := by
    intro x hx
    exact hfield x ⟨hx.1, le_of_lt hx.2⟩
  have hmv :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      (a := (0 : ℝ)) (b := residenceUsableTime ε δ)
      (f := u) (f' := fun x => field (u x))
      hwithin hbound t ht
  simpa [hu0] using hmv

/-- Terminal R830 compiler using a *direct* ballwise one-sided Lipschitz
estimate for the selected rate.  This lets B_P be proved by polynomial
difference estimates without packaging the full `fderiv` operator. -/
theorem negativeIntegral_from_residence_ball_lipschitz
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : E → E)
    (u : ℝ → E) (u₀ : E) (rate : E → ℝ)
    {ε δ radius : ℝ}
    (hε : 0 < ε)
    (hδ : 0 < δ)
    (hradius : 0 < radius)
    (hu0 : u 0 = u₀)
    (hderiv :
      ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt u (field (u t)) t)
    (hresidence :
      ∀ t : ℝ, |t| < δ →
        u t ∈ Metric.closedBall u₀ radius)
    (hfieldBall :
      ∀ x ∈ Metric.closedBall u₀ radius,
        ‖field x‖ ≤ odeComponentBound)
    (hrateBall :
      ∀ x ∈ Metric.closedBall u₀ radius,
        rate x - rate u₀ ≤ rateLipschitzBound * ‖x - u₀‖)
    (hrateContinuous : Continuous rate)
    (hinitial : rate u₀ ≤ -integerMargin) :
    (∫ t in (0 : ℝ)..residenceUsableTime ε δ, rate (u t)) < 0 := by
  let T := residenceUsableTime ε δ
  have hTpos : 0 < T := residenceUsableTime_pos hε hδ
  have hstay : ∀ t ∈ Icc (0 : ℝ) T,
      u t ∈ Metric.closedBall u₀ radius := by
    intro t ht
    exact hresidence t (residence_Icc_abs_lt hδ ht)
  have hdisp : ∀ t ∈ Icc (0 : ℝ) T,
      ‖u t - u₀‖ ≤ odeComponentBound * t := by
    apply displacement_le_on_residence field u u₀ hε hu0 hderiv
    intro t ht
    exact hfieldBall (u t) (hstay t ht)
  have hneg : ∀ t ∈ Icc (0 : ℝ) T, rate (u t) < 0 := by
    intro t ht
    have hrate := hrateBall (u t) (hstay t ht)
    have hdisp_t := hdisp t ht
    have hbudget :
        rateLipschitzBound * odeComponentBound * t
          ≤ integerMargin / 2 := by
      calc
        rateLipschitzBound * odeComponentBound * t
            ≤ rateLipschitzBound * odeComponentBound * T := by gcongr
        _ ≤ rateLipschitzBound * odeComponentBound * certifiedTime := by
              gcongr
              exact residenceUsableTime_le_certified ε δ
        _ = integerMargin / 2 := certifiedBudget_exact
    have hgrowth : rate (u t) - rate u₀ ≤ integerMargin / 2 := by
      calc
        rate (u t) - rate u₀
            ≤ rateLipschitzBound * ‖u t - u₀‖ := hrate
        _ ≤ rateLipschitzBound * (odeComponentBound * t) := by gcongr
        _ = rateLipschitzBound * odeComponentBound * t := by ring
        _ ≤ integerMargin / 2 := hbudget
    have hm : 0 < integerMargin := by norm_num [integerMargin]
    linarith
  apply intervalIntegral_strictlyNegative hTpos
  · exact hrateContinuous.continuousOn.comp
      (solution_continuousOn_residence hε hderiv)
      (fun _ ht => ht)
  · exact hneg

end Rational345R830ResidenceInterval
end NSBControl

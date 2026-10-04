import Mathlib.Tactic
import NSBControl.Rational345R830ResidenceInterval

/-!
# R830 pointwise negative-rate compiler

The residence-aware R830 proof already shows the selected rate is strictly
negative at every time in the certified interval before integrating it.  This
file exposes that fact publicly so later physical-subspace arguments may shrink
the terminal time again without rerunning B_Q/B_P arithmetic.
-/

open Set

namespace NSBControl
namespace Rational345R830PointwiseNegative

open Rational345ShortTime
open Rational345R830ResidenceInterval

/-- Direct public form of the pointwise inequality hidden inside the terminal
integration proof. -/
theorem negative_rate_on_residence
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
    (hinitial : rate u₀ ≤ -integerMargin) :
    ∀ t ∈ Icc (0 : ℝ) (residenceUsableTime ε δ),
      rate (u t) < 0 := by
  let T := residenceUsableTime ε δ
  have hstay : ∀ t ∈ Icc (0 : ℝ) T,
      u t ∈ Metric.closedBall u₀ radius := by
    intro t ht
    exact hresidence t (residence_Icc_abs_lt hδ ht)
  have hdisp : ∀ t ∈ Icc (0 : ℝ) T,
      ‖u t - u₀‖ ≤ odeComponentBound * t := by
    apply displacement_le_on_residence field u u₀ hε hu0 hderiv
    intro t ht
    exact hfieldBall (u t) (hstay t ht)
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

/-- Any smaller positive terminal time inherits strict negative integrated
payment.  This is the compiler consumed after imposing reality/divergence
invariance intervals. -/
theorem negative_integral_on_subinterval
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℝ → E) (rate : E → ℝ)
    {ε δ T : ℝ}
    (hT : 0 < T)
    (hTle : T ≤ residenceUsableTime ε δ)
    (hcont : ContinuousOn (fun t => rate (u t)) (Icc (0 : ℝ) T))
    (hneg :
      ∀ t ∈ Icc (0 : ℝ) (residenceUsableTime ε δ),
        rate (u t) < 0) :
    (∫ t in (0 : ℝ)..T, rate (u t)) < 0 := by
  apply intervalIntegral_strictlyNegative hT hcont
  intro t ht
  exact hneg t ⟨ht.1, ht.2.trans hTle⟩

end Rational345R830PointwiseNegative
end NSBControl

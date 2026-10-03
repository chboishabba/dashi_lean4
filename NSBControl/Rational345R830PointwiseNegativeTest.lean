import NSBControl.Rational345R830PointwiseNegative

namespace NSBControl
namespace Rational345R830PointwiseNegativeTest

open Set
open Rational345ShortTime
open Rational345R830ResidenceInterval
open Rational345R830PointwiseNegative

example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : E → E) (u : ℝ → E) (u₀ : E) (rate : E → ℝ)
    {ε δ radius : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hr : 0 < radius)
    (hu0 : u 0 = u₀)
    (hderiv : ∀ t ∈ Ioo (-ε) ε, HasDerivAt u (field (u t)) t)
    (hres : ∀ t : ℝ, |t| < δ → u t ∈ Metric.closedBall u₀ radius)
    (hfield : ∀ x ∈ Metric.closedBall u₀ radius, ‖field x‖ ≤ odeComponentBound)
    (hrate : ∀ x ∈ Metric.closedBall u₀ radius,
      rate x - rate u₀ ≤ rateLipschitzBound * ‖x-u₀‖)
    (hinit : rate u₀ ≤ -integerMargin) :
    ∀ t ∈ Icc (0 : ℝ) (residenceUsableTime ε δ), rate (u t) < 0 := by
  exact negative_rate_on_residence
    field u u₀ rate hε hδ hr hu0 hderiv hres hfield hrate hinit

end Rational345R830PointwiseNegativeTest
end NSBControl

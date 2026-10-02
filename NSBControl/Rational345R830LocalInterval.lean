import Mathlib.Tactic
import NSBControl.Rational345LocalODE
import NSBControl.Rational345ShortTime

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

end Rational345R830LocalInterval
end NSBControl

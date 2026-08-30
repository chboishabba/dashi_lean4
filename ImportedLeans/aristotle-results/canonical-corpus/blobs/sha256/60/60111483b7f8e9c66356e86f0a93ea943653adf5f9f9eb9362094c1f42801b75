/-
# Unit-mass normalization and endpoint bounds for window responses

`LiteralWeilWindowRatioSeparation` provides the two window estimates

* `crossIntegral_le` — an upper bound by the extreme kernel value of the common
  modulus bracket times the product of the two masses;
* `crossIntegral_ge` — a lower bound by the extreme kernel value on the gap between
  two separated windows times the product of the two masses.

Both become *purely geometric* once the tapers are normalized to unit mass.  This
module

* normalizes an arbitrary window taper without changing its window, sign, continuity
  or compact support (`WindowTaper.normalized`);
* records the resulting endpoint upper bound for the polarised cross response
  (`covForm_le_unitMass`), the endpoint upper bound for the *within-window* self
  response (`targetLeadingCoeff_le_unitMass`), and the endpoint lower bound for the
  cross response of two separated windows (`covForm_ge_unitMass`).

The self-response cap of a window of half-width `e` around a centre `c` is

    3/4 · ((c+e)² - (c-e)²) · (cosh (x (c+e)) - cosh (x (c-e)))

which vanishes at `e = 0`, whereas the cross-response floor of two windows around
`c < c'` tends to the strictly positive constant `3/4 (c'² - c²)(cosh (x c') - cosh (x c))`.
That contrast is what drives the narrow-window domination of the quartic remainder.

No `sorry`, no `axiom`, no Boolean receipt, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilWindowRatioSeparation

noncomputable section

open scoped Real
open MeasureTheory Set

namespace Zeta23Bridge
namespace LiteralWeilNormalizedWindowBounds

open Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient
open Zeta23Bridge.LiteralWeilLeadingCoefficientCovariance
open Zeta23Bridge.LiteralWeilWindowRatioSeparation
open Zeta23Bridge.CoshWindowSeparation

/-! ## Unit-mass normalization -/

/-- The unit-mass rescaling of a taper. -/
def normalized (f : ℝ → ℝ) : ℝ → ℝ := fun u => (∫ t : ℝ, f t)⁻¹ * f u

/-- Normalization preserves the window, the sign, continuity and compact support. -/
theorem windowTaper_normalized {f : ℝ → ℝ} {lo hi : ℝ} (h : WindowTaper f lo hi) :
    WindowTaper (normalized f) lo hi := by
  have hmass : (0:ℝ) < ∫ t : ℝ, f t := h.mass
  have hinv : (0:ℝ) < (∫ t : ℝ, f t)⁻¹ := inv_pos.mpr hmass
  refine ⟨continuous_const.mul h.cont, h.cpt.mul_left, fun u => mul_nonneg hinv.le (h.nonneg u),
    ?_, ?_⟩
  · intro u hu
    refine h.supp u ?_
    intro hf
    apply hu
    simp [normalized, hf]
  · have : (∫ u : ℝ, normalized f u)
        = (∫ t : ℝ, f t)⁻¹ * ∫ u : ℝ, f u := by
      simpa [normalized] using
        integral_const_mul (μ := (volume : Measure ℝ)) ((∫ t : ℝ, f t)⁻¹) f
    rw [this]
    exact mul_pos hinv hmass

/-- The normalization really has unit mass. -/
theorem integral_normalized {f : ℝ → ℝ} (hf : (0:ℝ) < ∫ t : ℝ, f t) :
    (∫ u : ℝ, normalized f u) = 1 := by
  have h : (∫ u : ℝ, normalized f u) = (∫ t : ℝ, f t)⁻¹ * ∫ u : ℝ, f u := by
    simpa [normalized] using
      integral_const_mul (μ := (volume : Measure ℝ)) ((∫ t : ℝ, f t)⁻¹) f
  rw [h, inv_mul_cancel₀ hf.ne']

/-! ## Endpoint caps and floors -/

/-- The endpoint cap of the polarised response of two unit-mass tapers sharing the
modulus bracket `[lo, hi]`. -/
def responseCap (x lo hi : ℝ) : ℝ := 3 / 4 * ((hi ^ 2 - lo ^ 2) * coshDiff x lo hi)

/-- The endpoint floor of the polarised response of two unit-mass tapers in the
separated windows `[·, be0]` and `[al1, ·]`. -/
def responseFloor (x be0 al1 : ℝ) : ℝ := 3 / 4 * ((al1 ^ 2 - be0 ^ 2) * coshDiff x be0 al1)

theorem responseCap_nonneg {x lo hi : ℝ} (hx : 0 < x) (hlo : 0 < lo) (hhi : lo ≤ hi) :
    0 ≤ responseCap x lo hi := by
  have h1 : 0 ≤ hi ^ 2 - lo ^ 2 := by nlinarith
  have h2 : 0 ≤ coshDiff x lo hi := by
    rcases eq_or_lt_of_le hhi with rfl | h
    · simp [coshDiff]
    · exact (coshDiff_pos hx hlo h).le
  have : 0 ≤ (hi ^ 2 - lo ^ 2) * coshDiff x lo hi := mul_nonneg h1 h2
  unfold responseCap
  linarith

theorem responseFloor_pos {x be0 al1 : ℝ} (hx : 0 < x) (hbe0 : 0 < be0) (h : be0 < al1) :
    0 < responseFloor x be0 al1 := by
  have h1 : 0 < al1 ^ 2 - be0 ^ 2 := by nlinarith
  have h2 : 0 < coshDiff x be0 al1 := coshDiff_pos hx hbe0 h
  unfold responseFloor
  positivity

/-- **Endpoint cap for the polarised cross response.**  Two unit-mass window tapers in
a common modulus bracket respond at most by the extreme kernel value of the bracket. -/
theorem covForm_le_unitMass {p q : ℝ → ℝ} {lo hi x : ℝ}
    (hp : WindowTaper p lo hi) (hq : WindowTaper q lo hi)
    (hpm : (∫ u : ℝ, p u) = 1) (hqm : (∫ u : ℝ, q u) = 1) (hx : 0 < x) (hlo : 0 < lo) :
    covForm p q x ≤ responseCap x lo hi := by
  have hcross := crossIntegral_le hp hq hx hlo
  rw [hpm, hqm] at hcross
  rw [covForm_eq_crossIntegral' hp.cont hp.cpt hq.cont hq.cpt]
  unfold responseCap
  nlinarith [hcross]

/-- **Endpoint cap for the within-window self response.** -/
theorem targetLeadingCoeff_le_unitMass {p : ℝ → ℝ} {lo hi x : ℝ}
    (hp : WindowTaper p lo hi) (hpm : (∫ u : ℝ, p u) = 1) (hx : 0 < x) (hlo : 0 < lo) :
    targetLeadingCoeff p x ≤ responseCap x lo hi := by
  rw [← covForm_self]
  exact covForm_le_unitMass hp hp hpm hpm hx hlo

/-- **Endpoint floor for the polarised cross response of two separated windows.** -/
theorem covForm_ge_unitMass {p q : ℝ → ℝ} {al0 be0 al1 be1 x : ℝ}
    (hp : WindowTaper p al0 be0) (hq : WindowTaper q al1 be1)
    (hpm : (∫ u : ℝ, p u) = 1) (hqm : (∫ u : ℝ, q u) = 1)
    (hx : 0 < x) (hal0 : 0 < al0) (h0 : al0 ≤ be0) (h01 : be0 < al1) :
    responseFloor x be0 al1 ≤ covForm p q x := by
  have hcross := crossIntegral_ge hp hq hx hal0 h0 h01
  rw [hpm, hqm] at hcross
  rw [covForm_eq_crossIntegral' hp.cont hp.cpt hq.cont hq.cpt]
  unfold responseFloor
  nlinarith [hcross]

end LiteralWeilNormalizedWindowBounds
end Zeta23Bridge

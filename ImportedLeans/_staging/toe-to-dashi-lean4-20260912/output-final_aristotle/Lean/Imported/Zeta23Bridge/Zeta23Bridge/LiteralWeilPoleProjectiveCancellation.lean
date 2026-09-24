/-
# The pole channel at determinant level: a quadratic gain, with no extra taper condition

The previous lane asked a single taper to kill the even pole response at *both*
sampling radii,

    P_t(r) = P_t(2r) = 0,

two linear constraints, of which only the first was ever achieved
(`exists_positive_taper_poleEven_zero`); the doubled radius then stayed exposed as
the term `4 |P_t(2r)| |A_0(r)|` of `reducedEnvelope`.

The observable, however, is only the *determinant*

    𝔇_Π(r) = -4 ( P_t(2r) A_0(r) - P_t(r) A_0(2r) ),

so what one really wants is the single scalar condition `𝔇_Π = 0`, i.e. that the
pole profile be projectively collinear with the on-line profile.

This module proves something better than an existence statement for that one
condition: for **every** admissible taper the pole projective defect is
*automatically* quadratically small in the sampling radius.  The reason is
structural.  The pole channel is the cosine transform, in the sampling radius, of
the fixed weight

    W_Π(u) = g(u) cosh(u/2) cos(t u),

so by `LiteralWeilProjectiveTaper.cosineChannelProjective` its determinant against
the on-line profile is the *same* channel read at sampling radius `0` with the
taper replaced by the projective taper `h_r = g B_r`:

    𝔇_Π(r) = -4 · P_t^{(h_r)}(0)                     (`poleProjectiveDefect_eq_projTaper`),

and the bracket `B_r` is `O(r²)` uniformly on the support.  Hence

    |𝔇_Π(r)| ≤ 20 r² Λ² ‖g‖₁ ‖W_Π‖₁ ≤ 20 r² Λ² cosh(Λ/2) ‖g‖₁²   (`abs_poleProjectiveDefect_le`).

The old radiuswise envelope for this channel was `4|P_t(2r)||A_0(r)| + 4|P_t(r)||A_0(2r)|`,
which is `O(1)`.  So the projective treatment converts the pole channel from an
`O(1)` obstruction into an `O(r²)` one, without imposing any new condition on the
taper — in particular the search for an exactly projectively collinear pole profile
is unnecessary.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilProjectiveTaper

noncomputable section

open MeasureTheory
open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilPoleProjectiveCancellation

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilProjectiveTaper

/-! ## The pole channel is a cosine transform in the sampling radius -/

/-- The fixed weight of the pole channel, `W_Π(u) = g(u) cosh(u/2) cos(tu)`. -/
def poleWeight (g : ℝ → ℝ) (t : ℝ) : ℝ → ℝ :=
  fun u => g u * (Real.cosh (u / 2) * Real.cos (t * u))

theorem poleWeight_continuous {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ) :
    Continuous (poleWeight g t) := by
  unfold poleWeight; fun_prop

theorem poleWeight_hasCompactSupport {g : ℝ → ℝ} (hgc : HasCompactSupport g) (t : ℝ) :
    HasCompactSupport (poleWeight g t) :=
  hgc.mul_right

theorem poleWeight_support {g : ℝ → ℝ} {Λ : ℝ} (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (t : ℝ) :
    ∀ u, poleWeight g t u ≠ 0 → |u| ≤ Λ := by
  intro u hu
  refine hsupp u fun h => hu ?_
  simp [poleWeight, h]

/-- The even pole response is the cosine transform of the pole weight. -/
theorem poleEvenResp_eq_cosineTransform (g : ℝ → ℝ) (t s : ℝ) :
    poleEvenResp g t s = ∫ u : ℝ, poleWeight g t u * Real.cos (s * u) := by
  unfold poleEvenResp poleWeight
  congr 1
  funext u
  ring

/-- The projective taper's pole weight is the original pole weight times the bracket. -/
theorem poleWeight_projTaper (g : ℝ → ℝ) (t r : ℝ) :
    poleWeight (projTaper g r) t = fun u => poleWeight g t u * twoRadiusBracket g r u := by
  funext u
  unfold poleWeight projTaper
  ring

/-! ## Transport: the pole determinant is the pole channel of the projective taper -/

/-- **`poleDeterminant_eq_projTaper`.**  The determinant of the pole profile against
the on-line profile is the even pole response of the projective taper, read at
sampling radius `0`. -/
theorem poleDeterminant_eq_projTaper {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (t r : ℝ) :
    poleEvenResp g t (2 * r) * evenResp g 0 r - poleEvenResp g t r * evenResp g 0 (2 * r)
      = poleEvenResp (projTaper g r) t 0 := by
  have hFc : Continuous (poleWeight g t) := poleWeight_continuous hg t
  have hFk : HasCompactSupport (poleWeight g t) := poleWeight_hasCompactSupport hgc t
  rw [poleEvenResp_eq_cosineTransform g t (2 * r), poleEvenResp_eq_cosineTransform g t r,
    cosineChannelProjective hFc hFk g r, poleEvenResp_eq_cosineTransform (projTaper g r) t 0,
    poleWeight_projTaper]
  congr 1
  funext u
  simp

/-- **`poleProjectiveDefect_eq_projTaper`.**  The pole projective defect is `-4`
times the pole response of the projective taper at sampling radius `0`. -/
theorem poleProjectiveDefect_eq_projTaper {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    poleProjectiveDefect g t r = -4 * poleEvenResp (projTaper g r) t 0 := by
  rw [poleProjectiveDefect_eq hg hgc heven t r, poleDeterminant_eq_projTaper hg hgc t r]

/-! ## The quadratic envelope -/

/-- **`abs_poleProjectiveDefect_le`.**  The pole projective defect is quadratically
small in the sampling radius, with an explicit constant, for *every* admissible
taper: no extra collinearity condition is needed. -/
theorem abs_poleProjectiveDefect_le {g : ℝ → ℝ} {Λ : ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (t r : ℝ) :
    |poleProjectiveDefect g t r|
      ≤ 20 * r ^ 2 * Λ ^ 2 * taperMass g * taperMass (poleWeight g t) := by
  have hFc : Continuous (poleWeight g t) := poleWeight_continuous hg t
  have hFk : HasCompactSupport (poleWeight g t) := poleWeight_hasCompactSupport hgc t
  have hFs : ∀ u, poleWeight g t u ≠ 0 → |u| ≤ Λ := poleWeight_support hsupp t
  have hbound := abs_integral_mul_bracket_le hg hgc hsupp hFc hFk hFs r
  have hid : poleProjectiveDefect g t r
      = -4 * ∫ u : ℝ, poleWeight g t u * twoRadiusBracket g r u := by
    rw [poleProjectiveDefect_eq hg hgc heven t r, poleEvenResp_eq_cosineTransform g t (2 * r),
      poleEvenResp_eq_cosineTransform g t r, cosineChannelProjective hFc hFk g r]
  rw [hid, abs_mul]
  have : |(-4 : ℝ)| = 4 := by norm_num
  rw [this]
  linarith

/-- The pole weight's mass is controlled by the taper's, with the strip factor. -/
theorem taperMass_poleWeight_le {g : ℝ → ℝ} {Λ : ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (t : ℝ) :
    taperMass (poleWeight g t) ≤ Real.cosh (Λ / 2) * taperMass g := by
  have hi : Integrable (fun u : ℝ => |poleWeight g t u|) :=
    ((poleWeight_continuous hg t).abs).integrable_of_hasCompactSupport
      (poleWeight_hasCompactSupport hgc t).abs
  have hb : Integrable (fun u : ℝ => Real.cosh (Λ / 2) * |g u|) :=
    ((hg.abs).integrable_of_hasCompactSupport hgc.abs).const_mul _
  have hpt : ∀ u : ℝ, |poleWeight g t u| ≤ Real.cosh (Λ / 2) * |g u| := by
    intro u
    rcases eq_or_ne (g u) 0 with h | h
    · simp [poleWeight, h]
    · have hu : |u| ≤ Λ := hsupp u h
      have hcosh : Real.cosh (u / 2) ≤ Real.cosh (Λ / 2) := by
        rw [Real.cosh_le_cosh]
        rw [abs_div, abs_div]
        have : |u| ≤ |Λ| := hu.trans (le_abs_self Λ)
        have h2 : |(2 : ℝ)| = 2 := by norm_num
        rw [h2]
        exact div_le_div_of_nonneg_right this (by norm_num) |>.trans_eq rfl
      have hcoshpos : 0 < Real.cosh (u / 2) := Real.cosh_pos _
      unfold poleWeight
      rw [abs_mul, abs_mul]
      have hc : |Real.cos (t * u)| ≤ 1 := Real.abs_cos_le_one _
      have habs : |Real.cosh (u / 2)| = Real.cosh (u / 2) := abs_of_pos hcoshpos
      rw [habs]
      calc |g u| * (Real.cosh (u / 2) * |Real.cos (t * u)|)
          ≤ |g u| * (Real.cosh (Λ / 2) * 1) := by
            gcongr
        _ = Real.cosh (Λ / 2) * |g u| := by ring
  calc taperMass (poleWeight g t) = ∫ u : ℝ, |poleWeight g t u| := rfl
    _ ≤ ∫ u : ℝ, Real.cosh (Λ / 2) * |g u| := integral_mono hi hb hpt
    _ = Real.cosh (Λ / 2) * taperMass g := by rw [integral_const_mul]; rfl

/-- **`abs_poleProjectiveDefect_le'`.**  The same envelope, with the pole weight
eliminated in favour of the taper mass and the strip factor `cosh(Λ/2)`. -/
theorem abs_poleProjectiveDefect_le' {g : ℝ → ℝ} {Λ : ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (t r : ℝ) :
    |poleProjectiveDefect g t r|
      ≤ 20 * r ^ 2 * Λ ^ 2 * Real.cosh (Λ / 2) * taperMass g ^ 2 := by
  have h1 := abs_poleProjectiveDefect_le hg hgc heven hsupp t r
  have h2 := taperMass_poleWeight_le hg hgc hsupp t
  have hM := taperMass_nonneg g
  have hc : 0 < 20 * r ^ 2 * Λ ^ 2 * taperMass g ∨ 20 * r ^ 2 * Λ ^ 2 * taperMass g = 0 := by
    rcases lt_or_eq_of_le (by positivity : (0:ℝ) ≤ 20 * r ^ 2 * Λ ^ 2 * taperMass g) with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  have hstep : 20 * r ^ 2 * Λ ^ 2 * taperMass g * taperMass (poleWeight g t)
      ≤ 20 * r ^ 2 * Λ ^ 2 * taperMass g * (Real.cosh (Λ / 2) * taperMass g) := by
    refine mul_le_mul_of_nonneg_left h2 (by positivity)
  have hfin : 20 * r ^ 2 * Λ ^ 2 * taperMass g * (Real.cosh (Λ / 2) * taperMass g)
      = 20 * r ^ 2 * Λ ^ 2 * Real.cosh (Λ / 2) * taperMass g ^ 2 := by ring
  linarith [hfin ▸ hstep]

end LiteralWeilPoleProjectiveCancellation
end Zeta23Bridge

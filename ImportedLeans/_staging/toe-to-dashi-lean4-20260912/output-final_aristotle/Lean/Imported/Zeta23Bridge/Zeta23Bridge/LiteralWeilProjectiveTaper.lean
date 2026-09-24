/-
# The projective taper: one modified test profile that carries every two-radius determinant

The projective defect of a channel `C`,

    𝔇_C(r) = C(2r) A_0(r) - C(r) A_0(2r),

is a *determinant*, and every literal channel is a linear functional of the taper.
Consequently `𝔇_C` is the same channel evaluated at a *single* modified profile.
The modification is the **two-radius bracket**

    B_r(u) = A_0(r) cos(2 r u) - A_0(2r) cos(r u)                (`twoRadiusBracket`)

and the modified profile is the **projective taper**

    h_r(u) = g(u) B_r(u)                                        (`projTaper`).

The point of the construction is that `B_r` is *quadratically small in `r`* on the
support of the taper, uniformly, with completely explicit constants:

    |B_r(u)|   ≤ 5 r² Λ² ‖g‖₁,
    |B_r'(u)|  ≤ 5 r² Λ  ‖g‖₁,
    |B_r''(u)| ≤ 5 r²    ‖g‖₁            for `|u| ≤ Λ`.

At `r = 0` the two columns of the determinant coincide, which is exactly why the
bracket vanishes to second order; the radiuswise triangle inequality
`|C(2r)||A_0(r)| + |C(r)||A_0(2r)|` destroys this and is `O(1)`.

This module proves the bracket bounds and the transport identity for any channel
given by a cosine transform,

    (∫ F cos(2r·)) A_0(r) - (∫ F cos(r·)) A_0(2r) = ∫ F B_r      (`cosineChannelProjective`),

together with the resulting quadratic envelope.  The pole, off-ordinate and gamma
channels are treated in the modules that follow.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition

noncomputable section

open MeasureTheory
open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilProjectiveTaper

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition

/-! ## The `L¹` mass of a taper -/

/-- The `L¹` mass `‖g‖₁` of the taper. -/
def taperMass (g : ℝ → ℝ) : ℝ := ∫ u : ℝ, |g u|

theorem taperMass_nonneg (g : ℝ → ℝ) : 0 ≤ taperMass g :=
  integral_nonneg fun _ => abs_nonneg _

theorem evenResp_zero_height (g : ℝ → ℝ) (s : ℝ) :
    evenResp g 0 s = ∫ u : ℝ, g u * Real.cos (s * u) := by
  unfold evenResp
  simp

/-- The absolute value of the on-line even response never exceeds the taper mass. -/
theorem abs_evenResp_zero_le {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (s : ℝ) : |evenResp g 0 s| ≤ taperMass g := by
  have hi : Integrable (fun u : ℝ => g u * Real.cos (s * u)) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hgc.mul_right
  have habs : Integrable (fun u : ℝ => |g u|) :=
    (hg.abs).integrable_of_hasCompactSupport (hgc.abs)
  rw [evenResp_zero_height]
  calc |∫ u : ℝ, g u * Real.cos (s * u)| ≤ ∫ u : ℝ, |g u * Real.cos (s * u)| := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun u : ℝ => g u * Real.cos (s * u))
    _ ≤ ∫ u : ℝ, |g u| := by
        refine integral_mono (hi.abs) habs (fun u => ?_)
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    _ = taperMass g := rfl

/-! ## The two-radius bracket -/

/-- **The two-radius bracket** `B_r(u) = A_0(r) cos(2ru) - A_0(2r) cos(ru)`. -/
def twoRadiusBracket (g : ℝ → ℝ) (r : ℝ) : ℝ → ℝ := fun u =>
  evenResp g 0 r * Real.cos (2 * r * u) - evenResp g 0 (2 * r) * Real.cos (r * u)

theorem twoRadiusBracket_even (g : ℝ → ℝ) (r u : ℝ) :
    twoRadiusBracket g r (-u) = twoRadiusBracket g r u := by
  unfold twoRadiusBracket
  rw [show 2 * r * -u = -(2 * r * u) by ring, show r * -u = -(r * u) by ring,
    Real.cos_neg, Real.cos_neg]

theorem twoRadiusBracket_contDiff (g : ℝ → ℝ) (r : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (twoRadiusBracket g r) := by
  unfold twoRadiusBracket
  fun_prop

/-! ### Elementary quadratic estimates -/

/-- `|cos a - 1| ≤ a²/2`. -/
theorem abs_cos_sub_one_le (a : ℝ) : |Real.cos a - 1| ≤ a ^ 2 / 2 := by
  have h1 : Real.cos a ≤ 1 := Real.cos_le_one a
  have h2 : 1 - a ^ 2 / 2 ≤ Real.cos a := Real.one_sub_sq_div_two_le_cos
  rw [abs_le]
  constructor <;> linarith

/-- The difference of the two on-line responses is quadratically small. -/
theorem abs_evenResp_sub_le {g : ℝ → ℝ} {Λ : ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (r : ℝ) :
    |evenResp g 0 r - evenResp g 0 (2 * r)| ≤ 5 / 2 * r ^ 2 * Λ ^ 2 * taperMass g := by
  have hi1 : Integrable (fun u : ℝ => g u * Real.cos (r * u)) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hgc.mul_right
  have hi2 : Integrable (fun u : ℝ => g u * Real.cos (2 * r * u)) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hgc.mul_right
  have hb : Integrable (fun u : ℝ => 5 / 2 * r ^ 2 * Λ ^ 2 * |g u|) :=
    ((hg.abs).integrable_of_hasCompactSupport (hgc.abs)).const_mul _
  have hpt : ∀ u : ℝ, |g u * Real.cos (r * u) - g u * Real.cos (2 * r * u)|
      ≤ 5 / 2 * r ^ 2 * Λ ^ 2 * |g u| := by
    intro u
    rcases eq_or_ne (g u) 0 with h | h
    · simp [h]
    · have hu : |u| ≤ Λ := hsupp u h
      have hu2 : u ^ 2 ≤ Λ ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
      have e1 : |Real.cos (r * u) - 1| ≤ (r * u) ^ 2 / 2 := abs_cos_sub_one_le _
      have e2 : |Real.cos (2 * r * u) - 1| ≤ (2 * r * u) ^ 2 / 2 := abs_cos_sub_one_le _
      have hdiff : |Real.cos (r * u) - Real.cos (2 * r * u)|
          ≤ |Real.cos (r * u) - 1| + |Real.cos (2 * r * u) - 1| := by
        calc |Real.cos (r * u) - Real.cos (2 * r * u)|
            = |(Real.cos (r * u) - 1) - (Real.cos (2 * r * u) - 1)| := by ring_nf
          _ ≤ |Real.cos (r * u) - 1| + |Real.cos (2 * r * u) - 1| := abs_sub _ _
      have hsum : |Real.cos (r * u) - Real.cos (2 * r * u)| ≤ 5 / 2 * r ^ 2 * Λ ^ 2 := by
        nlinarith [sq_nonneg r, sq_nonneg u]
      calc |g u * Real.cos (r * u) - g u * Real.cos (2 * r * u)|
          = |g u| * |Real.cos (r * u) - Real.cos (2 * r * u)| := by
            rw [← abs_mul]; ring_nf
        _ ≤ |g u| * (5 / 2 * r ^ 2 * Λ ^ 2) := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
        _ = 5 / 2 * r ^ 2 * Λ ^ 2 * |g u| := by ring
  rw [evenResp_zero_height, evenResp_zero_height, ← integral_sub hi1 hi2]
  calc |∫ u : ℝ, (g u * Real.cos (r * u) - g u * Real.cos (2 * r * u))|
      ≤ ∫ u : ℝ, |g u * Real.cos (r * u) - g u * Real.cos (2 * r * u)| := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm
            (fun u : ℝ => g u * Real.cos (r * u) - g u * Real.cos (2 * r * u))
    _ ≤ ∫ u : ℝ, 5 / 2 * r ^ 2 * Λ ^ 2 * |g u| := integral_mono (hi1.sub hi2).abs hb hpt
    _ = 5 / 2 * r ^ 2 * Λ ^ 2 * taperMass g := by
        rw [integral_const_mul]; rfl

/-- **The bracket is quadratically small on the support of the taper.** -/
theorem abs_twoRadiusBracket_le {g : ℝ → ℝ} {Λ : ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (r : ℝ) {u : ℝ}
    (hu : |u| ≤ Λ) : |twoRadiusBracket g r u| ≤ 5 * r ^ 2 * Λ ^ 2 * taperMass g := by
  have hM := taperMass_nonneg g
  have hA1 := abs_evenResp_zero_le hg hgc r
  have hA2 := abs_evenResp_zero_le hg hgc (2 * r)
  have hd := abs_evenResp_sub_le hg hgc hsupp r
  have hu2 : u ^ 2 ≤ Λ ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
  have e1 : |Real.cos (2 * r * u) - 1| ≤ (2 * r * u) ^ 2 / 2 := abs_cos_sub_one_le _
  have e2 : |Real.cos (r * u) - 1| ≤ (r * u) ^ 2 / 2 := abs_cos_sub_one_le _
  have hsplit : twoRadiusBracket g r u
      = evenResp g 0 r * (Real.cos (2 * r * u) - 1)
        - evenResp g 0 (2 * r) * (Real.cos (r * u) - 1)
        + (evenResp g 0 r - evenResp g 0 (2 * r)) := by
    unfold twoRadiusBracket; ring
  have h1 : |evenResp g 0 r * (Real.cos (2 * r * u) - 1)| ≤ 2 * taperMass g * (r ^ 2 * u ^ 2) := by
    rw [abs_mul]
    calc |evenResp g 0 r| * |Real.cos (2 * r * u) - 1|
        ≤ taperMass g * ((2 * r * u) ^ 2 / 2) := mul_le_mul hA1 e1 (abs_nonneg _) hM
      _ = 2 * taperMass g * (r ^ 2 * u ^ 2) := by ring
  have h2 : |evenResp g 0 (2 * r) * (Real.cos (r * u) - 1)|
      ≤ taperMass g * (r ^ 2 * u ^ 2) / 2 := by
    rw [abs_mul]
    calc |evenResp g 0 (2 * r)| * |Real.cos (r * u) - 1|
        ≤ taperMass g * ((r * u) ^ 2 / 2) := mul_le_mul hA2 e2 (abs_nonneg _) hM
      _ = taperMass g * (r ^ 2 * u ^ 2) / 2 := by ring
  have hkey : taperMass g * (r ^ 2 * u ^ 2) ≤ taperMass g * (r ^ 2 * Λ ^ 2) := by
    have : r ^ 2 * u ^ 2 ≤ r ^ 2 * Λ ^ 2 := by nlinarith [sq_nonneg r]
    exact mul_le_mul_of_nonneg_left this hM
  have hchain := abs_add_le (evenResp g 0 r * (Real.cos (2 * r * u) - 1)
      - evenResp g 0 (2 * r) * (Real.cos (r * u) - 1)) (evenResp g 0 r - evenResp g 0 (2 * r))
  have hsub := abs_sub (evenResp g 0 r * (Real.cos (2 * r * u) - 1))
      (evenResp g 0 (2 * r) * (Real.cos (r * u) - 1))
  rw [hsplit]
  linarith

/-! ### The derivatives of the bracket -/

/-- The closed form of the first derivative of the bracket. -/
def bracketDeriv (g : ℝ → ℝ) (r : ℝ) : ℝ → ℝ := fun u =>
  evenResp g 0 r * (-Real.sin (2 * r * u) * (2 * r))
    - evenResp g 0 (2 * r) * (-Real.sin (r * u) * r)

theorem hasDerivAt_twoRadiusBracket (g : ℝ → ℝ) (r u : ℝ) :
    HasDerivAt (twoRadiusBracket g r) (bracketDeriv g r u) u := by
  have hl1 : HasDerivAt (fun u : ℝ => 2 * r * u) (2 * r) u := by
    simpa using (hasDerivAt_id u).const_mul (2 * r)
  have hl2 : HasDerivAt (fun u : ℝ => r * u) r u := by
    simpa using (hasDerivAt_id u).const_mul r
  exact (hl1.cos.const_mul (evenResp g 0 r)).sub (hl2.cos.const_mul (evenResp g 0 (2 * r)))

theorem deriv_twoRadiusBracket (g : ℝ → ℝ) (r : ℝ) :
    deriv (twoRadiusBracket g r) = bracketDeriv g r :=
  funext fun u => (hasDerivAt_twoRadiusBracket g r u).deriv

theorem hasDerivAt_bracketDeriv (g : ℝ → ℝ) (r u : ℝ) :
    HasDerivAt (bracketDeriv g r)
      (evenResp g 0 r * (-(Real.cos (2 * r * u) * (2 * r)) * (2 * r))
        - evenResp g 0 (2 * r) * (-(Real.cos (r * u) * r) * r)) u := by
  have hl1 : HasDerivAt (fun u : ℝ => 2 * r * u) (2 * r) u := by
    simpa using (hasDerivAt_id u).const_mul (2 * r)
  have hl2 : HasDerivAt (fun u : ℝ => r * u) r u := by
    simpa using (hasDerivAt_id u).const_mul r
  exact (((hl1.sin).neg.mul_const (2 * r)).const_mul (evenResp g 0 r)).sub
    (((hl2.sin).neg.mul_const r).const_mul (evenResp g 0 (2 * r)))

/-- **The first derivative of the bracket is quadratically small.** -/
theorem abs_deriv_twoRadiusBracket_le {g : ℝ → ℝ} {Λ : ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (r : ℝ) {u : ℝ} (hu : |u| ≤ Λ) :
    |deriv (twoRadiusBracket g r) u| ≤ 5 * r ^ 2 * Λ * taperMass g := by
  have hM := taperMass_nonneg g
  have hA1 := abs_evenResp_zero_le hg hgc r
  have hA2 := abs_evenResp_zero_le hg hgc (2 * r)
  have h2r : |2 * r| = 2 * |r| := by rw [abs_mul]; norm_num
  have hs1 : |Real.sin (2 * r * u)| ≤ 2 * |r| * |u| := by
    refine Real.abs_sin_le_abs.trans ?_
    rw [abs_mul, h2r]
  have hs2 : |Real.sin (r * u)| ≤ |r| * |u| := by
    refine Real.abs_sin_le_abs.trans ?_
    rw [abs_mul]
  have hrr : |r| * |r| = r * r := abs_mul_abs_self r
  have e1 : |evenResp g 0 r * (-Real.sin (2 * r * u) * (2 * r))|
      ≤ taperMass g * (2 * |r| * |u|) * (2 * |r|) := by
    rw [abs_mul, abs_mul, abs_neg, h2r]
    have hstep : |evenResp g 0 r| * |Real.sin (2 * r * u)| ≤ taperMass g * (2 * |r| * |u|) :=
      mul_le_mul hA1 hs1 (abs_nonneg _) hM
    calc |evenResp g 0 r| * (|Real.sin (2 * r * u)| * (2 * |r|))
        = |evenResp g 0 r| * |Real.sin (2 * r * u)| * (2 * |r|) := by ring
      _ ≤ taperMass g * (2 * |r| * |u|) * (2 * |r|) := by
          exact mul_le_mul_of_nonneg_right hstep (by positivity)
  have e2 : |evenResp g 0 (2 * r) * (-Real.sin (r * u) * r)|
      ≤ taperMass g * (|r| * |u|) * |r| := by
    rw [abs_mul, abs_mul, abs_neg]
    have hstep : |evenResp g 0 (2 * r)| * |Real.sin (r * u)| ≤ taperMass g * (|r| * |u|) :=
      mul_le_mul hA2 hs2 (abs_nonneg _) hM
    calc |evenResp g 0 (2 * r)| * (|Real.sin (r * u)| * |r|)
        = |evenResp g 0 (2 * r)| * |Real.sin (r * u)| * |r| := by ring
      _ ≤ taperMass g * (|r| * |u|) * |r| := mul_le_mul_of_nonneg_right hstep (abs_nonneg _)
  have hsum := abs_sub (evenResp g 0 r * (-Real.sin (2 * r * u) * (2 * r)))
    (evenResp g 0 (2 * r) * (-Real.sin (r * u) * r))
  have hid : taperMass g * (2 * |r| * |u|) * (2 * |r|) + taperMass g * (|r| * |u|) * |r|
      = 5 * (|r| * |r|) * |u| * taperMass g := by ring
  rw [hrr] at hid
  have hfin : 5 * (r * r) * |u| * taperMass g ≤ 5 * r ^ 2 * Λ * taperMass g := by
    have hpos : 0 ≤ r * r * (Λ - |u|) * taperMass g :=
      mul_nonneg (mul_nonneg (mul_self_nonneg r) (sub_nonneg.mpr hu)) hM
    have hsq : r ^ 2 = r * r := pow_two r
    rw [hsq]
    nlinarith [hpos]
  rw [deriv_twoRadiusBracket]
  unfold bracketDeriv
  linarith

/-- **The second derivative of the bracket is quadratically small.** -/
theorem abs_deriv2_twoRadiusBracket_le {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (r u : ℝ) :
    |deriv (deriv (twoRadiusBracket g r)) u| ≤ 5 * r ^ 2 * taperMass g := by
  have hM := taperMass_nonneg g
  have hA1 := abs_evenResp_zero_le hg hgc r
  have hA2 := abs_evenResp_zero_le hg hgc (2 * r)
  have hc1 : |Real.cos (2 * r * u)| ≤ 1 := Real.abs_cos_le_one _
  have hc2 : |Real.cos (r * u)| ≤ 1 := Real.abs_cos_le_one _
  have h2r : |2 * r| = 2 * |r| := by rw [abs_mul]; norm_num
  have hrr : |r| * |r| = r * r := abs_mul_abs_self r
  have e1 : |evenResp g 0 r * (-(Real.cos (2 * r * u) * (2 * r)) * (2 * r))|
      ≤ taperMass g * (2 * |r|) * (2 * |r|) := by
    rw [abs_mul, abs_mul, abs_neg, abs_mul, h2r]
    have hstep : |evenResp g 0 r| * |Real.cos (2 * r * u)| ≤ taperMass g :=
      by nlinarith [abs_nonneg (evenResp g 0 r), abs_nonneg (Real.cos (2 * r * u))]
    calc |evenResp g 0 r| * (|Real.cos (2 * r * u)| * (2 * |r|) * (2 * |r|))
        = |evenResp g 0 r| * |Real.cos (2 * r * u)| * ((2 * |r|) * (2 * |r|)) := by ring
      _ ≤ taperMass g * ((2 * |r|) * (2 * |r|)) := by
          exact mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = taperMass g * (2 * |r|) * (2 * |r|) := by ring
  have e2 : |evenResp g 0 (2 * r) * (-(Real.cos (r * u) * r) * r)|
      ≤ taperMass g * |r| * |r| := by
    rw [abs_mul, abs_mul, abs_neg, abs_mul]
    have hstep : |evenResp g 0 (2 * r)| * |Real.cos (r * u)| ≤ taperMass g :=
      by nlinarith [abs_nonneg (evenResp g 0 (2 * r)), abs_nonneg (Real.cos (r * u))]
    calc |evenResp g 0 (2 * r)| * (|Real.cos (r * u)| * |r| * |r|)
        = |evenResp g 0 (2 * r)| * |Real.cos (r * u)| * (|r| * |r|) := by ring
      _ ≤ taperMass g * (|r| * |r|) := mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = taperMass g * |r| * |r| := by ring
  have hsum := abs_sub (evenResp g 0 r * (-(Real.cos (2 * r * u) * (2 * r)) * (2 * r)))
    (evenResp g 0 (2 * r) * (-(Real.cos (r * u) * r) * r))
  have hid : taperMass g * (2 * |r|) * (2 * |r|) + taperMass g * |r| * |r|
      = 5 * (|r| * |r|) * taperMass g := by ring
  rw [hrr] at hid
  have hsq : r * r = r ^ 2 := by ring
  rw [deriv_twoRadiusBracket, (hasDerivAt_bracketDeriv g r u).deriv]
  linarith [hid, hsum, e1, e2, hsq]

/-! ## The projective taper -/

/-- **The projective taper** `h_r = g · B_r`. -/
def projTaper (g : ℝ → ℝ) (r : ℝ) : ℝ → ℝ := fun u => g u * twoRadiusBracket g r u

theorem projTaper_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (r : ℝ) :
    ContDiff ℝ 2 (projTaper g r) :=
  hg.mul (twoRadiusBracket_contDiff g r)

theorem projTaper_continuous {g : ℝ → ℝ} (hg : Continuous g) (r : ℝ) :
    Continuous (projTaper g r) :=
  hg.mul (twoRadiusBracket_contDiff (n := 2) g r).continuous

theorem projTaper_hasCompactSupport {g : ℝ → ℝ} (hgc : HasCompactSupport g) (r : ℝ) :
    HasCompactSupport (projTaper g r) :=
  hgc.mul_right

theorem projTaper_support {g : ℝ → ℝ} {Λ : ℝ} (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (r : ℝ) :
    ∀ u, projTaper g r u ≠ 0 → |u| ≤ Λ := by
  intro u hu
  refine hsupp u fun h => hu ?_
  simp [projTaper, h]

theorem projTaper_short {g : ℝ → ℝ} {L : ℝ} (hshort : ∀ u, g u ≠ 0 → |u| < L) (r : ℝ) :
    ∀ u, projTaper g r u ≠ 0 → |u| < L := by
  intro u hu
  refine hshort u fun h => hu ?_
  simp [projTaper, h]

theorem projTaper_even {g : ℝ → ℝ} (heven : ∀ u, g (-u) = g u) (r : ℝ) :
    ∀ u, projTaper g r (-u) = projTaper g r u := by
  intro u
  unfold projTaper
  rw [heven, twoRadiusBracket_even]

/-! ## Transport of a cosine-transform channel -/

/-- **`cosineChannelProjective`.**  For a channel given by the cosine transform of a
fixed weight `F`, the two-radius determinant is the same transform of `F` against
the bracket — i.e. the channel of the *projective taper* at sampling radius `0`. -/
theorem cosineChannelProjective {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (g : ℝ → ℝ) (r : ℝ) :
    (∫ u : ℝ, F u * Real.cos (2 * r * u)) * evenResp g 0 r
        - (∫ u : ℝ, F u * Real.cos (r * u)) * evenResp g 0 (2 * r)
      = ∫ u : ℝ, F u * twoRadiusBracket g r u := by
  have hi1 : Integrable (fun u : ℝ => F u * Real.cos (2 * r * u)) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hFc.mul_right
  have hi2 : Integrable (fun u : ℝ => F u * Real.cos (r * u)) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hFc.mul_right
  calc (∫ u : ℝ, F u * Real.cos (2 * r * u)) * evenResp g 0 r
        - (∫ u : ℝ, F u * Real.cos (r * u)) * evenResp g 0 (2 * r)
      = (∫ u : ℝ, evenResp g 0 r * (F u * Real.cos (2 * r * u)))
        - ∫ u : ℝ, evenResp g 0 (2 * r) * (F u * Real.cos (r * u)) := by
        rw [integral_const_mul, integral_const_mul]; ring
    _ = ∫ u : ℝ, (evenResp g 0 r * (F u * Real.cos (2 * r * u))
          - evenResp g 0 (2 * r) * (F u * Real.cos (r * u))) :=
        (integral_sub (hi1.const_mul _) (hi2.const_mul _)).symm
    _ = ∫ u : ℝ, F u * twoRadiusBracket g r u := by
        congr 1; funext u; unfold twoRadiusBracket; ring

/-- **The quadratic envelope for a cosine-transform channel.**  If the weight `F`
is supported where the taper is, its two-radius determinant is `O(r²)`. -/
theorem abs_integral_mul_bracket_le {g F : ℝ → ℝ} {Λ : ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ)
    (hF : Continuous F) (hFc : HasCompactSupport F) (hFsupp : ∀ u, F u ≠ 0 → |u| ≤ Λ)
    (r : ℝ) :
    |∫ u : ℝ, F u * twoRadiusBracket g r u| ≤ 5 * r ^ 2 * Λ ^ 2 * taperMass g * taperMass F := by
  have hi : Integrable (fun u : ℝ => F u * twoRadiusBracket g r u) :=
    Continuous.integrable_of_hasCompactSupport
      (hF.mul (twoRadiusBracket_contDiff (n := 2) g r).continuous) hFc.mul_right
  have hb : Integrable (fun u : ℝ => 5 * r ^ 2 * Λ ^ 2 * taperMass g * |F u|) :=
    ((hF.abs).integrable_of_hasCompactSupport (hFc.abs)).const_mul _
  have hpt : ∀ u : ℝ, |F u * twoRadiusBracket g r u|
      ≤ 5 * r ^ 2 * Λ ^ 2 * taperMass g * |F u| := by
    intro u
    rcases eq_or_ne (F u) 0 with h | h
    · simp [h]
    · have hu : |u| ≤ Λ := hFsupp u h
      have hB := abs_twoRadiusBracket_le hg hgc hsupp r hu
      rw [abs_mul]
      calc |F u| * |twoRadiusBracket g r u|
          ≤ |F u| * (5 * r ^ 2 * Λ ^ 2 * taperMass g) :=
            mul_le_mul_of_nonneg_left hB (abs_nonneg _)
        _ = 5 * r ^ 2 * Λ ^ 2 * taperMass g * |F u| := by ring
  calc |∫ u : ℝ, F u * twoRadiusBracket g r u|
      ≤ ∫ u : ℝ, |F u * twoRadiusBracket g r u| := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun u : ℝ => F u * twoRadiusBracket g r u)
    _ ≤ ∫ u : ℝ, 5 * r ^ 2 * Λ ^ 2 * taperMass g * |F u| := integral_mono hi.abs hb hpt
    _ = 5 * r ^ 2 * Λ ^ 2 * taperMass g * taperMass F := by
        rw [integral_const_mul]; rfl

end LiteralWeilProjectiveTaper
end Zeta23Bridge

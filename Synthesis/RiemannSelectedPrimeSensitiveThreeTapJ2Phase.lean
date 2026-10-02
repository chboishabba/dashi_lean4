import Synthesis.RiemannSelectedPrimeSensitiveThreeTapJ2Polynomial

/-!
# Phase-normal form for the transformed J2 coefficients

For S_L g(u)=g(u-L)+g(u+L), the zero-height response is

  A0(S_L g;s) = 2 cos(sL) A0(g;s).

The u^2-weighted response is

  S2(S_L g;s)
    = 2 cos(sL) (S2(g;s)+L^2 A0(g;s))
      - 4 L sin(sL) U1(g;s),

where U1(g;s)=integral g(u) u sin(su).

When the baseline projective J2 determinant vanishes, these formulas collapse
the linear and quadratic epsilon coefficients to explicit phase terms.  This
is the sign-decision normal form; no sign is asserted.
-/

noncomputable section
namespace Synthesis

open MeasureTheory
open scoped Real

def projectiveSinFirstResp (g : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ u : ℝ, g u * u * Real.sin (s*u)

theorem evenResp_shiftPair_zero_eq
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (L s : ℝ) :
    Zeta23Bridge.LiteralWeilParityBalance.evenResp
        (threeTapShiftPair g L) 0 s
      =
    2 * Real.cos (s*L)
      * Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 s := by
  have hminus :
      (∫ u : ℝ, g (u-L) * Real.cos (s*u))
        =
      ∫ v : ℝ, g v * Real.cos (s*(v+L)) := by
    have h :=
      integral_add_right_eq_self
        (fun v : ℝ => g v * Real.cos (s*(v+L))) (-L)
    simpa [sub_eq_add_neg, add_assoc] using h
  have hplus :
      (∫ u : ℝ, g (u+L) * Real.cos (s*u))
        =
      ∫ v : ℝ, g v * Real.cos (s*(v-L)) := by
    have h :=
      integral_add_right_eq_self
        (fun v : ℝ => g v * Real.cos (s*(v-L))) L
    simpa [sub_eq_add_neg, add_assoc] using h
  unfold Zeta23Bridge.LiteralWeilParityBalance.evenResp
  simp only [zero_mul, Real.cosh_zero, one_mul]
  unfold threeTapShiftPair
  rw [show
      (fun u : ℝ =>
        (g (u-L) + g (u+L)) * Real.cos (s*u))
      =
      fun u =>
        g (u-L) * Real.cos (s*u)
          + g (u+L) * Real.cos (s*u) by
      funext u; ring]
  have hm :
      Integrable (fun u : ℝ => g (u-L) * Real.cos (s*u)) := by
    have hc : Continuous (fun u : ℝ => g (u-L) * Real.cos (s*u)) := by fun_prop
    have hk : HasCompactSupport (fun u : ℝ => g (u-L)) := by
      have heq : (fun u : ℝ => g (u-L))
          = g ∘ (Homeomorph.addRight (-L) : ℝ ≃ₜ ℝ) := by
        funext u
        simp [Function.comp_def, sub_eq_add_neg]
      rw [heq]
      exact hgc.comp_homeomorph _
    exact hc.integrable_of_hasCompactSupport hk.mul_right
  have hp :
      Integrable (fun u : ℝ => g (u+L) * Real.cos (s*u)) := by
    have hc : Continuous (fun u : ℝ => g (u+L) * Real.cos (s*u)) := by fun_prop
    have hk : HasCompactSupport (fun u : ℝ => g (u+L)) := by
      have heq : (fun u : ℝ => g (u+L))
          = g ∘ (Homeomorph.addRight L : ℝ ≃ₜ ℝ) := by rfl
      rw [heq]
      exact hgc.comp_homeomorph _
    exact hc.integrable_of_hasCompactSupport hk.mul_right
  rw [integral_add hm hp, hminus, hplus, ← integral_add]
  · apply integral_congr_ae
    filter_upwards with v
    rw [show
        Real.cos (s*(v+L)) + Real.cos (s*(v-L))
          = 2 * Real.cos (s*v) * Real.cos (s*L) by
          rw [mul_add, mul_sub, Real.cos_add, Real.cos_sub]
          ring]
    ring
  · exact
      (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  · exact
      (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right

theorem projectiveSqEvenResp_shiftPair_eq
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (L s : ℝ) :
    projectiveSqEvenResp (threeTapShiftPair g L) s
      =
    2 * Real.cos (s*L)
      * (projectiveSqEvenResp g s
          + L^2 *
            Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 s)
      -
    4 * L * Real.sin (s*L) * projectiveSinFirstResp g s := by
  have hmK : HasCompactSupport (fun u : ℝ => g (u-L)) := by
    have heq : (fun u : ℝ => g (u-L))
        = g ∘ (Homeomorph.addRight (-L) : ℝ ≃ₜ ℝ) := by
      funext u
      simp [Function.comp_def, sub_eq_add_neg]
    rw [heq]
    exact hgc.comp_homeomorph _
  have hpK : HasCompactSupport (fun u : ℝ => g (u+L)) := by
    have heq : (fun u : ℝ => g (u+L))
        = g ∘ (Homeomorph.addRight L : ℝ ≃ₜ ℝ) := by rfl
    rw [heq]
    exact hgc.comp_homeomorph _
  have hm :
      Integrable (fun u : ℝ => g (u-L) * u^2 * Real.cos (s*u)) :=
    (by fun_prop : Continuous
      (fun u : ℝ => g (u-L) * u^2 * Real.cos (s*u)))
      |>.integrable_of_hasCompactSupport ((hmK.mul_right).mul_right)
  have hp :
      Integrable (fun u : ℝ => g (u+L) * u^2 * Real.cos (s*u)) :=
    (by fun_prop : Continuous
      (fun u : ℝ => g (u+L) * u^2 * Real.cos (s*u)))
      |>.integrable_of_hasCompactSupport ((hpK.mul_right).mul_right)
  have hminus :
      (∫ u : ℝ, g (u-L) * u^2 * Real.cos (s*u))
        =
      ∫ v : ℝ, g v * (v+L)^2 * Real.cos (s*(v+L)) := by
    have h :=
      integral_add_right_eq_self
        (fun v : ℝ => g v * (v+L)^2 * Real.cos (s*(v+L))) (-L)
    simpa [sub_eq_add_neg, add_assoc] using h
  have hplus :
      (∫ u : ℝ, g (u+L) * u^2 * Real.cos (s*u))
        =
      ∫ v : ℝ, g v * (v-L)^2 * Real.cos (s*(v-L)) := by
    have h :=
      integral_add_right_eq_self
        (fun v : ℝ => g v * (v-L)^2 * Real.cos (s*(v-L))) L
    simpa [sub_eq_add_neg, add_assoc] using h
  unfold projectiveSqEvenResp threeTapShiftPair
  rw [show
      (fun u : ℝ =>
        (g (u-L) + g (u+L)) * u^2 * Real.cos (s*u))
      =
      fun u =>
        g (u-L) * u^2 * Real.cos (s*u)
          + g (u+L) * u^2 * Real.cos (s*u) by
      funext u; ring,
      integral_add hm hp, hminus, hplus, ← integral_add]
  · rw [show
      (fun v : ℝ =>
        g v * (v+L)^2 * Real.cos (s*(v+L))
          + g v * (v-L)^2 * Real.cos (s*(v-L)))
      =
      fun v =>
        2 * Real.cos (s*L) *
          (g v * v^2 * Real.cos (s*v)
            + L^2 * (g v * Real.cos (s*v)))
        -
        4 * L * Real.sin (s*L)
          * (g v * v * Real.sin (s*v)) by
      funext v
      rw [mul_add, mul_sub, Real.cos_add, Real.cos_sub]
      ring]
    have hS2 :
        Integrable (fun v : ℝ => g v * v^2 * Real.cos (s*v)) :=
      (by fun_prop : Continuous
        (fun v : ℝ => g v * v^2 * Real.cos (s*v)))
        |>.integrable_of_hasCompactSupport ((hgc.mul_right).mul_right)
    have hA :
        Integrable (fun v : ℝ => g v * Real.cos (s*v)) :=
      (by fun_prop : Continuous (fun v : ℝ => g v * Real.cos (s*v)))
        |>.integrable_of_hasCompactSupport hgc.mul_right
    have hU :
        Integrable (fun v : ℝ => g v * v * Real.sin (s*v)) :=
      (by fun_prop : Continuous
        (fun v : ℝ => g v * v * Real.sin (s*v)))
        |>.integrable_of_hasCompactSupport ((hgc.mul_right).mul_right)
    rw [integral_sub,
        integral_const_mul, integral_const_mul,
        integral_add hS2 (hA.const_mul _),
        integral_const_mul]
    unfold Zeta23Bridge.LiteralWeilParityBalance.evenResp
      projectiveSinFirstResp
    simp only [zero_mul, Real.cosh_zero, one_mul]
    ring
  · exact
      (by fun_prop : Continuous
        (fun v : ℝ => g v * (v+L)^2 * Real.cos (s*(v+L))))
        |>.integrable_of_hasCompactSupport ((hgc.mul_right).mul_right)
  · exact
      (by fun_prop : Continuous
        (fun v : ℝ => g v * (v-L)^2 * Real.cos (s*(v-L))))
        |>.integrable_of_hasCompactSupport ((hgc.mul_right).mul_right)

theorem projectiveBracketSecondMomentThreeTapLinearCoeff_eq_phase
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    {L r : ℝ}
    (hJ2 : projectiveBracketSecondMoment g r = 0) :
    projectiveBracketSecondMomentThreeTapLinearCoeff g L r
      =
    2 * L^2
      *
      (Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 r)
      *
      (Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 (2*r))
      * (Real.cos ((2*r)*L) - Real.cos (r*L))
    +
    4 * L *
      (
        (Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 (2*r))
          * Real.sin (r*L) * projectiveSinFirstResp g r
        -
        (Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 r)
          * Real.sin ((2*r)*L) * projectiveSinFirstResp g (2*r)
      ) := by
  have hdet :=
    projectiveBracketSecondMoment_eq_response_det hg hgc r
  rw [hJ2] at hdet
  have hAr := evenResp_shiftPair_zero_eq hg hgc L r
  have hA2 := evenResp_shiftPair_zero_eq hg hgc L (2*r)
  have hSr := projectiveSqEvenResp_shiftPair_eq hg hgc L r
  have hS2 := projectiveSqEvenResp_shiftPair_eq hg hgc L (2*r)
  unfold projectiveBracketSecondMomentThreeTapLinearCoeff
  dsimp
  rw [hAr,hA2,hSr,hS2]
  linarith [hdet]

theorem projectiveBracketSecondMomentThreeTapQuadraticCoeff_eq_phase
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    {L r : ℝ}
    (hJ2 : projectiveBracketSecondMoment g r = 0) :
    projectiveBracketSecondMomentThreeTapQuadraticCoeff g L r
      =
    8 * L *
      (
        Real.cos ((2*r)*L)
          * (Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 (2*r))
          * Real.sin (r*L) * projectiveSinFirstResp g r
        -
        Real.cos (r*L)
          * (Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 r)
          * Real.sin ((2*r)*L) * projectiveSinFirstResp g (2*r)
      ) := by
  have hdet :=
    projectiveBracketSecondMoment_eq_response_det hg hgc r
  rw [hJ2] at hdet
  have hAr := evenResp_shiftPair_zero_eq hg hgc L r
  have hA2 := evenResp_shiftPair_zero_eq hg hgc L (2*r)
  have hSr := projectiveSqEvenResp_shiftPair_eq hg hgc L r
  have hS2 := projectiveSqEvenResp_shiftPair_eq hg hgc L (2*r)
  unfold projectiveBracketSecondMomentThreeTapQuadraticCoeff
  dsimp
  rw [hAr,hA2,hSr,hS2]
  linarith [hdet]

end Synthesis

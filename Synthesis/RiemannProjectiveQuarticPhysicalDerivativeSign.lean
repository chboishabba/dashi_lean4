import Synthesis.RiemannProjectiveQuarticDerivativeSign
import Synthesis.RiemannProjectiveQuarticZetaMuAbel

/-!
# Physical derivative sign band for the quartic Abel test

The normalized quartic kernel satisfies

  q * Phi_Q'(q) < 0

on a punctured band.  Since

  phi_t'(x) = r^-3 Phi_Q'((x-t)/r),  r=t/16>0,

the physical ordinate test inherits

  (x-t) * phi_t'(x) < 0

whenever 0<|x-t|<r eps.

This is the exact local orientation seen by the signed Abel functional.
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace Synthesis

structure QuarticDerivativeSignBand (W : QuarticHighWitness) where
  eps : ℝ
  epsPos : 0 < eps
  radialNeg :
    ∀ q : ℝ, 0 < |q| -> |q| < eps ->
      q *
        compactCosineD1
          (genericProjectivePhysicalProfile
            (quarticThreeWindowProfile W.R W.lam) 1) q < 0

theorem exists_quarticDerivativeSignBand
    (W : QuarticHighWitness) :
    ∃ D : QuarticDerivativeSignBand W, True := by
  obtain ⟨eps,heps,hneg⟩ :=
    exists_genericProjectiveBaseKernel_deriv_radial_neg
      (quarticThreeWindowProfile_continuous W.Rpos)
      (quarticThreeWindowProfile_compact W.Rpos)
      W.J2zero W.J4neg
  exact ⟨{
    eps := eps
    epsPos := heps
    radialNeg := hneg
  }, trivial⟩

theorem quarticNegativeOrdinateTestDeriv_scaled
    (W : QuarticHighWitness)
    {t x : ℝ} (ht : 0 < t) :
    quarticNegativeOrdinateTestDeriv W t x
      =
    (1 / (quarticNegativeWindowRadius t)^3) *
      compactCosineD1
        (genericProjectivePhysicalProfile
          (quarticThreeWindowProfile W.R W.lam) 1)
        ((x-t)/quarticNegativeWindowRadius t) := by
  rfl

theorem QuarticDerivativeSignBand.physical_radial_neg
    {W : QuarticHighWitness}
    (D : QuarticDerivativeSignBand W)
    {t x : ℝ} (ht : 0 < t)
    (hx0 : 0 < |x-t|)
    (hxband :
      |x-t| <
        quarticNegativeWindowRadius t * D.eps) :
    (x-t) * quarticNegativeOrdinateTestDeriv W t x < 0 := by
  have hr : 0 < quarticNegativeWindowRadius t := by
    unfold quarticNegativeWindowRadius
    positivity
  let q : ℝ := (x-t)/quarticNegativeWindowRadius t
  have hq0 : 0 < |q| := by
    dsimp [q]
    rw [abs_div, abs_of_pos hr]
    exact div_pos hx0 hr
  have hqband : |q| < D.eps := by
    dsimp [q]
    rw [abs_div, abs_of_pos hr, div_lt_iff₀ hr]
    exact hxband
  have hq := D.radialNeg q hq0 hqband
  rw [quarticNegativeOrdinateTestDeriv_scaled W ht]
  have hscale :
      x-t = q * quarticNegativeWindowRadius t := by
    dsimp [q]
    field_simp [hr.ne']
  rw [hscale]
  have hfac : 0 < 1 / (quarticNegativeWindowRadius t)^2 := by
    positivity
  have heq :
      (q * quarticNegativeWindowRadius t)
          * ((1 / (quarticNegativeWindowRadius t)^3)
            * compactCosineD1
                (genericProjectivePhysicalProfile
                  (quarticThreeWindowProfile W.R W.lam) 1) q)
        =
      (1 / (quarticNegativeWindowRadius t)^2)
        * (q *
            compactCosineD1
              (genericProjectivePhysicalProfile
                (quarticThreeWindowProfile W.R W.lam) 1) q) := by
    field_simp [hr.ne']
    ring
  rw [heq]
  exact mul_neg_of_pos_of_neg hfac hq

end Synthesis

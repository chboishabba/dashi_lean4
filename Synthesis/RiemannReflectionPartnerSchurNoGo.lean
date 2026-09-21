import Synthesis.RiemannConstructedSmoothShortWindowSchur
import Zeta23Bridge.LiteralWeilOtherZerosChannel
import Zeta23Bridge.LiteralWeilTwoTaperCoefficientGate

/-!
# Reflection-partner Schur no-go and signal folding

Every off-line zeta zero rho has the functional-equation partner

  rho# = 1 - conj rho,

at the same ordinate and opposite height.  The two-radius height defect depends
on height through cosh, hence is even in the height.  Therefore every taper sees
rho and rho# with exactly the same zero-response vector.

So the unavoidable same-ordinate reflection partner is not a nuisance direction
which can be Schur-eliminated while preserving the target: it is literally the
same response direction.  The correct high-side signal is the reflection pair
(or the whole equal-|height| orbit), with the remaining same-ordinate cluster
treated separately.
-/

noncomputable section

open Complex
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilTwoTaperCoefficientGate
open Zeta23Bridge.MultiTaperSchurCore

theorem reflectZero_im (rho : Zeros) :
    ((reflectZero rho : Zeros) : ℂ).im = (rho : ℂ).im := by
  rfl

theorem heightOf_reflectZero (rho : Zeros) :
    heightOf (reflectZero rho) = - heightOf rho := by
  unfold heightOf reflectZero Zeta23.reflect
  simp
  ring

theorem reflectZero_ne_of_height_ne_zero
    {rho : Zeros} (hoff : heightOf rho ≠ 0) :
    reflectZero rho ≠ rho := by
  intro h
  have hh := congrArg heightOf h
  rw [heightOf_reflectZero] at hh
  exact hoff (by linarith)

theorem zeroRespVec_reflectZero
    (g : Fin 2 → ℝ → ℝ) (r : ℝ) (rho : Zeros) :
    zeroRespVec g r (reflectZero rho) = zeroRespVec g r rho := by
  funext j
  unfold zeroRespVec zeroHeightDefect
  rw [reflectZero_mult, heightOf_reflectZero]
  rw [heightDefect_neg_height]

theorem crossDet_reflect_target_zero
    (g : Fin 2 → ℝ → ℝ) (r : ℝ) (rho : Zeros) :
    crossDet g r (reflectZero rho) rho = 0 := by
  unfold crossDet
  rw [zeroRespVec_reflectZero]
  unfold det2
  ring

theorem transverse_target_after_reflect_is_zero
    (g : Fin 2 → ℝ → ℝ) (r : ℝ) (rho : Zeros)
    (hresp : zeroRespVec g r rho ≠ 0) :
    transverseComp
      (zeroRespVec g r (reflectZero rho))
      (zeroRespVec g r rho) = 0 := by
  rw [zeroRespVec_reflectZero]
  exact transverseComp_self hresp

/--
The unavoidable functional-equation partner can never inhabit the corrected
one-zero Schur target-survival certificate.
-/
theorem reflectZero_cannot_be_schur_nuisance
    (g : Fin 2 → ℝ → ℝ) (r : ℝ) (rho : Zeros)
    (hresp : zeroRespVec g r rho ≠ 0) :
    ¬ targetProjected g r rho (reflectZero rho) ≠ 0 := by
  intro h
  apply h
  unfold targetProjected
  exact transverse_target_after_reflect_is_zero g r rho hresp

/-- Reflection folding doubles the target response exactly. -/
theorem zeroRespVec_add_reflect
    (g : Fin 2 → ℝ → ℝ) (r : ℝ) (rho : Zeros) :
    zeroRespVec g r rho + zeroRespVec g r (reflectZero rho)
      = (2 : ℝ) • zeroRespVec g r rho := by
  rw [zeroRespVec_reflectZero]
  funext j
  simp
  ring

end Synthesis

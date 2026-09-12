/-
# Exact reflection symmetrization of the off-ordinate projective zero tail

This module performs the infinite-carrier reindex that the signed tail estimate
needs.  No orbit representatives are chosen.  Instead the functional-equation
reflection is used as an involutive equivalence of the off-ordinate carrier and

  tsum f = (1/2) * tsum (fun ρ => f ρ + f (R ρ)).

Combining this with `LiteralWeilOffOrdinateReflectionPair` turns the literal
projective zero tail into a signed sum of oscillatory reflection-pair kernels.
Critical-line fixed points are handled automatically by the symmetrization.
-/
import Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilOffOrdinateReflectionSymmetrization

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilOffOrdinateProjectiveTail
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair

/-- Reflection is literally involutive on the zero carrier. -/
theorem reflectZero_involutive (ρ : Zeros) : reflectZero (reflectZero ρ) = ρ := by
  apply Subtype.ext
  change Zeta23.reflect (Zeta23.reflect (ρ : ℂ)) = (ρ : ℂ)
  unfold Zeta23.reflect
  apply Complex.ext <;> simp

/-- Reflection preserves the complement of the target-ordinate fibre. -/
def reflectOffOrdEquiv (t : ℝ) : ((SameOrd t)ᶜ : Set Zeros) ≃ ((SameOrd t)ᶜ : Set Zeros) where
  toFun σ := ⟨reflectZero (σ : Zeros), by
    have hne : ((σ : Zeros) : ℂ).im ≠ t := by
      simpa [SameOrd] using σ.property
    simpa [SameOrd, im_reflectZero] using hne⟩
  invFun σ := ⟨reflectZero (σ : Zeros), by
    have hne : ((σ : Zeros) : ℂ).im ≠ t := by
      simpa [SameOrd] using σ.property
    simpa [SameOrd, im_reflectZero] using hne⟩
  left_inv σ := by
    apply Subtype.ext
    exact reflectZero_involutive (σ : Zeros)
  right_inv σ := by
    apply Subtype.ext
    exact reflectZero_involutive (σ : Zeros)

/-- Generic exact symmetrization under an equivalence of a summable real family. -/
theorem tsum_eq_half_tsum_add_equiv {α : Type*} (e : α ≃ α) (f : α → ℝ)
    (hf : Summable f) (hfe : Summable (fun x => f (e x))) :
    (∑' x, f x) = (1 / 2 : ℝ) * ∑' x, (f x + f (e x)) := by
  have hreindex : (∑' x, f (e x)) = ∑' x, f x := e.tsum_eq f
  rw [hf.tsum_add hfe, hreindex]
  ring

/-- The literal projective per-zero family is summable on the off-ordinate carrier. -/
theorem projectiveZeroSummable {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (t r : ℝ) :
    Summable fun σ : ((SameOrd t)ᶜ : Set Zeros) =>
      2 * reim (zeroTerm (sampleTest (projTaper g r) t 0) (σ : Zeros)) := by
  have hpd : ContDiff ℝ 2 (projTaper g r) := projTaper_contDiff hgs r
  have hpk : HasCompactSupport (projTaper g r) := projTaper_hasCompactSupport hgc r
  have hsum : Summable fun σ : ((SameOrd t)ᶜ : Set Zeros) =>
      zeroTerm (sampleTest (projTaper g r) t 0) (σ : Zeros) :=
    (zeroTerm_summable (sampleTest_contDiff hpd t 0)
      (sampleTest_hasCompactSupport hpk t 0)).subtype _
  have hre : Summable fun σ : ((SameOrd t)ᶜ : Set Zeros) =>
      reim (zeroTerm (sampleTest (projTaper g r) t 0) (σ : Zeros)) := by
    have hR := (Complex.hasSum_re hsum.hasSum).summable
    have hI := (Complex.hasSum_im hsum.hasSum).summable
    exact hR.add hI
  simpa [mul_comm] using hre.mul_left 2

/-- Exact infinite-carrier reflection symmetrization of the literal off-ordinate
projective defect.  This is the no-representatives version of the orbit split. -/
theorem offOrdProjectiveDefect_eq_half_reflection_tsum {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    offOrdProjectiveDefect g t r
      = (1 / 2 : ℝ) * ∑' σ : ((SameOrd t)ᶜ : Set Zeros),
          ((2 * reim (zeroTerm (sampleTest (projTaper g r) t 0) (σ : Zeros)))
            + (2 * reim (zeroTerm (sampleTest (projTaper g r) t 0)
                ((reflectOffOrdEquiv t σ : ((SameOrd t)ᶜ : Set Zeros)) : Zeros)))) := by
  rw [offOrdProjectiveDefect_eq_tsum hgs hgc heven t r]
  let f : ((SameOrd t)ᶜ : Set Zeros) → ℝ := fun σ =>
    2 * reim (zeroTerm (sampleTest (projTaper g r) t 0) (σ : Zeros))
  have hf : Summable f := projectiveZeroSummable hgs hgc t r
  have hfe : Summable (fun σ => f (reflectOffOrdEquiv t σ)) := by
    exact (reflectOffOrdEquiv t).summable_iff.mpr hf
  exact tsum_eq_half_tsum_add_equiv (reflectOffOrdEquiv t) f hf hfe

/-- The symmetrized summand is the genuine multiplicity times the signed
reflection-pair oscillatory kernel. -/
theorem projectiveZero_add_reflect_eq_pairIntegral {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t r : ℝ)
    (σ : ((SameOrd t)ᶜ : Set Zeros)) :
    2 * reim (zeroTerm (sampleTest (projTaper g r) t 0) (σ : Zeros))
      + 2 * reim (zeroTerm (sampleTest (projTaper g r) t 0) (reflectZero (σ : Zeros)))
      = ((Zeta23.zetaZeroConfig).mult (σ : Zeros) : ℝ)
          * ∫ u : ℝ,
              reflectionPairWeight (projTaper g r)
                (heightOf (σ : Zeros)) (((σ : Zeros) : ℂ).im - t) u := by
  have hpc := projTaper_continuous hgs.continuous r
  have hpk := projTaper_hasCompactSupport hgc r
  have hpe := projTaper_even heven r
  have hpair := zeroConeValue_add_reflect_eq_integral hpc hpk hpe t 0 (σ : Zeros)
  unfold zeroConeValue at hpair
  simp only [neg_zero] at hpair
  simpa [two_mul] using hpair

/-- Final exact U3 carrier: the off-ordinate projective defect is one half of the
literal zero-carrier sum of signed oscillatory reflection-pair kernels. -/
theorem offOrdProjectiveDefect_eq_signedReflectionKernelTsum {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    offOrdProjectiveDefect g t r
      = (1 / 2 : ℝ) * ∑' σ : ((SameOrd t)ᶜ : Set Zeros),
          ((Zeta23.zetaZeroConfig).mult (σ : Zeros) : ℝ)
            * ∫ u : ℝ,
                reflectionPairWeight (projTaper g r)
                  (heightOf (σ : Zeros)) (((σ : Zeros) : ℂ).im - t) u := by
  rw [offOrdProjectiveDefect_eq_half_reflection_tsum hgs hgc heven t r]
  congr 1
  apply tsum_congr
  intro σ
  change
    2 * reim (zeroTerm (sampleTest (projTaper g r) t 0) (σ : Zeros))
      + 2 * reim (zeroTerm (sampleTest (projTaper g r) t 0) (reflectZero (σ : Zeros)))
      = _
  exact projectiveZero_add_reflect_eq_pairIntegral hgs hgc heven t r σ

end LiteralWeilOffOrdinateReflectionSymmetrization
end Zeta23Bridge

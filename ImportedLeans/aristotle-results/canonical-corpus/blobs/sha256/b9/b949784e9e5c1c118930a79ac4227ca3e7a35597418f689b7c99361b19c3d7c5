/-
# Exact reflection symmetrization in the universal even-cone observer

This is the representation-matched U3 carrier.  Unlike the earlier projective
symmetrization file, this module works directly with

  evenConeFunctional (offOrdVec (sampleFam g t r) t),

the exact off-ordinate term consumed by `literalWeilSameOrdinateEvenCone` and
`primeEvenConeUnreachable`.

The functional-equation involution is applied before absolute values.  No orbit
representatives are chosen.
-/
import Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilOffOrdinateEvenConeReflectionSymmetrization

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilOffOrdinateProjectiveTail
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair

/-- The functional-equation reflection is an involution on actual zeta zeros. -/
theorem reflectZero_involutive (ρ : Zeros) : reflectZero (reflectZero ρ) = ρ := by
  apply Subtype.ext
  simp [reflectZero]

/-- Reflection preserves the off-ordinate fibre at target ordinate `t`. -/
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

/-- Generic exact symmetrization under a summation equivalence. -/
theorem tsum_eq_half_tsum_add_equiv {α : Type*} (e : α ≃ α) (f : α → ℝ)
    (hf : Summable f) :
    (∑' x, f x) = (1 / 2 : ℝ) * ∑' x, (f x + f (e x)) := by
  have hfe : Summable (fun x => f (e x)) := e.summable_iff.mpr hf
  have hreindex : (∑' x, f (e x)) = ∑' x, f x := e.tsum_eq f
  rw [hf.tsum_add hfe, hreindex]
  ring

/-- The literal per-zero even-cone family is summable on the off-ordinate carrier. -/
theorem zeroConeValue_summable {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (t s : ℝ) :
    Summable fun σ : ((SameOrd t)ᶜ : Set Zeros) => zeroConeValue g t s (σ : Zeros) := by
  have h1 : Summable fun σ : ((SameOrd t)ᶜ : Set Zeros) =>
      zeroTerm (sampleTest g t s) (σ : Zeros) :=
    (zeroTerm_summable (sampleTest_contDiff hgs t s)
      (sampleTest_hasCompactSupport hgc t s)).subtype _
  have h2 : Summable fun σ : ((SameOrd t)ᶜ : Set Zeros) =>
      zeroTerm (sampleTest g t (-s)) (σ : Zeros) :=
    (zeroTerm_summable (sampleTest_contDiff hgs t (-s))
      (sampleTest_hasCompactSupport hgc t (-s))).subtype _
  have hr1 : Summable fun σ : ((SameOrd t)ᶜ : Set Zeros) =>
      reim (zeroTerm (sampleTest g t s) (σ : Zeros)) := by
    exact (Complex.hasSum_re h1.hasSum).summable.add (Complex.hasSum_im h1.hasSum).summable
  have hr2 : Summable fun σ : ((SameOrd t)ᶜ : Set Zeros) =>
      reim (zeroTerm (sampleTest g t (-s)) (σ : Zeros)) := by
    exact (Complex.hasSum_re h2.hasSum).summable.add (Complex.hasSum_im h2.hasSum).summable
  exact hr1.add hr2

/-- Exact reflection symmetrization of the actual off-ordinate even-cone channel. -/
theorem offOrdChannel_eq_half_reflection_tsum {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (t s : ℝ) :
    offOrdChannel g t s
      = (1 / 2 : ℝ) * ∑' σ : ((SameOrd t)ᶜ : Set Zeros),
          (zeroConeValue g t s (σ : Zeros)
            + zeroConeValue g t s (reflectZero (σ : Zeros))) := by
  rw [offOrdChannel_eq_tsum hgs hgc t s]
  let f : ((SameOrd t)ᶜ : Set Zeros) → ℝ := fun σ => zeroConeValue g t s (σ : Zeros)
  have hf : Summable f := zeroConeValue_summable hgs hgc t s
  simpa [f, reflectOffOrdEquiv] using tsum_eq_half_tsum_add_equiv (reflectOffOrdEquiv t) f hf

/-- Final representation-matched U3 carrier.  The exact off-ordinate term used by
`literalWeilSameOrdinateEvenCone` is one half of the literal off-ordinate zero sum
of signed reflection-pair cosine kernels. -/
theorem offOrdEvenCone_eq_signedReflectionKernelTsum {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t s : ℝ) :
    evenConeFunctional (offOrdVec (sampleFam g t s) t)
      = (1 / 2 : ℝ) * ∑' σ : ((SameOrd t)ᶜ : Set Zeros),
          ((Zeta23.zetaZeroConfig).mult (σ : Zeros) : ℝ)
            * ∫ u : ℝ,
                reflectionPairWeight g (heightOf (σ : Zeros))
                  (((σ : Zeros) : ℂ).im - t) u * Real.cos (s * u) := by
  change offOrdChannel g t s = _
  rw [offOrdChannel_eq_half_reflection_tsum hgs hgc t s]
  congr 1
  apply tsum_congr
  intro σ
  exact zeroConeValue_add_reflect_eq_integral hgs.continuous hgc heven t s (σ : Zeros)

end LiteralWeilOffOrdinateEvenConeReflectionSymmetrization
end Zeta23Bridge

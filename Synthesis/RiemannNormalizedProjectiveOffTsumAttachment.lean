import Synthesis.RiemannNormalizedProjectiveOffAtomicMeasure
import Zeta23Bridge.LiteralWeilOffOrdinateReflectionSymmetrization

/-!
# Infinite normalized projective Off attachment

The finite normalized projective atom is already the exact two-radius
reflection-pair observable.  The literal Off channel, however, is an infinite
`tsum` over individual off-ordinate zeros.

The imported reflection symmetrization supplies the exact no-representatives
identity

  D_off^proj = (1/2) * sum' (single rho + single (R rho)).

This file identifies that symmetrized summand with the literal reflection-pair
projective defect and then with the normalized projective atom.  Consequently,
for the canonical radius r=t/16,

  D_off^proj = (1/(2t)) * sum' A_rho^proj.

The factor 1/2 is essential: the full off-ordinate carrier contains both members
of every functional-equation orbit, so a reflection-pair atom indexed by every
zero counts each orbit twice.

No orbit representatives and no finite-tail approximation are introduced.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilOffOrdinateProjectiveTail
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionSymmetrization

/-- The literal reflection-pair projective defect is exactly the sum of the two
single-zero projective summands used by the infinite Off `tsum`. -/
theorem literalPairProjectiveDefect_eq_projectiveZero_add_reflect
    {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (t r : ℝ)
    (rho : Zeros) :
    literalPairProjectiveDefect g t r rho
      =
    2 * reim (zeroTerm (sampleTest (projTaper g r) t 0) rho)
      +
    2 * reim (zeroTerm (sampleTest (projTaper g r) t 0) (reflectZero rho)) := by
  unfold literalPairProjectiveDefect literalPairRadiusChannel
    channelProjectiveDefect
  rw [singleOffOrdProjectiveDefect_eq hgs.continuous hgc heven t r rho,
    singleOffOrdProjectiveDefect_eq hgs.continuous hgc heven t r (reflectZero rho)]
  ring

/-- The symmetrized infinite literal carrier is summable. -/
theorem literalPairProjectiveDefect_summable_offOrd
    {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (t r : ℝ) :
    Summable fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
      literalPairProjectiveDefect g t r (sigma : Zeros) := by
  let f : ((SameOrd t)ᶜ : Set Zeros) → ℝ := fun sigma =>
    2 * reim (zeroTerm (sampleTest (projTaper g r) t 0) (sigma : Zeros))
  have hf : Summable f := projectiveZeroSummable hgs hgc t r
  have hfe : Summable (fun sigma => f (reflectOffOrdEquiv t sigma)) := by
    exact (reflectOffOrdEquiv t).summable_iff.mpr hf
  have hp := hf.add hfe
  refine hp.congr ?_
  intro sigma
  change
    f sigma + f (reflectOffOrdEquiv t sigma)
      =
    literalPairProjectiveDefect g t r (sigma : Zeros)
  rw [literalPairProjectiveDefect_eq_projectiveZero_add_reflect
    hgs hgc heven t r (sigma : Zeros)]
  rfl

/-- Exact infinite reflection-pair attachment.  The factor one half is the
full-carrier double-counting correction; no representatives are chosen. -/
theorem offOrdProjectiveDefect_eq_half_literalPair_tsum
    {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (t r : ℝ) :
    offOrdProjectiveDefect g t r
      =
    (1 / 2 : ℝ) *
      ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        literalPairProjectiveDefect g t r (sigma : Zeros) := by
  rw [offOrdProjectiveDefect_eq_half_reflection_tsum hgs hgc heven t r]
  congr 1
  apply tsum_congr
  intro sigma
  change
    2 * reim (zeroTerm (sampleTest (projTaper g r) t 0) (sigma : Zeros))
      +
    2 * reim (zeroTerm (sampleTest (projTaper g r) t 0)
      (reflectZero (sigma : Zeros)))
      =
    literalPairProjectiveDefect g t r (sigma : Zeros)
  exact (literalPairProjectiveDefect_eq_projectiveZero_add_reflect
    hgs hgc heven t r (sigma : Zeros)).symm

/-- The canonical normalized projective atoms are genuinely summable on the
literal off-ordinate carrier. -/
theorem normalizedProjectiveOffZeroAtom_summable_offOrd
    {t : ℝ} (ht : 18 <= t) :
    Summable fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
      normalizedProjectiveOffZeroAtom t (sigma : Zeros) := by
  have ht0 : t ≠ 0 := by linarith
  have hp :
      Summable fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
        literalPairProjectiveDefect
          (quantitativeCanonicalTaper t)
          t (quantitativeSampleRadius t) (sigma : Zeros) :=
    literalPairProjectiveDefect_summable_offOrd
      (quantitativeCanonicalTaper_contDiff ht)
      (quantitativeCanonicalTaper_compact ht)
      quantitativeCanonicalTaper_even
      t (quantitativeSampleRadius t)
  have hscaled := hp.mul_left t
  refine hscaled.congr ?_
  intro sigma
  rw [literalPairProjectiveDefect_eq_one_div_t_mul_normalizedAtom
    ht (sigma : Zeros)]
  field_simp [ht0]

/--
The sought literal infinite same-object attachment:

  D_off^proj = (1/(2t)) * sum' A_rho^proj.

This is the exact observable consumed by the reflection-pair signed cutset, now
written on the normalized projective zero carrier used by the RvM machinery.
-/
theorem canonical_offOrdProjectiveDefect_eq_normalizedProjectiveTsum
    {t : ℝ} (ht : 18 <= t) :
    offOrdProjectiveDefect
        (quantitativeCanonicalTaper t)
        t (quantitativeSampleRadius t)
      =
    (1 / (2 * t)) *
      ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        normalizedProjectiveOffZeroAtom t (sigma : Zeros) := by
  have ht0 : t ≠ 0 := by linarith
  rw [offOrdProjectiveDefect_eq_half_literalPair_tsum
    (quantitativeCanonicalTaper_contDiff ht)
    (quantitativeCanonicalTaper_compact ht)
    quantitativeCanonicalTaper_even
    t (quantitativeSampleRadius t)]
  have hterm :
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        literalPairProjectiveDefect
          (quantitativeCanonicalTaper t)
          t (quantitativeSampleRadius t) (sigma : Zeros))
        =
      (1 / t) *
        ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          normalizedProjectiveOffZeroAtom t (sigma : Zeros) := by
    calc
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        literalPairProjectiveDefect
          (quantitativeCanonicalTaper t)
          t (quantitativeSampleRadius t) (sigma : Zeros))
        =
      ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        (1 / t) * normalizedProjectiveOffZeroAtom t (sigma : Zeros) := by
          apply tsum_congr
          intro sigma
          exact literalPairProjectiveDefect_eq_one_div_t_mul_normalizedAtom
            ht (sigma : Zeros)
      _ =
      (1 / t) *
        ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          normalizedProjectiveOffZeroAtom t (sigma : Zeros) := by
          rw [tsum_mul_left]
  rw [hterm]
  field_simp [ht0]
  ring

end Synthesis

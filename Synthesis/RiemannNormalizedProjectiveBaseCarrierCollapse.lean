import Synthesis.RiemannNormalizedProjectiveOffInfiniteSplit
import Synthesis.RiemannNormalizedProjectiveFullCarrier
import Synthesis.RiemannNormalizedProjectiveBaseZeroAtSameOrd

/-!
# The projective base carrier is unchanged by deleting SameOrd(t)

The normalized projective q-only source term is

  B_sigma(t) = m_sigma * Phi_proj((Im sigma - t)/t).

On the target ordinate q=0, and the projective determinant has exact zero base
mode:

  Phi_proj(0)=0.

Hence every SameOrd(t) base source is exactly zero.  Consequently the full
literal base tsum and the off-ordinate base tsum are the same object:

  sum'_all B_sigma(t) = sum'_{sigma notin SameOrd(t)} B_sigma(t).

This matters for the RvM lane: the base channel may be estimated against the
ordinary full zero-counting measure without any target-fibre deletion
correction.  All deletion geometry is confined to the horizontal source term.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone

theorem normalizedProjectiveBaseSourceTerm_eq_zero_of_sameOrd
    {t : ℝ} (ht : 18 ≤ t)
    {rho : Zeros}
    (him : (rho : ℂ).im = t) :
    normalizedProjectiveBaseSourceTerm t rho = 0 := by
  have ht0 : t ≠ 0 := by linarith
  unfold normalizedProjectiveBaseSourceTerm
  rw [normalizedGap_eq_zero_of_sameOrd ht0 him,
      normalizedProjectiveBaseTransform_zero (by linarith : 0 < t)]
  ring

theorem normalizedProjectiveBaseSourceTerm_summable_full
    {t : ℝ} (ht : 18 ≤ t) :
    Summable (normalizedProjectiveBaseSourceTerm t) := by
  have ht0 : t ≠ 0 := by linarith
  have hatom :=
    normalizedProjectiveOffZeroAtom_summable_full ht
  have hhoriz :=
    normalizedProjectiveHorizontalSourceTerm_summable_full ht
  have hsub := hatom.sub hhoriz
  refine hsub.congr ?_
  intro rho
  have hsplit :=
    normalizedProjectiveOffZeroAtom_eq_baseSource_add_horizontalSource
      ht0 rho
  linarith

theorem tsum_sameOrd_normalizedProjectiveBaseSourceTerm_zero
    {t : ℝ} (ht : 18 ≤ t) :
    (∑' rho : SameOrd t,
      normalizedProjectiveBaseSourceTerm t (rho : Zeros)) = 0 := by
  apply tsum_eq_zero
  intro rho
  exact normalizedProjectiveBaseSourceTerm_eq_zero_of_sameOrd
    ht rho.property

/--
Deleting the target ordinate does not change the q-only projective base tsum.
-/
theorem tsum_full_normalizedProjectiveBaseSourceTerm_eq_offOrd
    {t : ℝ} (ht : 18 ≤ t) :
    (∑' rho : Zeros,
      normalizedProjectiveBaseSourceTerm t rho)
      =
    (∑' rho : ((SameOrd t)ᶜ : Set Zeros),
      normalizedProjectiveBaseSourceTerm t (rho : Zeros)) := by
  have hfull :=
    normalizedProjectiveBaseSourceTerm_summable_full ht
  have hsame := hfull.subtype (SameOrd t)
  have hoff := hfull.subtype ((SameOrd t)ᶜ)
  have hsplit :=
    (Summable.tsum_add_tsum_compl hsame hoff).symm
  rw [tsum_sameOrd_normalizedProjectiveBaseSourceTerm_zero ht,
      zero_add] at hsplit
  exact hsplit

/--
The literal projective Off defect may therefore be written with the FULL zero
carrier in the base term and only the horizontal term restricted off-ordinate.
-/
theorem canonical_offOrdProjectiveDefect_eq_fullBaseTsum_add_offHorizontalTsum
    {t : ℝ} (ht : 18 ≤ t) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
        (quantitativeCanonicalTaper t)
        t (quantitativeSampleRadius t)
      =
    (1 / (2 * t)) *
      (∑' rho : Zeros,
        normalizedProjectiveBaseSourceTerm t rho)
      +
    (1 / (2 * t)) *
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros)) := by
  rw [canonical_offOrdProjectiveDefect_eq_baseTsum_add_horizontalTsum ht]
  rw [← tsum_full_normalizedProjectiveBaseSourceTerm_eq_offOrd ht]

end Synthesis

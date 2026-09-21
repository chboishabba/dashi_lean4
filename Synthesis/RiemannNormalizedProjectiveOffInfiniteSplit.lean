import Synthesis.RiemannNormalizedProjectiveHorizontalPhaseOneBand
import Synthesis.RiemannNormalizedProjectiveOffTsumAttachment

/-!
# Infinite projective Off = base tsum + horizontal tsum

The per-zero normalized projective atom already has the exact split

  A_sigma^proj = B_sigma^proj + H_sigma^proj.

The atom family and the horizontal family are both summable on the literal
off-ordinate carrier.  Therefore the base family is summable as their
difference, and the split passes through the actual infinite tsum.

Combining with the exact reflection-pair normalization gives

  D_off^proj
    = (1/(2t)) sum'_off B_sigma^proj
      + (1/(2t)) sum'_off H_sigma^proj.

The sharpened phase-one signed-band theorem can then be applied directly to the
second term.  Thus, for every natural cutoff J inside the physical monotonicity
window, the literal Off defect is bounded above by the exact q-only base tsum
plus a theorem-bearing far-shell remainder.  There is no finite middle carrier
left and the factor 1/(2t) is retained exactly.
-/

noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.FarShellCutoffTailBound

def normalizedProjectiveBaseSourceTerm
    (t : ℝ) (sigma : Zeros) : ℝ :=
  ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
    * normalizedProjectiveBaseTransform t (normalizedGap t sigma)

theorem normalizedProjectiveOffZeroAtom_eq_baseSource_add_horizontalSource
    {t : ℝ} (ht : t ≠ 0) (sigma : Zeros) :
    normalizedProjectiveOffZeroAtom t sigma
      =
    normalizedProjectiveBaseSourceTerm t sigma
      + normalizedProjectiveHorizontalSourceTerm t sigma := by
  unfold normalizedProjectiveBaseSourceTerm
  exact normalizedProjectiveOffZeroAtom_eq_base_add_sourceHorizontal
    ht sigma

theorem normalizedProjectiveBaseSourceTerm_summable_offOrd
    {t : ℝ} (ht : 18 ≤ t) :
    Summable fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
      normalizedProjectiveBaseSourceTerm t (sigma : Zeros) := by
  have ht0 : t ≠ 0 := by linarith
  have hatom :=
    normalizedProjectiveOffZeroAtom_summable_offOrd ht
  have hhoriz :=
    normalizedProjectiveHorizontalSourceTerm_summable_offOrd ht
  have hsub := hatom.sub hhoriz
  refine hsub.congr ?_
  intro sigma
  have hsplit :=
    normalizedProjectiveOffZeroAtom_eq_baseSource_add_horizontalSource
      ht0 (sigma : Zeros)
  linarith

theorem tsum_offOrd_normalizedProjectiveAtom_eq_base_add_horizontal
    {t : ℝ} (ht : 18 ≤ t) :
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      normalizedProjectiveOffZeroAtom t (sigma : Zeros))
      =
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      normalizedProjectiveBaseSourceTerm t (sigma : Zeros))
      +
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros)) := by
  have ht0 : t ≠ 0 := by linarith
  have hbase :=
    normalizedProjectiveBaseSourceTerm_summable_offOrd ht
  have hhoriz :=
    normalizedProjectiveHorizontalSourceTerm_summable_offOrd ht
  rw [← hbase.tsum_add hhoriz]
  apply tsum_congr
  intro sigma
  exact
    normalizedProjectiveOffZeroAtom_eq_baseSource_add_horizontalSource
      ht0 (sigma : Zeros)

/--
Exact literal infinite Off split on the actual projective consumer.
-/
theorem canonical_offOrdProjectiveDefect_eq_baseTsum_add_horizontalTsum
    {t : ℝ} (ht : 18 ≤ t) :
    offOrdProjectiveDefect
        (quantitativeCanonicalTaper t)
        t (quantitativeSampleRadius t)
      =
    (1 / (2 * t)) *
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        normalizedProjectiveBaseSourceTerm t (sigma : Zeros))
      +
    (1 / (2 * t)) *
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros)) := by
  rw [canonical_offOrdProjectiveDefect_eq_normalizedProjectiveTsum ht,
      tsum_offOrd_normalizedProjectiveAtom_eq_base_add_horizontal ht]
  ring

/--
Inside any phase-one cutoff, the literal projective Off defect is bounded above
by its exact q-only base tsum plus only the far-shell horizontal remainder.
-/
theorem exists_canonicalOffProjective_le_base_add_horizontalFarShell
    {t : ℝ} (ht : 18 ≤ t)
    {J : ℕ} (hJ : 1 ≤ J)
    (hJphase :
      (J : ℝ) * (9 * Real.pi / (4 * t)) < 1) :
    ∃ A K : ℝ, 1 ≤ A ∧ 0 ≤ K ∧
      offOrdProjectiveDefect
          (quantitativeCanonicalTaper t)
          t (quantitativeSampleRadius t)
        ≤
      (1 / (2 * t)) *
        (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          normalizedProjectiveBaseSourceTerm t (sigma : Zeros))
        +
      (1 / (2 * t)) * (K * farShellBound A |t| J) := by
  obtain ⟨A, K, hA, hK, hhoriz⟩ :=
    exists_offOrdProjectiveHorizontal_le_farShell_of_cutoff_phase_one
      ht hJ hJphase
  have htpos : 0 < 1 / (2 * t) := by
    positivity
  have hscaled :=
    mul_le_mul_of_nonneg_left hhoriz htpos.le
  refine ⟨A, K, hA, hK, ?_⟩
  rw [canonical_offOrdProjectiveDefect_eq_baseTsum_add_horizontalTsum ht]
  exact add_le_add_left hscaled _

end Synthesis

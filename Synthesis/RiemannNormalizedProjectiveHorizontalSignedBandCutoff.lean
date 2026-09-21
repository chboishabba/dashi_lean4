import Synthesis.RiemannNormalizedProjectiveHorizontalLinearBand

/-!
# Horizontal signed-band cutoff compiler

The arbitrary-cutoff horizontal theorem has the exact shape

  horizontal_tsum <= refinedMiddle(J) + K * farShellBound(A,|t|,J).

The canonical radial-monotonicity theorem proves every source in the window

  |Im rho - t| < J <= t/9

has nonpositive horizontal contribution.  Hence, whenever the cutoff is chosen
inside that signed band, the finite middle disappears from the positive budget:

  horizontal_tsum <= K * farShellBound(A,|t|,J).

This is the first literal infinite horizontal upper bound with no surviving
finite local carrier.

For every t >= 18, J=2 is admissible, giving an unconditional theorem on the
whole high region.  Larger J may be used whenever J <= t/9.
-/

noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.FarShellCutoffTailBound

/--
If the literal cutoff lies inside the canonical signed band, the finite middle
carrier is nonpositive and drops from the one-sided horizontal budget.
-/
theorem exists_offOrdProjectiveHorizontal_le_farShell_of_cutoff_le_ninth
    {t : ℝ} (ht : 18 ≤ t)
    {J : ℕ} (hJ : 1 ≤ J)
    (hJband : (J : ℝ) ≤ t / 9) :
    ∃ A K : ℝ, 1 ≤ A ∧ 0 ≤ K ∧
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
        ≤ K * farShellBound A |t| J := by
  obtain ⟨A, K, hA, hK, hcut, hlim⟩ :=
    exists_offOrdProjectiveHorizontal_cutoff_reduction ht
  have hraw := hcut J hJ
  have hmiddle :=
    refinedMiddle_sum_nonpos_of_cutoff_le_ninth
      (t := t) ht (J := J) hJband
  refine ⟨A, K, hA, hK, ?_⟩
  linarith

/--
Uniform high-region specialization: J=2 lies in the signed band for every
t >= 18.
-/
theorem exists_offOrdProjectiveHorizontal_le_farShell_two
    {t : ℝ} (ht : 18 ≤ t) :
    ∃ A K : ℝ, 1 ≤ A ∧ 0 ≤ K ∧
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros))
        ≤ K * farShellBound A |t| 2 := by
  have hband : (2 : ℝ) ≤ t / 9 := by
    linarith
  exact
    exists_offOrdProjectiveHorizontal_le_farShell_of_cutoff_le_ninth
      ht (J := 2) (by norm_num) hband

end Synthesis

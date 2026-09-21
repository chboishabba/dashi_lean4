import Synthesis.RiemannZeta23RvMArbitraryEndpointDiscrepancy

/-!
# Lower bound for actual zero counts from the exact mu discrepancy

The arbitrary-endpoint theorem already gives

  |N(A,B) - integral_A^B mu|
    <= C (log(A+3) + log(B+4)).

For the quartic negative-window argument we need the one-sided consequence

  N(A,B)
    >= integral_A^B mu
       - C (log(A+3) + log(B+4)).

This file packages exactly that direction on the literal zeta zero-count carrier.
No new asymptotic or smooth surrogate is introduced.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23

theorem exists_zetaCount_ge_muIntegral_sub_logError :
    ∃ C T0 : ℝ, 0 <= C ∧
      ∀ A B : ℝ,
        max T0 4 <= A ->
        A < B ->
        (∫ tau in A..B, Zeta23.mu tau)
          - C * (Real.log (A + 3) + Real.log (B + 4))
          <=
        (zetaZeroConfig.N A B : ℝ) := by
  obtain ⟨C, T0, hC, hD⟩ :=
    exists_zetaMuWindowDiscrepancy_arbitrary_bound
  refine ⟨C, T0, hC, ?_⟩
  intro A B hA hAB
  have h :=
    hD A B hA hAB
  unfold zetaMuWindowDiscrepancy at h
  have hlo :=
    (abs_le.mp h).1
  linarith

theorem exists_zetaCount_le_muIntegral_add_logError :
    ∃ C T0 : ℝ, 0 <= C ∧
      ∀ A B : ℝ,
        max T0 4 <= A ->
        A < B ->
        (zetaZeroConfig.N A B : ℝ)
          <=
        (∫ tau in A..B, Zeta23.mu tau)
          + C * (Real.log (A + 3) + Real.log (B + 4)) := by
  obtain ⟨C, T0, hC, hD⟩ :=
    exists_zetaMuWindowDiscrepancy_arbitrary_bound
  refine ⟨C, T0, hC, ?_⟩
  intro A B hA hAB
  have h :=
    hD A B hA hAB
  unfold zetaMuWindowDiscrepancy at h
  have hhi :=
    (abs_le.mp h).2
  linarith

end Synthesis

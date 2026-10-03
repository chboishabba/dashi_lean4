import Synthesis.RiemannZeta23RvMArbitraryEndpointDiscrepancy

/-!
# Arbitrary-endpoint literal zero-count bound

The inverse-square max-cut needs a count estimate on literal zeta ordinate
windows, not only a discrepancy estimate.  The existing arbitrary-endpoint RvM
theorem gives

  |N(A,B) - ∫_A^B mu| <= C_D (log(A+3) + log(B+4))

for 5 <= A < B.  The existing pointwise bound

  |mu(x)| <= C_mu log(x+3)

therefore yields the source-native count estimate

  N(A,B) <= C_N (B-A+1) log(B+4).

This file performs only that conversion.  It does not yet sum dyadic shells and
it does not change the zero-count carrier.
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23.RvM

/-- A theorem-bearing arbitrary-endpoint upper bound for the literal zeta zero
count.  Multiplicity is exactly the multiplicity already carried by `Ncount`.
-/
theorem exists_zetaZeroCount_arbitrary_bound_at_five :
    ∃ C : ℝ, 0 <= C ∧
      ∀ A B : ℝ,
        5 <= A ->
        A < B ->
        (zetaZeroConfig.N A B : ℝ)
          <= C * ((B - A) + 1) * Real.log (B + 4) := by
  obtain ⟨CD, hCD0, hD⟩ :=
    exists_zetaMuWindowDiscrepancy_arbitrary_bound_at_five
  obtain ⟨CM, hCM0, hMu⟩ := Zeta23.RvM.mu_le_log Zeta23.gammaFacts
  let C : ℝ := CM + 2 * CD + 1
  have hC0 : 0 <= C := by
    dsimp [C]
    linarith
  refine ⟨C, hC0, ?_⟩
  intro A B hA hAB
  have hAleB : A <= B := hAB.le
  have hA1 : 1 <= A := by linarith
  have hB1 : 1 <= B := by linarith
  have hlogB0 : 0 <= Real.log (B + 4) :=
    Real.log_nonneg (by linarith)
  have hmuPoint :
      ∀ x ∈ Set.uIoc A B,
        |Zeta23.mu x| <= CM * Real.log (B + 4) := by
    intro x hx
    rw [Set.uIoc_of_le hAleB] at hx
    have hx1 : 1 <= x := le_trans hA1 hx.1.le
    have hlog : Real.log (x + 3) <= Real.log (B + 4) :=
      Real.log_le_log (by linarith) (by linarith [hx.2])
    exact (hMu x hx1).trans
      (mul_le_mul_of_nonneg_left hlog hCM0)
  have hmuRaw :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := Zeta23.mu) hmuPoint
  rw [Real.norm_eq_abs] at hmuRaw
  have hlen : |B - A| = B - A :=
    abs_of_nonneg (sub_nonneg.mpr hAleB)
  rw [hlen] at hmuRaw
  have hmuAbs :
      |∫ x in A..B, Zeta23.mu x|
        <= CM * Real.log (B + 4) * (B - A) := by
    simpa using hmuRaw
  have hmuUpper :
      (∫ x in A..B, Zeta23.mu x)
        <= CM * Real.log (B + 4) * (B - A) :=
    (le_abs_self _).trans hmuAbs

  have hDraw := hD A B hA hAB
  have hdiff :
      (zetaZeroConfig.N A B : ℝ)
        - ∫ x in A..B, Zeta23.mu x
      <= CD * (Real.log (A + 3) + Real.log (B + 4)) := by
    have hle := (le_abs_self (zetaMuWindowDiscrepancy A B)).trans hDraw
    simpa [zetaMuWindowDiscrepancy] using hle
  have hlogA : Real.log (A + 3) <= Real.log (B + 4) :=
    Real.log_le_log (by linarith) (by linarith)
  have hdiscSimple :
      CD * (Real.log (A + 3) + Real.log (B + 4))
        <= 2 * CD * Real.log (B + 4) := by
    have hs := mul_le_mul_of_nonneg_left
      (add_le_add hlogA le_rfl) hCD0
    nlinarith
  have hcount :
      (zetaZeroConfig.N A B : ℝ)
        <= CM * Real.log (B + 4) * (B - A)
          + 2 * CD * Real.log (B + 4) := by
    linarith
  have hgap0 : 0 <= B - A := sub_nonneg.mpr hAleB
  dsimp [C]
  nlinarith [mul_nonneg hCM0 hlogB0,
    mul_nonneg hCD0 hlogB0]

end Synthesis

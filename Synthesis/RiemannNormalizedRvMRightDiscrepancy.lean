import Synthesis.RiemannZeta23RvMArbitraryEndpointDiscrepancy
import Synthesis.RiemannNormalizedCountingAbelCompiler

/-!
# Target-centred normalized cumulative zeta-minus-mu discrepancy

For a positive target ordinate t and normalized right gap q >= 0 define

  D_t^+(q)
    = N(t, t(1+q))
      - integral_t^{t(1+q)} mu.

This is the cumulative discrepancy between the actual zeta counting measure and
the exact smooth RvM measure on the normalized q-axis.

The arbitrary-endpoint RvM theorem immediately gives

  |D_t^+(q)|
    <= C [ log(t+3) + log(t(1+q)+4) ]

for all sufficiently high t.

This is exactly the prefix-bound species consumed by finite Abel summation once
a finite increasing q-grid is chosen.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23

def normalizedRightMuCountDiscrepancy (t q : ℝ) : ℝ :=
  (zetaZeroConfig.N t (t * (1 + q)) : ℝ)
    - ∫ tau in t..(t * (1 + q)), Zeta23.mu tau

theorem normalizedRightMuCountDiscrepancy_eq_window
    (t q : ℝ) :
    normalizedRightMuCountDiscrepancy t q
      =
    zetaMuWindowDiscrepancy t (t * (1 + q)) := by
  rfl

theorem exists_normalizedRightMuCountDiscrepancy_bound :
    ∃ C T0 : ℝ, 0 <= C ∧
      ∀ t q : ℝ,
        max T0 4 <= t ->
        0 < q ->
        |normalizedRightMuCountDiscrepancy t q|
          <=
        C * (Real.log (t + 3)
          + Real.log (t * (1 + q) + 4)) := by
  obtain ⟨C, T0, hC, hD⟩ :=
    exists_zetaMuWindowDiscrepancy_arbitrary_bound
  refine ⟨C, T0, hC, ?_⟩
  intro t q ht hq
  rw [normalizedRightMuCountDiscrepancy_eq_window]
  exact hD t (t * (1 + q)) ht (by
    have ht0 : 0 < t := by linarith
    nlinarith)

theorem normalizedRightMuCountDiscrepancy_zero (t : ℝ) :
    normalizedRightMuCountDiscrepancy t 0 = 0 := by
  unfold normalizedRightMuCountDiscrepancy
  simp

/--
For a finite increasing normalized grid q_0=0 < q_1 < ... < q_n, define the
actual-minus-mu increment on each adjacent normalized interval.
-/
def normalizedRightMuIncrement
    (t : ℝ) (q : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then
    normalizedRightMuCountDiscrepancy t (q 0)
  else
    normalizedRightMuCountDiscrepancy t (q i)
      - normalizedRightMuCountDiscrepancy t (q (i - 1))

theorem abelPrefix_normalizedRightMuIncrement
    (t : ℝ) (q : ℕ → ℝ) (k : ℕ)
    (hq0 : q 0 = 0) :
    abelPrefix (normalizedRightMuIncrement t q) k
      =
    normalizedRightMuCountDiscrepancy t (q k) := by
  induction k with
  | zero =>
      simp [abelPrefix, normalizedRightMuIncrement, hq0,
        normalizedRightMuCountDiscrepancy_zero]
  | succ k ih =>
      rw [abelPrefix_succ, ih]
      unfold normalizedRightMuIncrement
      simp only [Nat.add_eq, Nat.succ_ne_zero, ↓reduceIte,
        Nat.succ_sub_one]
      ring

/--
Direct Abel-ready prefix estimate on a finite normalized right-gap grid.
-/
theorem exists_normalizedRightMuIncrement_prefix_bound :
    ∃ C T0 : ℝ, 0 <= C ∧
      ∀ (t : ℝ) (q : ℕ → ℝ) (n : ℕ),
        max T0 4 <= t ->
        q 0 = 0 ->
        (∀ k, k <= n -> 0 <= q k) ->
        ∀ k, k <= n ->
          |abelPrefix (normalizedRightMuIncrement t q) k|
            <=
          C * (Real.log (t + 3)
            + Real.log (t * (1 + q k) + 4)) := by
  obtain ⟨C, T0, hC, hD⟩ :=
    exists_normalizedRightMuCountDiscrepancy_bound
  refine ⟨C, T0, hC, ?_⟩
  intro t q n ht hq0 hq k hk
  rw [abelPrefix_normalizedRightMuIncrement t q k hq0]
  rcases eq_or_lt_of_le (hq k hk) with hzero | hpos
  · rw [← hzero, normalizedRightMuCountDiscrepancy_zero, abs_zero]
    have hlog1 : 0 <= Real.log (t + 3) :=
      Real.log_nonneg (by linarith)
    have hlog2 : 0 <= Real.log (t * (1 + q k) + 4) := by
      rw [← hzero]
      exact Real.log_nonneg (by linarith)
    positivity
  · exact hD t (q k) ht hpos

end Synthesis

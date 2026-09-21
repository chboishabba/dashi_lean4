import Synthesis.RiemannNormalizedRvMRightDiscrepancy

/-!
# Target-centred normalized left cumulative zeta-minus-mu discrepancy

For 0 <= p < 1 define the left normalized cutoff

  gamma = t(1-p)

and cumulative discrepancy

  D_t^-(p)
    = N(t(1-p), t)
      - integral_{t(1-p)}^t mu.

Whenever the left endpoint remains in the high RvM range, the arbitrary-endpoint
theorem gives the same O(log)-type cumulative control as on the right.

This is the high-positive-ordinate left half of the target-centred Abel input.
It deliberately does not drag genuinely low ordinates into the high analysis;
those remain available to the located-low/R3 split.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23

def normalizedLeftMuCountDiscrepancy (t p : ℝ) : ℝ :=
  (zetaZeroConfig.N (t * (1 - p)) t : ℝ)
    - ∫ tau in (t * (1 - p))..t, Zeta23.mu tau

theorem normalizedLeftMuCountDiscrepancy_eq_window
    (t p : ℝ) :
    normalizedLeftMuCountDiscrepancy t p
      =
    zetaMuWindowDiscrepancy (t * (1 - p)) t := by
  rfl

theorem exists_normalizedLeftMuCountDiscrepancy_bound :
    ∃ C T0 : ℝ, 0 <= C ∧
      ∀ t p : ℝ,
        0 < p ->
        p < 1 ->
        max T0 4 <= t * (1 - p) ->
        |normalizedLeftMuCountDiscrepancy t p|
          <=
        C * (Real.log (t * (1 - p) + 3)
          + Real.log (t + 4)) := by
  obtain ⟨C, T0, hC, hD⟩ :=
    exists_zetaMuWindowDiscrepancy_arbitrary_bound
  refine ⟨C, T0, hC, ?_⟩
  intro t p hp hp1 hleft
  rw [normalizedLeftMuCountDiscrepancy_eq_window]
  have ht0 : 0 < t := by
    have hprod : 0 < t * (1-p) := by
      linarith
    have hone : 0 < 1-p := by linarith
    positivity
  exact hD (t * (1-p)) t hleft (by
    have hone : 0 < 1-p := by linarith
    nlinarith)

theorem normalizedLeftMuCountDiscrepancy_zero (t : ℝ) :
    normalizedLeftMuCountDiscrepancy t 0 = 0 := by
  unfold normalizedLeftMuCountDiscrepancy
  simp

/--
Adjacent increments on an increasing left-distance grid p_0=0 < ... < p_n.
The cumulative prefix telescopes to D_t^-(p_k).
-/
def normalizedLeftMuIncrement
    (t : ℝ) (p : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then
    normalizedLeftMuCountDiscrepancy t (p 0)
  else
    normalizedLeftMuCountDiscrepancy t (p i)
      - normalizedLeftMuCountDiscrepancy t (p (i - 1))

theorem abelPrefix_normalizedLeftMuIncrement
    (t : ℝ) (p : ℕ → ℝ) (k : ℕ)
    (hp0 : p 0 = 0) :
    abelPrefix (normalizedLeftMuIncrement t p) k
      =
    normalizedLeftMuCountDiscrepancy t (p k) := by
  induction k with
  | zero =>
      simp [abelPrefix, normalizedLeftMuIncrement, hp0,
        normalizedLeftMuCountDiscrepancy_zero]
  | succ k ih =>
      rw [abelPrefix_succ, ih]
      unfold normalizedLeftMuIncrement
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
      ring

/--
Abel-ready left prefix bound on a finite grid staying above the high RvM floor.
-/
theorem exists_normalizedLeftMuIncrement_prefix_bound :
    ∃ C T0 : ℝ, 0 <= C ∧
      ∀ (t : ℝ) (p : ℕ → ℝ) (n : ℕ),
        p 0 = 0 ->
        (∀ k, k <= n -> 0 <= p k) ->
        (∀ k, k <= n -> p k < 1) ->
        (∀ k, k <= n -> max T0 4 <= t * (1 - p k)) ->
        ∀ k, k <= n ->
          |abelPrefix (normalizedLeftMuIncrement t p) k|
            <=
          C * (Real.log (t * (1 - p k) + 3)
            + Real.log (t + 4)) := by
  obtain ⟨C, T0, hC, hD⟩ :=
    exists_normalizedLeftMuCountDiscrepancy_bound
  refine ⟨C, T0, hC, ?_⟩
  intro t p n hp0 hpnn hpone hhigh k hk
  rw [abelPrefix_normalizedLeftMuIncrement t p k hp0]
  rcases eq_or_lt_of_le (hpnn k hk) with hzero | hpos
  · rw [← hzero, normalizedLeftMuCountDiscrepancy_zero, abs_zero]
    have hleft := hhigh k hk
    have hlog1 : 0 <= Real.log (t * (1 - p k) + 3) := by
      rw [← hzero]
      exact Real.log_nonneg (by linarith)
    have hlog2 : 0 <= Real.log (t + 4) := by
      have : 0 < t := by
        rw [← hzero] at hleft
        linarith
      exact Real.log_nonneg (by linarith)
    positivity
  · exact hD t (p k) hpos (hpone k hk) (hhigh k hk)

end Synthesis

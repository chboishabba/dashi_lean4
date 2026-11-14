import Mathlib
import YangMills.SameHWilsonMixedHalfRateWeld

open Filter

/-!
# Dense half-rate bounds exclude spectral windows above one half

The source clustering estimate supplies vector-dependent constants, so it does
not imply an operator-norm estimate.  The correct spectral argument instead
uses a standard spectral projection lower bound.  If a continuous operator `P`
represents a spectral window with transfer eigenvalues bounded below by
`lambda > 1/2`, then

  lambda^n * ‖P x‖² ≤ |⟪x, T_n x⟫|

for every vector `x`.  On a dense family with the source half-rate, any nonzero
`P x` would force a strictly faster exponential to remain below `C_x 2^{-n}`
for all `n`, which is impossible.  Continuity then forces `P = 0`.

Functional calculus still has to supply the physical spectral projection and
this lower-bound property.  No spectrum or generator predicate is defined to be
true locally.
-/

namespace RequestProject.YangMills

/-- A strict exponential with base greater than `1/2` eventually beats every fixed half-rate. -/
theorem strict_exponential_eventually_beats_half_rate
    (λ C A : ℝ)
    (hλ : (1 / 2 : ℝ) < λ)
    (hA : 0 < A) :
    ∃ n : ℕ, C * (1 / 2 : ℝ) ^ n < λ ^ n * A := by
  have hr : 1 < 2 * λ := by
    nlinarith
  have hTop :
      Tendsto (fun n : ℕ => (2 * λ) ^ n * A) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hr).atTop_mul_const hA
  obtain ⟨n, hn⟩ :=
    Eventually.exists (hTop.eventually_gt_atTop C)
  refine ⟨n, ?_⟩
  have hhalf : 0 < (1 / 2 : ℝ) ^ n :=
    pow_pos (by norm_num) n
  have hmul := mul_lt_mul_of_pos_right hn hhalf
  calc
    C * (1 / 2 : ℝ) ^ n
        < ((2 * λ) ^ n * A) * (1 / 2 : ℝ) ^ n := hmul
    _ = (((2 * λ) * (1 / 2 : ℝ)) ^ n) * A := by
      rw [mul_pow]
      ring
    _ = λ ^ n * A := by
      ring_nf

/--
Abstract lower bound supplied by a genuine spectral projection/window for the
same discrete transfer family.
-/
def SpectralWindowLowerBound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : ℕ → H →L[ℝ] H)
    (P : H →L[ℝ] H) (λ : ℝ) : Prop :=
  ∀ x : H, ∀ n : ℕ,
    λ ^ n * ‖P x‖ ^ 2 ≤ |⟪x, T n x⟫_ℝ|

/-- One controlled vector cannot have a nonzero component in a strict-above-half spectral window. -/
theorem half_rate_forces_spectral_window_zero_on_vector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : ℕ → H →L[ℝ] H)
    (P : H →L[ℝ] H) (λ : ℝ)
    (hλ : (1 / 2 : ℝ) < λ)
    (hLower : SpectralWindowLowerBound T P λ)
    (x : H)
    (hRate : HalfRateMatrixBound T x x) :
    P x = 0 := by
  rcases hRate with ⟨C, hC, hUpper⟩
  by_contra hPx
  have hNorm : 0 < ‖P x‖ := norm_pos_iff.mpr hPx
  have hSquare : 0 < ‖P x‖ ^ 2 := sq_pos_of_pos hNorm
  obtain ⟨n, hBeat⟩ :=
    strict_exponential_eventually_beats_half_rate
      λ C (‖P x‖ ^ 2) hλ hSquare
  have hWindow := hLower x n
  have hDecay := hUpper n
  have hImpossible :
      λ ^ n * ‖P x‖ ^ 2 ≤ C * (1 / 2 : ℝ) ^ n :=
    hWindow.trans hDecay
  exact (not_lt_of_ge hImpossible) hBeat

/--
If the half-rate-controlled set is dense, every strict-above-half spectral
window operator satisfying the standard lower bound is identically zero.
-/
theorem dense_half_rate_forces_spectral_window_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : ℕ → H →L[ℝ] H)
    (controlled : Set H)
    (hDense : Dense controlled)
    (hRate : ∀ x ∈ controlled, HalfRateMatrixBound T x x)
    (P : H →L[ℝ] H) (λ : ℝ)
    (hλ : (1 / 2 : ℝ) < λ)
    (hLower : SpectralWindowLowerBound T P λ) :
    P = 0 := by
  have hEqOn : Set.EqOn P (0 : H →L[ℝ] H) controlled := by
    intro x hx
    exact half_rate_forces_spectral_window_zero_on_vector
      T P λ hλ hLower x (hRate x hx)
  have hClosure :
      Set.EqOn P (0 : H →L[ℝ] H) (closure controlled) :=
    Set.EqOn.closure hEqOn P.continuous (0 : H →L[ℝ] H).continuous
  have hAll : Set.EqOn P (0 : H →L[ℝ] H) Set.univ := by
    simpa [hDense.closure_eq] using hClosure
  ext x
  exact hAll (Set.mem_univ x)

end RequestProject.YangMills

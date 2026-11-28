import Mathlib
import YangMills.HalfRateSpectralNoPollution

namespace RequestProject.YangMills

example (λ C A : ℝ)
    (hλ : (1 / 2 : ℝ) < λ) (hA : 0 < A) :
    ∃ n : ℕ, C * (1 / 2 : ℝ) ^ n < λ ^ n * A :=
  strict_exponential_eventually_beats_half_rate λ C A hλ hA

example
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : ℕ → H →L[ℝ] H)
    (controlled : Set H) (hDense : Dense controlled)
    (hRate : ∀ x ∈ controlled, HalfRateMatrixBound T x x)
    (P : H →L[ℝ] H) (λ : ℝ) (hλ : (1 / 2 : ℝ) < λ)
    (hLower : SpectralWindowLowerBound T P λ) :
    P = 0 :=
  dense_half_rate_forces_spectral_window_zero
    T controlled hDense hRate P λ hλ hLower

end RequestProject.YangMills

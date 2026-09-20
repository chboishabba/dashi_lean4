import Synthesis.RiemannNormalizedRvMZeroModeFourier
import Synthesis.RiemannNormalizedRvMMainRemainderCompiler

/-!
# Smooth RvM main-term decomposition on the normalized q-grid

This file pays the algebraic part of the remaining smooth-main producer without
silently enlarging the theorem domain.

For a positive sample height t and normalized ordinate q > -1,

  log (t (1+q) / (2*pi))
    = log (t/(2*pi)) + log (1+q).

Thus the smooth Riemann--von Mangoldt density splits into

  constant-in-q mode + genuine q-shape.

On any finite normalized grid this gives an exact signed pairing decomposition.
If the test values have zero total mass, the dangerous constant mode vanishes
*exactly*, leaving only the log(1+q) shape pairing.

The existing Fourier-inversion owner
`RiemannNormalizedRvMZeroModeFourier` proves exact whole-line Fourier
annihilation from the physical zero-mode gap, conditional only on L1 Fourier
integrability.  This file deliberately does not identify that whole-line
statement with a finite/truncated q-grid sum: the grid/quadrature/domain-tail
transport remains an explicit theorem-bearing obligation.
-/

noncomputable section

open scoped BigOperators Real

namespace Synthesis

/-- The smooth RvM density in the normalized ordinate q=(gamma-t)/t. -/
def normalizedRvMSmoothDensity (t q : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * Real.log (t * (1 + q) / (2 * Real.pi))

/-- The q-independent coefficient of the smooth density. -/
def normalizedRvMConstantMode (t : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * Real.log (t / (2 * Real.pi))

/-- The residual normalized logarithmic shape. -/
def normalizedRvMLogShape (q : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * Real.log (1 + q)

theorem normalizedRvM_log_argument_factor
    (t q : ℝ) :
    t * (1 + q) / (2 * Real.pi)
      = (t / (2 * Real.pi)) * (1 + q) := by
  ring

theorem normalizedRvM_log_decompose
    {t q : ℝ} (ht : 0 < t) (hq : -1 < q) :
    Real.log (t * (1 + q) / (2 * Real.pi))
      =
    Real.log (t / (2 * Real.pi)) + Real.log (1 + q) := by
  rw [normalizedRvM_log_argument_factor]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have htq : t / (2 * Real.pi) ≠ 0 := div_ne_zero (ne_of_gt ht) hpi
  have hq1 : (1 + q : ℝ) ≠ 0 := by linarith
  rw [Real.log_mul htq hq1]

theorem normalizedRvMSmoothDensity_decompose
    {t q : ℝ} (ht : 0 < t) (hq : -1 < q) :
    normalizedRvMSmoothDensity t q
      =
    normalizedRvMConstantMode t + normalizedRvMLogShape q := by
  unfold normalizedRvMSmoothDensity normalizedRvMConstantMode
    normalizedRvMLogShape
  rw [normalizedRvM_log_decompose ht hq]
  ring

/--
Exact finite signed smooth-main pairing decomposition.

This is the discrete theorem-facing form consumed by the existing normalized
Abel/RvM compiler.  No absolute value is introduced.
-/
theorem finite_normalizedRvMSmoothPair_decompose
    (t : ℝ) (q phi : ℕ → ℝ) (n : ℕ)
    (ht : 0 < t)
    (hq : ∀ i, i < n + 1 -> -1 < q i) :
    (∑ i ∈ Finset.range (n + 1),
        normalizedRvMSmoothDensity t (q i) * phi i)
      =
    normalizedRvMConstantMode t *
        (∑ i ∈ Finset.range (n + 1), phi i)
      +
    ∑ i ∈ Finset.range (n + 1),
        normalizedRvMLogShape (q i) * phi i := by
  rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < n + 1 := Finset.mem_range.mp hi
  rw [normalizedRvMSmoothDensity_decompose ht (hq i hi')]
  ring

/--
If the normalized test grid annihilates constants, the apparent log(t) growth
of the smooth RvM main term disappears exactly.
-/
theorem finite_normalizedRvMSmoothPair_zeroMode_cancel
    (t : ℝ) (q phi : ℕ → ℝ) (n : ℕ)
    (ht : 0 < t)
    (hq : ∀ i, i < n + 1 -> -1 < q i)
    (hzero : ∑ i ∈ Finset.range (n + 1), phi i = 0) :
    (∑ i ∈ Finset.range (n + 1),
        normalizedRvMSmoothDensity t (q i) * phi i)
      =
    ∑ i ∈ Finset.range (n + 1),
        normalizedRvMLogShape (q i) * phi i := by
  rw [finite_normalizedRvMSmoothPair_decompose t q phi n ht hq, hzero]
  ring

/--
Interface theorem making the remaining bridge explicit: any producer of exact
constant-mode annihilation on the actual ordered q-grid immediately removes the
q-independent RvM main density from the signed main pairing.
-/
theorem finite_normalizedRvMSmoothPair_cancel_of_zeroModeProducer
    (t : ℝ) (q phi : ℕ → ℝ) (n : ℕ)
    (ht : 0 < t)
    (hq : ∀ i, i < n + 1 -> -1 < q i)
    (zeroModeProducer :
      ∑ i ∈ Finset.range (n + 1), phi i = 0) :
    (∑ i ∈ Finset.range (n + 1),
        normalizedRvMSmoothDensity t (q i) * phi i)
      =
    ∑ i ∈ Finset.range (n + 1),
        normalizedRvMLogShape (q i) * phi i :=
  finite_normalizedRvMSmoothPair_zeroMode_cancel
    t q phi n ht hq zeroModeProducer

end Synthesis

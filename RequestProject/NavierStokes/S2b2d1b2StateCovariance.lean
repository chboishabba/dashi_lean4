import Mathlib
import RequestProject.NavierStokes.R571PairedSecondMoment

noncomputable section

namespace RequestProject.NavierStokes.S2b2d1b2StateCovariance

open Finset

/-- The positive second moment of a finite real family. -/
def secondMoment {ι : Type*} (s : Finset ι) (f : ι → ℝ) : ℝ :=
  ∑ i ∈ s, (f i) ^ 2

/-- The signed bilinear covariance numerator on a finite family. Absolute
values are intentionally absent here: cancellation is retained until after
the finite sum is formed. -/
def signedCovariance {ι : Type*} (s : Finset ι) (a b : ι → ℝ) : ℝ :=
  ∑ i ∈ s, a i * b i

theorem secondMoment_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    0 ≤ secondMoment s f := by
  unfold secondMoment
  exact Finset.sum_nonneg fun i _ => sq_nonneg (f i)

/-- Finite Young/Cauchy payment, proved without termwise absolute-value
majorisation before the signed sum:

  2 |Σ aᵢ bᵢ| ≤ Σ aᵢ² + Σ bᵢ².

This is the quantitative bridge needed after the exact centred-covariance
identity: the signed covariance is reduced to two positive second moments. -/
theorem two_mul_abs_signedCovariance_le_secondMoments
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    2 * |signedCovariance s a b|
      ≤ secondMoment s a + secondMoment s b := by
  have hplus :
      2 * signedCovariance s a b
        ≤ secondMoment s a + secondMoment s b := by
    unfold signedCovariance secondMoment
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i hi => by
      nlinarith [sq_nonneg (a i - b i)]
  have hminus :
      -2 * signedCovariance s a b
        ≤ secondMoment s a + secondMoment s b := by
    unfold signedCovariance secondMoment
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i hi => by
      nlinarith [sq_nonneg (a i + b i)]
  by_cases h : 0 ≤ signedCovariance s a b
  · rw [abs_of_nonneg h]
    exact hplus
  · rw [abs_of_neg (lt_of_not_ge h)]
    nlinarith

/-- Pair-difference second moment on the full ordered finite pair fibre. The
ordered fibre is deliberate: it avoids choosing an arbitrary total order on
physical interaction cells and keeps the theorem permutation-invariant. -/
def pairDifferenceSecondMoment {ι : Type*} (s : Finset ι) (f : ι → ℝ) : ℝ :=
  ∑ z ∈ s ×ˢ s, (f z.1 - f z.2) ^ 2

/-- Signed pair-difference covariance on the same ordered pair fibre. -/
def pairDifferenceCovariance {ι : Type*} (s : Finset ι)
    (rate work : ι → ℝ) : ℝ :=
  ∑ z ∈ s ×ˢ s,
    (rate z.1 - rate z.2) * (work z.1 - work z.2)

/-- The literal pair-difference covariance payment:

  2 |Σ_{i,j} (rᵢ-rⱼ)(wᵢ-wⱼ)|
    ≤ Σ_{i,j}(rᵢ-rⱼ)² + Σ_{i,j}(wᵢ-wⱼ)².

This is exactly the positive-second-moment reduction suggested by the
R571 paired donor. It does not assume a sign for covariance and it does not
introduce a Galerkin-cardinality constant. -/
theorem two_mul_abs_pairDifferenceCovariance_le
    {ι : Type*} (s : Finset ι) (rate work : ι → ℝ) :
    2 * |pairDifferenceCovariance s rate work|
      ≤ pairDifferenceSecondMoment s rate
        + pairDifferenceSecondMoment s work := by
  simpa only [pairDifferenceCovariance, pairDifferenceSecondMoment]
    using two_mul_abs_signedCovariance_le_secondMoments
      (s ×ˢ s)
      (fun z => rate z.1 - rate z.2)
      (fun z => work z.1 - work z.2)

/-- Same payment for a finite family whose physical adapter has already
absorbed any nonnegative square-root weight into the two factors. -/
theorem two_mul_abs_weightedSignedSum_le
    {ι : Type*} (s : Finset ι) (left right : ι → ℝ) :
    2 * |∑ i ∈ s, left i * right i|
      ≤ (∑ i ∈ s, (left i) ^ 2) + ∑ i ∈ s, (right i) ^ 2 := by
  simpa only [signedCovariance, secondMoment]
    using two_mul_abs_signedCovariance_le_secondMoments s left right

/-- Once the two pair-difference second moments have physical bounds R and W,
the signed covariance is bounded by their sum. -/
theorem pairDifferenceCovariance_of_secondMoment_bounds
    {ι : Type*} (s : Finset ι) (rate work : ι → ℝ) {R W : ℝ}
    (hR : pairDifferenceSecondMoment s rate ≤ R)
    (hW : pairDifferenceSecondMoment s work ≤ W) :
    2 * |pairDifferenceCovariance s rate work| ≤ R + W := by
  calc
    2 * |pairDifferenceCovariance s rate work|
        ≤ pairDifferenceSecondMoment s rate
          + pairDifferenceSecondMoment s work :=
      two_mul_abs_pairDifferenceCovariance_le s rate work
    _ ≤ R + W := add_le_add hR hW

end RequestProject.NavierStokes.S2b2d1b2StateCovariance

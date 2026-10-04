import Synthesis.RiemannSelectedPrimeSensitiveThreeTapInverseSquareWindow

/-!
# Dyadic shell geometry and the geometric/log series

This file is deliberately independent of the witness-curvature side.  It pays
only the numerical shell bookkeeping needed after the literal all-real
unit-window inverse-square estimate.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators

/-- Radius of dyadic shell `k`, starting at the half-height cutoff `t/2`. -/
def threeTapDyadicRadius (t : ℝ) (k : ℕ) : ℝ :=
  (2 : ℝ)^k * (t / 2)

/-- Left shell `(t-2R_k, t-R_k]`. -/
def threeTapLeftShellLower (t : ℝ) (k : ℕ) : ℝ :=
  t - 2 * threeTapDyadicRadius t k

def threeTapLeftShellUpper (t : ℝ) (k : ℕ) : ℝ :=
  t - threeTapDyadicRadius t k

/-- Right shell `(t+R_k, t+2R_k]`. -/
def threeTapRightShellLower (t : ℝ) (k : ℕ) : ℝ :=
  t + threeTapDyadicRadius t k

def threeTapRightShellUpper (t : ℝ) (k : ℕ) : ℝ :=
  t + 2 * threeTapDyadicRadius t k

@[simp] theorem threeTapDyadicRadius_zero (t : ℝ) :
    threeTapDyadicRadius t 0 = t / 2 := by
  simp [threeTapDyadicRadius]

@[simp] theorem threeTapDyadicRadius_succ (t : ℝ) (k : ℕ) :
    threeTapDyadicRadius t (k+1) = 2 * threeTapDyadicRadius t k := by
  simp [threeTapDyadicRadius, pow_succ]
  ring

/-- Consecutive left half-open shells meet at exactly one endpoint. -/
theorem threeTapLeftShellLower_eq_nextUpper (t : ℝ) (k : ℕ) :
    threeTapLeftShellLower t k = threeTapLeftShellUpper t (k+1) := by
  simp [threeTapLeftShellLower, threeTapLeftShellUpper]

/-- Consecutive right half-open shells meet at exactly one endpoint. -/
theorem threeTapRightShellUpper_eq_nextLower (t : ℝ) (k : ℕ) :
    threeTapRightShellUpper t k = threeTapRightShellLower t (k+1) := by
  simp [threeTapRightShellUpper, threeTapRightShellLower]

/-- At the first shell the two charts begin exactly at the half-height cut. -/
theorem threeTapLeftShellUpper_zero (t : ℝ) :
    threeTapLeftShellUpper t 0 = t / 2 := by
  simp [threeTapLeftShellUpper]
  ring

theorem threeTapRightShellLower_zero (t : ℝ) :
    threeTapRightShellLower t 0 = 3 * t / 2 := by
  simp [threeTapRightShellLower]
  ring

/-- Positive heights give strictly increasing dyadic radii. -/
theorem threeTapDyadicRadius_pos {t : ℝ} (ht : 0 < t) (k : ℕ) :
    0 < threeTapDyadicRadius t k := by
  unfold threeTapDyadicRadius
  positivity

/-- Numerical shell majorant.  A literal shell estimate of this shape sums to
`O(log t/t)` because both the geometric and `k * geometric` series converge. -/
def threeTapDyadicLogMajorant (t : ℝ) (k : ℕ) : ℝ :=
  ((Real.log t + 1) + (k : ℝ)) * (1 / 2 : ℝ)^k / t

/-- Exact sum of the numerical shell majorant.  The identity packages the only
infinite-series algebra needed by the shell proof:

  sum_k ((log t + 1) + k) 2^{-k} / t = (2 log t + 4)/t.
-/
theorem hasSum_threeTapDyadicLogMajorant {t : ℝ} (ht : t ≠ 0) :
    HasSum (threeTapDyadicLogMajorant t) ((2 * Real.log t + 4) / t) := by
  have hhalf : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have hgeom : HasSum (fun k : ℕ => (1 / 2 : ℝ)^k) 2 := by
    convert hasSum_geometric_of_norm_lt_one hhalf using 1 <;> norm_num
  have hnat : HasSum (fun k : ℕ => (k : ℝ) * (1 / 2 : ℝ)^k) 2 := by
    convert hasSum_coe_mul_geometric_of_norm_lt_one hhalf using 1 <;> norm_num
  have hscaled :
      HasSum
        (fun k : ℕ => (Real.log t + 1) * (1 / 2 : ℝ)^k
          + (k : ℝ) * (1 / 2 : ℝ)^k)
        ((Real.log t + 1) * 2 + 2) :=
    (hgeom.mul_left (Real.log t + 1)).add hnat
  have hdiv := hscaled.div_const t
  convert hdiv using 1
  · funext k
    simp only [threeTapDyadicLogMajorant]
    ring
  · field_simp [ht]
    ring

/-- Closed form of the shell series. -/
theorem tsum_threeTapDyadicLogMajorant {t : ℝ} (ht : t ≠ 0) :
    (∑' k : ℕ, threeTapDyadicLogMajorant t k)
      = (2 * Real.log t + 4) / t :=
  (hasSum_threeTapDyadicLogMajorant ht).tsum_eq

end Synthesis

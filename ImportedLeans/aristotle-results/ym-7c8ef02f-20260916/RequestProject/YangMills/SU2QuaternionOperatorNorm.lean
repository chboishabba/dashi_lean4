/-
# The quaternion → SU(2) representation weld, and the `ℓ¹ → operator` defect bound

The small-field lane produces its sharp link estimate in *quaternion*
coordinates: a stored bond is a unit quaternion `q = (a,b,c,d)` and the
estimate is on the `ℓ¹` size of `q - 1`.  Every downstream consumer (principal
chart admission, the relative-holonomy telescope, the logarithm) needs instead
the **operator** defect `‖U - I‖` of the corresponding `2 × 2` `SU(2)` matrix.
That gap is the representation-identification seam.

This module closes it, in Lean, on the nose:

* `su2` — the standard `2 × 2` complex matrix of a quaternion,
  `q = a + bi + cj + dk ↦ [[a+bi, c+di], [-c+di, a-bi]]`;
* `su2_mul`, `su2_one`, `su2_conjTranspose` — it is a `*`-homomorphism, so
  quaternion words and matrix words are literally the same object;
* `su2_norm` — its `L²` operator norm is exactly the quaternion norm
  `√(a²+b²+c²+d²)`;
* `su2_defect_le_l1` — hence the operator defect is bounded by the quaternion
  `ℓ¹` defect, `‖U_q - I‖ ≤ |a-1| + |b| + |c| + |d|`;
* `su2_defect_le_of_l1_le` and `su2_link_defect_le_inv_2048` — the numerical
  form used by the link budget.

The matrix norm here is Mathlib's `L²` operator norm on matrices (scoped
instance `Matrix.Norms.L2Operator`), i.e. the genuine operator norm on
`EuclideanSpace ℂ (Fin 2)`, not an entrywise surrogate.
-/
import Mathlib

namespace RequestProject.YangMills.SU2QuaternionOperatorNorm

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The standard `2 × 2` complex matrix representing a quaternion. -/
noncomputable def su2 (q : Quaternion ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(q.re : ℂ) + q.imI * Complex.I, (q.imJ : ℂ) + q.imK * Complex.I;
     -(q.imJ : ℂ) + q.imK * Complex.I, (q.re : ℂ) - q.imI * Complex.I]

@[simp] theorem su2_one : su2 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su2]

/-- The representation is multiplicative: quaternion words and matrix words are
the same object. -/
theorem su2_mul (q p : Quaternion ℝ) : su2 (q * p) = su2 q * su2 p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] <;>
      refine ⟨by ring, by ring⟩

/-- The representation intertwines quaternion conjugation with the adjoint. -/
theorem su2_conjTranspose (q : Quaternion ℝ) : (su2 q)ᴴ = su2 (star q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2, Matrix.conjTranspose_apply]

theorem su2_conjTranspose_mul_self (q : Quaternion ℝ) :
    (su2 q)ᴴ * (su2 q)
      = ((q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 : ℝ) : ℂ)
          • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Complex.ext_iff] <;> norm_num [← Complex.ofReal_pow] <;> refine ⟨by ring, by ring⟩

/-- **The operator norm of the represented quaternion is the quaternion norm.**
No comparison constant is lost in the representation step. -/
theorem su2_norm (q : Quaternion ℝ) :
    ‖su2 q‖ = Real.sqrt (q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2) := by
  have h := CStarRing.norm_star_mul_self (x := su2 q)
  rw [Matrix.star_eq_conjTranspose, su2_conjTranspose_mul_self, norm_smul] at h
  have hk : (0 : ℝ) ≤ q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 := by positivity
  rw [norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk] at h
  rw [h, Real.sqrt_mul_self (norm_nonneg _)]

/-- A unit quaternion is represented by a norm-one matrix. -/
theorem su2_norm_eq_one {q : Quaternion ℝ}
    (h : q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 = 1) : ‖su2 q‖ = 1 := by
  rw [su2_norm, h, Real.sqrt_one]

theorem su2_sub_one (q : Quaternion ℝ) : su2 q - 1 = su2 (q - 1) := by
  rw [show (1 : Matrix (Fin 2) (Fin 2) ℂ) = su2 1 from su2_one.symm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2, Complex.ext_iff]

/-- **The representation weld.** The operator defect of a represented
quaternion is bounded by the `ℓ¹` defect of its coordinates. -/
theorem su2_defect_le_l1 (q : Quaternion ℝ) :
    ‖su2 q - 1‖ ≤ |q.re - 1| + |q.imI| + |q.imJ| + |q.imK| := by
  rw [su2_sub_one, su2_norm]
  have ht : (0 : ℝ) ≤ |q.re - 1| + |q.imI| + |q.imJ| + |q.imK| := by positivity
  have hcross : (q.re - 1) ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2
      ≤ (|q.re - 1| + |q.imI| + |q.imJ| + |q.imK|) ^ 2 := by
    have h1 := sq_abs (q.re - 1)
    have h2 := sq_abs q.imI
    have h3 := sq_abs q.imJ
    have h4 := sq_abs q.imK
    have p12 := mul_nonneg (abs_nonneg (q.re - 1)) (abs_nonneg q.imI)
    have p13 := mul_nonneg (abs_nonneg (q.re - 1)) (abs_nonneg q.imJ)
    have p14 := mul_nonneg (abs_nonneg (q.re - 1)) (abs_nonneg q.imK)
    have p23 := mul_nonneg (abs_nonneg q.imI) (abs_nonneg q.imJ)
    have p24 := mul_nonneg (abs_nonneg q.imI) (abs_nonneg q.imK)
    have p34 := mul_nonneg (abs_nonneg q.imJ) (abs_nonneg q.imK)
    nlinarith
  calc Real.sqrt ((q - 1).re ^ 2 + (q - 1).imI ^ 2 + (q - 1).imJ ^ 2 + (q - 1).imK ^ 2)
      = Real.sqrt ((q.re - 1) ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2) := by
        simp
    _ ≤ Real.sqrt ((|q.re - 1| + |q.imI| + |q.imJ| + |q.imK|) ^ 2) :=
        Real.sqrt_le_sqrt hcross
    _ = |q.re - 1| + |q.imI| + |q.imJ| + |q.imK| := Real.sqrt_sq ht

/-- Quantitative form: an `ℓ¹` quaternion defect budget is an operator defect
budget with the same constant. -/
theorem su2_defect_le_of_l1_le {q : Quaternion ℝ} {ε : ℝ}
    (h : |q.re - 1| + |q.imI| + |q.imJ| + |q.imK| ≤ ε) : ‖su2 q - 1‖ ≤ ε :=
  (su2_defect_le_l1 q).trans h

/-- The link budget in the form the relative-holonomy telescope consumes. -/
theorem su2_link_defect_le_inv_2048 {q : Quaternion ℝ}
    (h : |q.re - 1| + |q.imI| + |q.imJ| + |q.imK| ≤ 1 / 2048) :
    ‖su2 q - 1‖ ≤ 1 / 2048 :=
  su2_defect_le_of_l1_le h

end RequestProject.YangMills.SU2QuaternionOperatorNorm

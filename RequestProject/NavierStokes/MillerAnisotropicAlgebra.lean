import Mathlib

/-!
# Miller 2021: finite algebraic strain/vorticity precursor

Source: Evan Miller, "A Locally Anisotropic Regularity Criterion for the
Navier–Stokes Equation in Terms of Vorticity",
Proc. AMS Series B 8 (2021), 60–74, DOI: 10.1090/bproc/74.
Relevant source: Eqs. (2.4)–(2.10), Theorem 1.6 / Theorem 2.1.

These theorems are DASHI *reconstructions of elementary algebra* occurring
inside the published proof. They are not a formal proof of integration by parts
on R³, the L⁴_t L²_x bound, a real PDE solution, or the source continuation
theorem. All such analytic inputs remain explicit in Agda's
NSMillerAnisotropicA3BridgeExact and in its canonical same-solution transfer.

The arrays a and b can later be instantiated as (∇u)v and (∇u)ᵀv,
with S v = (a+b)/2 and A v = (a-b)/2. That identification is not inferred
from an arbitrary pair of coordinate arrays.
-/

namespace RequestProject.NavierStokes.MillerAnisotropic

/-- Algebraic strain/antisymmetric square difference in one real component. -/
theorem symmetric_antisymmetric_component (a b : ℝ) :
    ((a + b) / 2)^2 = ((a - b) / 2)^2 + a * b := by
  ring

/-- Exact three-coordinate instance; avoids a symbolic continuum integral. -/
theorem symmetric_antisymmetric_three_components
    (a b : Fin 3 → ℝ) :
    (∑ i : Fin 3, ((a i + b i) / 2)^2) =
      (∑ i : Fin 3, ((a i - b i) / 2)^2) +
        (∑ i : Fin 3, a i * b i) := by
  calc
    (∑ i : Fin 3, ((a i + b i) / 2)^2) =
        ∑ i : Fin 3, (((a i - b i) / 2)^2 + a i * b i) := by
          apply Finset.sum_congr rfl
          intro i _
          exact symmetric_antisymmetric_component (a i) (b i)
    _ = (∑ i : Fin 3, ((a i - b i) / 2)^2) +
        (∑ i : Fin 3, a i * b i) := by
          rw [Finset.sum_add_distrib]

/-- The elementary quadratic splitting used before Miller's time estimate. -/
theorem square_of_sum_le_twice_squares (a b : ℝ) :
    (a + b)^2 ≤ 2 * a^2 + 2 * b^2 := by
  nlinarith [sq_nonneg (a - b)]

/-- Scaling bookkeeping only: vorticity L² has weight 2 - 3/2, and
an L⁴ time norm cancels the parabolic dt weight 2. This is NOT a
physical norm estimate or a proof that the direction gradient is bounded. -/
theorem projected_vorticity_L4L2_critical_arithmetic :
    (4 : ℚ) * (2 - 3 / 2) - 2 = 0 := by
  norm_num

end RequestProject.NavierStokes.MillerAnisotropic

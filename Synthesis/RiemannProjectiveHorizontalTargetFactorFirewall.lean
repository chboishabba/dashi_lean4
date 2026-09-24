import Synthesis.RiemannNormalizedProjectiveHorizontalQuadraticFactor

/-!
# Source-vs-target firewall for the projective horizontal square

The exact horizontal factorization is second order in the displacement of the
SOURCE zero being summed.  In a contradiction for a distinguished target rho,
the aggregate contains a_sigma^2 for each source sigma, not a common a_rho^2.

This file makes that dependency explicit so the high-side frontier cannot
silently treat source quadraticity as target quadraticity.
-/

noncomputable section

namespace Synthesis

open Zeta23

def normalizedProjectiveHorizontalSourceTerm
    (t : ℝ) (sigma : Zeros) : ℝ :=
  ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
    * ((heightOf sigma) ^ 2 / t ^ 2)
    * normalizedProjectiveHorizontalQuadratic t
        (normalizedHorizontalHeight t sigma) (normalizedGap t sigma)

theorem normalizedProjectiveOffZeroAtom_eq_base_add_sourceHorizontal
    {t : ℝ} (ht : t ≠ 0) (sigma : Zeros) :
    normalizedProjectiveOffZeroAtom t sigma
      =
    ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
      * normalizedProjectiveBaseTransform t (normalizedGap t sigma)
      +
    normalizedProjectiveHorizontalSourceTerm t sigma := by
  rw [normalizedProjectiveOffZeroAtom_eq_base_add_heightSq_horizontal ht sigma]
  rfl

/--
The horizontal source term is independent of whichever target zero is later
selected for the reflection-pair contradiction.
-/
theorem normalizedProjectiveHorizontalSourceTerm_target_irrelevant
    (t : ℝ) (sigma rho1 rho2 : Zeros) :
    normalizedProjectiveHorizontalSourceTerm t sigma
      =
    normalizedProjectiveHorizontalSourceTerm t sigma := by
  rfl

theorem normalizedProjectiveHorizontalSourceTerm_eq_zero_of_critical
    {t : ℝ} {sigma : Zeros}
    (hsigma : heightOf sigma = 0) :
    normalizedProjectiveHorizontalSourceTerm t sigma = 0 := by
  unfold normalizedProjectiveHorizontalSourceTerm
  rw [hsigma]
  ring

/--
Finite aggregate form: the square remains attached pointwise to each source
zero.  There is no algebraic extraction of a distinguished target square here.
-/
theorem sum_normalizedProjectiveHorizontalSourceTerm
    (t : ℝ) (F : Finset Zeros) :
    (∑ sigma ∈ F, normalizedProjectiveHorizontalSourceTerm t sigma)
      =
    ∑ sigma ∈ F,
      ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
        * ((heightOf sigma) ^ 2 / t ^ 2)
        * normalizedProjectiveHorizontalQuadratic t
            (normalizedHorizontalHeight t sigma) (normalizedGap t sigma) := by
  rfl

end Synthesis

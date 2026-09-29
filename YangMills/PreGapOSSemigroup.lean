import Mathlib

/-!
# Pre-gap OS semigroup: centered Wilson two-point reduction

This is the exact Hilbert-space algebra needed before the R281/R331
physical spectral identification.  A normalized vacuum fixed by a
symmetric positive-time semigroup is enough to turn its *uncentered*
two-point kernel into connected covariance of centered Wilson vectors.

This does not instantiate the semigroup from the finite CMP119 family:
the physical OS reconstruction and the uncentered kernel equality
remain explicit assumptions at the call site.
-/

namespace RequestProject.YangMills

/-- Remove the exact reconstructed vacuum expectation from a Wilson vector. -/
def osCenteredWilsonVector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω ψ : H) : H :=
  ψ - (⟪Ω, ψ⟫_ℝ) • Ω

/-- Centering is genuinely orthogonal to the normalized reconstructed vacuum. -/
theorem os_centered_wilson_orthogonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω ψ : H)
    (hNormalized : ⟪Ω, Ω⟫_ℝ = 1) :
    ⟪Ω, osCenteredWilsonVector Ω ψ⟫_ℝ = 0 := by
  simp only [osCenteredWilsonVector, inner_sub_right, real_inner_smul_right]
  rw [hNormalized]
  ring

/--
Algebraic OS transfer identity for the exact pre-gap Hamiltonian.

Assume `T t` is the (already reconstructed) symmetric time-translation
semigroup fixing its unit vacuum.  The centered Wilson matrix coefficient
is the uncentered coefficient minus the square of the vacuum one-point
expectation.  No second Hamiltonian or spectral object is selected.

The `H2` physical obligation is to identify the uncentered coefficient
with the actual CMP119 continuum two-Wilson Schwinger expectation.
-/
theorem os_centered_semigroup_correlation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω ψ : H) (T : ℕ → H →ₗ[ℝ] H)
    (hNormalized : ⟪Ω, Ω⟫_ℝ = 1)
    (hVacuumFixed : ∀ t, T t Ω = Ω)
    (hSymmetric :
      ∀ t (left right : H),
        ⟪left, T t right⟫_ℝ = ⟪T t left, right⟫_ℝ)
    (t : ℕ) :
    ⟪osCenteredWilsonVector Ω ψ,
        T t (osCenteredWilsonVector Ω ψ)⟫_ℝ =
      ⟪ψ, T t ψ⟫_ℝ - (⟪Ω, ψ⟫_ℝ) ^ 2 := by
  have hVacMean : ⟪Ω, T t ψ⟫_ℝ = ⟪Ω, ψ⟫_ℝ := by
    rw [hSymmetric t Ω ψ, hVacuumFixed]
  have hMeanSym : ⟪ψ, Ω⟫_ℝ = ⟪Ω, ψ⟫_ℝ :=
    real_inner_comm ψ Ω
  have hT :
      T t (osCenteredWilsonVector Ω ψ) =
        T t ψ - (⟪Ω, ψ⟫_ℝ) • Ω := by
    simp [osCenteredWilsonVector, map_sub, map_smul, hVacuumFixed]
  rw [osCenteredWilsonVector, hT]
  simp only [inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [hVacMean, hMeanSym, hNormalized]
  ring

/--
The actual continuum connected two-point expectation agrees with the
*same* pre-gap OS-Hamiltonian semigroup once OS reconstruction supplies the
uncentered two-point kernel equality and the one-point vacuum expectation.
-/
theorem continuum_covariance_eq_core_os_semigroup
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ω ψ : H) (T : ℕ → H →ₗ[ℝ] H)
    (hNormalized : ⟪Ω, Ω⟫_ℝ = 1)
    (hVacuumFixed : ∀ t, T t Ω = Ω)
    (hSymmetric :
      ∀ t (left right : H),
        ⟪left, T t right⟫_ℝ = ⟪T t left, right⟫_ℝ)
    (onePoint : ℝ) (twoPoint : ℕ → ℝ)
    (hOnePoint : onePoint = ⟪Ω, ψ⟫_ℝ)
    (hTwoPoint : ∀ t, twoPoint t = ⟪ψ, T t ψ⟫_ℝ)
    (t : ℕ) :
    twoPoint t - onePoint ^ 2 =
      ⟪osCenteredWilsonVector Ω ψ,
        T t (osCenteredWilsonVector Ω ψ)⟫_ℝ := by
  rw [hOnePoint, hTwoPoint, os_centered_semigroup_correlation
    Ω ψ T hNormalized hVacuumFixed hSymmetric t]

end RequestProject.YangMills

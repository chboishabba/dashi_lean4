import Mathlib
import YangMills.ContinuumWilsonCovariance

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

/--
The Cauchy--Schwarz estimate actually required by the OS4 extension.  It
only uses contractivity of the SAME reconstructed OS transfer operator.
Thus the time-uniform correlation modulus is a consequence of physical
OS-semigroup reconstruction, not an independent continuum RG estimate.
-/
theorem os_semigroup_correlation_error_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H)
    (hContract : ‖T‖ ≤ 1)
    (left left' right right' : H) :
    |⟪left, T right⟫_ℝ - ⟪left', T right'⟫_ℝ| ≤
      ‖left - left'‖ * ‖right‖ +
        ‖left'‖ * ‖right - right'‖ := by
  have hDifference :
      ⟪left, T right⟫_ℝ - ⟪left', T right'⟫_ℝ =
      ⟪left - left', T right⟫_ℝ +
        ⟪left', T (right - right')⟫_ℝ := by
    simp only [inner_sub_left, map_sub, inner_sub_right]
    ring
  have hNormT (v : H) : ‖T v‖ ≤ ‖v‖ := by
    calc
      ‖T v‖ ≤ ‖T‖ * ‖v‖ := T.le_opNorm v
      _ ≤ 1 * ‖v‖ :=
        mul_le_mul_of_nonneg_right hContract (norm_nonneg v)
      _ = ‖v‖ := one_mul _
  rw [hDifference]
  calc
    |⟪left - left', T right⟫_ℝ +
        ⟪left', T (right - right')⟫_ℝ|
      ≤ |⟪left - left', T right⟫_ℝ| +
          |⟪left', T (right - right')⟫_ℝ| :=
        abs_add_le _ _
    _ ≤ ‖left - left'‖ * ‖T right‖ +
          ‖left'‖ * ‖T (right - right')‖ :=
        add_le_add
          (abs_real_inner_le_norm _ _)
          (abs_real_inner_le_norm _ _)
    _ ≤ ‖left - left'‖ * ‖right‖ +
          ‖left'‖ * ‖right - right'‖ :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hNormT right)
            (norm_nonneg _))
          (mul_le_mul_of_nonneg_left
            (hNormT (right - right')) (norm_nonneg _))

/--
The OS transfer-semigroup contraction bound implies **pair-local**,
time-uniform continuity in the Hilbert norm.  Global equicontinuity of
bilinear matrix coefficients on an unbounded Hilbert space is not needed.
-/
theorem os_semigroup_locally_uniform_in_time
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : ℕ → H →L[ℝ] H)
    (hContract : ∀ t, ‖T t‖ ≤ 1)
    (left right : H) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (t : ℕ) (left' right' : H),
        dist left left' < δ →
        dist right right' < δ →
        |⟪left, T t right⟫_ℝ - ⟪left', T t right'⟫_ℝ| < ε := by
  let A : ℝ := ‖left‖ + ‖right‖ + 2
  have hA : 0 < A := by
    dsimp [A]
    positivity
  let δ : ℝ := min 1 (ε / (2 * A))
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (div_pos hε (by positivity))
  have hδone : δ ≤ 1 := min_le_left _ _
  have hδfrac : δ ≤ ε / (2 * A) := min_le_right _ _
  refine ⟨δ, hδpos, ?_⟩
  intro t left' right' hleft hright
  rw [dist_eq_norm] at hleft hright
  have hleftNorm : ‖left'‖ ≤ ‖left‖ + ‖left - left'‖ := by
    have hEq : left' = left - (left - left') := by abel
    calc
      ‖left'‖ = ‖left - (left - left')‖ := congrArg norm hEq
      _ ≤ ‖left‖ + ‖left - left'‖ := norm_sub_le _ _
  have hleftBound : ‖left'‖ ≤ ‖left‖ + 1 := by
    linarith
  have hError :=
    os_semigroup_correlation_error_le
      (T t) (hContract t) left left' right right'
  have hErrorBound :
      |⟪left, T t right⟫_ℝ - ⟪left', T t right'⟫_ℝ| ≤
        δ * ‖right‖ + (‖left‖ + 1) * δ := by
    calc
      _ ≤ ‖left - left'‖ * ‖right‖ +
            ‖left'‖ * ‖right - right'‖ := hError
      _ ≤ δ * ‖right‖ + (‖left‖ + 1) * δ := by
        gcongr
        exact le_of_lt hleft
        exact hleftBound
        exact le_of_lt hright
  have hProduct :
      δ * A ≤ ε / 2 := by
    calc
      δ * A ≤ (ε / (2 * A)) * A :=
        mul_le_mul_of_nonneg_right hδfrac hA.le
      _ = ε / 2 := by
        have hA0 : A ≠ 0 := ne_of_gt hA
        field_simp
  have hLess : δ * ‖right‖ + (‖left‖ + 1) * δ ≤ δ * A := by
    dsimp [A]
    ring
  linarith

/--
OS-Hilbert-norm Wilson density plus **actual** contracting pre-gap transfer
semigroup and clustering on the dense Wilson vectors implies clustering on
every vector of the reconstructed Hilbert sector.

The missing physics is producing the OS Hilbert completion, proving that
the actual Wilson vectors are dense in the required vacuum-orthogonal sector,
and identifying their Schwinger correlations with this SAME transfer
semigroup.  No uniform sup-norm approximation of unbounded local fields
appears in this theorem.
-/
theorem os_semigroup_clustering_of_dense_wilson_vectors
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : ℕ → H →L[ℝ] H)
    (hContract : ∀ t, ‖T t‖ ≤ 1)
    (wilsonVectors : Set H)
    (hDense : Dense wilsonVectors)
    (hWilson :
      ∀ left ∈ wilsonVectors, ∀ right ∈ wilsonVectors,
        Tendsto
          (fun t : ℕ => ⟪left, T t right⟫_ℝ)
          atTop (𝓝 0)) :
    ∀ left right : H,
      Tendsto
        (fun t : ℕ => ⟪left, T t right⟫_ℝ)
        atTop (𝓝 0) := by
  apply full_test_clustering_of_locally_uniform_dense_wilson_clustering
    wilsonVectors (fun t left right => ⟪left, T t right⟫_ℝ)
  · intro test δ hδ
    exact hDense.exists_dist_lt test hδ
  · intro left right ε hε
    exact os_semigroup_locally_uniform_in_time
      T hContract left right ε hε
  · exact hWilson

end RequestProject.YangMills

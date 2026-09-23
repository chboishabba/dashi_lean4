/-
# The literal Wilson transfer operator, and `F1` as a transfer-matrix estimate

`Lattice/UniformGapReduction.lean` reduced the finite side of the mass-gap
problem to the two-slice decorrelation inequality

    ‖⟪P₀ψ, P₁ψ⟫‖ ≤ c ‖ψ‖²     for every ψ ⊥ Ω,

for the two literal slice isometries `P₀ = embed0`, `P₁ = embed1` of
`Lattice/TransferForm.lean`.  That inequality was stated there in terms of the
two embeddings.  This file identifies it with the classical transfer-matrix
statement and sharpens the trajectory bookkeeping.

* `transferOp` — the **literal Euclidean transfer operator** of the Wilson–Gibbs
  measure, `T = P₁* P₀ : L²(μ_slice) → L²(μ_slice)`, defined as an honest
  Hilbert-space adjoint composition, not as a new abstraction.  Its defining
  identity `⟪Tφ, ψ⟫ = ⟪P₀φ, P₁ψ⟫` is `inner_transferOp_left`; `T` has norm at
  most one and fixes the vacuum, and the literal energy form is exactly
  `q(ψ,ψ) = ‖ψ‖² − Re⟪Tψ, ψ⟫` (`energyForm_re_eq_transferOp`).
* `decorrelation_of_transferOp_norm_le` — the decorrelation hypothesis follows
  from the textbook statement "the transfer operator has norm at most `c` on the
  vacuum complement".  So `F1` may be paid in the standard transfer-matrix form.
* `decorrelation_iff_phase_separated` — the same hypothesis is *equivalent* to a
  purely geometric separation statement about the two literal slice embeddings:
  the time-zero and time-one embeddings of a vacuum-orthogonal wavefunction stay
  at squared distance at least `2(1−c)‖ψ‖²` from each other, after any phase.
* `ym_uniform_gap_of_trajectory_decorrelation` — **the sharpened form of the
  `F1` payment**: the decorrelation constant need *not* be uniform along the
  trajectory.  What the weld consumes is the per-step spectral defect
  `1 − c_k ≥ Δ a_k`, which *degrades* as the spacing goes to zero.  A uniform
  `c < 1` is the special case `ym_trajectory_defect_of_uniform_constant`, and it
  is strictly stronger than necessary once `a_k → 0`.
* `ym_continuum_massGap_of_transfer_defect` — the composite: per-step transfer
  operator norm bounds `‖T_k ψ‖ ≤ c_k ‖ψ‖` on the vacuum complement with
  `Δ a_k ≤ 1 − c_k`, plus the continuum-limit data, give the continuum mass-gap
  conclusion.

Nothing here proves `F1`: the per-step estimate is an input in every statement.
What changes is its shape — it is now the standard transfer-matrix spectral
estimate with an explicit, spacing-dependent tolerance.
-/
import Mathlib
import RequestProject.YangMills.Lattice.UniformGapReduction

namespace RequestProject.YangMills.Lattice

open MeasureTheory
open scoped InnerProductSpace
open RequestProject.YangMills.VacuumSectorSpectralGap
open RequestProject.YangMills.VaryingCarrierTransport

/-! ## An optimal phase for a complex number -/

/-- For every complex number there is a unit phase rotating it onto its modulus. -/
theorem exists_unit_phase (w : ℂ) : ∃ z : ℂ, ‖z‖ = 1 ∧ (z * w).re = ‖w‖ := by
  rcases eq_or_ne w 0 with rfl | hw
  · exact ⟨1, by simp, by simp⟩
  · refine ⟨(starRingEnd ℂ) w / (‖w‖ : ℂ), ?_, ?_⟩
    · rw [norm_div, RCLike.norm_conj]
      simp [norm_ne_zero_iff.2 hw]
    · have hne : (‖w‖ : ℂ) ≠ 0 := by
        exact_mod_cast (norm_ne_zero_iff.2 hw)
      have h : (starRingEnd ℂ) w * w = ((‖w‖ : ℂ)) ^ 2 := by
        rw [mul_comm, Complex.mul_conj]
        norm_cast
        simp [Complex.normSq_eq_norm_sq]
      rw [div_mul_eq_mul_div, h, sq, mul_div_assoc, div_self hne, mul_one]
      simp

/-- Expansion of the squared distance between two vectors after a unit phase. -/
theorem norm_sub_phase_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u v : E) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖u - z • v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * (z * ⟪u, v⟫_ℂ).re := by
  have hexp := norm_sub_sq (𝕜 := ℂ) u (z • v)
  rw [inner_smul_right, norm_smul, hz, one_mul] at hexp
  simp only [RCLike.re_to_complex] at hexp
  rw [hexp]; ring

section Transfer

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] {n : ℕ} {chi : G → ℝ}

/-- **The literal Euclidean transfer operator of the Wilson–Gibbs measure**,
`T = P₁* P₀`, where `P₀, P₁` are the time-zero and time-one slice isometries.
No new object is introduced: `T` is the adjoint composition of the two literal
embeddings. -/
noncomputable def transferOp (hchi : Continuous chi) (beta : ℝ) :
    SliceL2 n G beta chi →L[ℂ] SliceL2 n G beta chi :=
  (ContinuousLinearMap.adjoint (embed1 hchi beta).toContinuousLinearMap).comp
    (embed0 n G beta chi).toContinuousLinearMap

/-- The defining identity of the transfer operator: `⟪Tφ, ψ⟫ = ⟪P₀φ, P₁ψ⟫`. -/
theorem inner_transferOp_left (hchi : Continuous chi) (beta : ℝ)
    (φ ψ : SliceL2 n G beta chi) :
    ⟪transferOp hchi beta φ, ψ⟫_ℂ
      = ⟪embed0 n G beta chi φ, embed1 hchi beta ψ⟫_ℂ := by
  simpa [transferOp] using ContinuousLinearMap.adjoint_inner_left
    (embed1 hchi beta).toContinuousLinearMap ψ (embed0 n G beta chi φ)

/-- The transfer operator is a contraction. -/
theorem norm_transferOp_apply_le (hchi : Continuous chi) (beta : ℝ)
    (φ : SliceL2 n G beta chi) : ‖transferOp hchi beta φ‖ ≤ ‖φ‖ := by
  have hself : (⟪transferOp hchi beta φ, transferOp hchi beta φ⟫_ℂ).re
      = ‖transferOp hchi beta φ‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (transferOp hchi beta φ)
  have hid := inner_transferOp_left hchi beta φ (transferOp hchi beta φ)
  have hbound : (⟪transferOp hchi beta φ, transferOp hchi beta φ⟫_ℂ).re
      ≤ ‖φ‖ * ‖transferOp hchi beta φ‖ := by
    rw [hid]
    calc (⟪embed0 n G beta chi φ, embed1 hchi beta (transferOp hchi beta φ)⟫_ℂ).re
        ≤ ‖⟪embed0 n G beta chi φ, embed1 hchi beta (transferOp hchi beta φ)⟫_ℂ‖ :=
          Complex.re_le_norm _
      _ ≤ ‖embed0 n G beta chi φ‖ * ‖embed1 hchi beta (transferOp hchi beta φ)‖ :=
          norm_inner_le_norm _ _
      _ = ‖φ‖ * ‖transferOp hchi beta φ‖ := by
          rw [(embed0 n G beta chi).norm_map, (embed1 hchi beta).norm_map]
  rw [hself] at hbound
  nlinarith [norm_nonneg (transferOp hchi beta φ), norm_nonneg φ]

/-- The transfer operator fixes the vacuum: `T Ω = Ω`. -/
theorem transferOp_vacuum (hchi : Continuous chi) (beta : ℝ) :
    transferOp hchi beta (vacuum hchi beta (n := n)) = vacuum hchi beta := by
  refine ext_inner_left ℂ ?_
  intro ψ
  have h := inner_transferOp_left hchi beta (vacuum hchi beta (n := n)) ψ
  have h2 : ⟪embed0 n G beta chi (vacuum hchi beta), embed1 hchi beta ψ⟫_ℂ
      = ⟪vacuum hchi beta (n := n), ψ⟫_ℂ := by
    rw [embed_vacuum hchi beta]
    exact (embed1 hchi beta).inner_map_map _ _
  have hconj := congrArg (starRingEnd ℂ) (h.trans h2)
  simpa [inner_conj_symm] using hconj

/-- The literal energy form in transfer-operator form:
`q(ψ,ψ) = ‖ψ‖² − Re⟪Tψ, ψ⟫`. -/
theorem energyForm_re_eq_transferOp (hchi : Continuous chi) (beta : ℝ)
    (ψ : SliceL2 n G beta chi) :
    ((energyForm hchi beta).form ψ ψ).re
      = ‖ψ‖ ^ 2 - (⟪transferOp hchi beta ψ, ψ⟫_ℂ).re := by
  have hre : (⟪ψ, ψ⟫_ℂ).re = ‖ψ‖ ^ 2 := by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ψ
  have hT : ⟪transferOp hchi beta ψ, ψ⟫_ℂ
      = ⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ := inner_transferOp_left hchi beta ψ ψ
  have hBA : ⟪embed1 hchi beta ψ, embed0 n G beta chi ψ⟫_ℂ
      = (starRingEnd ℂ) ⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ :=
    (inner_conj_symm _ _).symm
  rw [energyForm_apply, hBA, hT]
  have hhalf : (1 / 2 : ℂ) * (⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ
      + (starRingEnd ℂ) ⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ)
      = ((⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ).re : ℂ) := by
    rw [Complex.add_conj]; push_cast; ring
  rw [hhalf, Complex.sub_re, Complex.ofReal_re, hre]

/-- **The decorrelation hypothesis from a transfer-operator norm bound.**  This
is the classical form of the finite-volume mass gap: the Euclidean transfer
operator of the Wilson measure is a strict contraction on the vacuum
complement. -/
theorem decorrelation_of_transferOp_norm_le (hchi : Continuous chi) (beta : ℝ) {c : ℝ}
    (ψ : SliceL2 n G beta chi) (hT : ‖transferOp hchi beta ψ‖ ≤ c * ‖ψ‖) :
    ‖⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ‖ ≤ c * ‖ψ‖ ^ 2 := by
  rw [← inner_transferOp_left hchi beta ψ ψ]
  calc ‖⟪transferOp hchi beta ψ, ψ⟫_ℂ‖ ≤ ‖transferOp hchi beta ψ‖ * ‖ψ‖ :=
        norm_inner_le_norm _ _
    _ ≤ (c * ‖ψ‖) * ‖ψ‖ := by
        exact mul_le_mul_of_nonneg_right hT (norm_nonneg _)
    _ = c * ‖ψ‖ ^ 2 := by ring

/-- **Decorrelation is a geometric separation statement about the two literal
slice embeddings.**  The bound `‖⟪P₀ψ, P₁ψ⟫‖ ≤ c‖ψ‖²` holds if and only if the
time-zero and time-one embeddings of `ψ` stay, after an arbitrary phase, at
squared distance at least `2(1−c)‖ψ‖²`. -/
theorem decorrelation_iff_phase_separated (hchi : Continuous chi) (beta : ℝ) {c : ℝ}
    (ψ : SliceL2 n G beta chi) :
    ‖⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ‖ ≤ c * ‖ψ‖ ^ 2 ↔
      ∀ z : ℂ, ‖z‖ = 1 →
        2 * (1 - c) * ‖ψ‖ ^ 2
          ≤ ‖embed0 n G beta chi ψ - z • embed1 hchi beta ψ‖ ^ 2 := by
  have h0 : ‖embed0 n G beta chi ψ‖ = ‖ψ‖ := (embed0 n G beta chi).norm_map ψ
  have h1 : ‖embed1 hchi beta ψ‖ = ‖ψ‖ := (embed1 hchi beta).norm_map ψ
  constructor
  · intro hdec z hz
    have hexp := norm_sub_phase_sq (embed0 n G beta chi ψ) (embed1 hchi beta ψ) hz
    have hle : (z * ⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ).re ≤ c * ‖ψ‖ ^ 2 := by
      calc (z * ⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ).re
          ≤ ‖z * ⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ‖ := Complex.re_le_norm _
        _ = ‖⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ‖ := by rw [norm_mul, hz, one_mul]
        _ ≤ c * ‖ψ‖ ^ 2 := hdec
    rw [hexp, h0, h1]
    nlinarith
  · intro hsep
    obtain ⟨z, hz, hzval⟩ := exists_unit_phase ⟪embed0 n G beta chi ψ, embed1 hchi beta ψ⟫_ℂ
    have hexp := norm_sub_phase_sq (embed0 n G beta chi ψ) (embed1 hchi beta ψ) hz
    have := hsep z hz
    rw [hexp, h0, h1, hzval] at this
    nlinarith

end Transfer

/-! ## The sharpened `F1` payment along the physical trajectory -/

section Trajectory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **`F1` with a step-dependent decorrelation constant.**  The constant in the
two-slice estimate does *not* have to be uniform along the trajectory: all the
continuum weld consumes is that the *spectral defect* `1 − c_k` of the transfer
operator dominate `Δ a_k`.  Since `a_k → 0` along the physical trajectory, this
allows `c_k → 1`, which a uniform bound does not exploit. -/
theorem ym_uniform_gap_of_trajectory_decorrelation (vol : ℕ → ℕ) (beta a : ℕ → ℝ)
    (ha : ∀ k, 0 ≤ a k) {c : ℕ → ℝ} {Δ : ℝ}
    (hdec : ∀ k, ∀ ψ : ymPhysicalSlice (vol k) (beta k),
      ⟪ymPhysicalVacuum (vol k) (beta k), ψ⟫_ℂ = 0 →
        ‖⟪embed0 (vol k) SU2 (beta k) chiSU2 (ψ : SliceL2 (vol k) SU2 (beta k) chiSU2),
          embed1 continuous_chiSU2 (beta k)
            (ψ : SliceL2 (vol k) SU2 (beta k) chiSU2)⟫_ℂ‖ ≤ c k * ‖ψ‖ ^ 2)
    (hΔ : ∀ k, Δ ≤ (a k)⁻¹ * (1 - c k)) :
    ∀ k, HasVacuumFormGap (ymTrajectoryHam vol beta a ha k)
      (ymTrajectoryVacuum vol beta k) Δ := fun k =>
  phys_hasVacuumFormGap_of_decorrelation (G := SU2) continuous_chiSU2 chiSU2_conj
    (beta k) (a k) (ha k) (hdec k) (hΔ k)

/-- The gap tolerance in the sharpened payment, written as a *spectral defect*
condition: `Δ a_k ≤ 1 − c_k`. -/
theorem trajectory_gap_bound_of_defect {a : ℕ → ℝ} {c : ℕ → ℝ} {Δ : ℝ}
    (hapos : ∀ k, 0 < a k) (hdefect : ∀ k, Δ * a k ≤ 1 - c k) :
    ∀ k, Δ ≤ (a k)⁻¹ * (1 - c k) := by
  intro k
  have h := hdefect k
  rw [le_inv_mul_iff₀ (hapos k)]
  nlinarith

/-- A uniform decorrelation constant `c < 1` is the special case of the defect
condition in which the tolerance is not used: it forces `Δ a_k ≤ 1 − c` only
through the spacing bound `a_k ≤ (1−c)/Δ`, which is automatic once `a_k → 0`. -/
theorem ym_trajectory_defect_of_uniform_constant {a : ℕ → ℝ} {c Δ : ℝ} (hΔ : 0 < Δ)
    (hspace : ∀ k, a k ≤ (1 - c) / Δ) : ∀ k, Δ * a k ≤ 1 - c := by
  intro k
  have := mul_le_mul_of_nonneg_left (hspace k) hΔ.le
  rwa [mul_div_cancel₀ _ (ne_of_gt hΔ)] at this

/-- **The composite endpoint on the sharpened finite-side payment.**  Per-step
transfer-operator contractivity on the vacuum complement of the literal Wilson
theory, with spectral defect at least `Δ a_k`, plus the embeddings and the
embedded vacuum-sector graph limit, give the full continuum mass-gap conclusion
for the limit Hamiltonian. -/
theorem ym_continuum_massGap_of_transfer_defect
    (vol : ℕ → ℕ) (beta a : ℕ → ℝ) (hapos : ∀ k, 0 < a k)
    (J : ∀ k, ymPhysicalSlice (vol k) (beta k) →ₗᵢ[ℂ] E)
    {Hinf : E →ₗ.[ℂ] E} {vac : E} {c : ℕ → ℝ} {Δ : ℝ} (hΔpos : 0 < Δ)
    (hT : ∀ k, ∀ ψ : ymPhysicalSlice (vol k) (beta k),
      ⟪ymPhysicalVacuum (vol k) (beta k), ψ⟫_ℂ = 0 →
        ‖transferOp continuous_chiSU2 (beta k)
            (ψ : SliceL2 (vol k) SU2 (beta k) chiSU2)‖ ≤ c k * ‖ψ‖)
    (hdefect : ∀ k, Δ * a k ≤ 1 - c k)
    (hlim : IsEmbeddedVacuumGraphLimit J
      (ymTrajectoryHam vol beta a (fun k => (hapos k).le))
      (ymTrajectoryVacuum vol beta) Hinf vac)
    (hsa : IsSelfAdjoint Hinf) (hmem : vac ∈ Hinf.domain) (hunit : ‖vac‖ = 1)
    (hground : Hinf ⟨vac, hmem⟩ = 0) :
    Clay.MassGapConclusion Hinf vac Δ :=
  ym_continuum_massGap_of_uniform_gap_and_graphLimit vol beta a (fun k => (hapos k).le)
    J hΔpos
    (ym_uniform_gap_of_trajectory_decorrelation vol beta a (fun k => (hapos k).le)
      (fun k ψ hψ =>
        decorrelation_of_transferOp_norm_le continuous_chiSU2 (beta k)
          (ψ : SliceL2 (vol k) SU2 (beta k) chiSU2) (hT k ψ hψ))
      (trajectory_gap_bound_of_defect hapos hdefect))
    hlim hsa hmem hunit hground

end Trajectory

end RequestProject.YangMills.Lattice

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Lattice

#print axioms transferOp
#print axioms inner_transferOp_left
#print axioms norm_transferOp_apply_le
#print axioms transferOp_vacuum
#print axioms energyForm_re_eq_transferOp
#print axioms decorrelation_of_transferOp_norm_le
#print axioms decorrelation_iff_phase_separated
#print axioms ym_uniform_gap_of_trajectory_decorrelation
#print axioms trajectory_gap_bound_of_defect
#print axioms ym_continuum_massGap_of_transfer_defect

end Audit

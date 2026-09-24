/-
# Absorbing the nonlinear and pressure pairing

The similarity energy identity of `SimilarityEnergy.lean`,

  `ℋ′(τ) = −‖V_τ‖² − ⟪N, V_τ⟫`,          (S)

leaves exactly one enemy: the pairing of the nonlinear and pressure terms with
the scale velocity.  The naive route bounds it by `‖N‖·‖V_τ‖` and then
estimates each factor in the worst case.  This file records the two structural
moves that avoid that, both of them exact algebra:

* `ClayNS.pairing_young_absorption` — the cross term is *quadratic*: for every
  `η > 0`, `|⟪N,W⟫| ≤ η‖W‖² + ‖N‖²/(4η)`.  So the absorption hypothesis of the
  telescope is implied by a finite total weighted mass of `N`, and nothing
  stronger.
* `ClayNS.marginal_transverse_absorption` — **subtract the marginal channel
  before taking absolute values.**  With `P` the orthogonal projection onto the
  marginal (scaling/gauge) directions, the pairing splits *exactly* as
  `⟪N,W⟫ = ⟪N, PW⟫ + ⟪N_⊥, W_⊥⟫`, and only the transverse part is estimated:
  `|⟪N,W⟫| ≤ |⟪N,PW⟫| + η‖W_⊥‖² + ‖N_⊥‖²/(4η)`.
  The marginal term is computed, not bounded — it is the term that carries no
  coercivity and would destroy any absolute estimate.
* `ClayNS.similarity_energy_deriv_le` and
  `ClayNS.similarity_energy_deriv_le_transverse` — (S) combined with each of
  the two, in exactly the shape
  `ClayNS.similarity_transverse_expenditure` consumes.

The consequence for the ledger: the absorption input of the A side is now a
statement about the *size of the remainder*, `∫‖N_⊥‖²_ρ dτ < ∞` together with
the marginal channel, rather than an unspecified estimate.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.SimilarityEnergy

open RealInnerProductSpace

noncomputable section

namespace ClayNS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Quadratic (Young) absorption -/

/-- **The cross term is paid quadratically.**  For every `η > 0`,
`|⟪N,W⟫| ≤ η‖W‖² + ‖N‖²/(4η)`.  This is the completion of squares
`ClayNS.transverse_quadratic_debt` in Hilbert-space form. -/
theorem pairing_young_absorption (N W : E) {eta : ℝ} (heta : 0 < eta) :
    |⟪N, W⟫| ≤ eta * ‖W‖ ^ 2 + ‖N‖ ^ 2 / (4 * eta) := by
  have hcs : |⟪N, W⟫| ≤ ‖N‖ * ‖W‖ := abs_real_inner_le_norm N W
  have hyoung : ‖N‖ * ‖W‖ ≤ eta * ‖W‖ ^ 2 + ‖N‖ ^ 2 / (4 * eta) := by
    have h := sq_nonneg (Real.sqrt eta * ‖W‖ - ‖N‖ / (2 * Real.sqrt eta))
    obtain ⟨s, hs, hspos⟩ : ∃ s : ℝ, s ^ 2 = eta ∧ 0 < s :=
      ⟨Real.sqrt eta, Real.sq_sqrt heta.le, Real.sqrt_pos.2 heta⟩
    subst hs
    rw [Real.sqrt_sq hspos.le] at h
    have hne : s ≠ 0 := ne_of_gt hspos
    have hexp : (s * ‖W‖ - ‖N‖ / (2 * s)) ^ 2
        = s ^ 2 * ‖W‖ ^ 2 - ‖N‖ * ‖W‖ + ‖N‖ ^ 2 / (4 * s ^ 2) := by
      field_simp
      ring
    linarith [hexp ▸ h]
  linarith

/-! ## Exact subtraction of the marginal channel -/

/-- **The exact marginal/transverse split of the pairing.**  If `P` is an
orthogonal projection (idempotent and symmetric), then

  `⟪N, W⟫ = ⟪N, P W⟫ + ⟪N − P N, W − P W⟫`.

No inequality has been used: the marginal channel is separated exactly. -/
theorem pairing_marginal_split (P : E →L[ℝ] E)
    (hidem : ∀ v : E, P (P v) = P v) (hsym : ∀ u v : E, ⟪P u, v⟫ = ⟪u, P v⟫)
    (N W : E) :
    ⟪N, W⟫ = ⟪N, P W⟫ + ⟪N - P N, W - P W⟫ := by
  have hzero : (⟪N - P N, P W⟫ : ℝ) = 0 := by
    have h1 : (⟪N - P N, P W⟫ : ℝ) = ⟪P (N - P N), W⟫ := (hsym (N - P N) W).symm
    have h2 : P (N - P N) = 0 := by
      rw [map_sub, hidem N, sub_self]
    rw [h1, h2, inner_zero_left]
  have hexpand : (⟪N - P N, W⟫ : ℝ) = ⟪N - P N, P W⟫ + ⟪N - P N, W - P W⟫ := by
    rw [← inner_add_right]
    congr 1
    abel
  have hsplit : (⟪N, W⟫ : ℝ) = ⟪P N, W⟫ + ⟪N - P N, W⟫ := by
    rw [← inner_add_left]
    congr 1
    abel
  rw [hsplit, hexpand, hzero, zero_add, hsym N W]

/-- **Absorption after subtracting the marginal channel.**  Only the transverse
component is estimated, and it is estimated quadratically:

  `|⟪N,W⟫| ≤ |⟪N,PW⟫| + η‖W − PW‖² + ‖N − PN‖²/(4η)`.

This is the Navier–Stokes form of "remove the marginal directions before taking
absolute values, and pay the cross-coupling quadratically against transverse
coercivity". -/
theorem marginal_transverse_absorption (P : E →L[ℝ] E)
    (hidem : ∀ v : E, P (P v) = P v) (hsym : ∀ u v : E, ⟪P u, v⟫ = ⟪u, P v⟫)
    (N W : E) {eta : ℝ} (heta : 0 < eta) :
    |⟪N, W⟫| ≤ |⟪N, P W⟫| + eta * ‖W - P W‖ ^ 2 + ‖N - P N‖ ^ 2 / (4 * eta) := by
  have hsplit := pairing_marginal_split P hidem hsym N W
  have htr := pairing_young_absorption (N - P N) (W - P W) heta
  calc |⟪N, W⟫| = |⟪N, P W⟫ + ⟪N - P N, W - P W⟫| := by rw [hsplit]
    _ ≤ |⟪N, P W⟫| + |⟪N - P N, W - P W⟫| := abs_add_le _ _
    _ ≤ |⟪N, P W⟫| + (eta * ‖W - P W‖ ^ 2 + ‖N - P N‖ ^ 2 / (4 * eta)) := by linarith
    _ = |⟪N, P W⟫| + eta * ‖W - P W‖ ^ 2 + ‖N - P N‖ ^ 2 / (4 * eta) := by ring

/-! ## The energy derivative in telescope form -/

/-- **(S) with the pairing absorbed.**  The derivative supplied by the
similarity energy identity obeys `ℋ′ ≤ −(1−η)‖V_τ‖² + ‖N‖²/(4η)`: exactly the
hypothesis `hHle` of `ClayNS.similarity_transverse_expenditure`, with the
remainder identified as the weighted mass of the nonlinear and pressure
terms. -/
theorem similarity_energy_deriv_le (N W : E) {eta : ℝ} (heta : 0 < eta) :
    -⟪W, W⟫ - ⟪N, W⟫ ≤ -(1 - eta) * ‖W‖ ^ 2 + ‖N‖ ^ 2 / (4 * eta) := by
  have hW : (⟪W, W⟫ : ℝ) = ‖W‖ ^ 2 := real_inner_self_eq_norm_sq W
  have h := pairing_young_absorption N W heta
  have h2 : -⟪N, W⟫ ≤ |⟪N, W⟫| := neg_le_abs _
  rw [hW]
  linarith

/-- The same with the marginal channel subtracted first: the remainder is the
marginal pairing plus the *transverse* mass of `N`, and the coercive term is
the transverse speed. -/
theorem similarity_energy_deriv_le_transverse (P : E →L[ℝ] E)
    (hidem : ∀ v : E, P (P v) = P v) (hsym : ∀ u v : E, ⟪P u, v⟫ = ⟪u, P v⟫)
    (N W : E) {eta : ℝ} (heta : 0 < eta) :
    -⟪W, W⟫ - ⟪N, W⟫
      ≤ -‖W‖ ^ 2 + eta * ‖W - P W‖ ^ 2
        + (|⟪N, P W⟫| + ‖N - P N‖ ^ 2 / (4 * eta)) := by
  have hW : (⟪W, W⟫ : ℝ) = ‖W‖ ^ 2 := real_inner_self_eq_norm_sq W
  have h := marginal_transverse_absorption P hidem hsym N W heta
  have h2 : -⟪N, W⟫ ≤ |⟪N, W⟫| := neg_le_abs _
  rw [hW]
  linarith

end ClayNS

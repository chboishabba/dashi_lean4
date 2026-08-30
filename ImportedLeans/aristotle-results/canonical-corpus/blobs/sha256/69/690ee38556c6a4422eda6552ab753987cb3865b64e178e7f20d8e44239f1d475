/-
# Near/far relative absorption of the similarity pairing

`SimilarityAbsorption.lean` pays the nonlinear/pressure pairing `⟪N,W⟫` by a
*generic* Young inequality, leaving the remainder `‖N‖²/(4η)`, and then asks
for that remainder to have finite accumulated primitive (obligation **A1**).
That is too blunt: it measures the enemy in absolute terms.

This file installs the sharper architecture:

  `N = N_near + N_far + N_marg`,

with

* the **marginal** part `N_marg` living in the marginal (amplitude/gauge)
  subspace, so that it contributes to the pairing *only* through the exactly
  computed channel `⟪N, P W⟫`;
* the **near** part paid **relatively**: `|⟪N_near^⊥, W^⊥⟫| ≤ η‖W^⊥‖²` with
  `η < 1`, i.e. measured against the transverse expenditure that is already
  present rather than against an absolute constant;
* the **far** part paid by a summable tail: `|⟪N_far^⊥, W^⊥⟫| ≤ R_far(τ)` with
  `∫R_far < ∞`.

## What is proved

* `ClayNS.pythagoras_proj` — `‖W‖² = ‖PW‖² + ‖W − PW‖²` for an orthogonal
  projection `P` (used to keep the marginal coercivity, not throw it away).
* `ClayNS.pairing_near_far_split` — the **exact** three-way split of the
  pairing; no inequality is used.
* `ClayNS.pairing_near_far_marginal_split` — the same when `N_marg` is purely
  marginal: its transverse contribution is identically zero.
* `ClayNS.nearfar_relative_absorption` — the resulting bound on the pairing.
* `ClayNS.similarity_energy_deriv_le_nearfar` — identity (S) of
  `SimilarityEnergy.lean` combined with it:
  `ℋ′ ≤ −‖PW‖² − (1−η)‖W^⊥‖² + (|⟪N,PW⟫| + R_far)`.
* `ClayNS.similarity_energy_nonneg` — `ℋ ≥ 0` for a positive semidefinite
  Dirichlet form: the similarity energy is a genuine energy.
* `ClayNS.similarity_energy_uniform_bound` — **A2 collapses into A1**: with the
  near/far derivative bound, `ℋ(τ) ≤ ℋ(τ₀) + (ℛ(τ) − ℛ(τ₀))` on the whole
  window, hence `0 ≤ ℋ ≤ C_H + C_R` from a bound at the *single* endpoint `τ₀`.
* `ClayNS.similarity_energy_drop_of_nonneg` — consequently the energy drop
  obligation `ℋ(τ₀) − ℋ(τ₁) ≤ C_drop` is implied by a one-endpoint bound.
* `ClayNS.similarity_nearfar_transverse_expenditure` — the telescope in the
  near/far form: **one** initial energy bound plus **one** summable tail bound
  give the whole transverse expenditure
  `(1−η)∫‖W^⊥‖² ≤ C_H + C_R`.
* `ClayNS.amplitudeProj` and `ClayNS.amplitude_marginal_channel`,
  `ClayNS.amplitude_transverse_norm_sq` — the *physical* marginal direction is
  the amplitude direction `ℝ·V`; along it the marginal channel is the scalar
  `⟪N,V⟫⟪V,W⟫/⟪V,V⟫` (computed exactly for Navier–Stokes in
  `GaussianMarginalChannel.lean`) and the transverse coercive quantity is
  literally the scale-Gram defect `(AB − C²)/A`.

Nothing physical is proved here and nothing physical is hidden: the two
inputs are exactly the near relative contraction and the far summable tail.
The point is that after this file the A side carries a *single* quantitative
package instead of the pair (absorption, energy drop).

No `sorry`, no postulates, no axioms beyond the standard three.
-/
import RequestProject.NavierStokes.SimilarityAbsorption

open Set
open RealInnerProductSpace

noncomputable section

namespace ClayNS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Orthogonal decomposition -/

/-- The marginal and transverse components are orthogonal, so the squared
speed splits: `‖W‖² = ‖PW‖² + ‖W − PW‖²`. -/
theorem pythagoras_proj (P : E →L[ℝ] E)
    (hidem : ∀ v : E, P (P v) = P v) (hsym : ∀ u v : E, ⟪P u, v⟫ = ⟪u, P v⟫)
    (W : E) : ‖W‖ ^ 2 = ‖P W‖ ^ 2 + ‖W - P W‖ ^ 2 := by
  have hzero : (⟪P W, W - P W⟫ : ℝ) = 0 := by
    rw [hsym W (W - P W), map_sub, hidem W, sub_self, inner_zero_right]
  have hsum : P W + (W - P W) = W := by abel
  have := norm_add_sq_real (P W) (W - P W)
  rw [hsum, hzero] at this
  linarith

/-! ## The exact near/far/marginal split -/

/-- **The exact three-way split of the pairing.**  If `N = N_near + N_far +
N_marg` and `P` is an orthogonal projection, then

  `⟪N,W⟫ = ⟪N,PW⟫ + ⟪N_near − P N_near, W − PW⟫ + ⟪N_far − P N_far, W − PW⟫
            + ⟪N_marg − P N_marg, W − PW⟫`.

Only algebra: nothing has been estimated. -/
theorem pairing_near_far_split (P : E →L[ℝ] E)
    (hidem : ∀ v : E, P (P v) = P v) (hsym : ∀ u v : E, ⟪P u, v⟫ = ⟪u, P v⟫)
    (Nnear Nfar Nmarg W : E) :
    ⟪Nnear + Nfar + Nmarg, W⟫
      = ⟪Nnear + Nfar + Nmarg, P W⟫
        + (⟪Nnear - P Nnear, W - P W⟫ + ⟪Nfar - P Nfar, W - P W⟫
            + ⟪Nmarg - P Nmarg, W - P W⟫) := by
  have hsplit := pairing_marginal_split P hidem hsym (Nnear + Nfar + Nmarg) W
  have hlin : (⟪Nnear + Nfar + Nmarg - P (Nnear + Nfar + Nmarg), W - P W⟫ : ℝ)
      = ⟪Nnear - P Nnear, W - P W⟫ + ⟪Nfar - P Nfar, W - P W⟫
          + ⟪Nmarg - P Nmarg, W - P W⟫ := by
    rw [← inner_add_left, ← inner_add_left]
    congr 1
    simp only [map_add]
    abel
  rw [hsplit, hlin]

/-- **The marginal part contributes only through the computed channel.**  If
`N_marg` lies in the marginal subspace (`P N_marg = N_marg`), its transverse
contribution vanishes identically and

  `⟪N,W⟫ = ⟪N,PW⟫ + ⟪N_near^⊥, W^⊥⟫ + ⟪N_far^⊥, W^⊥⟫`. -/
theorem pairing_near_far_marginal_split (P : E →L[ℝ] E)
    (hidem : ∀ v : E, P (P v) = P v) (hsym : ∀ u v : E, ⟪P u, v⟫ = ⟪u, P v⟫)
    (Nnear Nfar Nmarg W : E) (hmarg : P Nmarg = Nmarg) :
    ⟪Nnear + Nfar + Nmarg, W⟫
      = ⟪Nnear + Nfar + Nmarg, P W⟫
        + (⟪Nnear - P Nnear, W - P W⟫ + ⟪Nfar - P Nfar, W - P W⟫) := by
  have h := pairing_near_far_split P hidem hsym Nnear Nfar Nmarg W
  have hz : (⟪Nmarg - P Nmarg, W - P W⟫ : ℝ) = 0 := by
    rw [hmarg, sub_self, inner_zero_left]
  rw [h, hz, add_zero]

/-! ## Relative absorption -/

/-- **Near/far relative absorption.**  With the near interaction paid
*relatively* against the transverse expenditure and the far interaction paid
by a tail,

  `|⟪N,W⟫| ≤ |⟪N,PW⟫| + η‖W^⊥‖² + R_far`.

Compared with `ClayNS.marginal_transverse_absorption` the remainder no longer
contains a `‖N^⊥‖²/(4η)` term: the near part is charged to the coercivity that
is already present. -/
theorem nearfar_relative_absorption (P : E →L[ℝ] E)
    (hidem : ∀ v : E, P (P v) = P v) (hsym : ∀ u v : E, ⟪P u, v⟫ = ⟪u, P v⟫)
    (Nnear Nfar Nmarg W : E) {eta Rfar : ℝ} (hmarg : P Nmarg = Nmarg)
    (hnear : |⟪Nnear - P Nnear, W - P W⟫| ≤ eta * ‖W - P W‖ ^ 2)
    (hfar : |⟪Nfar - P Nfar, W - P W⟫| ≤ Rfar) :
    |⟪Nnear + Nfar + Nmarg, W⟫|
      ≤ |⟪Nnear + Nfar + Nmarg, P W⟫| + eta * ‖W - P W‖ ^ 2 + Rfar := by
  set N : E := Nnear + Nfar + Nmarg with hN
  have hsplit := pairing_near_far_marginal_split P hidem hsym Nnear Nfar Nmarg W hmarg
  calc |⟪N, W⟫|
      = |⟪N, P W⟫ + (⟪Nnear - P Nnear, W - P W⟫ + ⟪Nfar - P Nfar, W - P W⟫)| := by
        rw [hsplit]
    _ ≤ |⟪N, P W⟫| + |⟪Nnear - P Nnear, W - P W⟫ + ⟪Nfar - P Nfar, W - P W⟫| :=
        abs_add_le _ _
    _ ≤ |⟪N, P W⟫| + (|⟪Nnear - P Nnear, W - P W⟫| + |⟪Nfar - P Nfar, W - P W⟫|) := by
        have := abs_add_le (⟪Nnear - P Nnear, W - P W⟫ : ℝ) ⟪Nfar - P Nfar, W - P W⟫
        linarith
    _ ≤ |⟪N, P W⟫| + eta * ‖W - P W‖ ^ 2 + Rfar := by linarith

/-- **(S) with the near/far absorption inserted.**  The derivative supplied by
`ClayNS.similarity_energy_identity` obeys

  `ℋ′ ≤ −‖PW‖² − (1−η)‖W^⊥‖² + (|⟪N,PW⟫| + R_far)`,

so the coercive term retains the *full* marginal speed and a fixed fraction
`1−η` of the transverse speed. -/
theorem similarity_energy_deriv_le_nearfar (P : E →L[ℝ] E)
    (hidem : ∀ v : E, P (P v) = P v) (hsym : ∀ u v : E, ⟪P u, v⟫ = ⟪u, P v⟫)
    (Nnear Nfar Nmarg W : E) {eta Rfar : ℝ} (hmarg : P Nmarg = Nmarg)
    (hnear : |⟪Nnear - P Nnear, W - P W⟫| ≤ eta * ‖W - P W‖ ^ 2)
    (hfar : |⟪Nfar - P Nfar, W - P W⟫| ≤ Rfar) :
    -⟪W, W⟫ - ⟪Nnear + Nfar + Nmarg, W⟫
      ≤ -‖P W‖ ^ 2 - (1 - eta) * ‖W - P W‖ ^ 2
        + (|⟪Nnear + Nfar + Nmarg, P W⟫| + Rfar) := by
  have hpy := pythagoras_proj P hidem hsym W
  have hW : (⟪W, W⟫ : ℝ) = ‖W‖ ^ 2 := real_inner_self_eq_norm_sq W
  have habs := nearfar_relative_absorption P hidem hsym Nnear Nfar Nmarg W hmarg hnear hfar
  have h2 : -(⟪Nnear + Nfar + Nmarg, W⟫ : ℝ) ≤ |⟪Nnear + Nfar + Nmarg, W⟫| := neg_le_abs _
  rw [hW, hpy]
  nlinarith [habs, h2]

/-- The same in the exact shape consumed by the telescope: only the transverse
speed is kept as the coercive quantity. -/
theorem similarity_energy_deriv_le_transverse_nearfar (P : E →L[ℝ] E)
    (hidem : ∀ v : E, P (P v) = P v) (hsym : ∀ u v : E, ⟪P u, v⟫ = ⟪u, P v⟫)
    (Nnear Nfar Nmarg W : E) {eta Rfar : ℝ} (hmarg : P Nmarg = Nmarg)
    (hnear : |⟪Nnear - P Nnear, W - P W⟫| ≤ eta * ‖W - P W‖ ^ 2)
    (hfar : |⟪Nfar - P Nfar, W - P W⟫| ≤ Rfar) :
    -⟪W, W⟫ - ⟪Nnear + Nfar + Nmarg, W⟫
      ≤ -(1 - eta) * ‖W - P W‖ ^ 2
        + (|⟪Nnear + Nfar + Nmarg, P W⟫| + Rfar) := by
  have h := similarity_energy_deriv_le_nearfar P hidem hsym Nnear Nfar Nmarg W hmarg hnear hfar
  have hP : (0 : ℝ) ≤ ‖P W‖ ^ 2 := sq_nonneg _
  linarith

/-! ## The similarity energy is a genuine energy -/

/-- `ℋ = ½𝔞(V,V) + ¼‖V‖² ≥ 0` whenever the Dirichlet form `𝔞` is positive
semidefinite.  (For `𝔞 = ν⟪∇·,∇·⟫_ρ` this is automatic.) -/
theorem similarity_energy_nonneg (bil : E →L[ℝ] E →L[ℝ] ℝ)
    (hpsd : ∀ v : E, 0 ≤ bil v v) (V : E) :
    0 ≤ (1 / 2) * bil V V + (1 / 4) * ⟪V, V⟫ := by
  have h1 := hpsd V
  have h2 : (0 : ℝ) ≤ ⟪V, V⟫ := real_inner_self_nonneg
  linarith

/-! ## A2 collapses into A1 -/

/-- **The similarity energy stays in the class it starts in.**  If

  `ℋ′(s) ≤ −(1−η)·q(s) + rem(s)`  with `q ≥ 0` and `η ≤ 1`,

then on the whole window `ℋ(s) ≤ ℋ(τ₀) + (ℛ(s) − ℛ(τ₀))`, where `ℛ` is a
primitive of `rem`.  So a bound at the *single* endpoint `τ₀` plus the far tail
budget bounds `ℋ` uniformly: obligation **A2** no longer needs an independent
argument. -/
theorem similarity_energy_uniform_bound {Hcal Rcal Hd q rem : ℝ → ℝ}
    {t0 t1 eta : ℝ} (heta : eta ≤ 1)
    (hq : ∀ s ∈ Icc t0 t1, 0 ≤ q s)
    (hH : ∀ s ∈ Icc t0 t1, HasDerivAt Hcal (Hd s) s)
    (hHle : ∀ s ∈ Icc t0 t1, Hd s ≤ -(1 - eta) * q s + rem s)
    (hR : ∀ s ∈ Icc t0 t1, HasDerivAt Rcal (rem s) s) :
    ∀ s ∈ Icc t0 t1, Hcal s ≤ Hcal t0 + (Rcal s - Rcal t0) := by
  intro s hs
  have hts : t0 ≤ s := hs.1
  have hsub : Icc t0 s ⊆ Icc t0 t1 := Icc_subset_Icc le_rfl hs.2
  have hderiv : ∀ u ∈ Icc t0 s, HasDerivAt (fun v => Rcal v - Hcal v) (rem u - Hd u) u :=
    fun u hu => (hR u (hsub hu)).sub (hH u (hsub hu))
  have hnn : ∀ u ∈ Icc t0 s, 0 ≤ rem u - Hd u := by
    intro u hu
    have h1 := hHle u (hsub hu)
    have h2 := hq u (hsub hu)
    nlinarith
  have hmono := le_of_hasDerivAt_nonneg_on_Icc hts hderiv hnn
  linarith [hmono]

/-- **The energy-drop obligation from a one-endpoint bound.**  A nonnegative
similarity energy bounded at the initial similarity time has a bounded drop
over the whole window. -/
theorem similarity_energy_drop_of_nonneg {Hcal : ℝ → ℝ} {t0 t1 CH : ℝ}
    (hnn : 0 ≤ Hcal t1) (hinit : Hcal t0 ≤ CH) :
    Hcal t0 - Hcal t1 ≤ CH := by linarith

/-! ## The near/far telescope -/

/-- **The whole A-side budget from the near/far package.**

Inputs:
* `hHle` — the near/far relative absorption in derivative form (produced by
  `similarity_energy_deriv_le_transverse_nearfar` from the two physical
  estimates);
* `hnn`, `hinit` — the similarity energy is nonnegative (automatic, see
  `similarity_energy_nonneg`) and bounded at the initial similarity time;
* `hrem` — the far tail has finite accumulated primitive.

Conclusions, simultaneously:
* the transverse expenditure is finite, `(1−η)∫‖W^⊥‖² ≤ C_H + C_R`;
* the energy drop is bounded, `ℋ(τ₀) − ℋ(τ₁) ≤ C_H`;
* the energy stays bounded on the window, `ℋ(τ) ≤ C_H + C_R`.

This is the collapse of **A1 + A2** into a single package. -/
theorem similarity_nearfar_transverse_expenditure {Hcal Ecal Rcal Hd q rem : ℝ → ℝ}
    {t0 t1 eta CH CR : ℝ} (h01 : t0 ≤ t1) (heta : eta ≤ 1)
    (hq : ∀ s ∈ Icc t0 t1, 0 ≤ q s)
    (hH : ∀ s ∈ Icc t0 t1, HasDerivAt Hcal (Hd s) s)
    (hHle : ∀ s ∈ Icc t0 t1, Hd s ≤ -(1 - eta) * q s + rem s)
    (hE : ∀ s ∈ Icc t0 t1, HasDerivAt Ecal (q s) s)
    (hR : ∀ s ∈ Icc t0 t1, HasDerivAt Rcal (rem s) s)
    (hnn : ∀ s ∈ Icc t0 t1, 0 ≤ Hcal s) (hinit : Hcal t0 ≤ CH)
    (hCR : ∀ s ∈ Icc t0 t1, Rcal s - Rcal t0 ≤ CR) :
    (1 - eta) * (Ecal t1 - Ecal t0) ≤ CH + CR
      ∧ Hcal t0 - Hcal t1 ≤ CH
      ∧ ∀ s ∈ Icc t0 t1, Hcal s ≤ CH + CR := by
  have hmem1 : t1 ∈ Icc t0 t1 := ⟨h01, le_rfl⟩
  have hbound := similarity_energy_uniform_bound heta hq hH hHle hR
  refine ⟨?_, ?_, ?_⟩
  · have hexp := similarity_transverse_expenditure (Hcal := Hcal) (Ecal := Ecal)
      (Rcal := Rcal) (Hd := Hd) (q := q) (rem := rem) (eta := eta) h01 hH hHle hE hR
    have h1 : Hcal t0 - Hcal t1 ≤ CH := by linarith [hnn t1 hmem1]
    have h2 : Rcal t1 - Rcal t0 ≤ CR := hCR t1 hmem1
    linarith
  · linarith [hnn t1 hmem1]
  · intro s hs
    have := hbound s hs
    have := hCR s hs
    linarith

/-! ## The physical marginal direction: the amplitude projection -/

/-- The orthogonal projection onto the amplitude (marginal) direction `ℝ·V`. -/
def amplitudeProj (V : E) : E →L[ℝ] E := (⟪V, V⟫ : ℝ)⁻¹ • ((innerSL ℝ V).smulRight V)

@[simp] lemma amplitudeProj_apply (V w : E) :
    amplitudeProj V w = ((⟪V, w⟫ : ℝ) / ⟪V, V⟫) • V := by
  simp [amplitudeProj, div_eq_inv_mul, smul_smul]

lemma amplitudeProj_idem {V : E} (hV : (0 : ℝ) < ⟪V, V⟫) (w : E) :
    amplitudeProj V (amplitudeProj V w) = amplitudeProj V w := by
  have hne : (⟪V, V⟫ : ℝ) ≠ 0 := ne_of_gt hV
  simp only [amplitudeProj_apply, real_inner_smul_right]
  congr 1
  field_simp

lemma amplitudeProj_symm (V u w : E) :
    (⟪amplitudeProj V u, w⟫ : ℝ) = ⟪u, amplitudeProj V w⟫ := by
  simp only [amplitudeProj_apply, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm u V]
  ring

/-- **The marginal channel of the pairing, in the amplitude direction.**
`⟪N, P W⟫ = ⟪N,V⟫·⟪V,W⟫/⟪V,V⟫`: it is entirely determined by the scalar
`⟪N,V⟫`, which `GaussianMarginalChannel.lean` computes exactly for the physical
nonlinear and pressure terms. -/
theorem amplitude_marginal_channel (V N W : E) :
    (⟪N, amplitudeProj V W⟫ : ℝ) = ⟪N, V⟫ * ⟪V, W⟫ / ⟪V, V⟫ := by
  simp only [amplitudeProj_apply, real_inner_smul_right]
  ring

/-- **The transverse speed is the scale-Gram defect.**  With `P` the amplitude
projection, `‖W − PW‖² = (AB − C²)/A` for `A = ⟪V,V⟫`, `B = ⟪W,W⟫`,
`C = ⟪V,W⟫`; combined with `ClayNS.projective_gram_speed` this identifies the
coercive term of the near/far absorption with the Gram defect that the
scale-charge assembly consumes. -/
theorem amplitude_transverse_norm_sq {V : E} (hV : (0 : ℝ) < ⟪V, V⟫) (W : E) :
    ‖W - amplitudeProj V W‖ ^ 2
      = (⟪V, V⟫ * ⟪W, W⟫ - ⟪V, W⟫ ^ 2) / ⟪V, V⟫ := by
  have hne : (⟪V, V⟫ : ℝ) ≠ 0 := ne_of_gt hV
  set c : ℝ := ⟪V, W⟫ / ⟪V, V⟫ with hc
  have hP : amplitudeProj V W = c • V := amplitudeProj_apply V W
  have h1 : ‖W - c • V‖ ^ 2 = ‖W‖ ^ 2 - 2 * ⟪W, c • V⟫ + ‖c • V‖ ^ 2 :=
    norm_sub_sq_real W (c • V)
  have h2 : (⟪W, c • V⟫ : ℝ) = c * ⟪V, W⟫ := by
    rw [real_inner_smul_right, real_inner_comm]
  have h3 : ‖c • V‖ ^ 2 = c ^ 2 * ⟪V, V⟫ := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← real_inner_self_eq_norm_sq]
  rw [hP, h1, h2, h3, ← real_inner_self_eq_norm_sq, hc]
  field_simp
  ring

/-! ## Two convenient reductions -/

/-- **The near relative contraction follows from a relative bound on the near
residual.**  If the transverse part of the near interaction is dominated by `η`
times the transverse speed, the relative-contraction hypothesis of
`ClayNS.nearfar_relative_absorption` holds.  (Cauchy–Schwarz; the point is that
the near interaction is compared with the expenditure that is already present,
not with an absolute constant.) -/
theorem near_relative_of_norm_domination (P : E →L[ℝ] E) (Nnear W : E) {eta : ℝ}
    (h : ‖Nnear - P Nnear‖ ≤ eta * ‖W - P W‖) :
    |⟪Nnear - P Nnear, W - P W⟫| ≤ eta * ‖W - P W‖ ^ 2 := by
  have hcs : |⟪Nnear - P Nnear, W - P W⟫| ≤ ‖Nnear - P Nnear‖ * ‖W - P W‖ :=
    abs_real_inner_le_norm _ _
  have hmul : ‖Nnear - P Nnear‖ * ‖W - P W‖ ≤ (eta * ‖W - P W‖) * ‖W - P W‖ :=
    mul_le_mul_of_nonneg_right h (norm_nonneg _)
  calc |⟪Nnear - P Nnear, W - P W⟫| ≤ ‖Nnear - P Nnear‖ * ‖W - P W‖ := hcs
    _ ≤ (eta * ‖W - P W‖) * ‖W - P W‖ := hmul
    _ = eta * ‖W - P W‖ ^ 2 := by ring

/-- **Relative contraction forces vanishing.**  A nonnegative quantity bounded
by a fixed fraction of itself is zero.  This is the rigidity step the relative
form of the absorption estimate is designed to reach: it is the reason the
estimate is stated as `≤ η·(expenditure)` with `η < 1` rather than as an
absolute smallness statement. -/
theorem relative_contraction_forces_zero {D eta : ℝ} (hD : 0 ≤ D) (heta : eta < 1)
    (h : D ≤ eta * D) : D = 0 := by
  by_contra hne
  have hpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hne)
  nlinarith

end ClayNS

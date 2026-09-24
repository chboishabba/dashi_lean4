/-
# The Ornstein–Uhlenbeck integration by parts in the Gaussian similarity space

`SimilarityEnergy.lean` runs the similarity energy identity (S) at the level of
an *abstract* symmetric form `𝔞` playing the role of `ν⟪∇·,∇·⟫_ρ`.  The
physical content of that abstraction is the classical fact that the linear part

  `L₀ = ν∆ − ½ y·∇`

of the similarity operator is symmetric and *negative* in the Gaussian space
`L²(ρ_ν)`, `ρ_ν(y) = exp(−|y|²/(4ν))`:

  `∫ ρ_ν ⟪L₀V, V⟫ = −ν ∫ ρ_ν |∇V|²`.

This file **derives** that identity for compactly supported `C²` profiles, from
the compactly supported divergence theorem
`ClayNS.integral_divergence_eq_zero_of_vanishing_outside` and the weight
commutator `∇ρ = −(y/2ν)ρ`, with the flux

  `F_i = ρ_ν ⟪∂_i V, V⟫`.

Nothing is assumed: `ν∆ − ½y·∇` is genuinely the Gaussian Dirichlet form.

## Results

* `ClayNS.lapSpace`, `ClayNS.gradSqSpace`, `ClayNS.dilTransport` — the vector
  Laplacian `∆V`, the squared gradient `|∇V|² = ∑ᵢ|∂ᵢV|²` and the dilation
  transport `(y·∇)V`;
* `ClayNS.gauss_OU_divergence_identity` — the raw divergence identity
  `∫ρ(⟪∆V,V⟫ + |∇V|² − (1/2ν)⟪(y·∇)V,V⟫) = 0`;
* `ClayNS.gauss_OU_energy_identity` — **the Ornstein–Uhlenbeck identity**
  `ν∫ρ⟪∆V,V⟫ − ½∫ρ⟪(y·∇)V,V⟫ = −ν∫ρ|∇V|²`, i.e. `⟪L₀V,V⟫_ρ = −ν‖∇V‖²_ρ`;
* `ClayNS.gauss_OU_nonpos` — in particular the linear similarity operator is
  dissipative in the Gaussian space.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GaussianMarginalChannel

open MeasureTheory Set
open RealInnerProductSpace
open scoped BigOperators

noncomputable section

namespace ClayNS

/-! ## The second-order spatial operators -/

/-- The vector Laplacian `∆V = ∑ᵢ ∂ᵢ∂ᵢV` of a time-frozen profile. -/
def lapSpace (V : E3 → E3) (y : E3) : E3 :=
  ∑ i, fderiv ℝ (fun z => fderiv ℝ V z (ee i)) y (ee i)

/-- The squared gradient `|∇V|² = ∑ᵢ |∂ᵢV|²`. -/
def gradSqSpace (V : E3 → E3) (y : E3) : ℝ := ∑ i, ‖fderiv ℝ V y (ee i)‖ ^ 2

/-- The dilation transport `(y·∇)V = ∑ᵢ yᵢ ∂ᵢV`. -/
def dilTransport (V : E3 → E3) (y : E3) : E3 := ∑ i, (y i) • fderiv ℝ V y (ee i)

lemma gradSqSpace_nonneg (V : E3 → E3) (y : E3) : 0 ≤ gradSqSpace V y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ## Smoothness and support bookkeeping -/

/-- The directional derivative of a `C²` field is `C¹`. -/
lemma contDiff_dir_fderiv {V : E3 → E3} (hV : ContDiff ℝ (2 : ℕ) V) (v : E3) :
    ContDiff ℝ (1 : ℕ) (fun y => fderiv ℝ V y v) :=
  (ContinuousLinearMap.apply ℝ E3 v).contDiff.comp (hV.fderiv_right (by norm_num))

/-- A field that vanishes outside a ball has vanishing derivative strictly
outside it. -/
lemma fderiv_eq_zero_outside {V : E3 → E3} {L : ℝ}
    (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0) {y : E3} (hy : L < ‖y‖) :
    fderiv ℝ V y = 0 := by
  have hnb : {z : E3 | L < ‖z‖} ∈ nhds y :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hy
  have hev : V =ᶠ[nhds y] (fun _ => (0 : E3)) := by
    filter_upwards [hnb] with z hz using hsupp z hz.le
  rw [hev.fderiv_eq]
  simp

/-- Consequently the second derivative also vanishes strictly outside the
support ball. -/
lemma fderiv_dir_eq_zero_outside {V : E3 → E3} {L : ℝ}
    (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0) (v : E3) {y : E3} (hy : L < ‖y‖) :
    fderiv ℝ (fun z => fderiv ℝ V z v) y = 0 := by
  have hnb : {z : E3 | L < ‖z‖} ∈ nhds y :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hy
  have hev : (fun z => fderiv ℝ V z v) =ᶠ[nhds y] (fun _ => (0 : E3)) := by
    filter_upwards [hnb] with z hz
    rw [fderiv_eq_zero_outside hsupp hz]
    simp
  rw [hev.fderiv_eq]
  simp

/-- A continuous scalar function vanishing outside a ball is integrable. -/
lemma integrable_of_continuous_vanishing_outside {f : E3 → ℝ} (hf : Continuous f)
    {L : ℝ} (hsupp : ∀ y : E3, L < ‖y‖ → f y = 0) : Integrable f := by
  refine hf.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall (0 : E3) L) ?_
  intro y hy
  by_cases h : L < ‖y‖
  · exact hsupp y h
  · exact absurd (by simpa [Metric.mem_closedBall] using (not_lt.mp h)) hy

/-! ## The divergence identity -/

/-- **The raw Ornstein–Uhlenbeck divergence identity.**  For a compactly
supported `C²` profile,

  `∫ ρ_ν (⟪∆V,V⟫ + |∇V|² − (1/2ν)⟪(y·∇)V,V⟫) = 0`.

This is the divergence theorem applied to the flux `F_i = ρ_ν⟪∂_iV,V⟫`, whose
divergence is exactly the integrand: the Gaussian weight contributes only the
commutator `∇ρ = −(y/2ν)ρ`. -/
theorem gauss_OU_divergence_identity {nu : ℝ} (hnu : nu ≠ 0) {V : E3 → E3}
    (hV : ContDiff ℝ (2 : ℕ) V) {L : ℝ} (hL : 0 < L)
    (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0) :
    ∫ y : E3, gaussWeight nu y * (⟪lapSpace V y, V y⟫ + gradSqSpace V y
        - (1 / (2 * nu)) * ⟪dilTransport V y, V y⟫) = 0 := by
  classical
  have hV1 : ContDiff ℝ (1 : ℕ) V := hV.of_le (by norm_num)
  have hVd : Differentiable ℝ V := hV1.differentiable (by norm_num)
  have hDC : ∀ i : Fin 3, ContDiff ℝ (1 : ℕ) (fun z => fderiv ℝ V z (ee i)) :=
    fun i => contDiff_dir_fderiv hV (ee i)
  have hDd : ∀ i : Fin 3, Differentiable ℝ (fun z => fderiv ℝ V z (ee i)) :=
    fun i => (hDC i).differentiable (by norm_num)
  set Fl : Fin 3 → E3 → ℝ :=
    fun i y => gaussWeight nu y * (⟪fderiv ℝ V y (ee i), V y⟫ : ℝ) with hFl
  have hFC : ∀ i, ContDiff ℝ (1 : ℕ) (Fl i) := fun i =>
    (contDiff_gaussWeight_one nu).mul ((hDC i).inner ℝ hV1)
  have hFsupp : ∀ (i : Fin 3) (y : E3), L ≤ ‖y‖ → Fl i y = 0 := by
    intro i y hy
    simp [hFl, hsupp y hy]
  have hpt : ∀ y : E3, ∑ i, fderiv ℝ (Fl i) y (ee i)
      = gaussWeight nu y * (⟪lapSpace V y, V y⟫ + gradSqSpace V y
          - (1 / (2 * nu)) * ⟪dilTransport V y, V y⟫) := by
    intro y
    have hstep : ∀ i : Fin 3, fderiv ℝ (Fl i) y (ee i)
        = -(y i / (2 * nu)) * gaussWeight nu y * (⟪fderiv ℝ V y (ee i), V y⟫ : ℝ)
          + gaussWeight nu y
            * ((⟪fderiv ℝ (fun z => fderiv ℝ V z (ee i)) y (ee i), V y⟫ : ℝ)
                + ‖fderiv ℝ V y (ee i)‖ ^ 2) := by
      intro i
      have hg : DifferentiableAt ℝ
          (fun z => (⟪fderiv ℝ V z (ee i), V z⟫ : ℝ)) y := ((hDd i) y).inner ℝ (hVd y)
      have hw : DifferentiableAt ℝ (gaussWeight nu) y := (differentiable_gaussWeight nu) y
      have hprod : HasFDerivAt (Fl i)
          (gaussWeight nu y • fderiv ℝ (fun z => (⟪fderiv ℝ V z (ee i), V z⟫ : ℝ)) y
            + (⟪fderiv ℝ V y (ee i), V y⟫ : ℝ) • fderiv ℝ (gaussWeight nu) y) y :=
        hw.hasFDerivAt.mul hg.hasFDerivAt
      rw [hprod.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [fderiv_inner_pair (hDd i) hVd y (ee i), fderiv_gaussWeight hnu y (ee i)]
      have hyi : (⟪y, ee i⟫ : ℝ) = y i := by
        simp [ee, EuclideanSpace.inner_single_right]
      have hself : (⟪fderiv ℝ V y (ee i), fderiv ℝ V y (ee i)⟫ : ℝ)
          = ‖fderiv ℝ V y (ee i)‖ ^ 2 := real_inner_self_eq_norm_sq _
      rw [hyi, hself]
      ring
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hstep i)]
    have hlap : (⟪lapSpace V y, V y⟫ : ℝ)
        = ∑ i, (⟪fderiv ℝ (fun z => fderiv ℝ V z (ee i)) y (ee i), V y⟫ : ℝ) := by
      rw [lapSpace, sum_inner]
    have hdil : (⟪dilTransport V y, V y⟫ : ℝ)
        = ∑ i, y i * (⟪fderiv ℝ V y (ee i), V y⟫ : ℝ) := by
      rw [dilTransport, sum_inner]
      exact Finset.sum_congr rfl fun i _ => real_inner_smul_left _ _ _
    have hne : (2 * nu) ≠ 0 := by
      simpa using mul_ne_zero (two_ne_zero) hnu
    rw [hlap, hdil, gradSqSpace]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
    ring
  have hzero := integral_divergence_eq_zero_of_vanishing_outside Fl hFC hL hFsupp
  rw [← hzero]
  exact (integral_congr_ae (Filter.Eventually.of_forall fun y => (hpt y).symm))

/-! ## Integrability of the Gaussian quadratic densities -/

/-- The Gaussian density `ρ⟪∆V,V⟫` of a compactly supported `C²` profile is
integrable. -/
lemma integrable_gauss_lap {nu L : ℝ} {V : E3 → E3} (hV : ContDiff ℝ (2 : ℕ) V)
    (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0) :
    Integrable (fun y : E3 => gaussWeight nu y * ⟪lapSpace V y, V y⟫) := by
  have hV1 : ContDiff ℝ (1 : ℕ) V := hV.of_le (by norm_num)
  have hDC : ∀ i : Fin 3, ContDiff ℝ (1 : ℕ) (fun z => fderiv ℝ V z (ee i)) :=
    fun i => contDiff_dir_fderiv hV (ee i)
  refine integrable_of_continuous_vanishing_outside (L := L) ?_ ?_
  · refine (contDiff_gaussWeight_one nu).continuous.mul ?_
    refine Continuous.inner ?_ hV1.continuous
    refine continuous_finset_sum _ fun i _ => ?_
    exact ((hDC i).continuous_fderiv (by norm_num)).clm_apply continuous_const
  · intro y hy
    simp [hsupp y hy.le]

/-- The Gaussian Dirichlet density `ρ|∇V|²` of a compactly supported `C²`
profile is integrable. -/
lemma integrable_gauss_gradSq {nu L : ℝ} {V : E3 → E3} (hV : ContDiff ℝ (2 : ℕ) V)
    (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0) :
    Integrable (fun y : E3 => gaussWeight nu y * gradSqSpace V y) := by
  have hDC : ∀ i : Fin 3, ContDiff ℝ (1 : ℕ) (fun z => fderiv ℝ V z (ee i)) :=
    fun i => contDiff_dir_fderiv hV (ee i)
  refine integrable_of_continuous_vanishing_outside (L := L) ?_ ?_
  · refine (contDiff_gaussWeight_one nu).continuous.mul ?_
    refine continuous_finset_sum _ fun i _ => ?_
    exact ((hDC i).continuous).norm.pow 2
  · intro y hy
    have hz : gradSqSpace V y = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [fderiv_eq_zero_outside hsupp hy]
      simp
    simp [hz]

/-- The Gaussian density `ρ⟪(y·∇)V,V⟫` of a compactly supported `C²` profile is
integrable. -/
lemma integrable_gauss_dil {nu L : ℝ} {V : E3 → E3} (hV : ContDiff ℝ (2 : ℕ) V)
    (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0) :
    Integrable (fun y : E3 => gaussWeight nu y * ⟪dilTransport V y, V y⟫) := by
  have hV1 : ContDiff ℝ (1 : ℕ) V := hV.of_le (by norm_num)
  have hDC : ∀ i : Fin 3, ContDiff ℝ (1 : ℕ) (fun z => fderiv ℝ V z (ee i)) :=
    fun i => contDiff_dir_fderiv hV (ee i)
  refine integrable_of_continuous_vanishing_outside (L := L) ?_ ?_
  · refine (contDiff_gaussWeight_one nu).continuous.mul ?_
    refine Continuous.inner ?_ hV1.continuous
    refine continuous_finset_sum _ fun i _ => ?_
    exact (continuous_apply i |>.comp (EuclideanSpace.equiv (Fin 3) ℝ).continuous).smul
      (hDC i).continuous
  · intro y hy
    simp [hsupp y hy.le]

/-- The Gaussian amplitude density `ρ|V|²` of a compactly supported continuous
profile is integrable. -/
lemma integrable_gauss_amp {nu L : ℝ} {V : E3 → E3} (hV : Continuous V)
    (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0) :
    Integrable (fun y : E3 => gaussWeight nu y * ‖V y‖ ^ 2) := by
  refine integrable_of_continuous_vanishing_outside (L := L)
    ((contDiff_gaussWeight_one nu).continuous.mul (hV.norm.pow 2)) ?_
  intro y hy
  simp [hsupp y hy.le]

/-! ## The Ornstein–Uhlenbeck energy identity -/

/-- **`⟪L₀V,V⟫_ρ = −ν‖∇V‖²_ρ`.**  For a compactly supported `C²` profile, the
linear part `L₀ = ν∆ − ½y·∇` of the similarity operator satisfies

  `ν∫ρ⟪∆V,V⟫ − ½∫ρ⟪(y·∇)V,V⟫ = −ν∫ρ|∇V|²`.

This is the physical content of the abstract symmetric form used in
`SimilarityEnergy.lean`: the Gaussian Dirichlet form. -/
theorem gauss_OU_energy_identity {nu : ℝ} (hnu : 0 < nu) {V : E3 → E3}
    (hV : ContDiff ℝ (2 : ℕ) V) {L : ℝ} (hL : 0 < L)
    (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0) :
    nu * (∫ y : E3, gaussWeight nu y * ⟪lapSpace V y, V y⟫)
        - (1 / 2) * ∫ y : E3, gaussWeight nu y * ⟪dilTransport V y, V y⟫
      = -(nu * ∫ y : E3, gaussWeight nu y * gradSqSpace V y) := by
  have hnu' : nu ≠ 0 := ne_of_gt hnu
  have hV1 : ContDiff ℝ (1 : ℕ) V := hV.of_le (by norm_num)
  have hDC : ∀ i : Fin 3, ContDiff ℝ (1 : ℕ) (fun z => fderiv ℝ V z (ee i)) :=
    fun i => contDiff_dir_fderiv hV (ee i)
  have hiLap := integrable_gauss_lap (nu := nu) hV hsupp
  have hiGrad := integrable_gauss_gradSq (nu := nu) hV hsupp
  have hiDil := integrable_gauss_dil (nu := nu) hV hsupp
  have hzero := gauss_OU_divergence_identity hnu' hV hL hsupp
  have hsplit : (∫ y : E3, gaussWeight nu y * (⟪lapSpace V y, V y⟫ + gradSqSpace V y
        - (1 / (2 * nu)) * ⟪dilTransport V y, V y⟫))
      = (∫ y : E3, gaussWeight nu y * ⟪lapSpace V y, V y⟫)
        + (∫ y : E3, gaussWeight nu y * gradSqSpace V y)
        - (1 / (2 * nu)) * ∫ y : E3, gaussWeight nu y * ⟪dilTransport V y, V y⟫ := by
    have hcomb : (fun y : E3 => gaussWeight nu y * (⟪lapSpace V y, V y⟫ + gradSqSpace V y
          - (1 / (2 * nu)) * ⟪dilTransport V y, V y⟫))
        = fun y : E3 => (gaussWeight nu y * ⟪lapSpace V y, V y⟫
            + gaussWeight nu y * gradSqSpace V y)
            - (1 / (2 * nu)) * (gaussWeight nu y * ⟪dilTransport V y, V y⟫) := by
      funext y; ring
    have hiSum : Integrable (fun y : E3 => gaussWeight nu y * ⟪lapSpace V y, V y⟫
        + gaussWeight nu y * gradSqSpace V y) volume := hiLap.add hiGrad
    have hiScal : Integrable (fun y : E3 =>
        (1 / (2 * nu)) * (gaussWeight nu y * ⟪dilTransport V y, V y⟫)) volume :=
      hiDil.const_mul _
    rw [hcomb, integral_sub hiSum hiScal, integral_add hiLap hiGrad, integral_const_mul]
  rw [hsplit] at hzero
  have h2 : (2 : ℝ) * nu ≠ 0 := by simpa using mul_ne_zero two_ne_zero hnu'
  field_simp at hzero ⊢
  nlinarith [hzero]

/-- The linear similarity operator is dissipative in the Gaussian space. -/
theorem gauss_OU_nonpos {nu : ℝ} (hnu : 0 < nu) {V : E3 → E3}
    (hV : ContDiff ℝ (2 : ℕ) V) {L : ℝ} (hL : 0 < L)
    (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0) :
    nu * (∫ y : E3, gaussWeight nu y * ⟪lapSpace V y, V y⟫)
        - (1 / 2) * ∫ y : E3, gaussWeight nu y * ⟪dilTransport V y, V y⟫ ≤ 0 := by
  rw [gauss_OU_energy_identity hnu hV hL hsupp]
  have hnn : 0 ≤ ∫ y : E3, gaussWeight nu y * gradSqSpace V y := by
    refine integral_nonneg fun y => ?_
    have := (gaussWeight_pos nu y).le
    have := gradSqSpace_nonneg V y
    positivity
  nlinarith [hnn, hnu]

end ClayNS

/-
# The marginal channel of the similarity pairing, computed exactly

`SimilarityNearFarAbsorption.lean` splits the nonlinear/pressure pairing into a
marginal channel `⟪N, PW⟫` and a transverse channel, and insists that the
marginal channel be **computed**, never estimated.  For the physical similarity
variables the marginal direction is the amplitude direction `V` itself, so the
marginal channel is governed by the single scalar

  `⟪N, V⟫_ρ = ∫ ρ ⟪(V·∇)V + ∇p, V⟫`,   `ρ(y) = exp(−|y|²/(4ν))`.

For the *unweighted* incompressible pairing this is exactly zero: the advective
term is the divergence of `V|V|²/2` and the pressure term the divergence of
`pV`.  In the Gaussian similarity space the weight does not commute with the
divergence, and the residue is entirely the weight commutator.  This file
computes it exactly:

  `∫ ρ ⟪(V·∇)V + ∇p, V⟫ = (1/(4ν)) ∫ ρ ⟪y,V⟫ (|V|² + 2p)`.

That is `ClayNS.gauss_weighted_marginal_channel`.  The same integration by
parts, `ClayNS.gauss_weighted_transport_by_parts`, gives two further exact
identities that the near/far estimate has to be built on:

* `ClayNS.gauss_weighted_transport_skew` — up to the weight commutator the
  advective pairing is antisymmetric,
  `∫ρ(⟪(V·∇)V,w⟫ + ⟪(V·∇)w,V⟫) = (1/2ν)∫ρ⟪y,V⟫⟪V,w⟫`, so the derivative can be
  moved off the profile onto the test field;
* `ClayNS.gauss_weighted_pressure_solenoidal` — against a solenoidal compactly
  supported test field the pressure survives only through the weight
  commutator, `∫ρ⟪∇p,w⟫ = (1/2ν)∫ρ p⟪y,w⟫`.
  Its two ingredients,
`ClayNS.fderiv_gaussWeight` (`∇ρ = −(y/2ν)ρ`) and
`ClayNS.inner_advSpace_add_gradSpace` (the advective and pressure pairings are
the transport of `|V|²/2 + p`), are proved here as well, and the compactly
supported divergence theorem `ClayNS.integral_divergence_eq_zero_of_vanishing_outside`
does the integration by parts.

The velocity is assumed `C¹` and compactly supported (the profile carries the
cutoff); no support hypothesis is needed on the pressure, since it appears only
in the flux `ρpV`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.CompactDivergence

open MeasureTheory Set
open RealInnerProductSpace
open scoped BigOperators

noncomputable section

namespace ClayNS

/-! ## The Gaussian similarity weight -/

/-- The similarity Gaussian weight `ρ_ν(y) = exp(−|y|²/(4ν))`. -/
def gaussWeight (nu : ℝ) (y : E3) : ℝ := Real.exp (-(‖y‖ ^ 2) / (4 * nu))

lemma gaussWeight_pos (nu : ℝ) (y : E3) : 0 < gaussWeight nu y := Real.exp_pos _

lemma contDiff_gaussWeight (nu : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (gaussWeight nu) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) fun y : E3 => -(‖y‖ ^ 2) / (4 * nu) :=
    ((contDiff_norm_sq ℝ).neg).div_const _
  exact Real.contDiff_exp.comp h

lemma contDiff_gaussWeight_one (nu : ℝ) : ContDiff ℝ (1 : ℕ) (gaussWeight nu) :=
  (contDiff_gaussWeight nu).of_le (by exact_mod_cast le_top)

lemma differentiable_gaussWeight (nu : ℝ) : Differentiable ℝ (gaussWeight nu) :=
  (contDiff_gaussWeight_one nu).differentiable (by norm_num)

/-- **`∇ρ = −(y/2ν)·ρ`.**  The weight commutator that will be the entire
residue of the marginal channel. -/
lemma fderiv_gaussWeight {nu : ℝ} (hnu : nu ≠ 0) (y m : E3) :
    fderiv ℝ (gaussWeight nu) y m = -(⟪y, m⟫ / (2 * nu)) * gaussWeight nu y := by
  have hsq : HasFDerivAt (fun x : E3 => ‖x‖ ^ 2) ((2 : ℝ) • innerSL ℝ y) y := by
    have h := (hasStrictFDerivAt_norm_sq y).hasFDerivAt
    convert h using 1
    ext v
    simp [two_smul]
  have hh : HasFDerivAt (fun x : E3 => -(‖x‖ ^ 2) / (4 * nu))
      ((-(1 / (2 * nu))) • innerSL ℝ y) y := by
    have h := (hsq.neg).mul_const ((4 * nu)⁻¹)
    have hcast : (fun x : E3 => -(‖x‖ ^ 2) / (4 * nu))
        = fun x : E3 => (-(‖x‖ ^ 2)) * (4 * nu)⁻¹ := by
      funext x; rw [div_eq_mul_inv]
    rw [hcast]
    convert h using 1
    ext v
    simp
    field_simp
    ring
  have hexp : HasFDerivAt (gaussWeight nu)
      (Real.exp (-(‖y‖ ^ 2) / (4 * nu)) • ((-(1 / (2 * nu))) • innerSL ℝ y)) y := hh.exp
  rw [hexp.fderiv]
  simp [gaussWeight]
  ring

/-! ## Spatial differential operators on a time-frozen profile -/

/-- The advective term `(V·∇)V` of a time-frozen profile. -/
def advSpace (V : E3 → E3) (y : E3) : E3 := ∑ i, (V y i) • fderiv ℝ V y (ee i)

/-- The gradient of a time-frozen scalar. -/
def gradSpace (p : E3 → ℝ) (y : E3) : E3 := ∑ i, (fderiv ℝ p y (ee i)) • ee i

/-- The divergence of a time-frozen profile. -/
def divSpace (V : E3 → E3) (y : E3) : ℝ := ∑ i, (fderiv ℝ V y (ee i)) i

/-- The transported scalar `g = |V|²/2 + p`: the Bernoulli-type head whose
transport is exactly the pairing of the nonlinear and pressure terms with the
velocity. -/
def bernoulliHead (V : E3 → E3) (p : E3 → ℝ) (y : E3) : ℝ := ‖V y‖ ^ 2 / 2 + p y

lemma fderiv_bernoulliHead {V : E3 → E3} {p : E3 → ℝ}
    (hV : Differentiable ℝ V) (hp : Differentiable ℝ p) (y m : E3) :
    fderiv ℝ (bernoulliHead V p) y m = ⟪V y, fderiv ℝ V y m⟫ + fderiv ℝ p y m := by
  have h1 : HasFDerivAt (fun z : E3 => ‖V z‖ ^ 2 / 2)
      ((innerSL ℝ (V y)).comp (fderiv ℝ V y)) y := by
    have h := ((hV y).hasFDerivAt).norm_sq
    have h2 := h.mul_const ((2 : ℝ)⁻¹)
    have hcast : (fun z : E3 => ‖V z‖ ^ 2 / 2) = fun z : E3 => ‖V z‖ ^ 2 * (2 : ℝ)⁻¹ := by
      funext z; rw [div_eq_mul_inv]
    rw [hcast]
    convert h2 using 1
    ext v
    simp [two_smul]
    ring
  have h3 : HasFDerivAt (bernoulliHead V p)
      ((innerSL ℝ (V y)).comp (fderiv ℝ V y) + fderiv ℝ p y) y := h1.add ((hp y).hasFDerivAt)
  rw [h3.fderiv]
  simp

/-- The pairing of a gradient with a vector field is the transport of the
scalar: `⟪∇p, w⟫ = ∑ᵢ wᵢ ∂ᵢp`. -/
lemma inner_gradSpace_eq (p : E3 → ℝ) (w : E3 → E3) (y : E3) :
    ⟪gradSpace p y, w y⟫ = ∑ i, w y i * fderiv ℝ p y (ee i) := by
  rw [gradSpace, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left]
  have hcoo : (⟪ee i, w y⟫ : ℝ) = w y i := by
    simp [ee, EuclideanSpace.inner_single_left]
  rw [hcoo]
  ring

/-- The pairing of a vector field with the inner product of two fields:
`∂ᵢ⟪V,w⟫ = ⟪∂ᵢV, w⟫ + ⟪V, ∂ᵢw⟫`. -/
lemma fderiv_inner_pair {V w : E3 → E3}
    (hV : Differentiable ℝ V) (hw : Differentiable ℝ w) (y m : E3) :
    fderiv ℝ (fun z => (⟪V z, w z⟫ : ℝ)) y m
      = ⟪fderiv ℝ V y m, w y⟫ + ⟪V y, fderiv ℝ w y m⟫ := by
  have h := ((hV y).hasFDerivAt).inner ℝ ((hw y).hasFDerivAt)
  rw [h.fderiv]
  simp
  ring

/-- **The nonlinear and pressure pairings are the transport of `|V|²/2 + p`.**
`⟪(V·∇)V + ∇p, V⟫ = (V·∇)(|V|²/2 + p)`. -/
lemma inner_advSpace_add_gradSpace {V : E3 → E3} {p : E3 → ℝ}
    (hV : Differentiable ℝ V) (hp : Differentiable ℝ p) (y : E3) :
    ⟪advSpace V y + gradSpace p y, V y⟫
      = ∑ i, V y i * fderiv ℝ (bernoulliHead V p) y (ee i) := by
  have hadv : (⟪advSpace V y, V y⟫ : ℝ)
      = ∑ i, V y i * ⟪V y, fderiv ℝ V y (ee i)⟫ := by
    rw [advSpace, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_left, real_inner_comm]
  have hgrad : (⟪gradSpace p y, V y⟫ : ℝ) = ∑ i, V y i * fderiv ℝ p y (ee i) := by
    rw [gradSpace, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_left]
    have : (⟪ee i, V y⟫ : ℝ) = V y i := by
      simp [ee, EuclideanSpace.inner_single_left]
    rw [this]
    ring
  rw [inner_add_left, hadv, hgrad, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_bernoulliHead hV hp y (ee i)]
  ring

/-! ## The exact marginal-channel identity -/

/-- **The marginal channel of the similarity pairing, computed exactly.**

For a `C¹`, divergence-free, compactly supported profile `V` and a `C¹`
pressure `p`,

  `∫ ρ_ν ⟪(V·∇)V + ∇p, V⟫ = (1/(4ν)) ∫ ρ_ν ⟪y,V⟫ (|V|² + 2p)`.

The left-hand side is the marginal (amplitude) channel of the near/far split:
the pairing of the nonlinear and pressure terms with the velocity direction
itself.  In the unweighted incompressible setting it vanishes identically; in
the Gaussian similarity space the entire residue is the weight commutator
`∇ρ = −(y/2ν)ρ`, and it is *computed*, not estimated. -/
theorem gauss_weighted_transport_by_parts {nu : ℝ} (hnu : nu ≠ 0)
    {V : E3 → E3} {g : E3 → ℝ}
    (hV : ContDiff ℝ (1 : ℕ) V) (hgC : ContDiff ℝ (1 : ℕ) g)
    (hdiv : ∀ y, divSpace V y = 0)
    {L : ℝ} (hL : 0 < L) (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0) :
    ∫ y : E3, gaussWeight nu y * (∑ i, V y i * fderiv ℝ g y (ee i))
      = (1 / (2 * nu)) * ∫ y : E3, gaussWeight nu y * (⟪y, V y⟫ * g y) := by
  classical
  have hVd : Differentiable ℝ V := hV.differentiable (by norm_num)
  have hgd : Differentiable ℝ g := hgC.differentiable (by norm_num)
  -- the flux `F i = ρ · V i · g`
  set Fl : Fin 3 → E3 → ℝ := fun i y => gaussWeight nu y * (V y i * g y) with hFl
  have hVi : ∀ i, ContDiff ℝ (1 : ℕ) fun y : E3 => V y i := by
    intro i
    exact (ContinuousLinearMap.contDiff (EuclideanSpace.proj (𝕜 := ℝ) i)).comp hV
  have hFC : ∀ i, ContDiff ℝ (1 : ℕ) (Fl i) := by
    intro i
    exact (contDiff_gaussWeight_one nu).mul ((hVi i).mul hgC)
  have hFsupp : ∀ (i : Fin 3) (y : E3), L ≤ ‖y‖ → Fl i y = 0 := by
    intro i y hy
    simp [hFl, hsupp y hy]
  -- the pointwise divergence of the flux
  have hpt : ∀ y : E3, ∑ i, fderiv ℝ (Fl i) y (ee i)
      = gaussWeight nu y * (∑ i, V y i * fderiv ℝ g y (ee i))
        - (1 / (2 * nu)) * (gaussWeight nu y * (⟪y, V y⟫ * g y)) := by
    intro y
    have hstep : ∀ i : Fin 3, fderiv ℝ (Fl i) y (ee i)
        = (-(⟪y, ee i⟫ / (2 * nu)) * gaussWeight nu y) * (V y i * g y)
          + gaussWeight nu y * ((fderiv ℝ V y (ee i) i) * g y
              + V y i * fderiv ℝ g y (ee i)) := by
      intro i
      have hw : HasFDerivAt (gaussWeight nu) (fderiv ℝ (gaussWeight nu) y) y :=
        ((differentiable_gaussWeight nu) y).hasFDerivAt
      have hvi : HasFDerivAt (fun z : E3 => V z i)
          (fderiv ℝ (fun z : E3 => V z i) y) y :=
        ((hVi i).differentiable (by norm_num) y).hasFDerivAt
      have hgy : HasFDerivAt g (fderiv ℝ g y) y := (hgd y).hasFDerivAt
      have hprod : HasFDerivAt (Fl i)
          (gaussWeight nu y • ((V y i) • fderiv ℝ g y
              + g y • fderiv ℝ (fun z : E3 => V z i) y)
            + ((V y i) * g y) • fderiv ℝ (gaussWeight nu) y) y :=
        hw.mul (hvi.mul hgy)
      rw [hprod.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have hcoord : fderiv ℝ (fun z : E3 => V z i) y (ee i) = (fderiv ℝ V y (ee i)) i := by
        have hcomp : HasFDerivAt (fun z : E3 => V z i)
            ((EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ V y)) y :=
          (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp y ((hVd y).hasFDerivAt)
        rw [hcomp.fderiv]
        simp
      rw [fderiv_gaussWeight hnu y (ee i), hcoord]
      ring
    have hdivy : ∑ i, (fderiv ℝ V y (ee i)) i = 0 := hdiv y
    have hyexp : ∑ i, ⟪y, ee i⟫ * (V y i) = ⟪y, V y⟫ := by
      have hinner : (⟪y, V y⟫ : ℝ) = ∑ i, y i * V y i := by
        simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
      rw [hinner]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hcoo : (⟪y, ee i⟫ : ℝ) = y i := by
        simp [ee, EuclideanSpace.inner_single_right]
      rw [hcoo]
    have hterm : ∀ i : Fin 3, fderiv ℝ (Fl i) y (ee i)
        = (-(1 / (2 * nu)) * gaussWeight nu y * g y) * (⟪y, ee i⟫ * V y i)
          + (gaussWeight nu y * g y) * ((fderiv ℝ V y (ee i)) i)
          + gaussWeight nu y * (V y i * fderiv ℝ g y (ee i)) := by
      intro i
      rw [hstep i]
      ring
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i),
      Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, hyexp, hdivy]
    ring
  -- integrate the divergence
  have hzero := integral_divergence_eq_zero_of_vanishing_outside Fl hFC hL hFsupp
  -- the two integrands
  set A : E3 → ℝ := fun y => gaussWeight nu y * (∑ i, V y i * fderiv ℝ g y (ee i)) with hA
  set B : E3 → ℝ := fun y => (1 / (2 * nu)) * (gaussWeight nu y * (⟪y, V y⟫ * g y)) with hB
  have hAcont : Continuous A := by
    refine ((contDiff_gaussWeight_one nu).continuous).mul (continuous_finset_sum _ fun i _ => ?_)
    exact ((hVi i).continuous).mul
      (((hgC.continuous_fderiv (by norm_num)).clm_apply continuous_const))
  have hBcont : Continuous B :=
    continuous_const.mul (((contDiff_gaussWeight_one nu).continuous).mul
      ((continuous_id.inner hVd.continuous).mul hgC.continuous))
  have hAsupp : ∀ y : E3, L ≤ ‖y‖ → A y = 0 := by
    intro y hy; simp [hA, hsupp y hy]
  have hBsupp : ∀ y : E3, L ≤ ‖y‖ → B y = 0 := by
    intro y hy; simp [hB, hsupp y hy]
  have hAint : Integrable A := by
    refine (hAcont.integrable_of_hasCompactSupport ?_)
    apply HasCompactSupport.intro (isCompact_closedBall (0 : E3) L)
    intro y hy
    have hy' : L < ‖y‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy
    exact hAsupp y hy'.le
  have hBint : Integrable B := by
    refine (hBcont.integrable_of_hasCompactSupport ?_)
    apply HasCompactSupport.intro (isCompact_closedBall (0 : E3) L)
    intro y hy
    have hy' : L < ‖y‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy
    exact hBsupp y hy'.le
  have hsub : (∫ y : E3, (A y - B y)) = 0 := by
    rw [← hzero]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => (hpt y).symm)
  have hAB : (∫ y : E3, A y) = ∫ y : E3, B y := by
    rw [integral_sub hAint hBint] at hsub
    linarith
  rw [hAB]
  simp only [hB]
  rw [integral_const_mul]

/-! ## The exact marginal-channel identity -/

/-- **The marginal channel of the similarity pairing, computed exactly.**

For a `C¹`, divergence-free, compactly supported profile `V` and a `C¹`
pressure `p`,

  `∫ ρ_ν ⟪(V·∇)V + ∇p, V⟫ = (1/(4ν)) ∫ ρ_ν ⟪y,V⟫ (|V|² + 2p)`.

The left-hand side is the marginal (amplitude) channel of the near/far split:
the pairing of the nonlinear and pressure terms with the velocity direction
itself.  In the unweighted incompressible setting it vanishes identically; in
the Gaussian similarity space the entire residue is the weight commutator
`∇ρ = −(y/2ν)ρ`, and it is *computed*, not estimated. -/
theorem gauss_weighted_marginal_channel {nu : ℝ} (hnu : nu ≠ 0)
    {V : E3 → E3} {p : E3 → ℝ}
    (hV : ContDiff ℝ (1 : ℕ) V) (hp : ContDiff ℝ (1 : ℕ) p)
    (hdiv : ∀ y, divSpace V y = 0)
    {L : ℝ} (hL : 0 < L) (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0) :
    ∫ y : E3, gaussWeight nu y * ⟪advSpace V y + gradSpace p y, V y⟫
      = (1 / (4 * nu)) * ∫ y : E3, gaussWeight nu y * (⟪y, V y⟫ * (‖V y‖ ^ 2 + 2 * p y)) := by
  have hVd : Differentiable ℝ V := hV.differentiable (by norm_num)
  have hpd : Differentiable ℝ p := hp.differentiable (by norm_num)
  have hgC : ContDiff ℝ (1 : ℕ) (bernoulliHead V p) :=
    ((hV.norm_sq ℝ).div_const 2).add hp
  have hbp := gauss_weighted_transport_by_parts hnu hV hgC hdiv hL hsupp
  have hLHS : (∫ y : E3, gaussWeight nu y * ⟪advSpace V y + gradSpace p y, V y⟫)
      = ∫ y : E3, gaussWeight nu y
          * (∑ i, V y i * fderiv ℝ (bernoulliHead V p) y (ee i)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [inner_advSpace_add_gradSpace hVd hpd y]
  rw [hLHS, hbp, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only [bernoulliHead]
  field_simp
  ring

/-! ## Two consequences: transport skewness and the solenoidal pressure -/

/-- The advective operator `(V·∇)w` acting on a second field. -/
def advSpaceOn (V w : E3 → E3) (y : E3) : E3 := ∑ i, (V y i) • fderiv ℝ w y (ee i)

/-- **Transport skewness in the Gaussian similarity space.**  For a `C¹`,
divergence-free, compactly supported `V` and any `C¹` field `w`,

  `∫ ρ_ν (⟪(V·∇)V, w⟫ + ⟪(V·∇)w, V⟫) = (1/(2ν)) ∫ ρ_ν ⟪y,V⟫⟪V,w⟫`.

Up to the weight commutator the advective pairing is antisymmetric, so the
derivative can be moved off the profile onto the test field.  This is the exact
identity the near-interaction estimate has to be built on. -/
theorem gauss_weighted_transport_skew {nu : ℝ} (hnu : nu ≠ 0)
    {V w : E3 → E3} (hV : ContDiff ℝ (1 : ℕ) V) (hw : ContDiff ℝ (1 : ℕ) w)
    (hdiv : ∀ y, divSpace V y = 0)
    {L : ℝ} (hL : 0 < L) (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0) :
    ∫ y : E3, gaussWeight nu y * (⟪advSpace V y, w y⟫ + ⟪advSpaceOn V w y, V y⟫)
      = (1 / (2 * nu)) * ∫ y : E3, gaussWeight nu y * (⟪y, V y⟫ * ⟪V y, w y⟫) := by
  have hVd : Differentiable ℝ V := hV.differentiable (by norm_num)
  have hwd : Differentiable ℝ w := hw.differentiable (by norm_num)
  have hgC : ContDiff ℝ (1 : ℕ) (fun z => (⟪V z, w z⟫ : ℝ)) := hV.inner ℝ hw
  have hbp := gauss_weighted_transport_by_parts hnu hV hgC hdiv hL hsupp
  have hLHS : (∫ y : E3, gaussWeight nu y * (⟪advSpace V y, w y⟫ + ⟪advSpaceOn V w y, V y⟫))
      = ∫ y : E3, gaussWeight nu y
          * (∑ i, V y i * fderiv ℝ (fun z => (⟪V z, w z⟫ : ℝ)) y (ee i)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    congr 1
    have hsum : ∀ i : Fin 3, V y i * fderiv ℝ (fun z => (⟪V z, w z⟫ : ℝ)) y (ee i)
        = V y i * ⟪fderiv ℝ V y (ee i), w y⟫ + V y i * ⟪V y, fderiv ℝ w y (ee i)⟫ := by
      intro i
      rw [fderiv_inner_pair hVd hwd y (ee i)]
      ring
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hsum i), Finset.sum_add_distrib]
    congr 1
    · rw [advSpace, sum_inner]
      exact Finset.sum_congr rfl fun i _ => by rw [real_inner_smul_left]
    · rw [advSpaceOn, sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_left, real_inner_comm]
  rw [hLHS, hbp]

/-- **The pressure disappears from the principal pairing against a solenoidal
test field.**  For a `C¹`, divergence-free, compactly supported `w` and any
`C¹` pressure `p`,

  `∫ ρ_ν ⟪∇p, w⟫ = (1/(2ν)) ∫ ρ_ν p ⟪y,w⟫`,

so the only surviving contribution is the Gaussian weight commutator; in the
unweighted setting it vanishes outright. -/
theorem gauss_weighted_pressure_solenoidal {nu : ℝ} (hnu : nu ≠ 0)
    {w : E3 → E3} {p : E3 → ℝ}
    (hw : ContDiff ℝ (1 : ℕ) w) (hp : ContDiff ℝ (1 : ℕ) p)
    (hdiv : ∀ y, divSpace w y = 0)
    {L : ℝ} (hL : 0 < L) (hsupp : ∀ y : E3, L ≤ ‖y‖ → w y = 0) :
    ∫ y : E3, gaussWeight nu y * ⟪gradSpace p y, w y⟫
      = (1 / (2 * nu)) * ∫ y : E3, gaussWeight nu y * (⟪y, w y⟫ * p y) := by
  have hbp := gauss_weighted_transport_by_parts hnu hw hp hdiv hL hsupp
  have hLHS : (∫ y : E3, gaussWeight nu y * ⟪gradSpace p y, w y⟫)
      = ∫ y : E3, gaussWeight nu y * (∑ i, w y i * fderiv ℝ p y (ee i)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [inner_gradSpace_eq p w y]
  rw [hLHS, hbp]

end ClayNS

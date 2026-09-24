/-
# A support-radius-free Reynolds threshold for stationary similarity profiles

`StationarySimilarityRigidity.lean` proves rigidity for the stationary Gaussian
similarity problem under the threshold `L·K < 2ν`, where `L` is the radius of
the support and `K` the Bernoulli-head domination constant.  That threshold
degenerates along a blow-up sequence whose profiles spread out: `L` grows.

This file removes `L` from the threshold entirely.  The mechanism is a **second
exact Gaussian identity**, obtained from the same compactly supported
divergence theorem with the *dilation flux* `F_i = ρ_ν y_i g`:

  `∫ρ_ν ⟨y, ∇g⟩ = (1/2ν)∫ρ_ν|y|²g − 3∫ρ_ν g`.        (M)

Applied to `g = |V|²` it computes the dilation pairing in terms of the
**Gaussian second moment** `ℳ = ∫ρ_ν|y|²|V|²`:

  `∫ρ_ν⟪(y·∇)V,V⟫ = ℳ/(4ν) − (3/2)𝒜`.

A pointwise Young inequality on the left-hand side then *bounds the moment by
the Dirichlet energy and the amplitude*,

  `ℳ ≤ 16ν²𝒟 + 12ν𝒜`,                                 (M-bound)

which is a genuine Gaussian weighted a priori estimate: it says the profile
cannot place its mass far out without paying Dirichlet energy.

With (M-bound) the marginal scalar `𝒥 = (1/4ν)∫ρ_ν⟨y,V⟩(|V|²+2p)` is bounded
*without* the support radius,

  `|𝒥| ≤ ℳ/(32ν) + K²𝒜/(2ν) ≤ (ν/2)𝒟 + (3/8 + K²/(2ν))𝒜`,

and identity (★) `ν𝒟 + ½𝒜 + 𝒥 = 0` closes as soon as `K² < ν/4`.

## Results

* `ClayNS.gaussMoment` — the Gaussian second moment `ℳ = ∫ρ_ν|y|²|V|²`;
* `ClayNS.gauss_dilation_scalar_identity` — **(M)**, derived from the divergence
  theorem;
* `ClayNS.gauss_moment_dilation_identity` — `∫ρ⟪(y·∇)V,V⟫ = ℳ/(4ν) − (3/2)𝒜`;
* `ClayNS.gaussMoment_le_dirichlet_amp` — **(M-bound)** `ℳ ≤ 16ν²𝒟 + 12ν𝒜`;
* `ClayNS.gaussMarginalJ_moment_bound` — `|𝒥| ≤ ℳ/(32ν) + K²𝒜/(2ν)`;
* `ClayNS.stationary_similarity_rigidity_moment` — **the support-radius-free
  rigidity theorem**: a compactly supported divergence-free `C²` stationary
  similarity profile with `4K² < ν` vanishes identically.

The threshold `4K² < ν` involves only the Bernoulli-head constant and the
viscosity; it is uniform along any sequence of profiles, however large their
supports.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.StationarySimilarityRigidity

open MeasureTheory Set
open RealInnerProductSpace
open scoped BigOperators

noncomputable section

namespace ClayNS

/-! ## The Gaussian second moment -/

/-- The Gaussian second moment `ℳ = ∫ρ_ν |y|²|V|²` of a profile. -/
def gaussMoment (nu : ℝ) (V : E3 → E3) : ℝ :=
  ∫ y : E3, gaussWeight nu y * (‖y‖ ^ 2 * ‖V y‖ ^ 2)

lemma gaussMoment_nonneg (nu : ℝ) (V : E3 → E3) : 0 ≤ gaussMoment nu V := by
  refine integral_nonneg fun y => ?_
  have := (gaussWeight_pos nu y).le
  positivity

/-- The coordinate expansion of the squared Euclidean norm. -/
lemma sum_coord_mul_self (y : E3) : ∑ i, y i * y i = ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Real.norm_eq_abs, sq_abs, sq]

/-- A scalar field vanishing outside a ball has vanishing derivative strictly
outside it. -/
lemma fderiv_scalar_eq_zero_outside {g : E3 → ℝ} {L : ℝ}
    (hsupp : ∀ y : E3, L ≤ ‖y‖ → g y = 0) {y : E3} (hy : L < ‖y‖) :
    fderiv ℝ g y = 0 := by
  have hnb : {z : E3 | L < ‖z‖} ∈ nhds y :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hy
  have hev : g =ᶠ[nhds y] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnb] with z hz using hsupp z hz.le
  rw [hev.fderiv_eq]
  simp

/-- The Gaussian moment density `ρ|y|²|V|²` of a compactly supported continuous
profile is integrable. -/
lemma integrable_gauss_moment {nu L : ℝ} {V : E3 → E3} (hV : Continuous V)
    (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0) :
    Integrable (fun y : E3 => gaussWeight nu y * (‖y‖ ^ 2 * ‖V y‖ ^ 2)) := by
  refine integrable_of_continuous_vanishing_outside (L := L)
    ((contDiff_gaussWeight_one nu).continuous.mul
      ((continuous_norm.pow 2).mul (hV.norm.pow 2))) ?_
  intro y hy
  simp [hsupp y hy.le]

/-! ## (M): the dilation flux identity -/

/-- **(M) The Gaussian dilation identity for a scalar.**  For a compactly
supported `C¹` scalar `g`,

  `∫ρ_ν ⟨y,∇g⟩ = (1/2ν)∫ρ_ν|y|²g − 3∫ρ_ν g`.

This is the divergence theorem for the flux `F_i = ρ_ν y_i g`: the weight
contributes the commutator `∇ρ = −(y/2ν)ρ` and the dilation field contributes
its divergence `3`. -/
theorem gauss_dilation_scalar_identity {nu : ℝ} (hnu : nu ≠ 0) {g : E3 → ℝ}
    (hg : ContDiff ℝ (1 : ℕ) g) {L : ℝ} (hL : 0 < L)
    (hsupp : ∀ y : E3, L ≤ ‖y‖ → g y = 0) :
    (∫ y : E3, gaussWeight nu y * (∑ i, y i * fderiv ℝ g y (ee i)))
      = (1 / (2 * nu)) * (∫ y : E3, gaussWeight nu y * (‖y‖ ^ 2 * g y))
        - 3 * ∫ y : E3, gaussWeight nu y * g y := by
  classical
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hproj : ∀ i : Fin 3, ContDiff ℝ (1 : ℕ) fun y : E3 => y i := by
    intro i
    exact ContinuousLinearMap.contDiff (EuclideanSpace.proj (𝕜 := ℝ) i)
  set Fl : Fin 3 → E3 → ℝ := fun i y => gaussWeight nu y * (y i * g y) with hFl
  have hFC : ∀ i, ContDiff ℝ (1 : ℕ) (Fl i) := fun i =>
    (contDiff_gaussWeight_one nu).mul ((hproj i).mul hg)
  have hFsupp : ∀ (i : Fin 3) (y : E3), L ≤ ‖y‖ → Fl i y = 0 := by
    intro i y hy
    simp [hFl, hsupp y hy]
  -- the pointwise divergence of the flux
  have hpt : ∀ y : E3, ∑ i, fderiv ℝ (Fl i) y (ee i)
      = gaussWeight nu y * (∑ i, y i * fderiv ℝ g y (ee i))
        + 3 * (gaussWeight nu y * g y)
        - (1 / (2 * nu)) * (gaussWeight nu y * (‖y‖ ^ 2 * g y)) := by
    intro y
    have hstep : ∀ i : Fin 3, fderiv ℝ (Fl i) y (ee i)
        = (-(⟪y, ee i⟫ / (2 * nu)) * gaussWeight nu y) * (y i * g y)
          + gaussWeight nu y * (1 * g y + y i * fderiv ℝ g y (ee i)) := by
      intro i
      have hw : HasFDerivAt (gaussWeight nu) (fderiv ℝ (gaussWeight nu) y) y :=
        ((differentiable_gaussWeight nu) y).hasFDerivAt
      have hci : HasFDerivAt (fun z : E3 => z i)
          (fderiv ℝ (fun z : E3 => z i) y) y :=
        (((hproj i).differentiable (by norm_num)) y).hasFDerivAt
      have hgy : HasFDerivAt g (fderiv ℝ g y) y := (hgd y).hasFDerivAt
      have hprod : HasFDerivAt (Fl i)
          (gaussWeight nu y • ((y i) • fderiv ℝ g y
              + g y • fderiv ℝ (fun z : E3 => z i) y)
            + ((y i) * g y) • fderiv ℝ (gaussWeight nu) y) y :=
        hw.mul (hci.mul hgy)
      rw [hprod.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have hcoord : fderiv ℝ (fun z : E3 => z i) y (ee i) = 1 := by
        have hlin : HasFDerivAt (fun z : E3 => z i)
            (EuclideanSpace.proj (𝕜 := ℝ) i) y :=
          (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
        rw [hlin.fderiv]
        simp [ee, EuclideanSpace.single_apply]
      rw [fderiv_gaussWeight hnu y (ee i), hcoord]
      ring
    have hyi : ∀ i : Fin 3, (⟪y, ee i⟫ : ℝ) = y i := by
      intro i
      simp [ee, EuclideanSpace.inner_single_right]
    have hterm : ∀ i : Fin 3, fderiv ℝ (Fl i) y (ee i)
        = (-(1 / (2 * nu)) * gaussWeight nu y * g y) * (y i * y i)
          + gaussWeight nu y * g y
          + gaussWeight nu y * (y i * fderiv ℝ g y (ee i)) := by
      intro i
      rw [hstep i, hyi i]
      ring
    have e1 : (∑ i, (-(1 / (2 * nu)) * gaussWeight nu y * g y) * (y i * y i))
        = (-(1 / (2 * nu)) * gaussWeight nu y * g y) * ‖y‖ ^ 2 := by
      rw [← Finset.mul_sum, sum_coord_mul_self]
    have e2 : (∑ _i : Fin 3, gaussWeight nu y * g y) = 3 * (gaussWeight nu y * g y) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_ofNat]
    have e3 : (∑ i, gaussWeight nu y * (y i * fderiv ℝ g y (ee i)))
        = gaussWeight nu y * ∑ i, y i * fderiv ℝ g y (ee i) := (Finset.mul_sum _ _ _).symm
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i),
      Finset.sum_add_distrib, Finset.sum_add_distrib, e1, e2, e3]
    ring
  have hzero := integral_divergence_eq_zero_of_vanishing_outside Fl hFC hL hFsupp
  -- integrability of the three pieces
  have hgcont : Continuous g := hg.continuous
  have hI1 : Integrable (fun y : E3 => gaussWeight nu y * (∑ i, y i * fderiv ℝ g y (ee i))) := by
    refine integrable_of_continuous_vanishing_outside (L := L) ?_ ?_
    · refine (contDiff_gaussWeight_one nu).continuous.mul (continuous_finset_sum _ fun i _ => ?_)
      exact ((continuous_apply i).comp (EuclideanSpace.equiv (Fin 3) ℝ).continuous).mul
        ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    · intro y hy
      have : fderiv ℝ g y = 0 := fderiv_scalar_eq_zero_outside hsupp hy
      simp [this]
  have hI2 : Integrable (fun y : E3 => gaussWeight nu y * g y) := by
    refine integrable_of_continuous_vanishing_outside (L := L)
      ((contDiff_gaussWeight_one nu).continuous.mul hgcont) ?_
    intro y hy
    simp [hsupp y hy.le]
  have hI3 : Integrable (fun y : E3 => gaussWeight nu y * (‖y‖ ^ 2 * g y)) := by
    refine integrable_of_continuous_vanishing_outside (L := L)
      ((contDiff_gaussWeight_one nu).continuous.mul ((continuous_norm.pow 2).mul hgcont)) ?_
    intro y hy
    simp [hsupp y hy.le]
  have hIa : Integrable (fun y : E3 => (3 : ℝ) * (gaussWeight nu y * g y)) := hI2.const_mul _
  have hIb : Integrable (fun y : E3 =>
      (1 / (2 * nu)) * (gaussWeight nu y * (‖y‖ ^ 2 * g y))) := hI3.const_mul _
  have hIsum : Integrable (fun y : E3 =>
      gaussWeight nu y * (∑ i, y i * fderiv ℝ g y (ee i))
        + 3 * (gaussWeight nu y * g y)) volume := hI1.add hIa
  have hsum : (∫ y : E3, ∑ i, fderiv ℝ (Fl i) y (ee i))
      = (∫ y : E3, gaussWeight nu y * (∑ i, y i * fderiv ℝ g y (ee i)))
        + 3 * (∫ y : E3, gaussWeight nu y * g y)
        - (1 / (2 * nu)) * ∫ y : E3, gaussWeight nu y * (‖y‖ ^ 2 * g y) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_sub hIsum hIb, integral_add hI1 hIa, integral_const_mul,
      integral_const_mul]
  rw [hzero] at hsum
  linarith [hsum]

/-! ## The dilation pairing computed by the moment -/

/-- **`∫ρ⟪(y·∇)V,V⟫ = ℳ/(4ν) − (3/2)𝒜`.**  Identity (M) applied to the scalar
`g = |V|²`. -/
theorem gauss_moment_dilation_identity {nu : ℝ} (hnu : nu ≠ 0) {V : E3 → E3}
    (hV : ContDiff ℝ (1 : ℕ) V) {L : ℝ} (hL : 0 < L)
    (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0) :
    (∫ y : E3, gaussWeight nu y * ⟪dilTransport V y, V y⟫)
      = gaussMoment nu V / (4 * nu) - (3 / 2) * gaussAmp nu V := by
  classical
  have hVd : Differentiable ℝ V := hV.differentiable (by norm_num)
  set g : E3 → ℝ := fun z => (⟪V z, V z⟫ : ℝ) with hg
  have hgC : ContDiff ℝ (1 : ℕ) g := hV.inner ℝ hV
  have hgsupp : ∀ y : E3, L ≤ ‖y‖ → g y = 0 := by
    intro y hy
    simp [hg, hsupp y hy]
  have hgval : ∀ y : E3, g y = ‖V y‖ ^ 2 := fun y => real_inner_self_eq_norm_sq _
  have hid := gauss_dilation_scalar_identity hnu hgC hL hgsupp
  -- the left-hand side is twice the dilation pairing
  have hlhs : ∀ y : E3, (∑ i, y i * fderiv ℝ g y (ee i))
      = 2 * (⟪dilTransport V y, V y⟫ : ℝ) := by
    intro y
    have hd : ∀ i : Fin 3, fderiv ℝ g y (ee i)
        = 2 * (⟪fderiv ℝ V y (ee i), V y⟫ : ℝ) := by
      intro i
      rw [hg, fderiv_inner_pair hVd hVd y (ee i), real_inner_comm (V y)]
      ring
    have hdil : (⟪dilTransport V y, V y⟫ : ℝ)
        = ∑ i, y i * (⟪fderiv ℝ V y (ee i), V y⟫ : ℝ) := by
      rw [dilTransport, sum_inner]
      exact Finset.sum_congr rfl fun i _ => real_inner_smul_left _ _ _
    rw [hdil, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hd i]; ring
  have hL1 : (∫ y : E3, gaussWeight nu y * (∑ i, y i * fderiv ℝ g y (ee i)))
      = 2 * ∫ y : E3, gaussWeight nu y * ⟪dilTransport V y, V y⟫ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [hlhs y]
    ring
  have hM : (∫ y : E3, gaussWeight nu y * (‖y‖ ^ 2 * g y)) = gaussMoment nu V := by
    rw [gaussMoment]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [hgval y]
  have hA : (∫ y : E3, gaussWeight nu y * g y) = gaussAmp nu V := by
    rw [gaussAmp]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [hgval y]
  rw [hL1, hM, hA] at hid
  have h4 : (4 : ℝ) * nu ≠ 0 := by
    simpa using mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) hnu
  field_simp at hid ⊢
  linarith [hid]

/-! ## (M-bound): the moment is controlled by the Dirichlet energy -/

/-- The pointwise Young bound `|⟪(y·∇)V,V⟫| ≤ (1/8ν)|y|²|V|² + 2ν|∇V|²`. -/
lemma abs_inner_dilTransport_le {nu : ℝ} (hnu : 0 < nu) (V : E3 → E3) (y : E3) :
    |(⟪dilTransport V y, V y⟫ : ℝ)|
      ≤ (1 / (8 * nu)) * (‖y‖ ^ 2 * ‖V y‖ ^ 2) + 2 * nu * gradSqSpace V y := by
  classical
  have hdil : (⟪dilTransport V y, V y⟫ : ℝ)
      = ∑ i, y i * (⟪fderiv ℝ V y (ee i), V y⟫ : ℝ) := by
    rw [dilTransport, sum_inner]
    exact Finset.sum_congr rfl fun i _ => real_inner_smul_left _ _ _
  have hterm : ∀ i : Fin 3, |y i * (⟪fderiv ℝ V y (ee i), V y⟫ : ℝ)|
      ≤ (1 / (8 * nu)) * (y i * y i * ‖V y‖ ^ 2)
        + 2 * nu * ‖fderiv ℝ V y (ee i)‖ ^ 2 := by
    intro i
    set a : ℝ := |y i| * ‖V y‖ with ha
    set b : ℝ := ‖fderiv ℝ V y (ee i)‖ with hb
    have hcs : |(⟪fderiv ℝ V y (ee i), V y⟫ : ℝ)| ≤ b * ‖V y‖ :=
      abs_real_inner_le_norm _ _
    have h1 : |y i * (⟪fderiv ℝ V y (ee i), V y⟫ : ℝ)| ≤ a * b := by
      rw [abs_mul, ha]
      calc |y i| * |(⟪fderiv ℝ V y (ee i), V y⟫ : ℝ)|
          ≤ |y i| * (b * ‖V y‖) := mul_le_mul_of_nonneg_left hcs (abs_nonneg _)
        _ = |y i| * ‖V y‖ * b := by ring
    have hyoung : a * b ≤ (1 / (8 * nu)) * a ^ 2 + 2 * nu * b ^ 2 := by
      have hsq : 0 ≤ (a - 4 * nu * b) ^ 2 := sq_nonneg _
      rw [← sub_nonneg]
      have hkey : (1 / (8 * nu)) * a ^ 2 + 2 * nu * b ^ 2 - a * b
          = (1 / (8 * nu)) * (a - 4 * nu * b) ^ 2 := by
        field_simp
        ring
      rw [hkey]
      positivity
    have ha2 : a ^ 2 = y i * y i * ‖V y‖ ^ 2 := by
      rw [ha, mul_pow, sq_abs]; ring
    have hb2 : b ^ 2 = ‖fderiv ℝ V y (ee i)‖ ^ 2 := rfl
    calc |y i * (⟪fderiv ℝ V y (ee i), V y⟫ : ℝ)| ≤ a * b := h1
      _ ≤ (1 / (8 * nu)) * a ^ 2 + 2 * nu * b ^ 2 := hyoung
      _ = (1 / (8 * nu)) * (y i * y i * ‖V y‖ ^ 2)
            + 2 * nu * ‖fderiv ℝ V y (ee i)‖ ^ 2 := by rw [ha2, hb2]
  calc |(⟪dilTransport V y, V y⟫ : ℝ)|
      = |∑ i, y i * (⟪fderiv ℝ V y (ee i), V y⟫ : ℝ)| := by rw [hdil]
    _ ≤ ∑ i, |y i * (⟪fderiv ℝ V y (ee i), V y⟫ : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ((1 / (8 * nu)) * (y i * y i * ‖V y‖ ^ 2)
          + 2 * nu * ‖fderiv ℝ V y (ee i)‖ ^ 2) := Finset.sum_le_sum fun i _ => hterm i
    _ = (1 / (8 * nu)) * (‖y‖ ^ 2 * ‖V y‖ ^ 2) + 2 * nu * gradSqSpace V y := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, gradSqSpace]
        congr 2
        rw [← Finset.sum_mul, sum_coord_mul_self]

/-- **(M-bound) `ℳ ≤ 16ν²𝒟 + 12ν𝒜`.**  The Gaussian second moment of a
compactly supported profile is controlled by its Gaussian Dirichlet energy and
amplitude: the exact dilation identity turns the moment into a pairing, and the
pairing is paid by Young's inequality against half of itself. -/
theorem gaussMoment_le_dirichlet_amp {nu : ℝ} (hnu : 0 < nu) {V : E3 → E3}
    (hV : ContDiff ℝ (2 : ℕ) V) {L : ℝ} (hL : 0 < L)
    (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0) :
    gaussMoment nu V ≤ 16 * nu ^ 2 * gaussDirichlet nu V + 12 * nu * gaussAmp nu V := by
  have hnu' : nu ≠ 0 := ne_of_gt hnu
  have hV1 : ContDiff ℝ (1 : ℕ) V := hV.of_le (by norm_num)
  have hid := gauss_moment_dilation_identity hnu' hV1 hL hsupp
  -- the pointwise Young domination
  have hIm : Integrable (fun y : E3 => gaussWeight nu y * (‖y‖ ^ 2 * ‖V y‖ ^ 2)) :=
    integrable_gauss_moment (nu := nu) hV1.continuous hsupp
  have hIg : Integrable (fun y : E3 => gaussWeight nu y * gradSqSpace V y) :=
    integrable_gauss_gradSq (nu := nu) hV hsupp
  have hdom : ∀ y : E3, ‖gaussWeight nu y * ⟪dilTransport V y, V y⟫‖
      ≤ (1 / (8 * nu)) * (gaussWeight nu y * (‖y‖ ^ 2 * ‖V y‖ ^ 2))
        + 2 * nu * (gaussWeight nu y * gradSqSpace V y) := by
    intro y
    have hwpos := (gaussWeight_pos nu y).le
    have hpt := abs_inner_dilTransport_le hnu V y
    calc ‖gaussWeight nu y * ⟪dilTransport V y, V y⟫‖
        = gaussWeight nu y * |(⟪dilTransport V y, V y⟫ : ℝ)| := by
          simp [Real.norm_eq_abs, abs_of_nonneg hwpos]
      _ ≤ gaussWeight nu y * ((1 / (8 * nu)) * (‖y‖ ^ 2 * ‖V y‖ ^ 2)
            + 2 * nu * gradSqSpace V y) := mul_le_mul_of_nonneg_left hpt hwpos
      _ = (1 / (8 * nu)) * (gaussWeight nu y * (‖y‖ ^ 2 * ‖V y‖ ^ 2))
            + 2 * nu * (gaussWeight nu y * gradSqSpace V y) := by ring
  have hgint : Integrable (fun y : E3 =>
      (1 / (8 * nu)) * (gaussWeight nu y * (‖y‖ ^ 2 * ‖V y‖ ^ 2))
        + 2 * nu * (gaussWeight nu y * gradSqSpace V y)) :=
    (hIm.const_mul _).add (hIg.const_mul _)
  have hle := norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall hdom)
  rw [integral_add (hIm.const_mul _) (hIg.const_mul _), integral_const_mul,
    integral_const_mul] at hle
  have habs : |∫ y : E3, gaussWeight nu y * ⟪dilTransport V y, V y⟫|
      ≤ (1 / (8 * nu)) * gaussMoment nu V + 2 * nu * gaussDirichlet nu V := by
    simpa [Real.norm_eq_abs, gaussMoment, gaussDirichlet] using hle
  have hupper : gaussMoment nu V / (4 * nu) - (3 / 2) * gaussAmp nu V
      ≤ (1 / (8 * nu)) * gaussMoment nu V + 2 * nu * gaussDirichlet nu V := by
    rw [← hid]
    exact le_trans (le_abs_self _) habs
  have h8 : (0 : ℝ) < 8 * nu := by linarith
  have hmul := mul_le_mul_of_nonneg_left hupper h8.le
  have hl : 8 * nu * (gaussMoment nu V / (4 * nu) - 3 / 2 * gaussAmp nu V)
      = 2 * gaussMoment nu V - 12 * nu * gaussAmp nu V := by
    field_simp
    ring
  have hr : 8 * nu * (1 / (8 * nu) * gaussMoment nu V + 2 * nu * gaussDirichlet nu V)
      = gaussMoment nu V + 16 * nu ^ 2 * gaussDirichlet nu V := by
    field_simp
    ring
  rw [hl, hr] at hmul
  linarith

/-! ## The marginal scalar without the support radius -/

/-- **`|𝒥| ≤ ℳ/(32ν) + K²𝒜/(2ν)`.**  With the Bernoulli head dominated by
`K|V|`, the computed marginal scalar is bounded by the Gaussian second moment
and the amplitude — the support radius does not appear. -/
theorem gaussMarginalJ_moment_bound {nu K : ℝ} (hnu : 0 < nu)
    {V : E3 → E3} {p : E3 → ℝ}
    (hhead : ∀ y : E3, |‖V y‖ ^ 2 + 2 * p y| ≤ K * ‖V y‖)
    (hIm : Integrable (fun y : E3 => gaussWeight nu y * (‖y‖ ^ 2 * ‖V y‖ ^ 2)))
    (hIa : Integrable (fun y : E3 => gaussWeight nu y * ‖V y‖ ^ 2)) :
    |gaussMarginalJ nu V p|
      ≤ gaussMoment nu V / (32 * nu) + K ^ 2 * gaussAmp nu V / (2 * nu) := by
  have hdom : ∀ y : E3, ‖gaussWeight nu y * (⟪y, V y⟫ * (‖V y‖ ^ 2 + 2 * p y))‖
      ≤ (1 / 8) * (gaussWeight nu y * (‖y‖ ^ 2 * ‖V y‖ ^ 2))
        + 2 * K ^ 2 * (gaussWeight nu y * ‖V y‖ ^ 2) := by
    intro y
    have hwpos := (gaussWeight_pos nu y).le
    have hcs : |(⟪y, V y⟫ : ℝ)| ≤ ‖y‖ * ‖V y‖ := abs_real_inner_le_norm _ _
    have hprod : |(⟪y, V y⟫ : ℝ)| * |‖V y‖ ^ 2 + 2 * p y|
        ≤ (‖y‖ * ‖V y‖) * (K * ‖V y‖) :=
      mul_le_mul hcs (hhead y) (abs_nonneg _) (by positivity)
    have hyoung : (‖y‖ * ‖V y‖) * (K * ‖V y‖)
        ≤ (1 / 8) * (‖y‖ ^ 2 * ‖V y‖ ^ 2) + 2 * K ^ 2 * ‖V y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖y‖ * ‖V y‖ - 4 * K * ‖V y‖), norm_nonneg (V y), norm_nonneg y]
    calc ‖gaussWeight nu y * (⟪y, V y⟫ * (‖V y‖ ^ 2 + 2 * p y))‖
        = gaussWeight nu y * (|(⟪y, V y⟫ : ℝ)| * |‖V y‖ ^ 2 + 2 * p y|) := by
          simp [Real.norm_eq_abs, abs_of_nonneg hwpos]
      _ ≤ gaussWeight nu y * ((1 / 8) * (‖y‖ ^ 2 * ‖V y‖ ^ 2) + 2 * K ^ 2 * ‖V y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hprod.trans hyoung) hwpos
      _ = (1 / 8) * (gaussWeight nu y * (‖y‖ ^ 2 * ‖V y‖ ^ 2))
            + 2 * K ^ 2 * (gaussWeight nu y * ‖V y‖ ^ 2) := by ring
  have hgint : Integrable (fun y : E3 =>
      (1 / 8) * (gaussWeight nu y * (‖y‖ ^ 2 * ‖V y‖ ^ 2))
        + 2 * K ^ 2 * (gaussWeight nu y * ‖V y‖ ^ 2)) :=
    (hIm.const_mul _).add (hIa.const_mul _)
  have hle := norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall hdom)
  rw [integral_add (hIm.const_mul _) (hIa.const_mul _), integral_const_mul,
    integral_const_mul] at hle
  have habs : |∫ y : E3, gaussWeight nu y * (⟪y, V y⟫ * (‖V y‖ ^ 2 + 2 * p y))|
      ≤ (1 / 8) * gaussMoment nu V + 2 * K ^ 2 * gaussAmp nu V := by
    simpa [Real.norm_eq_abs, gaussMoment, gaussAmp] using hle
  have hval : (1 / (4 * nu)) * ((1 / 8) * gaussMoment nu V + 2 * K ^ 2 * gaussAmp nu V)
      = gaussMoment nu V / (32 * nu) + K ^ 2 * gaussAmp nu V / (2 * nu) := by
    field_simp
    ring
  rw [gaussMarginalJ, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (4 * nu))]
  calc (1 / (4 * nu))
        * |∫ y : E3, gaussWeight nu y * (⟪y, V y⟫ * (‖V y‖ ^ 2 + 2 * p y))|
      ≤ (1 / (4 * nu)) * ((1 / 8) * gaussMoment nu V + 2 * K ^ 2 * gaussAmp nu V) :=
        mul_le_mul_of_nonneg_left habs (by positivity)
    _ = gaussMoment nu V / (32 * nu) + K ^ 2 * gaussAmp nu V / (2 * nu) := hval

/-! ## The support-radius-free rigidity theorem -/

/-- **Rigidity with a support-radius-free Reynolds threshold.**

A compactly supported, divergence-free `C²` stationary Gaussian similarity
profile whose Bernoulli head is dominated by `K|V|` vanishes identically as soon
as

  `4K² < ν`,

i.e. `K < √ν/2`.  In contrast with `ClayNS.stationary_similarity_rigidity`, the
threshold does **not** involve the radius `L` of the support: it is uniform
along any sequence of profiles, however far their mass spreads.  The extra
ingredient is the exact Gaussian moment identity (M) and the resulting a priori
bound `ℳ ≤ 16ν²𝒟 + 12ν𝒜`, which lets the Dirichlet energy — hitherto
discarded — pay for the far part of the marginal scalar. -/
theorem stationary_similarity_rigidity_moment {nu K : ℝ} (hnu : 0 < nu)
    {V : E3 → E3} {p : E3 → ℝ}
    (hV : ContDiff ℝ (2 : ℕ) V) (hp : ContDiff ℝ (1 : ℕ) p)
    (hdiv : ∀ y, divSpace V y = 0)
    {L : ℝ} (hL : 0 < L) (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0)
    (hhead : ∀ y : E3, |‖V y‖ ^ 2 + 2 * p y| ≤ K * ‖V y‖)
    (heq : IsStationarySimilarity nu V p)
    (hsmall : 4 * K ^ 2 < nu) :
    ∀ y : E3, V y = 0 := by
  have hV1 : ContDiff ℝ (1 : ℕ) V := hV.of_le (by norm_num)
  have hIa : Integrable (fun y : E3 => gaussWeight nu y * ‖V y‖ ^ 2) :=
    integrable_gauss_amp (nu := nu) hV1.continuous hsupp
  have hIm : Integrable (fun y : E3 => gaussWeight nu y * (‖y‖ ^ 2 * ‖V y‖ ^ 2)) :=
    integrable_gauss_moment (nu := nu) hV1.continuous hsupp
  have hid := stationary_similarity_gauss_identity hnu hV hp hdiv hL hsupp heq
  have hJ := gaussMarginalJ_moment_bound hnu hhead hIm hIa
  have hM := gaussMoment_le_dirichlet_amp hnu hV hL hsupp
  set D := gaussDirichlet nu V with hD
  set A := gaussAmp nu V with hA
  set M := gaussMoment nu V with hMdef
  have hDnn : 0 ≤ D := gaussDirichlet_nonneg nu V
  have hAnn : 0 ≤ A := gaussAmp_nonneg nu V
  -- the marginal scalar is dominated by half the Dirichlet energy plus a
  -- strictly sub-critical fraction of the amplitude
  have hJle : -gaussMarginalJ nu V p ≤ M / (32 * nu) + K ^ 2 * A / (2 * nu) :=
    le_trans (neg_le_abs _) hJ
  have hkey : nu * D + (1 / 2) * A ≤ M / (32 * nu) + K ^ 2 * A / (2 * nu) := by
    have : -gaussMarginalJ nu V p = nu * D + (1 / 2) * A := by linarith [hid]
    linarith [hJle, this]
  have h32 : (0 : ℝ) < 32 * nu := by linarith
  have hMdiv : M / (32 * nu) ≤ (nu / 2) * D + (3 / 8) * A := by
    rw [div_le_iff₀ h32]
    nlinarith [hM, hnu]
  have hfinal : (nu / 2) * D + (1 / 8 - K ^ 2 / (2 * nu)) * A ≤ 0 := by
    have hKA : K ^ 2 * A / (2 * nu) = (K ^ 2 / (2 * nu)) * A := by ring
    rw [hKA] at hkey
    linarith [hkey, hMdiv]
  have hcoef : 0 < 1 / 8 - K ^ 2 / (2 * nu) := by
    rw [sub_pos, div_lt_div_iff₀ (by positivity : (0:ℝ) < 2 * nu) (by norm_num : (0:ℝ) < 8)]
    linarith
  have hAz : A = 0 := by
    by_contra hne
    have hApos : 0 < A := lt_of_le_of_ne hAnn (Ne.symm hne)
    nlinarith [hfinal, hApos, hDnn, hnu, hcoef]
  exact eq_zero_of_gaussAmp_eq_zero hV1.continuous hIa hAz

end ClayNS

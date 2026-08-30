/-
# Rigidity for stationary Gaussian similarity profiles

`FiniteProjectiveExpenditure.lean` reduces the C lane to two obligations:
compactness/equation passage, and **rigidity for the stationary similarity
limit**.  This file proves the second one under an explicit, quantitative,
*relative* smallness condition — no Liouville theorem for arbitrary ancient
solutions is invoked.

The mechanism is the one the whole programme uses: an exact identity plus a
relative contraction.  Pairing the stationary similarity equation

  `0 = ν∆V − ½y·∇V − ½V − (V·∇)V − ∇p`

with `V` in the Gaussian space `L²(ρ_ν)` and using

* `ClayNS.gauss_OU_energy_identity` — the linear part is the negative Gaussian
  Dirichlet form, `ν∫ρ⟪∆V,V⟫ − ½∫ρ⟪(y·∇)V,V⟫ = −ν∫ρ|∇V|²`, and
* `ClayNS.gauss_weighted_marginal_channel` — the nonlinear/pressure pairing is
  *computed*, `∫ρ⟪(V·∇)V+∇p,V⟫ = 𝒥(V,p) = (1/4ν)∫ρ⟪y,V⟫(|V|²+2p)`,

gives the exact identity

  `ν𝒟 + ½𝒜 + 𝒥 = 0`,   `𝒟 = ∫ρ|∇V|²`, `𝒜 = ∫ρ|V|²`.        (★)

Both `ν𝒟` and `½𝒜` are nonnegative, so the *entire* content of rigidity is
whether the computed marginal scalar `𝒥` is a strict relative contraction of
them.  It is, whenever the Bernoulli head `|V|²+2p` is dominated by `|V|` on
the support:

  `|𝒥| ≤ (L·K/(4ν))·𝒜`,

`L` the support radius and `K` the head domination constant.  Hence `L·K < 2ν`
forces `𝒜 = 0`, i.e. `V ≡ 0`.

## Results

* `ClayNS.IsStationarySimilarity` — the pointwise stationary similarity
  equation;
* `ClayNS.gaussDirichlet`, `ClayNS.gaussAmp` — the Gaussian Dirichlet energy
  and amplitude of a profile;
* `ClayNS.stationary_similarity_gauss_identity` — **(★)**, derived;
* `ClayNS.gaussMarginalJ_relative_bound` — the marginal scalar is relatively
  bounded by the amplitude, `|𝒥| ≤ (LK/(4ν))𝒜`;
* `ClayNS.stationary_rigidity_of_relative_bound` — the abstract relative
  contraction: `ν𝒟 + ½𝒜 + 𝒥 = 0` and `|𝒥| ≤ θ𝒜` with `θ < ½` force
  `𝒜 = 𝒟 = 0`;
* `ClayNS.stationary_similarity_rigidity` — the physical rigidity theorem: a
  compactly supported stationary similarity profile with `L·K < 2ν` vanishes
  identically.

## Scope

The profile is taken compactly supported (radius `L`), which is what makes the
Gaussian integrations by parts unconditional; the smallness condition
`L·K < 2ν` is then a genuine Reynolds-type threshold, and no decay hypothesis
at infinity is smuggled in.  Extending the same identity to Gaussian-decaying
profiles is a matter of the integration-by-parts hypotheses only: the algebra
of (★) and of the relative contraction is unchanged.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GaussianOrnsteinUhlenbeck
import RequestProject.NavierStokes.GaussianMarginalTelescope

open MeasureTheory Set
open RealInnerProductSpace
open scoped BigOperators

noncomputable section

namespace ClayNS

/-! ## The stationary similarity problem -/

/-- The Gaussian Dirichlet energy `𝒟 = ∫ρ_ν|∇V|²` of a profile. -/
def gaussDirichlet (nu : ℝ) (V : E3 → E3) : ℝ :=
  ∫ y : E3, gaussWeight nu y * gradSqSpace V y

/-- The Gaussian amplitude `𝒜 = ∫ρ_ν|V|²` of a profile. -/
def gaussAmp (nu : ℝ) (V : E3 → E3) : ℝ :=
  ∫ y : E3, gaussWeight nu y * ‖V y‖ ^ 2

/-- **The stationary similarity equation**
`0 = ν∆V − ½y·∇V − ½V − (V·∇)V − ∇p`, pointwise. -/
def IsStationarySimilarity (nu : ℝ) (V : E3 → E3) (p : E3 → ℝ) : Prop :=
  ∀ y : E3, nu • lapSpace V y - (1 / 2 : ℝ) • dilTransport V y - (1 / 2 : ℝ) • V y
      - (advSpace V y + gradSpace p y) = 0

lemma gaussAmp_nonneg (nu : ℝ) (V : E3 → E3) : 0 ≤ gaussAmp nu V := by
  refine integral_nonneg fun y => ?_
  have := (gaussWeight_pos nu y).le
  positivity

lemma gaussDirichlet_nonneg (nu : ℝ) (V : E3 → E3) : 0 ≤ gaussDirichlet nu V := by
  refine integral_nonneg fun y => ?_
  have := (gaussWeight_pos nu y).le
  have := gradSqSpace_nonneg V y
  positivity

/-! ## The exact identity (★) -/

/-- Continuity of the interaction density `ρ⟪(V·∇)V+∇p,V⟫`. -/
lemma continuous_gauss_interaction {nu : ℝ} {V : E3 → E3} {p : E3 → ℝ}
    (hV : ContDiff ℝ (1 : ℕ) V) (hp : ContDiff ℝ (1 : ℕ) p) :
    Continuous fun y : E3 => gaussWeight nu y * ⟪advSpace V y + gradSpace p y, V y⟫ := by
  refine (contDiff_gaussWeight_one nu).continuous.mul (Continuous.inner ?_ hV.continuous)
  refine Continuous.add ?_ ?_
  · refine continuous_finset_sum _ fun i _ => ?_
    exact Continuous.smul
      ((continuous_apply i).comp
        ((EuclideanSpace.equiv (Fin 3) ℝ).continuous.comp hV.continuous))
      ((hV.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  · refine continuous_finset_sum _ fun i _ => ?_
    exact ((hp.continuous_fderiv (by norm_num)).clm_apply continuous_const).smul
      continuous_const

lemma integrable_gauss_interaction {nu L : ℝ} {V : E3 → E3} {p : E3 → ℝ}
    (hV : ContDiff ℝ (1 : ℕ) V) (hp : ContDiff ℝ (1 : ℕ) p)
    (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0) :
    Integrable fun y : E3 => gaussWeight nu y * ⟪advSpace V y + gradSpace p y, V y⟫ := by
  refine integrable_of_continuous_vanishing_outside (L := L)
    (continuous_gauss_interaction hV hp) ?_
  intro y hy
  simp [hsupp y hy.le]

/-- **(★) The stationary Gaussian similarity identity.**  For a compactly
supported, divergence-free `C²` profile solving the stationary similarity
equation with a `C¹` pressure,

  `ν𝒟 + ½𝒜 + 𝒥 = 0`.

Both the Dirichlet energy and the amplitude enter with a positive sign; the
whole of the nonlinearity and the pressure is the computed scalar `𝒥`. -/
theorem stationary_similarity_gauss_identity {nu : ℝ} (hnu : 0 < nu)
    {V : E3 → E3} {p : E3 → ℝ}
    (hV : ContDiff ℝ (2 : ℕ) V) (hp : ContDiff ℝ (1 : ℕ) p)
    (hdiv : ∀ y, divSpace V y = 0)
    {L : ℝ} (hL : 0 < L) (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0)
    (heq : IsStationarySimilarity nu V p) :
    nu * gaussDirichlet nu V + (1 / 2) * gaussAmp nu V + gaussMarginalJ nu V p = 0 := by
  have hnu' : nu ≠ 0 := ne_of_gt hnu
  have hV1 : ContDiff ℝ (1 : ℕ) V := hV.of_le (by norm_num)
  -- the four Gaussian densities
  have hI1 : Integrable (fun y : E3 => gaussWeight nu y * ⟪lapSpace V y, V y⟫) :=
    integrable_gauss_lap (nu := nu) hV hsupp
  have hI2 : Integrable (fun y : E3 => gaussWeight nu y * ⟪dilTransport V y, V y⟫) :=
    integrable_gauss_dil (nu := nu) hV hsupp
  have hI3 : Integrable (fun y : E3 => gaussWeight nu y * ‖V y‖ ^ 2) :=
    integrable_gauss_amp (nu := nu) hV1.continuous hsupp
  have hI4 : Integrable
      (fun y : E3 => gaussWeight nu y * ⟪advSpace V y + gradSpace p y, V y⟫) :=
    integrable_gauss_interaction (nu := nu) hV1 hp hsupp
  -- the pointwise pairing of the equation with `V`
  have hpt : ∀ y : E3, nu * (gaussWeight nu y * ⟪lapSpace V y, V y⟫)
      - (1 / 2) * (gaussWeight nu y * ⟪dilTransport V y, V y⟫)
      - (1 / 2) * (gaussWeight nu y * ‖V y‖ ^ 2)
      - gaussWeight nu y * ⟪advSpace V y + gradSpace p y, V y⟫ = 0 := by
    intro y
    have h := congrArg (fun u : E3 => (⟪u, V y⟫ : ℝ)) (heq y)
    simp only [inner_sub_left, real_inner_smul_left, inner_zero_left] at h
    have hself : (⟪V y, V y⟫ : ℝ) = ‖V y‖ ^ 2 := real_inner_self_eq_norm_sq _
    rw [hself] at h
    have hw : gaussWeight nu y * (nu * ⟪lapSpace V y, V y⟫
        - 1 / 2 * ⟪dilTransport V y, V y⟫ - 1 / 2 * ‖V y‖ ^ 2
        - ⟪advSpace V y + gradSpace p y, V y⟫) = gaussWeight nu y * 0 := by
      rw [h]
    rw [mul_zero] at hw
    linarith [hw]
  -- integrate
  have hzero : (∫ y : E3, (nu * (gaussWeight nu y * ⟪lapSpace V y, V y⟫)
      - (1 / 2) * (gaussWeight nu y * ⟪dilTransport V y, V y⟫)
      - (1 / 2) * (gaussWeight nu y * ‖V y‖ ^ 2)
      - gaussWeight nu y * ⟪advSpace V y + gradSpace p y, V y⟫)) = 0 :=
    (integral_congr_ae (Filter.Eventually.of_forall hpt)).trans (integral_zero _ _)
  have hs1 : Integrable (fun y : E3 => nu * (gaussWeight nu y * ⟪lapSpace V y, V y⟫)) :=
    hI1.const_mul _
  have hs2 : Integrable
      (fun y : E3 => (1 / 2 : ℝ) * (gaussWeight nu y * ⟪dilTransport V y, V y⟫)) :=
    hI2.const_mul _
  have hs3 : Integrable
      (fun y : E3 => (1 / 2 : ℝ) * (gaussWeight nu y * ‖V y‖ ^ 2)) := hI3.const_mul _
  have hs12 : Integrable (fun y : E3 => nu * (gaussWeight nu y * ⟪lapSpace V y, V y⟫)
      - (1 / 2 : ℝ) * (gaussWeight nu y * ⟪dilTransport V y, V y⟫)) := hs1.sub hs2
  have hs123 : Integrable (fun y : E3 => nu * (gaussWeight nu y * ⟪lapSpace V y, V y⟫)
      - (1 / 2 : ℝ) * (gaussWeight nu y * ⟪dilTransport V y, V y⟫)
      - (1 / 2 : ℝ) * (gaussWeight nu y * ‖V y‖ ^ 2)) := hs12.sub hs3
  rw [integral_sub hs123 hI4, integral_sub hs12 hs3, integral_sub hs1 hs2,
    integral_const_mul, integral_const_mul, integral_const_mul] at hzero
  -- the two exact identities
  have hOU := gauss_OU_energy_identity hnu hV hL hsupp
  have hmarg := gauss_weighted_marginal_channel hnu' hV1 hp hdiv hL hsupp
  rw [gaussDirichlet, gaussAmp, gaussMarginalJ, ← hmarg]
  linarith [hzero, hOU]

/-! ## The marginal scalar is a relative contraction of the amplitude -/

/-- **`|𝒥| ≤ (LK/(4ν))·𝒜`.**  If the Bernoulli head `|V|²+2p` is dominated by
`K|V|` and the profile is supported in the ball of radius `L`, the computed
marginal scalar is *relatively* bounded by the Gaussian amplitude.  (On the
support `|⟪y,V⟫| ≤ L|V|`, so the integrand is at most `LK ρ|V|²`.) -/
theorem gaussMarginalJ_relative_bound {nu L K : ℝ} (hnu : 0 < nu) (hL : 0 ≤ L)
    {V : E3 → E3} {p : E3 → ℝ}
    (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0)
    (hhead : ∀ y : E3, |‖V y‖ ^ 2 + 2 * p y| ≤ K * ‖V y‖)
    (hI3 : Integrable (fun y : E3 => gaussWeight nu y * ‖V y‖ ^ 2)) :
    |gaussMarginalJ nu V p| ≤ (L * K / (4 * nu)) * gaussAmp nu V := by
  have hdom : ∀ y : E3, ‖gaussWeight nu y * (⟪y, V y⟫ * (‖V y‖ ^ 2 + 2 * p y))‖
      ≤ (L * K) * (gaussWeight nu y * ‖V y‖ ^ 2) := by
    intro y
    have hwpos := (gaussWeight_pos nu y).le
    by_cases hy : L ≤ ‖y‖
    · simp [hsupp y hy]
    · have hyL : ‖y‖ ≤ L := le_of_lt (lt_of_not_ge hy)
      have hcs : |(⟪y, V y⟫ : ℝ)| ≤ ‖y‖ * ‖V y‖ := abs_real_inner_le_norm _ _
      have h1 : |(⟪y, V y⟫ : ℝ)| ≤ L * ‖V y‖ :=
        hcs.trans (mul_le_mul_of_nonneg_right hyL (norm_nonneg _))
      have h2 := hhead y
      have hprod : |(⟪y, V y⟫ : ℝ)| * |‖V y‖ ^ 2 + 2 * p y| ≤ (L * ‖V y‖) * (K * ‖V y‖) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      calc ‖gaussWeight nu y * (⟪y, V y⟫ * (‖V y‖ ^ 2 + 2 * p y))‖
          = gaussWeight nu y * (|(⟪y, V y⟫ : ℝ)| * |‖V y‖ ^ 2 + 2 * p y|) := by
            simp [Real.norm_eq_abs, abs_of_nonneg hwpos]
        _ ≤ gaussWeight nu y * ((L * ‖V y‖) * (K * ‖V y‖)) :=
            mul_le_mul_of_nonneg_left hprod hwpos
        _ = (L * K) * (gaussWeight nu y * ‖V y‖ ^ 2) := by ring
  have hg : Integrable (fun y : E3 => (L * K) * (gaussWeight nu y * ‖V y‖ ^ 2)) :=
    hI3.const_mul _
  have hle := norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hdom)
  rw [integral_const_mul] at hle
  have habs : |∫ y : E3, gaussWeight nu y * (⟪y, V y⟫ * (‖V y‖ ^ 2 + 2 * p y))|
      ≤ (L * K) * gaussAmp nu V := by
    simpa [Real.norm_eq_abs, gaussAmp] using hle
  have hquot : (0 : ℝ) < 4 * nu := by linarith
  rw [gaussMarginalJ, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (4 * nu))]
  calc (1 / (4 * nu)) * |∫ y : E3, gaussWeight nu y * (⟪y, V y⟫ * (‖V y‖ ^ 2 + 2 * p y))|
      ≤ (1 / (4 * nu)) * ((L * K) * gaussAmp nu V) := by
        exact mul_le_mul_of_nonneg_left habs (by positivity)
    _ = (L * K / (4 * nu)) * gaussAmp nu V := by ring

/-! ## Rigidity -/

/-- A continuous profile with vanishing Gaussian amplitude vanishes. -/
lemma eq_zero_of_gaussAmp_eq_zero {nu : ℝ} {V : E3 → E3} (hV : Continuous V)
    (hI3 : Integrable (fun y : E3 => gaussWeight nu y * ‖V y‖ ^ 2))
    (hA : gaussAmp nu V = 0) : ∀ y : E3, V y = 0 := by
  have hcont : Continuous fun y : E3 => gaussWeight nu y * ‖V y‖ ^ 2 :=
    (contDiff_gaussWeight_one nu).continuous.mul (hV.norm.pow 2)
  have hnn : ∀ y : E3, 0 ≤ gaussWeight nu y * ‖V y‖ ^ 2 := by
    intro y
    have := (gaussWeight_pos nu y).le
    positivity
  have hae : (fun y : E3 => gaussWeight nu y * ‖V y‖ ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun y => hnn y) hI3).mp (by simpa [gaussAmp] using hA)
  have hzero : (fun y : E3 => gaussWeight nu y * ‖V y‖ ^ 2) = 0 :=
    (hcont.ae_eq_iff_eq volume continuous_zero).mp hae
  intro y
  have hy : gaussWeight nu y * ‖V y‖ ^ 2 = 0 := congrFun hzero y
  have hwne : gaussWeight nu y ≠ 0 := ne_of_gt (gaussWeight_pos nu y)
  have hsq : ‖V y‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp hy with h | h
    · exact absurd h hwne
    · exact h
  have : ‖V y‖ = 0 := by nlinarith [norm_nonneg (V y)]
  exact norm_eq_zero.mp this


/-- **The abstract relative contraction.**  From the exact identity
`ν𝒟 + ½𝒜 + 𝒥 = 0` with `𝒟, 𝒜 ≥ 0` and a relative bound `|𝒥| ≤ θ𝒜` with
`θ < ½`, both the amplitude and the Dirichlet energy vanish. -/
theorem stationary_rigidity_of_relative_bound {nu D A J theta : ℝ} (hnu : 0 < nu)
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hid : nu * D + (1 / 2) * A + J = 0)
    (hth : theta < 1 / 2) (hJ : |J| ≤ theta * A) : A = 0 ∧ D = 0 := by
  have hJle : -J ≤ theta * A := by
    have := neg_le_abs J
    linarith
  have hkey : nu * D + (1 / 2 - theta) * A ≤ 0 := by
    have hJeq : J = -(nu * D + (1 / 2) * A) := by linarith
    have : nu * D + (1 / 2) * A ≤ theta * A := by
      rw [hJeq] at hJle
      linarith
    linarith
  have hAz : A = 0 := by
    by_contra hne
    have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hne)
    nlinarith [hkey, hApos, hD, hnu]
  refine ⟨hAz, ?_⟩
  by_contra hne
  have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hne)
  nlinarith [hkey, hAz, hDpos, hnu]

/-- **Rigidity for stationary Gaussian similarity profiles.**  A compactly
supported, divergence-free `C²` stationary similarity profile whose Bernoulli
head is dominated by `K|V|` on a support of radius `L` vanishes identically as
soon as

  `L·K < 2ν`.

This is the C-lane rigidity input, proved rather than assumed, and it is a
*relative* contraction statement: the computed marginal scalar is a fraction
`LK/(4ν) < ½` of the amplitude it would have to overcome. -/
theorem stationary_similarity_rigidity {nu L K : ℝ} (hnu : 0 < nu) (hL : 0 < L)
    {V : E3 → E3} {p : E3 → ℝ}
    (hV : ContDiff ℝ (2 : ℕ) V) (hp : ContDiff ℝ (1 : ℕ) p)
    (hdiv : ∀ y, divSpace V y = 0)
    (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0)
    (hhead : ∀ y : E3, |‖V y‖ ^ 2 + 2 * p y| ≤ K * ‖V y‖)
    (heq : IsStationarySimilarity nu V p)
    (hsmall : L * K < 2 * nu) :
    ∀ y : E3, V y = 0 := by
  have hV1 : ContDiff ℝ (1 : ℕ) V := hV.of_le (by norm_num)
  have hI3 : Integrable (fun y : E3 => gaussWeight nu y * ‖V y‖ ^ 2) :=
    integrable_gauss_amp (nu := nu) hV1.continuous hsupp
  have hid := stationary_similarity_gauss_identity hnu hV hp hdiv hL hsupp heq
  have hJ := gaussMarginalJ_relative_bound hnu hL.le hsupp hhead hI3
  have hth : L * K / (4 * nu) < 1 / 2 := by
    rw [div_lt_iff₀ (by linarith : (0:ℝ) < 4 * nu)]
    linarith
  obtain ⟨hAz, -⟩ := stationary_rigidity_of_relative_bound (nu := nu) hnu
    (gaussDirichlet_nonneg nu V) (gaussAmp_nonneg nu V) hid hth hJ
  exact eq_zero_of_gaussAmp_eq_zero hV1.continuous hI3 hAz

/-- **Rigidity from the identity alone.**  The same relative contraction, stated
directly from (★) rather than from the differential equation: any continuous
profile whose Gaussian densities satisfy `ν𝒟 + ½𝒜 + 𝒥 = 0` with `𝒟 ≥ 0` and a
relative bound `|𝒥| ≤ θ𝒜`, `θ < ½`, is trivial.  This is the form to use for
profiles that are not compactly supported but for which the two Gaussian
integrations by parts are available. -/
theorem stationary_similarity_rigidity_of_identity {nu theta D J : ℝ} (hnu : 0 < nu)
    {V : E3 → E3} (hcont : Continuous V)
    (hI3 : Integrable (fun y : E3 => gaussWeight nu y * ‖V y‖ ^ 2))
    (hD : 0 ≤ D) (hid : nu * D + (1 / 2) * gaussAmp nu V + J = 0)
    (hth : theta < 1 / 2) (hJ : |J| ≤ theta * gaussAmp nu V) :
    ∀ y : E3, V y = 0 := by
  obtain ⟨hAz, -⟩ := stationary_rigidity_of_relative_bound (nu := nu) hnu hD
    (gaussAmp_nonneg nu V) hid hth hJ
  exact eq_zero_of_gaussAmp_eq_zero hcont hI3 hAz

end ClayNS

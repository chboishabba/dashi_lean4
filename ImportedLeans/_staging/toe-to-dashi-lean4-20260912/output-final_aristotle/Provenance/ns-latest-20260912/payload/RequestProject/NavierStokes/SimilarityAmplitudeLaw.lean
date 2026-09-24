/-
# The amplitude law: the marginal scalar `𝒥` computed in closed form

The marginal channel of the A lane is `⟪N,P_VW⟫ = (A′/2A)·𝒥` with

  `𝒥(V,p) = (1/4ν)∫ρ_ν⟪y,V⟫(|V|²+2p)`

the scalar computed in `GaussianMarginalChannel.lean`.  The telescope of
`GaussianMarginalTelescope.lean` needs `𝒥` to split as an *amplitude law*
`F(A)` plus a controlled remainder.  This file **computes `𝒥` outright**.

Pairing the similarity equation

  `V_τ = ν∆V − ½y·∇V − ½V − (V·∇)V − ∇p`

with `V` in `L²(ρ_ν)` and using

* `ClayNS.gauss_OU_energy_identity` (the Gaussian Dirichlet form), and
* `ClayNS.gauss_weighted_marginal_channel` (the exact marginal computation),

gives

  `⟪W,V⟫_ρ = −ν𝒟 − ½𝒜 − 𝒥`,  i.e.  `𝒥 = −ν𝒟 − ½𝒜 − ½A′`,       (AL)

because `⟪W,V⟫_ρ = ½A′`.  So the marginal scalar is *not* an independent
unknown: it is the amplitude `𝒜 = A`, its derivative, and the Gaussian
Dirichlet energy.  In particular the amplitude law of the telescope is
`F(A) = −½A` and the whole remainder is `−ν𝒟 − ½A′`.

Substituting into the marginal channel gives its closed form

  `⟪N,P_VW⟫ = −¼A′ − (A′)²/(4A) − (ν𝒟/2)·(log A)′,                (MC)

whose first term is the exact derivative of `−A/4` and whose second has a
favourable sign.  Only the third term — the Dirichlet energy against the
logarithmic amplitude speed — carries any content, which is exactly the
"compute the marginal direction rather than estimate it" doctrine.

## Results

* `ClayNS.IsSimilarityEvolution` — the pointwise similarity equation with a
  prescribed similarity velocity `W = V_τ`;
* `ClayNS.similarity_amplitude_law` — **(AL)**, derived;
* `ClayNS.gaussMarginalJ_eq_of_ampDeriv` — (AL) in terms of `A′`;
* `ClayNS.marginal_channel_closed_form` — **(MC)**;
* `ClayNS.marginal_channel_le_of_closed_form` — the consequence used by the
  energy inequality: up to the exact derivative `−¼A′` the marginal channel is
  bounded above by `−(ν𝒟/2)(log A)′`, the `(A′)²/(4A)` term being a gain.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.StationarySimilarityRigidity

open MeasureTheory Set
open RealInnerProductSpace

noncomputable section

namespace ClayNS

/-- **The similarity equation with a prescribed similarity velocity.**
`W = ν∆V − ½y·∇V − ½V − (V·∇)V − ∇p`, pointwise; `W` plays the role of
`V_τ` at a frozen similarity time. -/
def IsSimilarityEvolution (nu : ℝ) (V W : E3 → E3) (p : E3 → ℝ) : Prop :=
  ∀ y : E3, W y = nu • lapSpace V y - (1 / 2 : ℝ) • dilTransport V y - (1 / 2 : ℝ) • V y
      - (advSpace V y + gradSpace p y)

/-- **(AL) The amplitude law.**  For a compactly supported, divergence-free
`C²` profile evolving by the similarity equation,

  `𝒥 = −ν𝒟 − ½𝒜 − ⟪W,V⟫_ρ`.

The computed marginal scalar is the Gaussian Dirichlet energy, the amplitude
and the amplitude's rate of change — nothing else. -/
theorem similarity_amplitude_law {nu : ℝ} (hnu : 0 < nu) {V W : E3 → E3} {p : E3 → ℝ}
    (hV : ContDiff ℝ (2 : ℕ) V) (hp : ContDiff ℝ (1 : ℕ) p)
    (hdiv : ∀ y, divSpace V y = 0)
    {L : ℝ} (hL : 0 < L) (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0)
    (heq : IsSimilarityEvolution nu V W p) :
    gaussMarginalJ nu V p = -(nu * gaussDirichlet nu V) - (1 / 2) * gaussAmp nu V
      - ∫ y : E3, gaussWeight nu y * ⟪W y, V y⟫ := by
  have hnu' : nu ≠ 0 := ne_of_gt hnu
  have hV1 : ContDiff ℝ (1 : ℕ) V := hV.of_le (by norm_num)
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
  have hpt : ∀ y : E3, gaussWeight nu y * ⟪W y, V y⟫
      = nu * (gaussWeight nu y * ⟪lapSpace V y, V y⟫)
        - (1 / 2) * (gaussWeight nu y * ⟪dilTransport V y, V y⟫)
        - (1 / 2) * (gaussWeight nu y * ‖V y‖ ^ 2)
        - gaussWeight nu y * ⟪advSpace V y + gradSpace p y, V y⟫ := by
    intro y
    have h := congrArg (fun u : E3 => (⟪u, V y⟫ : ℝ)) (heq y)
    simp only [inner_sub_left, real_inner_smul_left] at h
    have hself : (⟪V y, V y⟫ : ℝ) = ‖V y‖ ^ 2 := real_inner_self_eq_norm_sq _
    rw [hself] at h
    have hw : gaussWeight nu y * (⟪W y, V y⟫ : ℝ)
        = gaussWeight nu y * (nu * ⟪lapSpace V y, V y⟫
          - 1 / 2 * ⟪dilTransport V y, V y⟫ - 1 / 2 * ‖V y‖ ^ 2
          - ⟪advSpace V y + gradSpace p y, V y⟫) := by
      rw [h]
    rw [hw]
    ring
  -- integrate the pointwise identity
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
  have hint : (∫ y : E3, gaussWeight nu y * ⟪W y, V y⟫)
      = (∫ y : E3, (nu * (gaussWeight nu y * ⟪lapSpace V y, V y⟫)
          - (1 / 2) * (gaussWeight nu y * ⟪dilTransport V y, V y⟫)
          - (1 / 2) * (gaussWeight nu y * ‖V y‖ ^ 2)
          - gaussWeight nu y * ⟪advSpace V y + gradSpace p y, V y⟫)) :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [integral_sub hs123 hI4, integral_sub hs12 hs3, integral_sub hs1 hs2,
    integral_const_mul, integral_const_mul, integral_const_mul] at hint
  have hOU := gauss_OU_energy_identity hnu hV hL hsupp
  have hmarg := gauss_weighted_marginal_channel hnu' hV1 hp hdiv hL hsupp
  rw [gaussDirichlet, gaussAmp, gaussMarginalJ, ← hmarg]
  linarith [hint, hOU]

/-- **(AL) in terms of `A′`.**  With `⟪W,V⟫_ρ = ½A′` — the identity
`C = ½A′` of `GaussianMarginalTelescope.lean` — the amplitude law reads
`𝒥 = −ν𝒟 − ½A − ½A′`. -/
theorem gaussMarginalJ_eq_of_ampDeriv {nu Ad : ℝ} (hnu : 0 < nu) {V W : E3 → E3} {p : E3 → ℝ}
    (hV : ContDiff ℝ (2 : ℕ) V) (hp : ContDiff ℝ (1 : ℕ) p)
    (hdiv : ∀ y, divSpace V y = 0)
    {L : ℝ} (hL : 0 < L) (hsupp : ∀ y : E3, L ≤ ‖y‖ → V y = 0)
    (heq : IsSimilarityEvolution nu V W p)
    (hC : (∫ y : E3, gaussWeight nu y * ⟪W y, V y⟫) = Ad / 2) :
    gaussMarginalJ nu V p = -(nu * gaussDirichlet nu V) - (1 / 2) * gaussAmp nu V - Ad / 2 := by
  rw [similarity_amplitude_law hnu hV hp hdiv hL hsupp heq, hC]

/-- **(MC) The marginal channel in closed form.**  Substituting the amplitude
law into `⟪N,P_VW⟫ = (A′/2A)·𝒥` gives

  `⟪N,P_VW⟫ = −¼A′ − (A′)²/(4A) − (ν𝒟/2)(log A)′`.

The first term is the derivative of `−A/4`; the second is a gain; only the
third is a genuine channel. -/
theorem marginal_channel_closed_form {A Ad D J nu : ℝ} (hA : 0 < A)
    (hJ : J = -(nu * D) - (1 / 2) * A - Ad / 2) :
    (Ad / (2 * A)) * J
      = -(Ad / 4) - Ad ^ 2 / (4 * A) - (nu * D / 2) * (Ad / A) := by
  rw [hJ]
  field_simp
  ring

/-- The form in which the energy inequality consumes (MC): the marginal channel
is at most the exact derivative term `−¼A′` plus the Dirichlet-times-log-speed
term, the quadratic `(A′)²/(4A)` being a gain. -/
theorem marginal_channel_le_of_closed_form {A Ad D J nu : ℝ} (hA : 0 < A)
    (hJ : J = -(nu * D) - (1 / 2) * A - Ad / 2) :
    (Ad / (2 * A)) * J ≤ -(Ad / 4) - (nu * D / 2) * (Ad / A) := by
  rw [marginal_channel_closed_form hA hJ]
  have : 0 ≤ Ad ^ 2 / (4 * A) := by positivity
  linarith

end ClayNS

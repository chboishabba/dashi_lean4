/-
# `GaussianSimilarityInteractionClosure`: the whole A lane from one interaction package

The four A-side facets — near estimate, far estimate, marginal estimate and
flux splitting — are facets of a single decomposition of the physical
interaction

  `N = (V·∇)V + ∇P`,  `W = V_τ`,  `P_VW = (⟪V,W⟫/⟪V,V⟫)V`,

in Gaussian similarity variables.  This file assembles them into one theorem.

## The package

  `N = N_near + N_far + N_marg`,   `P_V N_marg = N_marg`,

* **(A-near)** `|⟪(N_near)_⊥, W_⊥⟫| ≤ η‖W_⊥‖²`, `η < 1` — relative contraction;
* **(A-far)**  `|⟪(N_far)_⊥, W_⊥⟫| ≤ R_far(τ)` with finite accumulated
  primitive;
* **(A-marg)** *not* an estimate: the marginal channel is the exact derivative
  supplied by `GaussianMarginalTelescope.lean`,
  `⟪N,P_VW⟫ = d/dτ(𝒦(A) + ℛ)` with `𝒦′(a) = F(a)/(2a)` and `ℛ` a primitive of
  the marginal remainder `(A′/2A)R`.

## What is new here relative to `SimilarityNearFarAbsorption.lean`

That file pays the marginal channel through `|⟪N,PW⟫|`, i.e. it still
*estimates* it.  Here the channel enters **signed**
(`ClayNS.similarity_energy_deriv_le_transverse_signed`), which is what allows
it to telescope: the accumulated marginal cost of the window is the variation
of a primitive, not the integral of an absolute value.

## Results

* `ClayNS.similarity_energy_deriv_le_transverse_signed` — identity (S) with the
  near/far absorption and the **signed** marginal channel:
  `ℋ′ ≤ −(1−η)‖W_⊥‖² − ⟪N,P_VW⟫ + R_far`.
* `ClayNS.gaussian_similarity_interaction_closure` — the closure: from the
  package above plus one *initial-time* energy bound,

    `(1−η)·∫‖W_⊥‖² ≤ C_H + C_tel + C_far`,

  the finite transverse (projective) expenditure that the rest of the chain
  consumes, together with a uniform bound on the similarity energy.
* `ClayNS.nearfar_cutoff_optimization` — the shared near/far optimization
  criterion: if at some cutoff the near gain and the far tail are both
  relative and sum to less than one, the pair is a strict relative
  contraction.  (`η_near(Δ) + η_far(Δ) < 1` for a judiciously chosen `Δ`.)
* `ClayNS.amplitude_marginal_remainder_absorbed`,
  `ClayNS.similarity_energy_deriv_le_marginal_absorbed`,
  `ClayNS.gaussian_similarity_interaction_closure_absorbed` — the marginal
  *remainder* of the telescope is paid quadratically against the marginal
  coercivity already present in identity (S): the accumulated marginal cost is
  the variation of the primitive `𝒦(A)` plus `∫R²/(2A)`, never an absolute
  bound on the channel.
* `ClayNS.transverse_pairing_eq` — the bridge to the concrete near/far bounds
  of `GaussianNearFarSplit.lean`.
* `ClayNS.clay_A_dyn_of_gaussian_similarity_interaction_closure` — the A-side
  gate `DynamicVelocityScaleDefect` from the same package, with
  * the marginal channel telescoped rather than bounded, and
  * the flux splitting **instantiated**: it is supplied in the scale-generator
    form `[F]₊ ≤ C_G·𝒢 + ℛ` together with the probe coercivity
    `c_*·𝒢 ≤ Δ_scale` proved in `PositiveParabolicEnergyScaleProbe.lean`, and
    converted internally by `ClayNS.scaleCharge_split_of_coercivity`.

Nothing physical is assumed beyond (A-near), (A-far) and the amplitude law
behind the telescope; those are exactly the remaining physical content of the
A lane.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GaussianMarginalTelescope
import RequestProject.NavierStokes.SimilarityNearFarScaleCharge

open Set
open RealInnerProductSpace

noncomputable section

namespace ClayNS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## The signed marginal channel -/

/-- **(S) with the near/far absorption and the signed marginal channel.**

  `−⟪W,W⟫ − ⟪N,W⟫ ≤ −(1−η)‖W_⊥‖² + (−⟪N,P W⟫ + R_far)`.

The marginal channel appears with its sign, so a primitive of it may be
subtracted off; that is what makes the telescope of
`GaussianMarginalTelescope.lean` usable inside the energy inequality. -/
theorem similarity_energy_deriv_le_transverse_signed (P : E →L[ℝ] E)
    (hidem : ∀ v : E, P (P v) = P v) (hsym : ∀ u v : E, ⟪P u, v⟫ = ⟪u, P v⟫)
    (Nnear Nfar Nmarg W : E) {eta Rfar : ℝ} (hmarg : P Nmarg = Nmarg)
    (hnear : |⟪Nnear - P Nnear, W - P W⟫| ≤ eta * ‖W - P W‖ ^ 2)
    (hfar : |⟪Nfar - P Nfar, W - P W⟫| ≤ Rfar) :
    -⟪W, W⟫ - ⟪Nnear + Nfar + Nmarg, W⟫
      ≤ -(1 - eta) * ‖W - P W‖ ^ 2
        + (-(⟪Nnear + Nfar + Nmarg, P W⟫ : ℝ) + Rfar) := by
  have hsplit := pairing_near_far_marginal_split P hidem hsym Nnear Nfar Nmarg W hmarg
  have hpy := pythagoras_proj P hidem hsym W
  have hW : (⟪W, W⟫ : ℝ) = ‖W‖ ^ 2 := real_inner_self_eq_norm_sq W
  have h1 : -(⟪Nnear - P Nnear, W - P W⟫ : ℝ) ≤ eta * ‖W - P W‖ ^ 2 := by
    have := neg_le_abs (⟪Nnear - P Nnear, W - P W⟫ : ℝ)
    linarith [hnear]
  have h2 : -(⟪Nfar - P Nfar, W - P W⟫ : ℝ) ≤ Rfar := by
    have := neg_le_abs (⟪Nfar - P Nfar, W - P W⟫ : ℝ)
    linarith [hfar]
  have hPW : (0 : ℝ) ≤ ‖P W‖ ^ 2 := sq_nonneg _
  rw [hW, hpy, hsplit]
  linarith

/-- **The transverse pairing forgets the projection of the first argument.**
For an orthogonal projection `P`, `⟪u − Pu, W − PW⟫ = ⟪u, W − PW⟫`.  This is
what lets the concrete near/far bounds of `GaussianNearFarSplit.lean`, which
pair the *whole* near (resp. far) field against the transverse velocity, be
used verbatim as the hypotheses (A-near), (A-far) of the closure. -/
theorem transverse_pairing_eq (P : E →L[ℝ] E)
    (hidem : ∀ v : E, P (P v) = P v) (hsym : ∀ u v : E, ⟪P u, v⟫ = ⟪u, P v⟫)
    (u W : E) : (⟪u - P u, W - P W⟫ : ℝ) = ⟪u, W - P W⟫ := by
  have hz : (⟪P u, W - P W⟫ : ℝ) = 0 := by
    rw [hsym u (W - P W), map_sub, hidem W, sub_self, inner_zero_right]
  rw [inner_sub_left, hz, sub_zero]

/-! ## The near/far cutoff optimization -/

/-- **The shared near/far optimization criterion.**  If at a given cutoff both
pieces are charged *relatively* to the transverse expenditure, with gains
`η_near` and `η_far` whose sum is `< 1`, then the total interaction is a strict
relative contraction of the expenditure.  This is the abstraction common to the
frequency-, shell- and log-frequency-separated settings: the cutoff itself is
the free parameter to be optimized. -/
theorem nearfar_cutoff_optimization (P : E →L[ℝ] E) (Nnear Nfar W : E)
    {etaNear etaFar : ℝ}
    (hnear : |⟪Nnear - P Nnear, W - P W⟫| ≤ etaNear * ‖W - P W‖ ^ 2)
    (hfar : |⟪Nfar - P Nfar, W - P W⟫| ≤ etaFar * ‖W - P W‖ ^ 2) :
    |⟪Nnear - P Nnear, W - P W⟫ + ⟪Nfar - P Nfar, W - P W⟫|
      ≤ (etaNear + etaFar) * ‖W - P W‖ ^ 2 := by
  have h := abs_add_le (⟪Nnear - P Nnear, W - P W⟫ : ℝ) ⟪Nfar - P Nfar, W - P W⟫
  nlinarith [hnear, hfar]

/-! ## The marginal remainder is absorbed by the marginal coercivity -/

/-- **The marginal remainder costs only `R²/2A`.**  With the amplitude
projection, `‖P_VW‖² = ⟪V,W⟫²/A`, so the marginal remainder of the telescope,
`(A′/2A)·R = (⟪V,W⟫/A)·R`, is paid by *half* the marginal coercivity that
identity (S) already contains:

  `−(⟪V,W⟫/A)·R ≤ ½‖P_VW‖² + R²/(2A)`.

Nothing absolute is used; the price is quadratic in the remainder. -/
theorem amplitude_marginal_remainder_absorbed {V W : E} (hVpos : (0 : ℝ) < ⟪V, V⟫)
    (Rm : ℝ) :
    -((⟪V, W⟫ / ⟪V, V⟫) * Rm)
      ≤ (1 / 2) * ‖amplitudeProj V W‖ ^ 2 + Rm ^ 2 / (2 * ⟪V, V⟫) := by
  have hP : ‖amplitudeProj V W‖ ^ 2 = (⟪V, W⟫ : ℝ) ^ 2 / ⟪V, V⟫ := by
    rw [amplitudeProj_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      ← real_inner_self_eq_norm_sq]
    field_simp
  rw [hP, ← sub_nonneg]
  have key : (1 / 2) * ((⟪V, W⟫ : ℝ) ^ 2 / ⟪V, V⟫) + Rm ^ 2 / (2 * ⟪V, V⟫)
      - -((⟪V, W⟫ / ⟪V, V⟫) * Rm) = ((⟪V, W⟫ : ℝ) + Rm) ^ 2 / (2 * ⟪V, V⟫) := by
    field_simp
    ring
  rw [key]
  exact div_nonneg (sq_nonneg _) (by linarith)

/-- **(S) with the marginal remainder absorbed.**  Suppose the marginal channel
has been telescoped,

  `⟪N, P_VW⟫ = 𝒦d + (⟪V,W⟫/A)·R`,

where `𝒦d` is the exact derivative produced by
`ClayNS.marginal_channel_telescope` and `R` is the marginal remainder.  Then

  `ℋ′ ≤ −½‖P_VW‖² − (1−η)‖W_⊥‖² + (−𝒦d + R²/(2A) + R_far)`,

so the marginal channel never needs an absolute bound: the exact part
telescopes and the remainder is paid quadratically against the marginal
coercivity that identity (S) already provides. -/
theorem similarity_energy_deriv_le_marginal_absorbed {V W Nnear Nfar Nmarg : E}
    {eta Rfar Kd Rm : ℝ} (hVpos : (0 : ℝ) < ⟪V, V⟫)
    (hmarg : amplitudeProj V Nmarg = Nmarg)
    (hnear : |⟪Nnear - amplitudeProj V Nnear, W - amplitudeProj V W⟫|
      ≤ eta * ‖W - amplitudeProj V W‖ ^ 2)
    (hfar : |⟪Nfar - amplitudeProj V Nfar, W - amplitudeProj V W⟫| ≤ Rfar)
    (hchan : (⟪Nnear + Nfar + Nmarg, amplitudeProj V W⟫ : ℝ)
      = Kd + (⟪V, W⟫ / ⟪V, V⟫) * Rm) :
    -⟪W, W⟫ - ⟪Nnear + Nfar + Nmarg, W⟫
      ≤ -(1 / 2) * ‖amplitudeProj V W‖ ^ 2
        - (1 - eta) * ‖W - amplitudeProj V W‖ ^ 2
        + (-Kd + Rm ^ 2 / (2 * ⟪V, V⟫) + Rfar) := by
  have hsplit := pairing_near_far_marginal_split (amplitudeProj V)
    (amplitudeProj_idem hVpos) (amplitudeProj_symm V) Nnear Nfar Nmarg W hmarg
  have hpy := pythagoras_proj (amplitudeProj V) (amplitudeProj_idem hVpos)
    (amplitudeProj_symm V) W
  have hW : (⟪W, W⟫ : ℝ) = ‖W‖ ^ 2 := real_inner_self_eq_norm_sq W
  have h1 : -(⟪Nnear - amplitudeProj V Nnear, W - amplitudeProj V W⟫ : ℝ)
      ≤ eta * ‖W - amplitudeProj V W‖ ^ 2 := by
    have := neg_le_abs (⟪Nnear - amplitudeProj V Nnear, W - amplitudeProj V W⟫ : ℝ)
    linarith [hnear]
  have h2 : -(⟪Nfar - amplitudeProj V Nfar, W - amplitudeProj V W⟫ : ℝ) ≤ Rfar := by
    have := neg_le_abs (⟪Nfar - amplitudeProj V Nfar, W - amplitudeProj V W⟫ : ℝ)
    linarith [hfar]
  have habs := amplitude_marginal_remainder_absorbed (V := V) (W := W) hVpos Rm
  rw [hW, hpy, hsplit, hchan]
  linarith

/-! ## The closure -/

/-- **`GaussianSimilarityInteractionClosure`.**

From the single interaction package

* the near part is a strict relative contraction of the transverse expenditure,
* the far part is a summable tail,
* the marginal channel is the exact derivative of `𝒦(A) + ℛ`
  (`ClayNS.marginal_channel_telescope`), so it costs only the *variation* of
  that primitive,
* the similarity energy is bounded at the initial similarity time,

one gets simultaneously the finite transverse expenditure

  `(1−η)(ℰ(τ₁) − ℰ(τ₀)) ≤ C_H + C_tel + C_far`,   `ℰ′ = ‖W_⊥‖²`,

and the uniform bound `ℋ ≤ C_H + C_tel + C_far` on the window.  With the
amplitude projection `P_V` the coercive quantity `‖W_⊥‖²` is literally the
scale-Gram defect `(AB − C²)/A`, i.e. the squared projective speed of the
normalized profile. -/
theorem gaussian_similarity_interaction_closure
    {Vcur Wcur Nnear Nfar Nmarg : ℝ → E}
    {Ecal Kprim Rmprim Rfprim Rfar : ℝ → ℝ}
    {t0 t1 eta CH Ctel Cfar : ℝ}
    (bil : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ u v : E, bil u v = bil v u)
    (hpsd : ∀ v : E, 0 ≤ bil v v)
    (h01 : t0 ≤ t1) (heta : eta ≤ 1)
    (hVpos : ∀ s, (0 : ℝ) < ⟪Vcur s, Vcur s⟫)
    (hV : ∀ s, HasDerivAt Vcur (Wcur s) s)
    (heq : ∀ s, ∀ w : E, ⟪Wcur s, w⟫
      = -bil (Vcur s) w - (1 / 2) * ⟪Vcur s, w⟫
        - ⟪Nnear s + Nfar s + Nmarg s, w⟫)
    (hmarg : ∀ s, amplitudeProj (Vcur s) (Nmarg s) = Nmarg s)
    (hnear : ∀ s, |⟪Nnear s - amplitudeProj (Vcur s) (Nnear s),
        Wcur s - amplitudeProj (Vcur s) (Wcur s)⟫|
      ≤ eta * ‖Wcur s - amplitudeProj (Vcur s) (Wcur s)‖ ^ 2)
    (hfar : ∀ s, |⟪Nfar s - amplitudeProj (Vcur s) (Nfar s),
        Wcur s - amplitudeProj (Vcur s) (Wcur s)⟫| ≤ Rfar s)
    (hEc : ∀ s ∈ Icc t0 t1,
      HasDerivAt Ecal (‖Wcur s - amplitudeProj (Vcur s) (Wcur s)‖ ^ 2) s)
    -- the marginal channel telescopes: it is the derivative of `𝒦(A) + ℛ`
    (htel : ∀ s ∈ Icc t0 t1, HasDerivAt (fun u => Kprim u + Rmprim u)
      (⟪Nnear s + Nfar s + Nmarg s, amplitudeProj (Vcur s) (Wcur s)⟫ : ℝ) s)
    (hRf : ∀ s ∈ Icc t0 t1, HasDerivAt Rfprim (Rfar s) s)
    (hinit : (1 / 2) * bil (Vcur t0) (Vcur t0) + (1 / 4) * ⟪Vcur t0, Vcur t0⟫ ≤ CH)
    (hmargtel : ∀ s ∈ Icc t0 t1, -((Kprim s + Rmprim s) - (Kprim t0 + Rmprim t0)) ≤ Ctel)
    (hfartot : ∀ s ∈ Icc t0 t1, Rfprim s - Rfprim t0 ≤ Cfar) :
    (1 - eta) * (Ecal t1 - Ecal t0) ≤ CH + Ctel + Cfar
      ∧ ∀ s ∈ Icc t0 t1,
          (1 / 2) * bil (Vcur s) (Vcur s) + (1 / 4) * ⟪Vcur s, Vcur s⟫
            ≤ CH + Ctel + Cfar := by
  classical
  set Hcal : ℝ → ℝ := fun s =>
    (1 / 2) * bil (Vcur s) (Vcur s) + (1 / 4) * ⟪Vcur s, Vcur s⟫ with hHcal
  set Hd : ℝ → ℝ := fun s =>
    -⟪Wcur s, Wcur s⟫ - ⟪Nnear s + Nfar s + Nmarg s, Wcur s⟫ with hHd
  set q : ℝ → ℝ := fun s =>
    ‖Wcur s - amplitudeProj (Vcur s) (Wcur s)‖ ^ 2 with hq
  set rem : ℝ → ℝ := fun s =>
    -(⟪Nnear s + Nfar s + Nmarg s, amplitudeProj (Vcur s) (Wcur s)⟫ : ℝ) + Rfar s with hrem
  set Rcal : ℝ → ℝ := fun s => -(Kprim s + Rmprim s) + Rfprim s with hRcal
  have hH : ∀ s ∈ Icc t0 t1, HasDerivAt Hcal (Hd s) s := fun s _ =>
    similarity_energy_identity bil hsymm (hV s) (heq s)
  have hHle : ∀ s ∈ Icc t0 t1, Hd s ≤ -(1 - eta) * q s + rem s := fun s _ =>
    similarity_energy_deriv_le_transverse_signed (amplitudeProj (Vcur s))
      (amplitudeProj_idem (hVpos s)) (amplitudeProj_symm (Vcur s))
      (Nnear s) (Nfar s) (Nmarg s) (Wcur s) (hmarg s) (hnear s) (hfar s)
  have hR : ∀ s ∈ Icc t0 t1, HasDerivAt Rcal (rem s) s := by
    intro s hs
    exact ((htel s hs).neg).add (hRf s hs)
  have hRvar : ∀ s ∈ Icc t0 t1, Rcal s - Rcal t0 ≤ Ctel + Cfar := by
    intro s hs
    simp only [hRcal]
    linarith [hmargtel s hs, hfartot s hs]
  have hnn : ∀ s, 0 ≤ Hcal s := by
    intro s
    exact similarity_energy_nonneg bil hpsd (Vcur s)
  refine ⟨?_, ?_⟩
  · have hexp := similarity_transverse_expenditure (Hcal := Hcal) (Ecal := Ecal)
      (Rcal := Rcal) (Hd := Hd) (q := q) (rem := rem) (eta := eta) h01 hH hHle hEc hR
    have hi : Hcal t0 ≤ CH := hinit
    have h1 : Hcal t0 - Hcal t1 ≤ CH := by
      have := hnn t1
      linarith
    have h2 := hRvar t1 ⟨h01, le_rfl⟩
    linarith
  · intro s hs
    have hqnn : ∀ u ∈ Icc t0 t1, 0 ≤ q u := fun u _ => sq_nonneg _
    have hbound := similarity_energy_uniform_bound (Hcal := Hcal) (Rcal := Rcal)
      (Hd := Hd) (q := q) (rem := rem) (t0 := t0) (t1 := t1) heta hqnn hH hHle hR s hs
    have hRs := hRvar s hs
    have hi : Hcal t0 ≤ CH := hinit
    show Hcal s ≤ CH + Ctel + Cfar
    linarith

/-- **The closure with the marginal remainder absorbed.**

Same as `ClayNS.gaussian_similarity_interaction_closure`, except that the
marginal channel is only required to be telescoped *up to a remainder*,

  `⟪N,P_VW⟫ = 𝒦d + (⟪V,W⟫/A)·R`,

and that remainder is paid quadratically against the marginal coercivity
(`ClayNS.amplitude_marginal_remainder_absorbed`).  The accumulated marginal
cost is then the variation of the primitive `𝒦` plus `∫R²/(2A)` — a quadratic
budget, never an absolute bound on the channel. -/
theorem gaussian_similarity_interaction_closure_absorbed
    {Vcur Wcur Nnear Nfar Nmarg : ℝ → E}
    {Ecal Kprim Qprim Rfprim Kd Rm Rfar : ℝ → ℝ}
    {t0 t1 eta CH Ctel Cq Cfar : ℝ}
    (bil : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ u v : E, bil u v = bil v u)
    (hpsd : ∀ v : E, 0 ≤ bil v v)
    (h01 : t0 ≤ t1)
    (hVpos : ∀ s, (0 : ℝ) < ⟪Vcur s, Vcur s⟫)
    (hV : ∀ s, HasDerivAt Vcur (Wcur s) s)
    (heq : ∀ s, ∀ w : E, ⟪Wcur s, w⟫
      = -bil (Vcur s) w - (1 / 2) * ⟪Vcur s, w⟫
        - ⟪Nnear s + Nfar s + Nmarg s, w⟫)
    (hmarg : ∀ s, amplitudeProj (Vcur s) (Nmarg s) = Nmarg s)
    (hnear : ∀ s, |⟪Nnear s - amplitudeProj (Vcur s) (Nnear s),
        Wcur s - amplitudeProj (Vcur s) (Wcur s)⟫|
      ≤ eta * ‖Wcur s - amplitudeProj (Vcur s) (Wcur s)‖ ^ 2)
    (hfar : ∀ s, |⟪Nfar s - amplitudeProj (Vcur s) (Nfar s),
        Wcur s - amplitudeProj (Vcur s) (Wcur s)⟫| ≤ Rfar s)
    (hchan : ∀ s, (⟪Nnear s + Nfar s + Nmarg s, amplitudeProj (Vcur s) (Wcur s)⟫ : ℝ)
      = Kd s + (⟪Vcur s, Wcur s⟫ / ⟪Vcur s, Vcur s⟫) * Rm s)
    (hEc : ∀ s ∈ Icc t0 t1,
      HasDerivAt Ecal (‖Wcur s - amplitudeProj (Vcur s) (Wcur s)‖ ^ 2) s)
    (hKp : ∀ s ∈ Icc t0 t1, HasDerivAt Kprim (Kd s) s)
    (hQp : ∀ s ∈ Icc t0 t1, HasDerivAt Qprim (Rm s ^ 2 / (2 * ⟪Vcur s, Vcur s⟫)) s)
    (hRf : ∀ s ∈ Icc t0 t1, HasDerivAt Rfprim (Rfar s) s)
    (hinit : (1 / 2) * bil (Vcur t0) (Vcur t0) + (1 / 4) * ⟪Vcur t0, Vcur t0⟫ ≤ CH)
    (hKtel : -(Kprim t1 - Kprim t0) ≤ Ctel)
    (hQtot : Qprim t1 - Qprim t0 ≤ Cq)
    (hfartot : Rfprim t1 - Rfprim t0 ≤ Cfar) :
    (1 - eta) * (Ecal t1 - Ecal t0) ≤ CH + Ctel + Cq + Cfar := by
  set Hcal : ℝ → ℝ := fun s =>
    (1 / 2) * bil (Vcur s) (Vcur s) + (1 / 4) * ⟪Vcur s, Vcur s⟫ with hHcal
  set Hd : ℝ → ℝ := fun s =>
    -⟪Wcur s, Wcur s⟫ - ⟪Nnear s + Nfar s + Nmarg s, Wcur s⟫ with hHd
  set q : ℝ → ℝ := fun s =>
    ‖Wcur s - amplitudeProj (Vcur s) (Wcur s)‖ ^ 2 with hq
  set rem : ℝ → ℝ := fun s =>
    -Kd s + Rm s ^ 2 / (2 * ⟪Vcur s, Vcur s⟫) + Rfar s with hrem
  set Rcal : ℝ → ℝ := fun s => -Kprim s + Qprim s + Rfprim s with hRcal
  have hH : ∀ s ∈ Icc t0 t1, HasDerivAt Hcal (Hd s) s := fun s _ =>
    similarity_energy_identity bil hsymm (hV s) (heq s)
  have hHle : ∀ s ∈ Icc t0 t1, Hd s ≤ -(1 - eta) * q s + rem s := by
    intro s _
    have h := similarity_energy_deriv_le_marginal_absorbed (hVpos s) (hmarg s)
      (hnear s) (hfar s) (hchan s)
    have hP : (0 : ℝ) ≤ ‖amplitudeProj (Vcur s) (Wcur s)‖ ^ 2 := sq_nonneg _
    simp only [hHd, hq, hrem]
    linarith
  have hR : ∀ s ∈ Icc t0 t1, HasDerivAt Rcal (rem s) s := by
    intro s hs
    exact (((hKp s hs).neg).add (hQp s hs)).add (hRf s hs)
  have hexp := similarity_transverse_expenditure (Hcal := Hcal) (Ecal := Ecal)
    (Rcal := Rcal) (Hd := Hd) (q := q) (rem := rem) (eta := eta) h01 hH hHle hEc hR
  have hi : Hcal t0 ≤ CH := hinit
  have hnn : 0 ≤ Hcal t1 := similarity_energy_nonneg bil hpsd (Vcur t1)
  have hRvar : Rcal t1 - Rcal t0 ≤ Ctel + Cq + Cfar := by
    simp only [hRcal]
    linarith [hKtel, hQtot, hfartot]
  linarith

/-! ## The A-side gate -/

/-- **`A_dyn` from the interaction closure.**

This is `ClayNS.clay_A_dyn_of_amplitude_nearfar_absorption` with two changes,
both of them removals of independently supplied inputs.

1. The marginal channel is no longer bounded in absolute value: it enters
   *signed*, and is discharged by the telescope of
   `GaussianMarginalTelescope.lean` — `htel` says exactly that `⟪N, P_VW⟫` is
   the derivative of `𝒦(A) + ℛ`, and the only quantitative input about it is
   the *variation* `C_tel` of that primitive.
2. The flux splitting is instantiated: it is supplied in the scale-generator
   form `[F]₊ ≤ C_G·𝒢 + ℛ` together with the probe coercivity
   `c_*·𝒢 ≤ Δ_scale` (proved for the actual parabolic energy probe in
   `PositiveParabolicEnergyScaleProbe.lean`), and converted here by
   `ClayNS.scaleCharge_split_of_coercivity`. -/
theorem clay_A_dyn_of_gaussian_similarity_interaction_closure
    {Ehil : Type*} [NormedAddCommGroup Ehil] [InnerProductSpace ℝ Ehil]
    {G : ℕ → ℝ → E3 → ℝ} {M : ℕ → ℝ} {t : ℕ → ℝ} {x : ℕ → E3}
    {F Qd Gcal Delta Rem Phi Psi Theta Ecal Kprim Rmprim Rfprim Rfar : ℕ → ℝ → ℝ}
    {Vsim Wsim Nnear Nfar Nmarg : ℕ → ℝ → Ehil}
    {eps CG cstar Crem K eta Cdrop Ctel Cfar : ℝ}
    (bil : Ehil →L[ℝ] Ehil →L[ℝ] ℝ) (hsymm : ∀ u v : Ehil, bil u v = bil v u)
    (hpsd : ∀ v : Ehil, 0 ≤ bil v v)
    (hVpos : ∀ k s, (0 : ℝ) < ⟪Vsim k s, Vsim k s⟫)
    (heps : 0 < eps) (hM : ∀ k, 0 < M k)
    (hCG : 0 ≤ CG) (hcstar : 0 < cstar)
    (hK : 0 ≤ K) (heta1 : eta < 1)
    (hle : ∀ k, 1 / M k ≤ cascadeStart (M k))
    (hpos : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)), 0 < QgradCyl (G k) (t k) (x k) r)
    (hderiv : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      HasDerivAt (fun s => QgradCyl (G k) (t k) (x k) s) (Qd k r) r)
    (hexact : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)), r * Qd k r = F k r)
    (hFG : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      max (F k r) 0 ≤ CG * Gcal k r + Rem k r)
    (hcoer : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      cstar * Gcal k r ≤ Delta k r)
    (hPhi : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      HasDerivAt (Phi k) (nsLogDefect (F k) (fun s => QgradCyl (G k) (t k) (x k) s) r) r)
    (hPsi : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      HasDerivAt (Psi k) (Delta k r / (r * QgradCyl (G k) (t k) (x k) r)) r)
    (hTheta : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      HasDerivAt (Theta k) (Rem k r / (r * QgradCyl (G k) (t k) (x k) r)) r)
    (hV : ∀ k s, HasDerivAt (Vsim k) (Wsim k s) s)
    (heq : ∀ k s, ∀ w : Ehil, ⟪Wsim k s, w⟫
      = -bil (Vsim k s) w - (1 / 2) * ⟪Vsim k s, w⟫
        - ⟪Nnear k s + Nfar k s + Nmarg k s, w⟫)
    (hmarg : ∀ k s, amplitudeProj (Vsim k s) (Nmarg k s) = Nmarg k s)
    (hnear : ∀ k s,
      |⟪Nnear k s - amplitudeProj (Vsim k s) (Nnear k s),
        Wsim k s - amplitudeProj (Vsim k s) (Wsim k s)⟫|
      ≤ eta * ((⟪Vsim k s, Vsim k s⟫ * ⟪Wsim k s, Wsim k s⟫ - ⟪Vsim k s, Wsim k s⟫ ^ 2)
          / ⟪Vsim k s, Vsim k s⟫))
    (hfar : ∀ k s,
      |⟪Nfar k s - amplitudeProj (Vsim k s) (Nfar k s),
        Wsim k s - amplitudeProj (Vsim k s) (Wsim k s)⟫| ≤ Rfar k s)
    (hEc : ∀ k, ∀ s : ℝ, HasDerivAt (Ecal k)
      ((⟪Vsim k s, Vsim k s⟫ * ⟪Wsim k s, Wsim k s⟫ - ⟪Vsim k s, Wsim k s⟫ ^ 2)
        / ⟪Vsim k s, Vsim k s⟫) s)
    (htel : ∀ k, ∀ s ∈ Icc (-Real.log (cascadeStart (M k))) (-Real.log (1 / M k)),
      HasDerivAt (fun u => Kprim k u + Rmprim k u)
        (⟪Nnear k s + Nfar k s + Nmarg k s,
          amplitudeProj (Vsim k s) (Wsim k s)⟫ : ℝ) s)
    (hRf : ∀ k, ∀ s ∈ Icc (-Real.log (cascadeStart (M k))) (-Real.log (1 / M k)),
      HasDerivAt (Rfprim k) (Rfar k s) s)
    (hmargtel : ∀ k,
      -((Kprim k (-Real.log (1 / M k)) + Rmprim k (-Real.log (1 / M k)))
        - (Kprim k (-Real.log (cascadeStart (M k)))
            + Rmprim k (-Real.log (cascadeStart (M k))))) ≤ Ctel)
    (hfartot : ∀ k, Rfprim k (-Real.log (1 / M k))
      - Rfprim k (-Real.log (cascadeStart (M k))) ≤ Cfar)
    (hinit : ∀ k,
      (1 / 2) * bil (Vsim k (-Real.log (cascadeStart (M k))))
          (Vsim k (-Real.log (cascadeStart (M k))))
        + (1 / 4) * ⟪Vsim k (-Real.log (cascadeStart (M k))),
            Vsim k (-Real.log (cascadeStart (M k)))⟫ ≤ Cdrop)
    (hdom : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      Delta k r / QgradCyl (G k) (t k) (x k) r
        ≤ K * ((⟪Vsim k (-Real.log r), Vsim k (-Real.log r)⟫
              * ⟪Wsim k (-Real.log r), Wsim k (-Real.log r)⟫
            - ⟪Vsim k (-Real.log r), Wsim k (-Real.log r)⟫ ^ 2)
          / ⟪Vsim k (-Real.log r), Vsim k (-Real.log r)⟫))
    (hrem : ∀ k, Theta k (cascadeStart (M k)) - Theta k (1 / M k) ≤ Crem)
    (hstart : ∀ k, eps ≤ QgradCyl (G k) (t k) (x k) (cascadeStart (M k))) :
    DynamicVelocityScaleDefect G M t x := by
  have htr : ∀ k s, ‖Wsim k s - amplitudeProj (Vsim k s) (Wsim k s)‖ ^ 2
      = (⟪Vsim k s, Vsim k s⟫ * ⟪Wsim k s, Wsim k s⟫ - ⟪Vsim k s, Wsim k s⟫ ^ 2)
        / ⟪Vsim k s, Vsim k s⟫ := fun k s =>
    amplitude_transverse_norm_sq (hVpos k s) (Wsim k s)
  have hsplit : ∀ k, ∀ r ∈ Icc (1 / M k) (cascadeStart (M k)),
      max (F k r) 0 ≤ (CG / cstar) * Delta k r + Rem k r := fun k =>
    scaleCharge_split_of_coercivity hCG hcstar (hFG k) (hcoer k)
  have hcinv : (0 : ℝ) ≤ CG / cstar := by positivity
  refine clay_A_dyn_of_similarity_absorption
    (Hcal := fun k s => (1 / 2) * bil (Vsim k s) (Vsim k s)
      + (1 / 4) * ⟪Vsim k s, Vsim k s⟫)
    (Ecal := Ecal)
    (Rcal := fun k s => -(Kprim k s + Rmprim k s) + Rfprim k s)
    (Hd := fun k s => -⟪Wsim k s, Wsim k s⟫
      - ⟪Nnear k s + Nfar k s + Nmarg k s, Wsim k s⟫)
    (q := fun k s => ‖Wsim k s - amplitudeProj (Vsim k s) (Wsim k s)‖ ^ 2)
    (rem := fun k s => -(⟪Nnear k s + Nfar k s + Nmarg k s,
        amplitudeProj (Vsim k s) (Wsim k s)⟫ : ℝ) + Rfar k s)
    (Cdrop := Cdrop) (Cabs := Ctel + Cfar)
    heps hM hcinv hK heta1 hle hpos hderiv hexact hsplit hPhi hPsi hTheta
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hrem hstart
  · intro k s _
    exact similarity_energy_identity bil hsymm (hV k s) (heq k s)
  · intro k s _
    refine similarity_energy_deriv_le_transverse_signed (amplitudeProj (Vsim k s))
      (amplitudeProj_idem (hVpos k s)) (amplitudeProj_symm (Vsim k s))
      (Nnear k s) (Nfar k s) (Nmarg k s) (Wsim k s) (hmarg k s) ?_ (hfar k s)
    rw [htr k s]
    exact hnear k s
  · intro k s
    dsimp only
    rw [htr k s]
    exact hEc k s
  · intro k s hs
    exact ((htel k s hs).neg).add (hRf k s hs)
  · intro k
    linarith [hmargtel k, hfartot k]
  · intro k
    have hnn := similarity_energy_nonneg bil hpsd (Vsim k (-Real.log (1 / M k)))
    linarith [hinit k]
  · intro k r hr
    dsimp only
    rw [htr k (-Real.log r)]
    exact hdom k r hr

end ClayNS

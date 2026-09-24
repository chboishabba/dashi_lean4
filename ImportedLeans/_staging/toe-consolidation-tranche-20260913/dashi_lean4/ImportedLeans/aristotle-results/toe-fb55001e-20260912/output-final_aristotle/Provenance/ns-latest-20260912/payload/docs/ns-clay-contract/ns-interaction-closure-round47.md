# Round 47 — the Gaussian similarity interaction closure

## Objective for this round

Package the four A-side facets (near estimate, far estimate, marginal estimate,
flux splitting) as **one** theorem about the actual similarity-variable
interaction

```
N = (V·∇)V + ∇P,   W = V_τ,   P_VW = (⟪V,W⟫/⟪V,V⟫)·V,
```

and carry out first the calculation the plan singles out: *compute* the
marginal direction rather than estimate it.

## What is now proved

### 1. The marginal channel is a logarithmic derivative (`GaussianMarginalTelescope.lean`)

* `ClayNS.hasDerivAt_ampSq` — `C = ⟪V,V_τ⟫ = ½A′`.
* `ClayNS.amplitude_marginal_channel_logDeriv` — identity (M),
  `⟪N,P_VW⟫ = (A′/2A)·⟪N,V⟫`, with no positivity hypothesis.
* `ClayNS.gauss_amplitude_marginal_channel` — the physical form:
  `⟪N,P_VW⟫ = ½(log A)′·𝒥`, where
  `𝒥 = (1/4ν)∫ρ_ν⟨y,V⟩(|V|²+2P)` is the integral computed exactly in
  `GaussianMarginalChannel.lean`.
* `ClayNS.marginal_channel_telescope` (and `..._exact`) — if `𝒥 = F(A) + R`
  and `𝒦′(a) = F(a)/(2a)` then `d/dτ 𝒦(A(τ)) = ⟪N,P_VW⟫ − (A′/2A)R`.
* `ClayNS.hasDerivAt_ampPrimitive_rpow`, `ClayNS.hasDerivAt_ampPrimitive_log` —
  closed-form primitives for `F(a) = κa^m` and `F(a) = κ`.
* `ClayNS.marginal_channel_total_le` — the accumulated channel is the variation
  of a primitive, not the integral of an absolute value.

### 2. The closure (`GaussianSimilarityInteractionClosure.lean`)

* `ClayNS.similarity_energy_deriv_le_transverse_signed` — identity (S) with the
  near/far absorption and the **signed** marginal channel:
  `ℋ′ ≤ −(1−η)‖W_⊥‖² − ⟪N,P_VW⟫ + R_far`.
* `ClayNS.amplitude_marginal_remainder_absorbed` — `‖P_VW‖² = ⟪V,W⟫²/A`, hence
  `−(⟪V,W⟫/A)R ≤ ½‖P_VW‖² + R²/(2A)`: the marginal remainder is paid by half of
  the marginal coercivity already present in (S).
* `ClayNS.similarity_energy_deriv_le_marginal_absorbed` — (S) with that
  absorption inserted.
* `ClayNS.gaussian_similarity_interaction_closure` and
  `..._absorbed` — from (A-near), (A-far), the telescope and **one**
  initial-time energy bound:
  `(1−η)∫‖W_⊥‖² ≤ C_H + C_tel + C_far` (respectively `+ C_q`), plus a uniform
  bound on the similarity energy on the window.
* `ClayNS.clay_A_dyn_of_gaussian_similarity_interaction_closure` — the A-side
  gate `DynamicVelocityScaleDefect` from the same package, with the flux
  splitting **instantiated**: it is supplied in the scale-generator form
  `[F]₊ ≤ C_G𝒢 + ℛ` together with the probe coercivity `c_*𝒢 ≤ Δ_scale`
  (`PositiveParabolicEnergyScaleProbe.lean`) and converted internally by
  `ClayNS.scaleCharge_split_of_coercivity`.
* `ClayNS.nearfar_cutoff_optimization` — the shared criterion
  `η_near(Δ) + η_far(Δ) < 1`.
* `ClayNS.transverse_pairing_eq` — `⟪u − Pu, W − PW⟫ = ⟪u, W − PW⟫`, the bridge
  that lets the concrete near/far bounds be used verbatim as (A-near), (A-far).

### 3. A literal near/far decomposition (`GaussianNearFarSplit.lean`)

`N_near = 1_{|y|≤R}N`, `N_far = 1_{|y|>R}N` in the similarity variable.

* `ClayNS.gaussWeight_le_tail` — `ρ_ν ≤ e^{−R²/(8ν)}ρ_{2ν}` on `|y| ≥ R`.
* `ClayNS.gauss_far_pairing_tail_bound` — **(A-far) is proved**:
  `|∫ρ_ν⟨N_far,W⟩| ≤ e^{−R²/(8ν)}∫ρ_{2ν}‖N‖‖W‖`.
* `ClayNS.gauss_far_sq_tail_bound` — the same for the weighted `L²` norm.
* `ClayNS.gauss_near_pairing_relative` — (A-near) reduces to the **pointwise**
  near-field domination `‖N(y)‖ ≤ η‖W_⊥(y)‖` for `|y| ≤ R`.
* `ClayNS.gauss_nearfar_interaction_bound` — the two together.

### 4. Finite projective expenditure (`FiniteProjectiveExpenditure.lean`)

* `ClayNS.projective_speed_eq_transverse_div_amp` — `‖∂_τV̂‖² = ‖W_⊥‖²/A`.
* `ClayNS.projective_expenditure_of_transverse_expenditure` — with the
  amplitude bounded below, the closure's transverse budget is a projective
  budget.
* `ClayNS.exists_small_value_of_finite_expenditure`,
  `ClayNS.exists_seq_tendsto_zero_of_finite_expenditure` — finite expenditure
  produces `τ_j → ∞` with `‖∂_τV̂(τ_j)‖ → 0`.
* `ClayNS.finite_projective_expenditure_ancient_rigidity` — the C-lane
  architecture: finite expenditure ⟹ almost-stationary sequence ⟹ (with
  compactness/equation passage and stationary rigidity, both explicit
  hypotheses) the normalized profile is trivial along that sequence.

### 5. The shared abstraction (`TiltedProjectiveSpeed.lean`)

For `w_α(i) = e^{αλ_i/2}a_i` and `S_j = Σλ_i^j w_α(i)²`, the Gram coefficients
are `A = S₀`, `C = ½S₁`, `B = ¼S₂`, so

```
‖∂_α ŵ_α‖² = ¼(S₀S₂ − S₁²)/S₀².
```

A tilted log-variance is literally a projective speed — the same quantity the
similarity analysis pays for (`ClayNS.tilted_projective_speed`).

## Ledger: what the A lane still needs

| Input | Status |
| --- | --- |
| (A-marg) marginal channel | **computed**; telescopes, remainder absorbed quadratically |
| (A-far) far interaction | **proved** for the literal cutoff split, exponentially small |
| flux splitting `hFG` | instantiated from the scale-generator form + proved probe coercivity |
| (A-near) near interaction | **open** — reduced to the pointwise near-field domination `‖N‖ ≤ η‖W_⊥‖` on `|y| ≤ R` with `η < 1` |
| amplitude law `𝒥 = F(A) + R` with `∫R²/(2A) < ∞` | **open** |
| initial-time similarity energy bound | input |

So the A lane now carries **one** physical estimate (the near-field relative
contraction) plus the amplitude law behind the telescope, instead of four
separate facets.

## Honest status

The literal Clay periodic regularity target is **not** proved and nothing here
weakens it. Everything above compiles with the rest of the library, contains no
`sorry`, no postulates and no added axioms, and every headline theorem depends
only on `propext`, `Classical.choice`, `Quot.sound`.

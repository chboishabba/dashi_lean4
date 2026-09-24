# Round 46 — near/far relative absorption and the exact marginal channel

Parent: [Navier–Stokes Clay contract README](README.md).
Previous round: [Round 45 similarity-variable scale expenditure](ns-similarity-expenditure-round45.md).

This round works only on the Navier–Stokes lane, and only on the A side. The
target was the single hardest A obligation: replace the generic Young remainder
`‖N‖²/(4η)` of `SimilarityAbsorption.lean` by a decomposition in which

* the marginal interaction is **computed**,
* the near interaction is charged **relatively** to the transverse expenditure
  that is already present (`≤ η‖W⊥‖²`, `η < 1`), and
* the far interaction is a **summable tail**.

Measure of progress used, as in the previous rounds: the number of independent
unproved continuum estimates entering the final contradiction.

## What is now proved

Everything below compiles with the rest of the library, contains no `sorry`,
no postulates and no added axioms, and depends only on `propext`,
`Classical.choice`, `Quot.sound`.

New file
[`SimilarityNearFarAbsorption.lean`](../../RequestProject/NavierStokes/SimilarityNearFarAbsorption.lean):

- `ClayNS.pythagoras_proj` — `‖W‖² = ‖PW‖² + ‖W − PW‖²`: the marginal
  coercivity is kept rather than discarded.
- `ClayNS.pairing_near_far_split` — the **exact** three-way split of the
  pairing for `N = N_near + N_far + N_marg`; no inequality is used.
- `ClayNS.pairing_near_far_marginal_split` — when `N_marg` lies in the marginal
  subspace, its transverse contribution vanishes identically, so it enters only
  through the computed channel `⟪N,PW⟫`.
- `ClayNS.nearfar_relative_absorption` — the resulting bound
  `|⟪N,W⟫| ≤ |⟪N,PW⟫| + η‖W⊥‖² + R_far`. There is no `‖N⊥‖²/(4η)` term any
  more.
- `ClayNS.similarity_energy_deriv_le_nearfar`,
  `ClayNS.similarity_energy_deriv_le_transverse_nearfar` — identity (S) of
  `SimilarityEnergy.lean` with that bound inserted:
  `ℋ′ ≤ −‖PW‖² − (1−η)‖W⊥‖² + (|⟪N,PW⟫| + R_far)`.
- `ClayNS.similarity_energy_nonneg` — `ℋ ≥ 0` for a positive semidefinite
  Dirichlet form.
- `ClayNS.similarity_energy_uniform_bound` — `ℋ(τ) ≤ ℋ(τ₀) + (ℛ(τ) − ℛ(τ₀))`
  on the whole window.
- `ClayNS.similarity_energy_drop_of_nonneg` and
  `ClayNS.similarity_nearfar_transverse_expenditure` — the telescope in
  near/far form: from one **initial-time** energy bound and one far-tail bound
  one gets simultaneously the finite transverse expenditure
  `(1−η)∫‖W⊥‖² ≤ C_H + C_R`, the energy drop `ℋ(τ₀) − ℋ(τ₁) ≤ C_H`, and a
  uniform bound on `ℋ` across the window.
- `ClayNS.amplitudeProj`, `ClayNS.amplitude_marginal_channel`,
  `ClayNS.amplitude_transverse_norm_sq` — the physical marginal direction is
  the amplitude direction `ℝ·V`; along it the marginal channel is the scalar
  `⟪N,V⟫⟪V,W⟫/⟪V,V⟫`, and the transverse coercive quantity is literally the
  scale-Gram defect, `‖W − PW‖² = (AB − C²)/A`.
- `ClayNS.near_relative_of_norm_domination`,
  `ClayNS.relative_contraction_forces_zero` — the two small reductions the
  relative formulation is aimed at.

New file
[`SimilarityNearFarScaleCharge.lean`](../../RequestProject/NavierStokes/SimilarityNearFarScaleCharge.lean):

- `ClayNS.clay_A_dyn_of_nearfar_relative_absorption` — the A-side gate
  (`DynamicVelocityScaleDefect`) from the near/far package, for an arbitrary
  family of marginal projections varying along the cascade and along
  similarity time.
- `ClayNS.clay_A_dyn_of_amplitude_nearfar_absorption` — the same with the
  marginal direction taken to be `ℝ·V(τ)`: the projection hypotheses are
  discharged, the domination hypothesis is stated directly in terms of the
  Gram defect `(AB − C²)/A`, and the marginal remainder is the exactly
  computable scalar.

New file
[`GaussianMarginalChannel.lean`](../../RequestProject/NavierStokes/GaussianMarginalChannel.lean):

- `ClayNS.gaussWeight`, `ClayNS.fderiv_gaussWeight` — the similarity Gaussian
  weight and its logarithmic derivative `∇ρ = −(y/2ν)ρ`.
- `ClayNS.advSpace`, `ClayNS.gradSpace`, `ClayNS.divSpace`,
  `ClayNS.bernoulliHead`, `ClayNS.inner_advSpace_add_gradSpace` — the pairing
  of the nonlinear and pressure terms with the velocity is the transport of
  the head `|V|²/2 + p`.
- `ClayNS.gauss_weighted_marginal_channel` — **the marginal channel computed
  exactly**: for a `C¹`, divergence-free, compactly supported profile `V` and a
  `C¹` pressure `p`,

  `∫ ρ_ν ⟪(V·∇)V + ∇p, V⟫ = (1/(4ν)) ∫ ρ_ν ⟪y,V⟫ (|V|² + 2p)`.

  In the unweighted incompressible setting this pairing vanishes identically;
  the entire residue in the Gaussian similarity space is the weight
  commutator, and it is computed by integration by parts (via the compactly
  supported divergence theorem of `CompactDivergence.lean`), never estimated.
- `ClayNS.gauss_weighted_transport_by_parts` — the underlying weighted
  integration by parts for a divergence-free compactly supported field:
  `∫ ρ_ν (V·∇)g = (1/2ν) ∫ ρ_ν ⟪y,V⟫ g`.
- `ClayNS.gauss_weighted_transport_skew` — the advective pairing is
  antisymmetric up to the weight commutator:
  `∫ ρ_ν (⟪(V·∇)V,w⟫ + ⟪(V·∇)w,V⟫) = (1/2ν) ∫ ρ_ν ⟪y,V⟫⟪V,w⟫`. This is what
  allows the derivative to be moved off the profile onto the test field, which
  is the first step of any near-interaction estimate.
- `ClayNS.gauss_weighted_pressure_solenoidal` — against a solenoidal, compactly
  supported test field the pressure contributes only the weight commutator:
  `∫ ρ_ν ⟪∇p,w⟫ = (1/2ν) ∫ ρ_ν p ⟪y,w⟫` (in the unweighted setting it drops out
  entirely).

## Effect on the A-side ledger

Before this round the A side carried two independent quantitative inputs:

1. a bound on the accumulated Young remainder `∫‖N‖²/(4η)` (A1), and
2. a uniform bound on the similarity energy drop `ℋ(τ₀) − ℋ(τ₁)` (A2).

After it the A side carries a single package:

* `|⟪N_near⊥, W⊥⟫| ≤ η‖W⊥‖²` with `η < 1` (near relative contraction),
* `∫|⟪N_far⊥, W⊥⟫| ≤ C` (far summable tail),
* the marginal channel, which is now an explicit integral rather than an
  estimate, and
* a bound on `ℋ` at the **initial** similarity time only — the drop is derived
  from nonnegativity of the energy.

So A2 no longer needs an independent argument, and A1 has been rewritten in
relative form. What genuinely remains open on the A side is the near relative
contraction and the far tail bound for the physical interaction — these are
still real PDE estimates and nothing here pretends otherwise.

## What is still open

Unchanged by this round, and still open:

* the near/far estimates just named, on the actual blow-up carrier with
  index-independent constants;
* ancient rigidity (`ClayNS.DirectionalLevelDrop`);
* equation, local-energy and pressure inheritance through the blow-up limit;
* classical periodic local existence and continuation;
* the flux splitting, which remains an input.

The literal Clay periodic regularity target is **not** proved, and nothing in
this round weakens it.

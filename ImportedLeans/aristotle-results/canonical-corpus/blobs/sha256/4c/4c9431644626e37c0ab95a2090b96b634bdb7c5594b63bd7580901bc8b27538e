# Round 48 — the Gaussian Dirichlet form, the amplitude law, and rigidity

## Objective for this round

Round 47 packaged the A lane as one interaction theorem and computed the
marginal channel as `(A′/2A)·𝒥`.  Two things were still assumed rather than
derived:

1. the *linear* part of the similarity operator was an abstract symmetric form
   `𝔞` (the Gaussian Dirichlet form only "morally");
2. the scalar `𝒥` was an independent unknown, to be split as an amplitude law
   `F(A)` plus a remainder.

Round 48 derives both, and cashes them in on the C lane.

## What is now proved

### 1. The Ornstein–Uhlenbeck identity (`GaussianOrnsteinUhlenbeck.lean`)

For a compactly supported `C²` profile,

```
ν∫ρ_ν⟪∆V,V⟫ − ½∫ρ_ν⟪(y·∇)V,V⟫ = −ν∫ρ_ν|∇V|².
```

* `ClayNS.gauss_OU_divergence_identity` — the raw divergence identity, obtained
  from the compactly supported divergence theorem applied to the flux
  `F_i = ρ_ν⟪∂_iV,V⟫` and the weight commutator `∇ρ = −(y/2ν)ρ`;
* `ClayNS.gauss_OU_energy_identity` — the identity above;
* `ClayNS.gauss_OU_nonpos` — the linear similarity operator is dissipative in
  the Gaussian space.

The abstract form `𝔞` of `SimilarityEnergy.lean` is therefore the genuine
Gaussian Dirichlet form, not a stand-in.

### 2. The amplitude law (`SimilarityAmplitudeLaw.lean`)

Pairing the similarity equation with `V` and combining the OU identity with the
exact marginal computation of `GaussianMarginalChannel.lean` gives

```
𝒥 = −ν𝒟 − ½𝒜 − ⟪W,V⟫_ρ = −ν𝒟 − ½A − ½A′.            (AL)
```

* `ClayNS.similarity_amplitude_law`, `ClayNS.gaussMarginalJ_eq_of_ampDeriv`.

So the marginal scalar is not an unknown at all: the telescope's amplitude law
is `F(A) = −½A`, and the remainder is `−ν𝒟 − ½A′`.  Substituting into
`⟪N,P_VW⟫ = (A′/2A)𝒥` gives the closed form

```
⟪N,P_VW⟫ = −¼A′ − (A′)²/(4A) − (ν𝒟/2)(log A)′,        (MC)
```

* `ClayNS.marginal_channel_closed_form`,
  `ClayNS.marginal_channel_le_of_closed_form`.

The first term telescopes exactly (primitive `−A/4`), the second has a
favourable sign, and only the Dirichlet-energy-against-log-amplitude-speed term
survives.

### 3. Stationary rigidity (`StationarySimilarityRigidity.lean`)

For a stationary profile (AL) reads `ν𝒟 + ½𝒜 + 𝒥 = 0`
(`ClayNS.stationary_similarity_gauss_identity`).  Both left-hand terms are
nonnegative, so rigidity is exactly a relative-contraction question, and

* `ClayNS.gaussMarginalJ_relative_bound` — `|𝒥| ≤ (LK/4ν)·𝒜` whenever the
  Bernoulli head obeys `||V|²+2p| ≤ K|V|` on a support of radius `L`;
* `ClayNS.stationary_rigidity_of_relative_bound` — `|𝒥| ≤ θ𝒜`, `θ < ½`, forces
  `𝒜 = 𝒟 = 0`;
* `ClayNS.stationary_similarity_rigidity` — hence a compactly supported
  stationary similarity profile with `L·K < 2ν` vanishes identically.

### 4. The C lane with rigidity discharged (`FiniteExpenditureSmallReynoldsRigidity.lean`)

* `ClayNS.finite_projective_expenditure_smallReynolds_rigidity` — finite
  projective expenditure plus compactness onto small-Reynolds stationary limits
  now give the trivial limit *without* assuming rigidity.  Only compactness and
  equation passage remain in that regime.

### 5. Small-Reynolds A-lane closure (`SmallReynoldsAmplitudeDecay.lean`)

(AL) plus the relative bound is a differential inequality for the amplitude:

```
½A′ ≤ −ν𝒟 − ½A + θA,   θ = LK/(4ν).
```

* `ClayNS.gauss_amplitude_differential_inequality` — the physical inequality;
* `ClayNS.amplitude_dirichlet_budget` — `∫ν𝒟 ≤ ½(A(τ₀) − A(τ₁)) ≤ ½A(τ₀)`;
* `ClayNS.amplitude_exponential_decay` — `A(τ₁) ≤ A(τ₀)e^{−(1−2θ)(τ₁−τ₀)}`;
* `ClayNS.smallReynolds_no_normalized_similarity_family` — hence no *normalized*
  similarity family (`A ≡ 1`, the record-point normalization) exists on a window
  of positive length when `L·K < 2ν`.

### 6. The near/far cutoff optimization (`GaussianNearFarOptimization.lean`)

* `ClayNS.gauss_pairing_young` — the weighted Young inequality;
* `ClayNS.gauss_near_pairing_relative_L2` — (A-near) from an `L²(ρ)` relative
  bound rather than a pointwise domination;
* `ClayNS.exists_cutoff_far_small` — the Gaussian tail beats any relative far
  constant;
* `ClayNS.gauss_nearfar_strict_relative_contraction` — the optimization
  `η_near(R) + η_far(R) < 1`: a cutoff-uniform near constant `η_∞ < 1` plus a
  relative far moment give a strict relative contraction of the whole
  interaction, which is exactly the (A-near)+(A-far) input of the round-47
  closure.

## What is still open

* **A lane, general case**: the cutoff-uniform near constant `η_∞ < 1` for the
  actual blow-up profile.  Everything downstream of it is now derived, and in
  the small-Reynolds regime the whole lane closes unconditionally.
* **C lane**: compactness and passage of the equation to the limit;
  rigidity is discharged below the Reynolds threshold, and above it the
  question is again a relative bound on the *same* computed scalar `𝒥`.
* **B, E**: unchanged (blow-up compactness/inheritance; periodic local theory
  and continuation).

All statements in this round are `sorry`-free and depend only on
`propext`, `Classical.choice`, `Quot.sound`.

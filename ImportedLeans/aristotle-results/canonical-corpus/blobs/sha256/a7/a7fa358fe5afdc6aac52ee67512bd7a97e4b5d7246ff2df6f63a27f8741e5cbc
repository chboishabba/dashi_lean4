# The Gaussian Fisher tranche: `C53`, `C54`, `C55`

All three lemmas of this tranche are proved in Lean, `sorry`-free, and depend
only on `propext`, `Classical.choice`, `Quot.sound`.  Files:

| Lemma | File | Headline result |
| --- | --- | --- |
| `C53` | `RequestProject/NavierStokes/GaussianFisherInformation.lean` | `ClayNS.torusGaussFisherInformationBound` |
| `C54` | `RequestProject/NavierStokes/GaussianWeightedAbsorption.lean` | `ClayNS.gaussianGradientWeightedAbsorption` |
| `C55` | `RequestProject/NavierStokes/LevelAnnulusPigeonhole.lean` | `ClayNS.smoothedModulusLevelAnnulusPigeonhole` |

## `C53` — the Fisher information of the torus Gaussian is `O(√a)`

For the exactly `ℤ³`-periodic weight `Φ_a(x) = exp(−Σ_j ψ(x_j−x₀_j)/(4a))`,
`ψ(s) = sin(πs)²/π²`,

```
∫_cell |∇Φ_a|²/Φ_a ≤ C_FI·√a,     C_FI = (3π⁵/2)·√(2π³).
```

The proof is the *exact* integration of the weighted quantity, not a supremum
bound.  Each coordinate contribution factorises,

```
(∂_iΦ_a)²/Φ_a = tgLapB(u_i)·Π_{j≠i} tgFac(u_j),
```

(`ClayNS.sq_dvec_div_torusGauss_eq_prod`), and the one-dimensional budgets
already present in `TorusGaussianIntegrals.lean` give `O(a^{-1/2})` for the
distinguished factor and `O(a^{1/2})` for each of the other two.  Net: `√a`.
This is the `a^{-1}·a^{3/2} = a^{1/2}` cancellation between the logarithmic
derivative and the mass of the region where the weight lives.

## `C54` — keep the weight through Young's inequality

Pointwise, for `Φ > 0` and any `θ > 0` (`ClayNS.abs_dvec_le_fisher_young`),

```
|∂_jΦ| ≤ (θ/2)Φ + (1/2θ)·|∇Φ|²/Φ.
```

Substituting this for the sup bound `|∂_jΦ| ≤ G` in the transferred stretching
budget replaces the single unweighted term `9AB²G·∫β′(q)` by

```
(9AB²θ/2)·∫Φβ′(q) + (9AB²/2θ)·∫β′(q)|∇Φ|²/Φ,
```

both weighted.  The whole chain has been re-run with that replacement:

* `ClayNS.increment_stretching_transfer_budget_weighted` — pointwise;
* `ClayNS.increment_stretching_transfer_cell_budget_weighted` — cell form;
* `ClayNS.approx_adjoint_caccioppoli_linear_budget_weighted` — the linear
  Caccioppoli budget with the approximate-adjoint residual `D`, containing **no
  unweighted term at all**;
* `ClayNS.gaussianGradientWeightedAbsorption` — the Gaussian instantiation.
  With the active-modulus bound `β′ ≤ 1/λ` (legitimate because De Giorgi levels
  are bounded away from `0`), the sources are

```
(9A²B²/2ν + 3BG_p + 9AB²θ/2)·(π³a)^{3/2}/λ
  + (9AB²/2θ)·C_FI√a/λ
  + ‖β‖_∞·(6π³A·a + ν·C·√a),
```

every one of which carries a **positive** power of `a`.
`ClayNS.gaussianWeightedSource_tendsto_zero` records that the total source tends
to `0` as `a ↓ 0`.

The earlier no-go `ClayNS.gaussian_gradient_term_blows_up` remains a theorem: it
is a no-go for the *sup-unweighted* estimate `9AB²K₀/(4πa)`, not for Gaussian
concentration.  Both statements now sit side by side in the development.

## `C55` — average over the level, do not control every level

`ClayNS.integral_annulusKernel_le_one`: for the annulus kernel
`K_λ(s) = δ^{-1}w((s−λ)/δ)` built from any nonnegative profile of mass `≤ 1`,

```
∫_{λ₀}^{λ₁} K_λ(s) dλ ≤ 1     for every s,
```

with no `δ^{-1}` left over.  `ClayNS.levelAnnulusFubini` exchanges the level and
space integrals (exact Fubini on the compact product `[λ₀,λ₁] × cell`), and the
first-moment method then gives `ClayNS.smoothedModulusLevelAnnulusPigeonhole`:

```
∃ λ_* ∈ [λ₀,λ₁] :   ∫_cell G·K_{λ_*}(r) ≤ (λ₁−λ₀)^{-1}∫_cell G.
```

`ClayNS.exists_level_smoothing_annulus_bound` is the form the modulus residual
consumes: any residual profile dominated by the annulus kernel — in practice
`ζ″_{λ,δ}` — has a level at which its weighted cell integral is at most the
average of the density, uniformly in `δ`.

## Cross-check against the Agda layer of this repository

The abstract multiscale machinery cited (`BalabanFiniteRectangularSchurSquaredExact`,
`BalabanClayDyadicCutoffTailExact`, `BalabanCMP98UnitaryOperatorDefectTelescopeExact`,
and the finite pigeonhole in `ClaySupportingPolymerCounting`) is present in
`DASHI/Physics/YangMills/` and is postulate-free, but it is *finite and
rational*: the objects are `ℚ`-valued finite sequences and matrices indexed by
`Nat`/`Fin`, and the theorems are the finite weighted Cauchy/Schur bound, the
finite geometric dyadic tail, the finite defect telescope, and the finite
cardinality pigeonhole.  None of them is an analytic producer, and none of them
states `C53`, `C54` or `C55`:

* `C53` needs a genuine Gaussian integral on `𝕋³` — proved here in Lean;
* `C54` is *methodologically* the same correction as the weighted-Schur layer
  (never replace a weighted pairing by an unweighted supremum), but the
  identification of the entries with the torus Gaussian is the analytic content
  and is new;
* `C55` is a continuous Fubini/level-average statement, not the finite
  cardinality pigeonhole, and is new.

So the tranche was proved where the analysis lives, in the Lean carrier, and the
Agda layer is confirmed as abstract scaffolding rather than a source of these
three results.

## What this does and does not close

It removes the `a^{-1}K₀` obstruction recorded in
`GaussianLinearBudgetAudit.lean`.  It does **not** by itself close `C`: the
assembly still needs the Sobolev/Gagliardo–Nirenberg parabolic embedding input
of the De Giorgi recurrence (`ClayNS.deGiorgi_recurrence_extraction` takes it as
an explicit hypothesis, and it is not derived anywhere in the project).

## Follow-up tranche (same run)

Three further files were added after `C53`–`C55`:

* `RequestProject/NavierStokes/GaussianSpacetimeBudget.lean` —
  `ClayNS.gaussian_weighted_spacetime_budget`.  The time integral of the
  weight-aware budget over a window `[t₀,t₁]`, the first term integrated exactly
  by the fundamental theorem of calculus into the increment of the weighted mass
  `M(t₁) − M(t₀)`.  This is the space-time shape the De Giorgi machinery
  consumes.

* `RequestProject/NavierStokes/ScaleInvariantWeightChoice.lean` — the
  scale-invariant choice `a = κR²` (Gaussian width `√a = √κ·R`, a fixed fraction
  of the cylinder radius at every scale).  `ClayNS.gwSource_scaleInvariant_eq`
  is the *exact* expansion of the source as `R·K₁(κ) + R²·K₂(κ) + R³·K₃(κ)`, with
  every coefficient independent of `R`; `ClayNS.gwSource_scaleInvariant_le`
  packages it as `source ≤ R·K(κ)` for `0 < R ≤ 1`; and
  `ClayNS.gaussianGradientWeightedAbsorption_scaleInvariant` is the budget
  itself at that weight.  This is the positive scaling dimension the dyadic tail
  machinery needs; note there is no constant term at all, so no `a → 0` limit at
  fixed geometry is being hidden.

* `RequestProject/NavierStokes/ScaleAnchor.lean` — the `A`-side anchor.
  `ClayNS.gram_anchor_lower_bound` is the exact analogue of the zeta anchor
  inequality: with an anchor mode `e` of weighted mass `≤ 1` satisfying
  `⟨e,Λu⟩_Γ = 0` and `⟨e,u⟩_Γ = a₀`, one gets `AB − C² ≥ a₀²B`.  The mechanism
  is that the anchor sees all of the profile and none of its scaling derivative,
  so no multiple `cΛu` can approximate `u` to weighted distance below `a₀`, and
  the Gram determinant is exactly that squared distance times `B`.  The
  complementary form `Δ ≥ c·‖P_⊥Λu‖²_Γ` is
  `ClayNS.scale_defect_ge_transverse`, its constant is supplied by
  `ClayNS.gramA_ge_of_lower_bound_on_set` (the record-point normalization), and
  `ClayNS.scaleGram_anchored_dichotomy` makes the dichotomy quantitative: on the
  near-self-similar branch the anchor forces `‖Λu‖²_Γ < ε·A/a₀²`.

* `RequestProject/NavierStokes/GaussianUnweighting.lean` — the bridge from the
  weighted budget to the unweighted quantities that
  `ClayNS.parabolic_gain_of_caccioppoli` consumes.  Since `ψ(s) = sin(πs)²/π² ≤ s²`
  (`ClayNS.tgProfile_le_sq`), the torus Gaussian dominates the Euclidean one and
  `Φ_a ≥ exp(−ρ²/(4a))` on the ball of radius `ρ`
  (`ClayNS.torusGauss_ge_exp_of_sq_le`).  At a fixed physical radius with
  `a → 0` that constant degenerates — which is precisely the reason not to take
  that limit — whereas at `a = κR²`, `ρ = R` it is the dimensionless
  `exp(−1/(4κ))`, independent of `R`
  (`ClayNS.torusGauss_ge_scaleInvariant`), giving the uniform transfer
  `∫_S f ≤ exp(1/(4κ))·∫_S Φ f`
  (`ClayNS.setIntegral_le_gaussianWeighted_scaleInvariant`).

What remains open on the `A` side is *producing* such an anchor mode for the
actual Navier–Stokes rescaling — the inequality itself is unconditional, but the
hypotheses `⟨e,ΛU⟩_Γ = 0`, `⟨e,U⟩_Γ = a₀ ≠ 0` are inputs, not theorems.

On the `C` side, the parabolic embedding itself *is* proved
(`ClayNS.parabolic_gain_of_caccioppoli`), and the unweighting constant is now
uniform.  The first still-unresolved obligation is the *compact-support*
matching: `parabolic_gain_of_caccioppoli` is stated for compactly supported
truncations on `ℝ³` with the Gagliardo–Nirenberg–Sobolev constant of `ℝ³`,
whereas the weighted budget lives on the periodic cell against a strictly
positive Gaussian.  Producing a cut-off truncation of the increment density that
simultaneously (i) is compactly supported in the concentration ball, (ii) obeys
the sup-in-time `L²` and total-dissipation bounds of the budget with constants
independent of the level index, is the next theorem to prove.  Nothing in the
development assumes it.

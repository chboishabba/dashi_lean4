# A lane gap ledger — physical near/far relative contraction

Scope of this round: the A lane only (plus one scope clarification for the C
lane). Nothing else in the proof tree was opened.

All statements below are in
`RequestProject/NavierStokes/PhysicalGaussianNearFarRelativeBound.lean` and
`RequestProject/NavierStokes/HeadBoundedRigidityScope.lean`; both files build
with no `sorry`, no postulates, and depend only on `propext`,
`Classical.choice`, `Quot.sound`.

## Starting point

`ClayNS.gauss_nearfar_strict_relative_contraction` (existing) consumes two
physical hypotheses:

* **(A-near)** `|⟪N_{≤R},W_⊥⟫_{ρ_ν}| ≤ η_∞‖W_⊥‖²_{ρ_ν}` uniformly in the cutoff
  `R`, with `η_∞ < 1`;
* **(A-far-rel)** `∫ρ_{2ν}‖N‖‖W_⊥‖ ≤ C_far·‖W_⊥‖²_{ρ_ν}`.

## 1. Reduction `2 → 1` (proved)

`ClayNS.physical_gauss_nearfar_relative_bound`,
`ClayNS.physical_gauss_nearfar_strict_relative_contraction`.

The *single* mixed-weight estimate

> **(A-single)** `∫ρ_{2ν}‖N‖‖W_⊥‖ ≤ K·∫ρ_ν‖W_⊥‖²`, `K < 1`

implies the target strict relative contraction
`|⟪N,W_⊥⟫_{ρ_ν}| ≤ K‖W_⊥‖²_{ρ_ν}` directly, because `ρ_ν ≤ ρ_{2ν}` pointwise
(`ClayNS.gaussWeight_le_two`). It also implies (A-near) at every cutoff with the
same constant (`ClayNS.gauss_near_pairing_of_mixed_moment`). So the A gate is
now fed by **one** scale-invariant norm estimate rather than two, which is the
`2 → 1` outcome named in the round's success metric.

A pointwise sufficient criterion for (A-single) is proved as well
(`ClayNS.mixed_moment_of_pointwise_gaussian_domination`): it suffices that

> `‖N(y)‖ ≤ K·e^{−|y|²/(8ν)}‖W_⊥(y)‖`,

using the exact identity `ρ_{2ν}(y)·e^{−|y|²/(8ν)} = ρ_ν(y)`.

## 2. Falsification: the cutoff optimization is not a weakening

`ClayNS.gauss_near_pairing_tendsto`,
`ClayNS.gauss_uniform_near_implies_contraction`,
`ClayNS.gauss_nearfar_optimization_no_gain`.

If the Gaussian pairing moment `∫ρ_ν‖N‖‖W_⊥‖` is finite, then (A-near)
*uniform in the cutoff* already yields the conclusion of the optimization
theorem, with the same constant and with **no** use of (A-far-rel): the near
pairings converge to the full pairing by dominated convergence. Hence no
refinement of the cutoff geometry (dyadic, Littlewood–Paley, log-frequency) can
reduce the physical content of the A gate; that content is exactly the constant
`η_∞ < 1`. This closes the "optimize the cutoff" branch of the search.

## 3. No-go: the surviving hypothesis is an amplitude (Reynolds) restriction

`ClayNS.gauss_relative_contraction_amplitude_no_go`,
`ClayNS.amplitude_bound_of_gauss_relative_contraction`.

Along the amplitude family `V = λV₀` the similarity equation gives, exactly,

  `N = λ²N₀`,  `W = V_τ = λ(M₀ − λN₀)`,

with `N₀ = (V₀·∇)V₀ + ∇P₀` the quadratic interaction of the shape and
`M₀ = ν∆V₀ − ½y·∇V₀ − ½V₀` its linear response. Writing
`a = ‖N₀‖²_ρ, b = ⟪N₀,M₀⟫_ρ, c = ‖M₀‖²_ρ` with `a > 0`, the relative
contraction `|⟪N,W⟫_ρ| ≤ η‖W‖²_ρ` **fails** for every `η < 1` as soon as

  `λ ≥ max(1, (|b| + |c| + 1)/((1−η)a))`.

Both sides are quartic in `λ` with leading coefficients `a` and `ηa`, so this is
not a matter of constants. The marginal projection is onto `ℝ·V = ℝ·V₀` and is
amplitude independent, so the same statement applies verbatim to the transverse
(projected) form of the gate.

Consequence, stated contrapositively in
`ClayNS.amplitude_bound_of_gauss_relative_contraction`: any proof of (A-near),
of (A-single), or of any strict relative contraction, **bounds the amplitude**
of the profile. No amplitude-homogeneous argument — cutoff geometry, shell
splitting, divergence-free/pressure cancellation, or Young/Cauchy–Schwarz
against the Gaussian weight — can produce it. The remaining A obligation is
therefore, precisely, a *dynamical amplitude normalization of the actual
blow-up profile*: a scale-invariant bound of the shape `‖V‖ ≲ √ν` in the norm
appearing in (A-single).

## Gap ledger after this round

| item | before | after |
|---|---|---|
| independent physical A hypotheses | 2 | **1** ((A-single)) |
| nature of the surviving A hypothesis | unclassified | proved to be an amplitude/Reynolds restriction, with explicit threshold |
| cutoff-optimization branch | open route | **closed** (no gain) |
| C-lane `HeadBoundedStationary` membership | described as a physical condition | proved to be gauge-coupled pointwise (pressure must vanish on the zero set of the velocity) |

The A wall itself is **not** closed: (A-single) with `K < 1` remains an
unproved physical continuum hypothesis, and by §3 it cannot be obtained without
an amplitude normalization supplied by the blow-up dynamics.

## C-lane scope note

`RequestProject/NavierStokes/HeadBoundedRigidityScope.lean` proves that the
head domination `|‖V‖² + 2p| ≤ K‖V‖` forces `p = 0` at every point where
`V = 0` (`ClayNS.head_pressure_eq_zero_of_velocity_eq_zero`), hence off the
support of `V`. Membership in the rigidity class is therefore a gauge-coupled
pointwise condition, not a norm bound, and a compactness/inheritance package
must pin the pressure normalization on the zero set of the limit profile before
`ClayNS.finite_projective_expenditure_headBounded_rigidity` can be applied to an
actual blow-up cluster point. `ClayNS.head_nonneg_of_nonzero` records that
`K ≥ 0` for a nontrivial profile, so `4K² < ν` is a genuine smallness
condition.

## Regression status

* `RequestProject.NavierStokes.FiniteExpenditureMomentRigidity` **builds**
  (previously unverified because of a timed-out build), and
  `ClayNS.finite_projective_expenditure_headBounded_rigidity` together with
  `ClayNS.headBounded_stationary_eq_zero` depend only on the three standard
  axioms.
* The whole library builds; the new files are part of the default target.

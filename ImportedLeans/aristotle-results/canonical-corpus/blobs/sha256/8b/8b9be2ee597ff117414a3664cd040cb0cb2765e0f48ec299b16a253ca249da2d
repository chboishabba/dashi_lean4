# The dyadic cascade, frequency monotonicity, and the De Giorgi engines

This note records the pass that answered the two questions posed for the
revised frontier `A_cascade + C_localDG`:

1. what a one-dyadic-step defect-persistence inequality has to look like in
   order to survive the `≍ (1/3)log₂ M` steps separating the energy scale
   `M^{-2/3}` from the velocity scale `M^{-1}`; and
2. what the Almgren/Poon frequency technology actually buys, as opposed to
   Carleman-type propagation of smallness.

Everything below is machine-checked Lean 4 + Mathlib, `sorry`-free, with only
Lean/Mathlib's three standard axioms.

## 1. The bookkeeping of the scale gap (`DyadicCascade.lean`)

`cascadeSteps M = ⌈log₂ M / 3⌉` and `cascadeStart M = 2^{cascadeSteps M}/M`.

* `cascadeStart_div_pow` — halving `cascadeStart M` exactly `cascadeSteps M`
  times lands **exactly** on `1/M`.  The cascade therefore terminates at the
  velocity scale with constant `c = 1`, not merely up to a factor.
* `cascadeStart_mem_Ico` — `M^{-2/3} ≤ cascadeStart M < 2·M^{-2/3}`: the
  starting radius *is* the energy scale, up to a factor `2`.
* `tendsto_cascadeSteps_atTop` — the number of steps is unbounded in `M`, which
  is the whole difficulty.

## 2. The iteration calculus: which one-step lemmas survive

| shape of the one-step loss | verdict | theorem |
| --- | --- | --- |
| `Q(r/2) ≥ c·Q(r)`, fixed `c<1` | **fatal**: guarantee `c^N ε → 0` as `M → ∞` | `geometric_guarantee_tendsto_zero` |
| `Q(r/2) ≥ Q(r) − C·Q(r)^{1+α}`, fixed `C, α` | **fatal** for fixed `ε`: the sufficient condition `N·C·ε^{1+α} ≤ ε/2` eventually fails; only `ε ≍ (log M)^{-1/α}` survives | `cascade_superlinear_threshold`, `superlinear_threshold_fails_eventually` |
| `Q(r_{n+1}) ≥ Q(r_n) − b_n` with `∑ b_n ≤ ε/2` | **works**, uniformly in the number of steps | `cascade_persistence_of_small_total_loss` |
| zero loss (monotone scale-critical quantity) | **works** | `velocityScaleDefect_of_scaleAntitone` |

So the calculation requested — "if every possible inequality loses a fixed
factor at each step, A is dead in this form" — is now a theorem, in both the
multiplicative and the superlinear variants; and the positive criterion is
exactly *summability in the step index*, not superlinearity in the defect.

## 3. What frequency monotonicity buys (`FrequencyDoubling.lean`)

The Almgren/Poon mechanism is formalized in the abstract form in which it is
used:

* `weightedScale_antitoneOn_of_frequency_le` — a bound on the logarithmic
  derivative, `r·H'(r) ≤ p·H(r)` (for Almgren's frequency in dimension `n`,
  `p = n−1+2N₀` with `N₀` an upper bound for the frequency), makes
  `r ↦ H(r)/r^p` nonincreasing.
* `doubling_of_frequency_le` — hence `H(2r) ≤ 2^p H(r)`: the loss per dyadic
  step is the **fixed factor** `2^{-p}`, i.e. polynomial in the scale ratio.
  This is precisely the sense in which the frequency route avoids the
  exponential loss of Carleman-based observability.
* `frequency_cascade_guarantee_tendsto_zero` — but by §2 a fixed factor is
  still fatal over `≍ log M` steps.  **Polynomial-in-the-scale-ratio is not
  enough by itself.**
* `weightedScale_defect_propagates` and `velocityScaleDefect_of_scaleAntitone` —
  what *is* enough is the critical exponent, i.e. the frequency bound with the
  weight matching the scaling of the defect functional.  Since `Q_∇` is already
  scale-invariant, the critical weight is `p = 0` and the required statement is
  literally antitonicity of `r ↦ Q_∇(r)` on `[1/M, cascadeStart M]`.
* `dynamicVelocityScaleDefect_of_cascade` — either hypothesis (zero loss, or a
  one-step inequality with summable loss) yields the gate
  `DynamicVelocityScaleDefect`, i.e. `A_dyn`, with `c = 1`.

**Net calibration.** The frequency route is not automatically better than the
observability route for this problem: it converts an exponential loss into a
fixed per-step factor, and a fixed per-step factor is exactly what §2 kills.
It closes `A_cascade` if and only if the frequency exponent is *critical* for
the chosen defect functional (zero loss), or the defect from exact monotonicity
is summable across scales.  That is a sharp, checkable target.

## 3b. Almost-monotonicity: the summable-defect version (`FrequencyAlmostMonotone.lean`)

Exact monotonicity is never available for a nonlinear equation.  What is
realistically provable is the frequency bound perturbed by a nonnegative defect
density,

`r·H'(r) ≤ (p + r·D(r))·H(r)`,   `D ≥ 0`,

and the perturbed estimate is proved here.  Writing `Φ` for a primitive of `D`
and `E = Φ(b) − Φ(a)` for the **total defect** across the range,

`H(a)/a^p ≥ e^{−E}·H(b)/b^p`   (`weightedScale_lower_of_almost_frequency_le`).

Two consequences, both machine-checked:

* the loss is the **single** factor `e^{−E}`; it does *not* compound over the
  `cascadeSteps M` dyadic steps.  So a total defect that is bounded uniformly
  along the singular sequence closes the cascade with a constant independent of
  `M` (`almostMonotone_defect_propagates`,
  `velocityScaleDefect_of_almostMonotone`,
  `dynamicVelocityScaleDefect_of_almostMonotone`);
* the exponent must still be **critical**: for `p > 0` the surviving factor is
  `(a/b)^p ≍ M^{−p/3} → 0`.

The discrete companion `cascade_multiplicative_persistence` says the same thing
for a one-step inequality `Q(n+1) ≥ (1 − δₙ)Q(n)`: a summable `∑δₙ ≤ 1/2`
costs a fixed factor, not a compounding one.

## 3c. The one-step inequality cannot be kinematic (`OneStepDyadicNoGo.lean`)

Before asking *which* one-step inequality holds, one should ask whether any
holds for free.  None does, and the failure is total.  For every radius `r > 0`
and every prescribed level `ε > 0` there is a nonnegative, continuous,
time-independent density — an explicit bump supported in the annulus
`13r/16 ≤ |y| ≤ 15r/16` — with

`Q_∇(r) = ε`   and   `Q_∇(r/2) = 0`

(`exists_density_with_prescribed_defect_and_vanishing_half`).  Hence any gain
function `Ψ` valid for all nonnegative continuous densities satisfies `Ψ(ε) ≤ 0`
for every `ε > 0` (`no_kinematic_one_step_persistence`).  The defect can hide
entirely in the annulus discarded by halving the radius, so a genuine one-step
lemma **must** consume the Navier–Stokes evolution — a local energy/Caccioppoli
inequality with its dissipation, or a monotonicity formula.

## 4. The A-side no-go that forces the dynamics (`GradientEnergyScaling.lean`)

* `QgradCyl_le_of_bounded` — if the density is bounded by `A` on the cylinder,
  `Q_∇(r) ≤ A·|B₁|·r⁴`.  So `Q_∇(r) → 0` as `r → 0` for *any* field with locally
  bounded gradient: the zero-loss gate (antitonicity in `r`) is false for
  regular fields, and any proof of it must consume the Navier–Stokes dynamics
  near the singularity.  This is the `A`-side analogue of the linear-skeleton
  no-go on the `C` side.
* `sup_gradient_ge_of_velocityScale_defect` — conversely `A_dyn` is
  scale-consistent: a defect `ε` at radius `1/M` forces
  `sup|∇u|² ≥ ε M⁴/|B₁|`, i.e. `|∇u| ≳ M²`, exactly the KNSŠ rate.

## 5. The `C_localDG` engines

* `IncrementConvexSubsolution.lean` — the pointwise half of `C_b`: for `ν ≥ 0`
  and every smooth convex `β`, `β(q)` with `q = ½|δ_h u|²` satisfies
  `∂_t β(q) + u(·+h)·∇β(q) ≤ νΔβ(q) + β'(q)·(source)`, the only inequality used
  being `−νβ''(q)|∇q|² ≤ 0`.  With an entrywise strain bound `K` and `β' ≥ 0`
  the source is `6K·q − δ_h u·∇δ_h p − ν|∇δ_h u|²`
  (`increment_convex_subsolution_strain`): a linear parabolic inequality with a
  potential coefficient, as expected.
* `IncrementLevelSetEnergy.lean` — the *integrated* half of `C_b` over the
  periodic cell: both structural terms vanish exactly (the Laplacian is a
  divergence of a periodic field; the transport is `div(β(q)·u(·+h))` because
  the shifted velocity is divergence free), leaving
  `d/dt ∫β(q) ≤ ∫β'(q)·(source)` for every smooth convex `β` simultaneously
  (`deriv_incrBetaEnergy_le`, potential form `deriv_incrBetaEnergy_le_potential`).
* `IncrementLocalizedLevelSet.lean` — the *localized* (cutoff) version, which is
  what the De Giorgi iteration actually consumes:
  `∂_t(Φβ(q)) + div(Φβ(q)u(·+h) − ν(Φ∇β(q) − β(q)∇Φ))
     ≤ ∇Φ·(β(q)u(·+h)) + νβ(q)ΔΦ + Φβ'(q)·(source)`
  (`increment_localized_level_set_inequality`, potential form
  `increment_localized_level_set_strain`).  The same file proves the structural
  half of `C_a`: with weight `W = Φβ'(q)` the pressure source is a divergence
  minus pairings of `δ_h p` with `∇Φ` and with `β''(q)∇q`
  (`incr_pressure_weighted_divergence`, `incr_pressure_localized_split`).  So no
  global pressure bound is needed — only the pressure *oscillation* where
  `∇Φ ≠ 0`, exactly the quantity the gauge invariance of
  `KarmanHowarthPressureGauge.lean` lets one normalise.
* `DeGiorgiIteration.lean` — the two abstract engines: the fast geometric
  convergence lemma `deGiorgi_fast_convergence` (with its threshold
  `Y₀ ≤ C^{-1/α}b^{-1/α²}` and conclusion `Y_n ≤ Y₀ b^{-n/α} → 0`), and the
  Giaquinta–Giusti hole-filling lemma `holeFilling_iteration`, which absorbs a
  Caccioppoli right-hand side containing the estimated quantity.

## 6. Status

The literal periodic Clay target `ClayNS.ClayPeriodicTargetB` is **not** proved,
and nothing was weakened, axiomatized, or replaced by a conditional bridge.
The two frontier items remain, now in the sharpened form recorded in
`OpenGates.lean`:

* **A_cascade** — a monotonicity (or summable-defect almost-monotonicity)
  formula for `r ↦ Q_∇(u; x, t, r)` between the energy and velocity scales along
  the singular sequence.  Everything around it — the step count, the shape
  criterion, the frequency mechanism, the scaling consistency, and the reduction
  to `A_dyn` — is proved.
* **C_localDG** — the pointwise subsolution property, the integrated level-set
  energy inequality, the localized (Caccioppoli) level-set inequality, the
  structural half of `C_a`, and both iteration engines are proved.  What is
  missing is the *quantitative* half of `C_a` — a Calderón–Zygmund/BMO bound on
  the pressure oscillation on the support of `∇Φ` — and `C_c`, i.e. feeding the
  localized inequality into `deGiorgi_fast_convergence`/`holeFilling_iteration`
  to produce unit-scale oscillation decay.

Additionally, the new §3c no-go removes a whole class of candidate `A_cascade`
proofs: no one-dyadic-step persistence inequality can be established by
measure-theoretic or geometric means alone.

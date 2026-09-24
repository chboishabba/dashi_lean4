# Round 43 — the three-lemma tranche (A₁, C₁, C₂)

This note records what was formalized in the round that targeted the three
named analytic lemmas

* `A₁ = NSCriticalGradientAlmostMonotonicity`,
* `C₁ = IncrementPressureBMOAbsorption`,
* `C₂ = IncrementDeGiorgiRecurrence`,

and — just as importantly — what is still open. Every Lean file cited below
compiles inside `lake build RequestProject` with no `sorry`, no `postulate`, no
`axiom`, and `#print axioms` reporting only `propext`, `Classical.choice`,
`Quot.sound`.

## C₁ — the pressure pairing: **delivered**, with one substitution

`RequestProject/NavierStokes/IncrementPressureAbsorption.lean`

```
ClayNS.increment_pressure_absorption :
  |∫ Φ β'(q) (δ_h u · ∇ δ_h p)|
      ≤ η ν ∫ Φ β''(q) |∇q|²
        + (D²B / 4ην) · Osc
        + D G K · √Osc,      Osc = 12 A² ∫ |∇u|².
```

Supporting material: `CellShift.lean` (translation invariance of the cell
integral), `CellL2.lean` (Cauchy–Schwarz and weighted Young on the cell),
`PressureL2Oscillation.lean` (`∫|∇p|² = −∫∇p·(u·∇)u`, hence
`∫|∇p|² ≤ A²∫|∇u|²` and the cell-Poincaré oscillation bound).

**Substitution made, and why.** The requested input was BMO + John–Nirenberg
for `δ_h p − c_A`. Mathlib carries no BMO/John–Nirenberg theory, and the Young
absorption step only ever consumes an `L²` oscillation bound. So the BMO step is
replaced by an elementary, fully proved *periodic `L²` pressure-oscillation
estimate* obtained by energy-testing the Poisson equation `−Δp = ∂ᵢ∂ⱼ(uᵢuⱼ)` and
applying the cell Poincaré inequality. The conclusion consumed downstream is the
same; the route to it is shorter and is proved rather than cited.

Gauge freedom (the "subtract an annular mean" step) is present and proved:
`cellInt_incrDrift_eq_zero` shows the pairing is unchanged by adding an arbitrary
constant to the pressure increment.

## C₂ — the De Giorgi recurrence: **delivered modulo one flagged input**

`RequestProject/NavierStokes/DeGiorgiRecurrence.lean`

```
ClayNS.deGiorgi_dyadic_recurrence :
  Y_{n+1} ≤ (C_S^{3/5} 4^{2/5} k_∞^{-4/5}) · (4^{7/5})ⁿ · Y_n^{1+2/5}
```

for the *actual* dyadic level sequence `k_n = k_∞(1 − 2^{-n})` and the actual
level-set energies `Y_n = ∫_{w>k_n}(w − k_n)²` of a bounded measurable density on
a finite measure space. The exponent `α = 2/5` is the three-dimensional
parabolic one, and `b = 4^{7/5} > 1`; this is exactly the hypothesis shape of the
already-proved `deGiorgi_fast_convergence` / `deGiorgi_tendsto_zero`
(`deGiorgi_recurrence_tendsto_zero` performs the chaining).

The two ingredients are proved separately:

* `chebyshev_deGiorgiLevel` — the measure estimate `m_{n+1} ≤ 4^{n+1}k_∞^{-2}Y_n`,
  i.e. `1_{w>k_{n+1}} ≤ (k_{n+1}−k_n)^{-2}(w−k_n)_+²` integrated;
* `hoelder_levelEnergy` / `deGiorgi_level_step_measure` — Hölder with the
  conjugate pair `(5/3, 5/2)`, producing the `3/5` and `2/5` exponents.

**Flagged input.** The parabolic Sobolev/Gagliardo–Nirenberg energy embedding

```
∫_{w>k_{n+1}} ((w−k_{n+1})²)^{5/3} ≤ C_S (4ⁿ Y_n)^{5/3}
```

(the `L^{10/3}` gain of the localized Caccioppoli inequality) enters as an
explicit hypothesis `hEmb`.

### The `L^{10/3}` gain itself is now proved

`RequestProject/NavierStokes/ParabolicGain.lean` supplies the analytic
inequality behind `hEmb`, from Mathlib's Gagliardo–Nirenberg–Sobolev theorem:

* `sobolev_L6_le` — `‖v‖_{L⁶(ℝ³)} ≤ C‖∇v‖_{L²(ℝ³)}` for `C¹` compactly supported
  `v`, with `C = sobolevConstE3`;
* `interpolation_L10over3` — `∫|v|^{10/3} ≤ (∫|v|⁶)^{1/3}(∫v²)^{2/3}` (Hölder
  with conjugate pair `(3, 3/2)`);
* `parabolic_L10over3_gain` — `∫|v|^{10/3} ≤ C²(∫|∇v|²)(∫v²)^{2/3}`;
* `parabolic_L10over3_gain_time` — the space-time form
  `∫_a^b∫|v|^{10/3} ≤ C²S^{2/3}∫_a^b∫|∇v|²` when `sup_t ∫v(t)² ≤ S`;
* `parabolic_gain_of_caccioppoli` — with a single Caccioppoli budget `K`
  bounding *both* the sup-in-time `L²` mass and the total dissipation,
  `∫∫|v|^{10/3} ≤ C²K^{5/3}`. Taking `K = 4ⁿY_n` this is *literally* `hEmb`, with
  `C_S = sobolevConstE3²`.

So what remains of C₂ is no longer the embedding: it is the localized
Caccioppoli bound `sup_t ∫Φ(q−k_n)_+² + ∫∫Φ|∇(q−k_n)_+|² ≲ 4ⁿY_n` for the
increment density `q = ½|δ_h u|²`, for which the pointwise and integrated
level-set inequalities and the pressure absorption `C₁` are in place.

## The rescaling audit — **the correctness condition is now a theorem**

`RequestProject/NavierStokes/RescalingAudit.lean`

The concern flagged with C₂ was that `AncientOscillationContraction.lean`
reduces the oscillation contraction to a single unit-scale improvement via
`contraction_of_unit_step`, whose hypothesis is closure of the class under
`U_λ(x,t) = λU(λx, λ²t)` for **all** `λ > 0`. The audit is now formal:

* `unitNormClass_parRescale_inward` — the KNSŠ class `‖U‖_∞ ≤ 1` *is* closed
  under inward rescaling `0 < λ ≤ 1`;
* `unitNormClass_not_rescaling_closed` — it is **not** closed under outward
  rescaling (`‖U_λ‖_∞ = λ > 1` for a constant unit field), so the reduction may
  not be applied to it;
* `contraction_of_unit_step_inward` — inward closure alone yields the
  contraction only at scales `R ≤ 1`;
* `exists_nonconstant_of_smallScale_contraction` — and that is genuinely
  insufficient: there is a normalized field which contracts at *every* scale
  `R ≤ 1`, for arbitrary `θ ∈ (0,1]` and arbitrary `σ`, and is not constant on
  the ancient region.

So a De Giorgi oscillation improvement obtained at one fixed unit cylinder,
however strong, cannot be welded to
`ancient_constant_of_oscillation_contraction`; the improvement must hold for a
Navier–Stokes-scale-invariant class. This is a genuine constraint on the
*statement* of the downstream C lemma, now recorded as a proved no-go rather than
a remark.

## A₁ — the almost-monotonicity for `Q_∇`: **template step proved, lemma open**

`RequestProject/NavierStokes/CriticalGradientMonotonicity.lean`

Working against the *actual* quantity
`Q_∇(r) = r⁻¹∫_{t₀−r²}^{t₀}∫_{B_r(x₀)}|∇u|²` (not by analogy with Almgren
frequency), write `E(r)` for the un-normalized cylinder dissipation, so
`Q_∇ = r⁻¹E`. Then:

```
ClayNS.rmul_QgradCylDeriv :  r · Q_∇'(r) = E'(r) − Q_∇(r).
```

Nothing is discarded here: the radial-boundary and bottom-time contributions are
*precisely* the two pieces of `E'(r)`. Consequently

```
ClayNS.critical_frequency_of_dissipation_growth
ClayNS.dissipation_growth_of_critical_frequency
```

show that the target inequality `r·Q_∇' ≤ r·D·Q_∇` is **equivalent** to the
dissipation-growth bound `E'(r) ≤ (1 + r·D(r))·Q_∇(r)`, and
`defect_propagates_of_dissipation_growth` feeds that directly into the
already-proved almost-monotonicity theorem, giving the single factor
`e^{−(Φ(b)−Φ(a))}`.

The residual gap is now quantified, not just named:

* `totalDefect_le_of_dissipation` — with `Q_∇ ≥ ε` on `[a,b]`, the only bound on
  the total defect available from *size* information is
  `∫_a^b D ≤ (E(b) − E(a))/(a·ε)`;
* `naive_defect_bound_degenerates` — at the cascade endpoints `a = 1/M`,
  `b ≍ M^{-2/3}` with `E(b) = b·Q_∇(b) ≍ b·ε`, that bound equals `M^{1/3}` and
  tends to infinity.

So the size-only route to a uniform `E_*` provably fails, by exactly the factor
`M^{1/3}` (the ratio of the two cascade scales). `A₁` must exhibit a genuine
cancellation inside the Navier–Stokes local energy identity — the correction term
of the Lin/CKN monotonicity argument. **That derivation is not present here, and
`A₁` is not proved.**

## Status of the literal Clay target

`ClayNS.ClayPeriodicTargetB` remains **not proved**. The first unresolved
obligations, in order, are:

1. `A₁` — the dissipation-growth bound `E'(r) ≤ (1 + rD(r))Q_∇(r)` with
   `∫_{1/M}^{M^{-2/3}} D ≤ E_*` uniform along the singular sequence, for which
   the size-only estimate is now proved to be insufficient;
2. the localized Caccioppoli budget `K = 4ⁿY_n` for the truncations of the
   increment density, which is now the *only* missing input of `hEmb`
   (the `L^{10/3}` embedding itself is proved in `ParabolicGain.lean`);
3. a scale-invariant formulation of the oscillation improvement, as forced by
   `exists_nonconstant_of_smallScale_contraction`.

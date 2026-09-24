# The Round 105 Waleffe network-forcing wall, made literal and reduced

This note records what the Lean development in `RequestProject/NavierStokes/Waleffe*.lean`
and `RequestProject/NavierStokes/CriticalSimonUpgradeObligations.lean` establishes about the
current Navier–Stokes frontier obligation
`PhysicalWeightedPositiveWaleffeNetworkForcingBudget`, and what remains open.

Everything cited below compiles with no `sorry` and depends only on the standard
axioms `propext`, `Classical.choice`, `Quot.sound`.

## 1. The object, made literal

The Agda frontier keeps the forcing in the damped–forced amplitude equation abstract
(the "physical Galerkin forcing identification" is recorded there as *not* closed).
The Lean development instantiates the whole object:

* lattice `Wave = ℤ³`, `|k|²` (`wsq`), Leray projection `leray`;
* truncated advection `((u·∇)u)^_k = ∑_{p ∈ modes} i (u_p · (k−p)) u_{k−p}` (`advection`)
  and modal forcing `f_k = −P_k ((u·∇)u)^_k` (`modalForcing`);
* `GalerkinFlow`: finite mode set of nonzero wavevectors, coefficients supported on it,
  transverse, obeying the reality condition, and solving `u̇_k = −ν|k|² u_k + f_k`;
* triad amplitude `A_τ = Re⟪u_k, u_p×u_q⟫`, rate `γ_τ = ν(|k|²+|p|²+|q|²)`, network
  forcing `F_τ` (the three product-rule slots).

`GalerkinFlow.triad_amplitude_ode` proves `Ȧ_τ = −γ_τ A_τ + F_τ` for the *literal*
projected nonlinearity — this is the identification step left open on the Agda side.

`weighted_integrated_production_payment` then shows exactly what the budget buys:
given the pointwise phase-damping comparison `ν P_τ ≤ 2 γ_τ (A_τ)₊`,

```
ν ∑_τ w_τ ∫ P_τ ≤ 2 ∑_τ w_τ (A_τ(t₀))₊ + 2 ∑_τ w_τ ∫ (F_τ)₊ .
```

The wall itself is `PhysicalWeightedPositiveWaleffeNetworkForcingBudget nu T w`:
for arbitrary rapidly decaying data and fixed viscosity, a bound on
`∑_τ w_τ ∫_0^T (F_τ)₊` that is **uniform over all Galerkin truncations**.

## 2. Structural facts proved about the forcing

* `pair_self_forcing_signed_square`: the pair contribution of a triad to its own
  forcing is the *signed square* `(λ_q − λ_p) ‖P_k(u_p × u_q)‖²`. Only the genuinely
  external part of the network forcing can be adverse.
* `netForcing_smul` / `modalForcing_smul`: the wall is quartic in the field, while the
  energy is quadratic — no scaling identity can convert one into the other.
* `nrm_modalForcing_le`: the literal forcing is bounded by the `ℓ¹` convolution
  majorant `∑_p |u_p| |k−p| |u_{k−p}|`.

## 3. Two reductions of the wall to one scalar quantity

Write, on the retained modes,

```
‖u‖_A  = ∑_k |u_k|            (Wiener)
‖u‖_D  = ∑_k |k| |u_k|
‖u‖_2  = (∑_k |u_k|²)^{1/2}    (energy)
‖u‖_Ḣ¹ = (∑_k |k|² |u_k|²)^{1/2}  (Dirichlet)
```

**First reduction** (`WaleffeWienerBudget.lean`). Summing the kinematic majorant over
the resonance set `k = p + q` gives, for weights `0 ≤ w_τ ≤ W`, the pointwise bound
`∑_τ w_τ (F_τ)₊ ≤ 3 W ‖u‖_A³ ‖u‖_D` (`network_forcing_pointwise_bound`), hence
`weightedPositiveForcing_le_wiener`, hence `budget_of_uniform_wiener_expenditure`: the
wall follows from `UniformWienerExpenditure`, a truncation-uniform bound on
`∫_0^T ‖u‖_A³ ‖u‖_D dt`.

**Second, sharper reduction** (`WaleffeSerrinReduction.lean`). The resonance sums are
convolutions, so discrete Young `ℓ¹ ⋆ ℓ² → ℓ²` keeps only one `ℓ¹` factor per
convolution:

* `forcingL2_le`: `‖f‖_2 ≤ ‖u‖_A ‖u‖_Ḣ¹` for the literal projected nonlinearity;
* `network_forcing_serrin_bound`: `∑_τ w_τ (F_τ)₊ ≤ 3 W ‖u‖_A² ‖u‖_2 ‖u‖_Ḣ¹`;
* `weightedPositiveForcing_le_serrin`, `budget_of_uniform_serrin_expenditure`: the wall
  follows from `UniformSerrinWienerExpenditure`, a truncation-uniform bound on
  `∫_0^T ‖u‖_A² ‖u‖_2 ‖u‖_Ḣ¹ dt`.

No derivative is left in `ℓ¹` after the second reduction. Of the three factors, `‖u‖_2`
and the time-integrated `‖u‖_Ḣ¹²` are exactly what a Navier–Stokes energy balance pays
for; the residue is the time-integrated **square of the Wiener norm** — a Serrin-type
`L⁴_t` condition in the Wiener algebra.

## 4. Why the residue cannot be paid by the energy

`WaleffeWienerSupercritical.lean` proves that the remaining input is genuinely
supercritical rather than an artefact of the majorisation:

* `wienerA_le_sqrt_card_energy`, `wienerD_le_sqrt_card_enstrophy`: passing from `ℓ²` to
  `ℓ¹` costs exactly `√(#modes)`, which is not uniform in the truncation;
* `wiener_norm_not_controlled_by_energy`: for every `M` there is a transverse,
  mode-supported field of total energy `1` whose Wiener norm exceeds `M`;
* `flat_spectrum_saturates`: the flat spectra attain the Cauchy–Schwarz loss.

So the `√(#modes)` loss is sharp for the energy, and any closure of the wall must use
dynamics (the equation), not kinematics.

## 5. Status of the wall

The wall is **neither proved nor falsified** here. What changed:

* it is now a literal statement about the physical Galerkin system, with the forcing
  identification closed;
* its self-forcing part is computed exactly and is a signed square;
* it is implied by a single scalar time-integrated quantity, in two successively
  sharper forms, the second free of `ℓ¹` derivatives;
* the residual quantity is proved not to be controlled by the energy, with a sharp
  constant and an explicit saturating family.

The single remaining A-side obligation is therefore:

> **(A)** a truncation-uniform bound on `∫_0^T ‖u(t)‖_A² ‖u(t)‖_2 ‖u(t)‖_Ḣ¹ dt`
> for the Galerkin flows of an arbitrary rapidly decaying datum
> (`UniformSerrinWienerExpenditure`).

## 6. The critical Sobolev/Simon upgrade

`CriticalSimonUpgradeObligations.lean` states the second frontier obligation as exactly
three `Prop`s in the same Fourier-lattice language (identification only; none is
asserted or used):

1. `CriticalTimeRegularity` — truncation-uniform `L^{4/3}_t H^{-1/2}_x` bound for `∂_t u_N`;
2. `StrongCriticalCompactness` — strong `L²_t H^{1/2}_x` convergence of a subsequence;
3. `CriticalBarrierLowerSemicontinuity` — the critical barrier passes to the limit for
   almost every time.

## 7. Ledger

| Item | Status |
| --- | --- |
| physical Galerkin forcing identification (`triad_amplitude_ode`) | proved |
| pointwise phase-damping payment, Kato integration, network summation | proved |
| self-forcing signed-square law | proved |
| kinematic majorant of the network forcing | proved |
| Wiener reduction of the wall | proved |
| Serrin-type sharpened reduction of the wall | proved |
| energy does not control the Wiener norm (sharp) | proved |
| `UniformSerrinWienerExpenditure` (the wall's residue) | **open** |
| three critical Simon-upgrade lemmas | **open** (stated) |
| Clay promotion | not established |

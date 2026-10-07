# Exact LeanDojo Fefferman C transport audit

Acceptance target: pinned `MillenniumNavierStokes.FeffermanC`.

The old statement-level assumption

```text
ClaySpec.ClayOptionC ↔ MillenniumNavierStokes.FeffermanC
```

is not used by the direct max-cut.

The released comparator theorem already supplies the breakdown witness, and `Gap.lean` already pays both semantic directions needed around the independent Clay representation:

```text
comparator data -> ClaySpec.AdmissibleDataR3
ClaySpec.ClaySolutionR3 -> comparator solution
```

`LeanDojoCarrierGeometry.lean` additionally source-writes:

```text
space (spacetime_point t x) = x
time  (spacetime_point t x) = t
pair-field packing/unpacking round-trip
closed-domain membership at spacetime_point
generic ambient-smooth -> pair-spacetime-smooth pullback
ClaySpec initial divergence -> LeanDojo initial divergence
```

The solution initial condition is also source-written directly from `GlobalSmoothSolution.initial_condition` and the carrier round-trip. LeanDojo's own `Breakdown.iff_no_finite_energy_solution` removes the redundant condition-(6) witness from the contradiction branch.

The surviving obligations are therefore exactly five:

1. `ClayInitialDecayToLeanDojo`
   - align ClaySpec coordinate-direction derivative packaging and nonnegative decay constants with LeanDojo `SmoothRapidDecayInitial` coordinate partials and positive constants.
2. `ClayForceToLeanDojo`
   - fixed packing through `pairFieldToLeanDojo` into time-first ambient `Fin 4` spacetime;
   - transport ClaySpec force derivative packaging to LeanDojo `SmoothRapidDecayForce`.
3. `LeanDojoMomentumToClay`
   - transport the ambient positive-time momentum equation to ClaySpec pair coordinates;
   - extend the equality to `t = 0` from the already-paid smoothness.
4. `LeanDojoIncompressibleToClay`
   - transport ambient divergence to ClaySpec pair coordinates;
   - extend from `t > 0` to `t = 0`.
5. `LeanDojoEnergyToClay`
   - identify LeanDojo's finite coordinate-square energy representation with ClaySpec's vector `MemLp` and norm-square integral representation.

The composition is now:

```text
released comparator C
-> existing comparator-data -> ClaySpec weld
-> paid carrier/smoothness/divergence/initial-condition geometry
-> five representation leaves
-> literal ClaySpec.ClaySolutionR3
-> existing ClaySpec-solution -> comparator weld
-> contradiction
-> exact pinned LeanDojo Fefferman C
```

There is no remaining fluid estimate in the external acceptance seam. The two boundary-extension leaves are routine analytic representation obligations, not a new Navier--Stokes estimate.

Promotion rule: NS remains fail-closed until all five residual transports are inhabited and the unconditional exact target theorem kernel-checks. A conditional compiler is not GREEN.

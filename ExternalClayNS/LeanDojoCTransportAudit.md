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

`LeanDojoCarrierGeometry.lean` additionally pays:

```text
space (spacetime_point t x) = x
time  (spacetime_point t x) = t
pair-field packing/unpacking round-trip
closed-domain membership at spacetime_point
ClaySpec initial divergence -> LeanDojo initial divergence
```

The surviving obligations are therefore exactly:

1. `ClayInitialDecayToLeanDojo`
   - the spatial carrier, smoothness field and divergence clause are already paid;
   - align only ClaySpec's coordinate-direction derivative packaging/weakly-nonnegative decay constant with LeanDojo `SmoothRapidDecayInitial`'s coordinate partial packaging/strictly-positive constant.
2. `ClayForceToLeanDojo`
   - fixed packing through `pairFieldToLeanDojo` into LeanDojo's time-first ambient `Fin 4` spacetime;
   - transport ClaySpec force smoothness / mixed coordinate-derivative decay to LeanDojo `SmoothRapidDecayForce`.
3. `LeanDojoSolutionToClaySpec`
   - fixed unpacking through `leanDojoFieldToPair`;
   - transport a LeanDojo `GlobalSmoothSolution + FiniteEnergy` into literal `ClaySpec.ClaySolutionR3`.

`leanDojoFeffermanC_of_transport` composes:

```text
released comparator C
-> existing comparator-data -> ClaySpec weld
-> paid carrier/divergence geometry
-> the three residual transports above
-> existing ClaySpec-solution -> comparator weld
-> contradiction
-> exact pinned LeanDojo Fefferman C
```

LeanDojo's own `Breakdown.iff_no_finite_energy_solution` also confirms that condition (6) is already carried by `GlobalSmoothSolution`; no separate smooth-solution proof is mathematically required at this boundary.

There is no remaining fluid estimate in this acceptance seam.

Promotion rule: NS remains fail-closed until all three residual representation transports are inhabited and the unconditional exact target theorem kernel-checks. A conditional compiler is not GREEN.

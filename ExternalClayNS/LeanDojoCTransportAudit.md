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

Therefore comparator derivative/PDE semantics are **not** reopened at the external adapter.  The surviving obligations are exactly the representation transports between ClaySpec's pair spacetime and LeanDojo's time-first ambient `Fin 4` spacetime:

1. `ClayInitialToLeanDojo`
   - the spatial carrier is already literally `EuclideanSpace ℝ (Fin 3)`;
   - align ClaySpec initial divergence / coordinate-derivative decay with LeanDojo `DivergenceFreeInitial` / `SmoothRapidDecayInitial`.
2. `ClayForceToLeanDojo`
   - fixed packing `f (space z) (time z)` into LeanDojo's ambient spacetime;
   - transport ClaySpec force smoothness / coordinate-derivative decay to LeanDojo `SmoothRapidDecayForce`.
3. `LeanDojoSolutionToClaySpec`
   - fixed unpacking `u (spacetime_point t x)` and `p (spacetime_point t x)` onto ClaySpec pair spacetime;
   - transport a LeanDojo `GlobalSmoothSolution + FiniteEnergy` into literal `ClaySpec.ClaySolutionR3`.

`leanDojoFeffermanC_of_transport` then composes:

```text
released comparator C
-> existing comparator-data -> ClaySpec weld
-> the three representation transports above
-> existing ClaySpec-solution -> comparator weld
-> contradiction
-> exact pinned LeanDojo Fefferman C
```

There is no remaining fluid estimate in this acceptance seam.

Promotion rule: NS remains fail-closed until all three representation transports are inhabited and the unconditional exact target theorem kernel-checks. A conditional compiler is not GREEN.

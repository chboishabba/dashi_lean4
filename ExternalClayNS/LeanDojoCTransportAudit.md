# Exact LeanDojo Fefferman C transport audit

Acceptance target: pinned `MillenniumNavierStokes.FeffermanC`.

The old statement-level assumption

```text
ClaySpec.ClayOptionC ↔ MillenniumNavierStokes.FeffermanC
```

is not used by the direct max-cut.  The released comparator theorem already supplies the breakdown witness.  The surviving representation obligations are exactly:

1. `ComparatorInitialToLeanDojo`
   - same literal spatial carrier `EuclideanSpace ℝ (Fin 3)`;
   - prove comparator smooth/divergence/operator-norm decay entails LeanDojo `SmoothRapidDecayInitial` and `DivergenceFreeInitial`.
2. `ComparatorForceToLeanDojo`
   - fixed force packing `f (space z) (time z)` from curried `(x,t)` to LeanDojo time-first `Fin 4` spacetime;
   - prove comparator smooth/operator-norm decay entails LeanDojo `SmoothRapidDecayForce`.
3. `LeanDojoSolutionToComparator`
   - fixed unpacking through `spacetime_point t x`;
   - prove a LeanDojo `GlobalSmoothSolution` with `FiniteEnergy` satisfies the exact comparator solution structure on the original curried force.

`leanDojoFeffermanC_of_transport` then composes those three representation lemmas with `SemanticGapAdapter.openAIComparatorOptionC`; there is no remaining fluid estimate in the external acceptance seam.

Promotion rule: NS remains fail-closed until all three transports are inhabited and the unconditional exact target theorem kernel-checks.  A conditional compiler is not GREEN.

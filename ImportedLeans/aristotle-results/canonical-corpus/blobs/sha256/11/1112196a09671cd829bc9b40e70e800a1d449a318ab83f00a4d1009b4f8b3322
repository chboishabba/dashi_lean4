import Integration.PipelineAdequacy
import AgdaMirror.FibreAveraging

/-!
# The averaging/residual pipeline, arrow by arrow

The corpus supplies a complete, checked, multi-stage numeric pipeline in
`Agda/DASHI/Analysis/NormalizedFibreAveragingExact.agda` and
`Agda/DASHI/Analysis/WeightedCoarseFineOrthogonalExact.agda`, transcribed in
`AgdaMirror.FibreAveraging`:

```
  fine observable  ──average──▶  within-domain aggregate
        │                                │
        │                             pullback
        ▼                                ▼
     residual  Q = id − P  ◀── subtract ── P = pullback ∘ average
```

This file classifies **every arrow** of that pipeline against the frozen
Level-II owners, and nothing else.  No new owner and no new abstraction is
introduced: each result below is `Integration.FactorisationCollision` or
`Integration.CoordinateSufficiency` applied to a mirror definition.

## The classification

| arrow | question | answer | owner |
|---|---|---|---|
| `pullback` | does reading a coarse quantity fibrewise lose anything? | no | `Determines` (`pullback_injective`) |
| `average` | does the within-domain aggregate preserve the residual? | **no** | `Collision` (`compensationCollision`) |
| `average` | does it preserve the coarse component? | yes, exactly | `Determines` (`average_determines_coarse`) |
| `decompose` | does the aggregate/residual pair determine the observable? | yes | `Determines` (`decompose_determines_observable`) |
| any downstream stage | can a later computation recover the residual? | **no** | `Collision.no_reading` (`no_reading_of_the_average_recovers_the_residual`) |

The middle row is the point.  The corpus's *compensation* phenomenon — two fine
observables whose fibre values cancel in the mean — is exactly
`Collision average Q`, and once it is filed there the whole tail of the
pipeline follows from `Integration.PipelineAdequacy` without any further
argument.  `averaging_repair_is_representational` records which of the two
repairs is available: not a different downstream computation, but carrying the
residual.

Every carrier is `ℚ`, `Unit`, a two-element fibre, or a function type built
from those.  Nothing here is a claim about measure theory, indicators or any
domain.
-/

namespace Integration.AveragingResidualWeld

open Integration.CoordinateSufficiency
open Integration.FactorisationCollision
open Integration.PipelineAdequacy
open AgdaMirror.FibreAveraging

/-! ## The arrows that lose nothing -/

/-- Reading a coarse observable fibrewise loses nothing: `pullback` is
injective, because fibre averaging inverts it (`averagePullback`, which is the
corpus's normalisation identity `fibreMass = 1`). -/
theorem pullback_injective {Base : Type} :
    Function.Injective (pullback : CoarseObservable Base → FineObservable Base) := by
  intro f g h
  funext y
  rw [← averagePullback f y, ← averagePullback g y, h]

/-- **Averaging preserves the coarse component exactly.**  `P` is a reading of
the aggregate, so two observables with the same aggregate have the same coarse
component. -/
theorem average_determines_coarse {Base : Type} :
    Determines (average : FineObservable Base → CoarseObservable Base) P := by
  intro f g h
  simp only [P, h]

/-- The aggregate of the coarse component is the aggregate itself. -/
theorem average_P {Base : Type} (g : FineObservable Base) : average (P g) = average g := by
  funext y
  simp only [average, P, pullback, weight]
  ring

/-- **The aggregate/residual pair determines the observable.**  This is the
corpus's `coarsePlusResidual`, read as a sufficiency statement. -/
theorem decompose_determines_observable {Base : Type} :
    Determines (decompose : FineObservable Base → Decomposition Base) id := by
  intro f g h
  funext x
  have h1 : P f = P g := congrArg Prod.fst h
  have h2 : Q f = Q g := congrArg Prod.snd h
  have := coarsePlusResidual f x
  rw [h1, h2, coarsePlusResidual g x] at this
  exact this.symm

/-! ## The arrow that loses the residual -/

/-- The zero fine observable over a one-point coarse carrier. -/
def flat : FineObservable Unit := fun _ => 0

/-- A fine observable whose two fibre values cancel in the mean: this is the
compensation configuration. -/
def compensating : FineObservable Unit := fun x =>
  match x.2 with
  | .leftFibre => 1
  | .rightFibre => -1

theorem average_flat : average flat = fun _ => 0 := by
  funext y; simp [average, flat, weight]

theorem average_compensating : average compensating = fun _ => 0 := by
  funext y; simp only [average, compensating, weight]; norm_num

/-- **The compensation phenomenon is a collision.**  Two fine observables with
the same within-domain aggregate and different residuals.  No new vocabulary is
needed for it: it is `Collision average Q`. -/
def compensationCollision : Collision (average (Base := Unit)) Q where
  left := flat
  right := compensating
  distinct := by
    intro h
    have := congrFun h ((), Fibre2.leftFibre)
    simp [flat, compensating] at this
  collide := by rw [average_flat, average_compensating]
  separate := by
    intro h
    have := congrFun h ((), Fibre2.leftFibre)
    simp only [Q, P, pullback, flat, compensating, average_flat, average_compensating] at this
    norm_num at this

/-- **The within-domain aggregate does not determine the residual vector.** -/
theorem average_does_not_determine_residual :
    ¬ Determines (average (Base := Unit)) Q :=
  compensationCollision.not_determines

/-- **And no later stage repairs it.**  No reading whatsoever of the aggregate
returns the residual, so no downstream deterministic processing can recover the
distinction the aggregate destroyed. -/
theorem no_reading_of_the_average_recovers_the_residual
    (f : CoarseObservable Unit → FineObservable Unit) :
    ¬ ∀ g, Q g = f (average g) :=
  compensationCollision.no_reading f

/-- **Which repair is available.**  Not a different downstream computation —
carrying the residual alongside the aggregate. -/
theorem averaging_repair_is_representational :
    ¬ ComputationRepair (average (Base := Unit)) Q ∧
      RepresentationRepair (average (Base := Unit)) Q :=
  repair_dichotomy compensationCollision

/-- And the repair is realised by the corpus's own `decompose`: it refines the
aggregate (the aggregate is recoverable from it) and it determines the
residual. -/
theorem decompose_is_the_repair {Base : Type} :
    (∀ g : FineObservable Base, average g = average (decompose g).1) ∧
      Determines (decompose : FineObservable Base → Decomposition Base) Q :=
  ⟨fun g => (average_P g).symm, fun _ _ h => congrArg Prod.snd h⟩

/-! ## The pipeline, collected -/

/-- **Every arrow of the corpus's averaging pipeline, classified.**  Pullback
loses nothing; averaging preserves the coarse component exactly and loses the
residual; the decomposition recovers the observable; and no reading of the
aggregate recovers what averaging lost. -/
theorem averaging_pipeline_classified :
    Function.Injective (pullback : CoarseObservable Unit → FineObservable Unit) ∧
      Determines (average (Base := Unit)) P ∧
      ¬ Determines (average (Base := Unit)) Q ∧
      Determines (decompose : FineObservable Unit → Decomposition Unit) id ∧
      (∀ f : CoarseObservable Unit → FineObservable Unit, ¬ ∀ g, Q g = f (average g)) :=
  ⟨pullback_injective, average_determines_coarse, average_does_not_determine_residual,
    decompose_determines_observable, no_reading_of_the_average_recovers_the_residual⟩

end Integration.AveragingResidualWeld

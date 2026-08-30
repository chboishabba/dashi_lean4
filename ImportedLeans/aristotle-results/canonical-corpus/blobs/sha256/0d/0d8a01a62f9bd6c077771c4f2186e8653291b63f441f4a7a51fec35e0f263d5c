import Integration.FactorisationCollision
import Integration.RealisationAdequacy

/-!
# Multi-stage pipelines: a collision at one stage is never repaired downstream

`Integration.FactorisationCollision` owns the single-stage statement: if an
observation `P` identifies two states that a consumer `C` separates, then `C`
does not factor through `P`, and `Collision.post` says the same of any further
processing of `P`.

A *pipeline* is a chain of such stages,

```
  A 0 ──step 0──▶ A 1 ──step 1──▶ A 2 ──▶ … ──▶ A n
```

and the question a mature pipeline needs answered is not about one stage but
about the whole tail: **once a consumer-relevant distinction has been collapsed
at stage `i`, can any later deterministic processing recover it?**  The answer
is no, and this file proves it in the form the corpus needs.

## The two repairs

The theorem separates two things that are easy to conflate.

* A **computation repair** keeps the representation and changes the downstream
  reading: `∃ f, ∀ x, C x = f (P x)`.
* A **representation repair** changes what is carried *before* the collision:
  a finer stage map `P'` from which `P` is still recoverable, and which does
  determine `C`.

`no_computation_repair` says the first is impossible in the presence of a
collision, at every later stage and for every downstream function.
`representationRepair_exists` says the second always exists.  Together
(`repair_dichotomy`) they are the precise statement that changing the algorithm
cannot substitute for restoring the information.

## Contents

* `Stages`, `Stages.upto`, `Stages.run`, `Stages.upto_add` — the chain and its
  tails;
* `Collision.congr` — a collision transports along a pointwise equality of
  observations;
* `collision_propagates` — **the propagation theorem**: a collision at stage `i`
  is a collision at every stage `j ≥ i`;
* `no_downstream_repair`, `no_downstream_determination` — hence no later stage,
  and no reading of a later stage, determines the consumer;
* `ComputationRepair`, `RepresentationRepair`, `no_computation_repair`,
  `representationRepair_exists`, `repair_dichotomy` — the two repairs and the
  theorem that distinguishes them;
* `not_adequateFor_of_state_collision`, `pipeline_adequacy_lost_at_realisation`
  — the same statement in the `Integration.RealisationAdequacy` vocabulary,
  so the consumer-indexed owner inherits it.

Every carrier below is an arbitrary type; nothing here is a claim about any
domain.
-/

namespace Integration.PipelineAdequacy

open Integration.CoordinateSufficiency
open Integration.FactorisationCollision
open Integration.RealisationAdequacy

/-! ## The chain -/

/-- A deterministic multi-stage pipeline: a carrier at each stage and a map to
the next one.  Nothing is assumed about the stages. -/
structure Stages where
  /-- The carrier at each stage. -/
  Carrier : ℕ → Type
  /-- The deterministic map from one stage to the next. -/
  step : ∀ i, Carrier i → Carrier (i + 1)

/-- The composite of the first `i` stages. -/
def Stages.upto (G : Stages) : ∀ i, G.Carrier 0 → G.Carrier i
  | 0 => id
  | i + 1 => fun x => G.step i (G.upto i x)

/-- The tail of the pipeline: `k` further stages starting from stage `i`. -/
def Stages.run (G : Stages) (i : ℕ) : ∀ k, G.Carrier i → G.Carrier (i + k)
  | 0 => id
  | k + 1 => fun x => G.step (i + k) (G.run i k x)

/-- Running `i` stages and then `k` more is running `i + k` stages. -/
theorem Stages.upto_add (G : Stages) (i k : ℕ) (x : G.Carrier 0) :
    G.upto (i + k) x = G.run i k (G.upto i x) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (G.step (i + k)) ih

/-! ## Collisions transport along the chain -/

variable {X Y Y' Z W : Type}

/-- A collision only depends on the observation pointwise. -/
def collisionCongr {P P' : X → Y} {C : X → Z} (w : Collision P C)
    (h : ∀ x, P x = P' x) : Collision P' C where
  left := w.left
  right := w.right
  distinct := w.distinct
  collide := by rw [← h, ← h]; exact w.collide
  separate := w.separate

variable (G : Stages) {Z : Type}

/-- **Propagation.**  A collision of the first `i` stages against a consumer of
the source is a collision of the first `i + k` stages, for every `k`: the
distinction is gone and stays gone. -/
def collision_propagates {C : G.Carrier 0 → Z} {i : ℕ}
    (w : Collision (G.upto i) C) (k : ℕ) : Collision (G.upto (i + k)) C :=
  collisionCongr (w.post (G.run i k)) (fun x => (G.upto_add i k x).symm)

/-- The same statement for an arbitrary later index `j ≥ i`. -/
def collision_propagates_le {C : G.Carrier 0 → Z} {i j : ℕ} (hij : i ≤ j)
    (w : Collision (G.upto i) C) : Collision (G.upto j) C :=
  Nat.add_sub_cancel' hij ▸ collision_propagates G w (j - i)

/-- **No later stage determines the consumer.** -/
theorem no_downstream_determination {C : G.Carrier 0 → Z} {i j : ℕ} (hij : i ≤ j)
    (w : Collision (G.upto i) C) : ¬ Determines (G.upto j) C :=
  (collision_propagates_le G hij w).not_determines

/-- **No later deterministic processing repairs adequacy.**  Once the
distinction is collapsed at stage `i`, no function of any later stage returns
the consumer's value.  This is the pipeline form of `Collision.post`. -/
theorem no_downstream_repair {C : G.Carrier 0 → Z} {i j : ℕ} (hij : i ≤ j)
    (w : Collision (G.upto i) C) (f : G.Carrier j → Z) :
    ¬ ∀ x, C x = f (G.upto j x) :=
  (collision_propagates_le G hij w).no_reading f

/-! ## Computation repair versus representation repair -/

/-- A **computation repair**: the representation is left alone and the
downstream reading is changed. -/
def ComputationRepair (P : X → Y) (C : X → Z) : Prop := ∃ f : Y → Z, ∀ x, C x = f (P x)

/-- A **representation repair**: a finer stage map `P'`, from which the old
observation `P` is still recoverable, that does determine the consumer. -/
def RepresentationRepair (P : X → Y) (C : X → Z) : Prop :=
  ∃ (Y' : Type) (P' : X → Y') (r : Y' → Y), (∀ x, P x = r (P' x)) ∧ Determines P' C

/-- A computation repair is exactly determination. -/
theorem computationRepair_iff_determines [Nonempty Z] (P : X → Y) (C : X → Z) :
    ComputationRepair P C ↔ Determines P C :=
  (determines_iff_refines P C).symm

/-- **Computation repair is impossible in the presence of a collision.** -/
theorem no_computation_repair {P : X → Y} {C : X → Z} (w : Collision P C) :
    ¬ ComputationRepair P C := by
  rintro ⟨f, hf⟩
  exact w.no_reading f hf

/-- **Representation repair always exists.**  Carrying the consumer's own value
alongside the observation is a finer stage map from which the observation is
recoverable and which determines the consumer.  So the obstruction is never
about the existence of a repair — only about *where* the repair has to be
made. -/
theorem representationRepair_exists (P : X → Y) (C : X → Z) : RepresentationRepair P C :=
  ⟨Y × Z, fun x => (P x, C x), Prod.fst, fun _ => rfl,
    fun _ _ h => congrArg Prod.snd h⟩

/-- **The dichotomy.**  A consumer-relevant collision rules out every
computation repair, while a representation repair exists.  Changing the
downstream algorithm cannot substitute for restoring the information before the
collision. -/
theorem repair_dichotomy {P : X → Y} {C : X → Z} (w : Collision P C) :
    ¬ ComputationRepair P C ∧ RepresentationRepair P C :=
  ⟨no_computation_repair w, representationRepair_exists P C⟩

/-- The pipeline form of the dichotomy: at every later stage the computation
repair is still unavailable. -/
theorem repair_dichotomy_downstream {C : G.Carrier 0 → Z} {i j : ℕ} (hij : i ≤ j)
    (w : Collision (G.upto i) C) :
    ¬ ComputationRepair (G.upto j) C ∧ RepresentationRepair (G.upto j) C :=
  repair_dichotomy (collision_propagates_le G hij w)

/-! ## The same statement in the adequacy vocabulary -/

variable {S R Xr : Type}

/-- A collision of the realised state against a consumer's question refutes
consumer adequacy: the consumer's observation is downstream of the realisation,
so `Collision.post` applies. -/
theorem not_adequateFor_of_state_collision (P : Pipeline S R Xr) (c : ConsumerSpec S Xr)
    (w : Collision P.state c.demand) : ¬ AdequateFor P c :=
  (w.post c.observe).not_determines

/-- **Adequacy lost at the realisation is lost for every consumer downstream of
it.**  A single collision of the realised state refutes adequacy for *every*
consumer that asks the colliding question, whatever it observes. -/
theorem pipeline_adequacy_lost_at_realisation (P : Pipeline S R Xr)
    {Ans : Type} {demand : S → Ans} (w : Collision P.state demand)
    (Obs : Type) (observe : Xr → Obs) :
    ¬ AdequateFor P ⟨Obs, observe, Ans, demand⟩ :=
  not_adequateFor_of_state_collision P ⟨Obs, observe, Ans, demand⟩ w

/-- And the representation stage is where the repair has to be made: the
realisation-level collision leaves a representation repair available. -/
theorem realisation_repair_is_representational (P : Pipeline S R Xr)
    {Ans : Type} {demand : S → Ans} (w : Collision P.state demand) :
    ¬ ComputationRepair P.state demand ∧ RepresentationRepair P.state demand :=
  repair_dichotomy w

end Integration.PipelineAdequacy

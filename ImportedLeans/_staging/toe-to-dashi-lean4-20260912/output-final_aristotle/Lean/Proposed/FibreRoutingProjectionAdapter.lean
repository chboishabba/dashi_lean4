/-!
# Candidate Spine adapter for the 2026-09-11 fibre-routing overlay

**Status: proposal, not a wired consumer.**  This file is a checked prototype
of the adapter proposed in `DELTA_20260911_OVERLAY.md` for

```
Agda/DASHI/Reasoning/FibreRoutingGrokkingMoEBrainCrossPollinationExact.agda
```

(donor `dashi_agda` commit `4c8ebfb733f5768ce7ed61388cc5272ececd5d0d`).  It is
deliberately **not** listed in any `lakefile.toml` glob: `Lean/Proposed` is
outside every declared library, so nothing in the corpus depends on it and it
changes no existing build target.  No Lean consumer of the fibre-routing
material exists yet; naming one is the precondition the intake ledger records
for promoting this prototype.

## Relation to the existing machinery

The corpus already owns the projection/consumer vocabulary this material needs:

* `Integration.ContextIndexedRole` — `FactorsThrough`, `NonFactorabilityWitness`,
  `Determines`, `witness_rules_out_every_factorisation`;
* `Integration.RealisationAdequacy` — `Pipeline`, `ConsumerSpec`,
  `RepresentationAdequate` / `RealisationAdequate` / `AdequateFor`, all defined
  as `Determines` of a projection against a consumer demand;
* `AgdaMirror.NonFactorabilityKernels` — the Lean mirror of the Agda
  `DASHI.Core.IntersectionalNonFactorability` kernel.

Those modules `import Mathlib`.  This prototype is Mathlib-free on purpose, so
that it can be elaborated on its own in a round where no build is requested;
`FactorsThrough`, `ProjectionCollision` and `Determines` below are therefore
local restatements of exactly those shapes, not a competing formulation.  The
migration, when a build round is allowed, is mechanical: delete the three
generic declarations here, `import Integration.RealisationAdequacy`, and read
`Determines K.fibreProfile K.encode` as
`Integration.RealisationAdequacy.RepresentationAdequate` for the pipeline whose
`represent` is `fibreProfile` and whose `realise` is `fun p => compose p.1 p.2`.

## What is and is not claimed

The specimen types transcribe the Agda module's finite Fly/VFB painted-domain
specimen.  Nothing here is a claim about neurons, brains, mixtures of experts,
grokking, or about the Fly result: the theorems are statements about functions
between four finite label types.  The interpretation firewall stays where the
Agda owner put it — in
`DASHI.Reasoning.FibreRoutingGrokkingMoEBrainCrossPollinationExact`'s
`FibreRoutingCrossPollinationBoundary`, whose Boolean fields are ledger
placeholders pinned by `refl`, not theorems.
-/

namespace Proposed.FibreRoutingProjectionAdapter

/-! ## Generic projection / consumer layer

Local Mathlib-free restatement of `Integration.ContextIndexedRole`. -/

/-- The consumer is a reading of the projection: mirror of the Agda
`NonFactor.FactorsThrough` and of `Integration.ContextIndexedRole.FactorsThrough`. -/
structure FactorsThrough {X Y Z : Type} (proj : X → Y) (consumer : X → Z) where
  /-- The claimed reading of the projected carrier. -/
  interpret : Y → Z
  /-- The claimed factorisation. -/
  factorisation : ∀ x, consumer x = interpret (proj x)

/-- The projection separates whatever the consumer separates. -/
def Determines {X Y Z : Type} (proj : X → Y) (consumer : X → Z) : Prop :=
  ∀ a b, proj a = proj b → consumer a = consumer b

theorem determines_of_factorsThrough {X Y Z : Type} {proj : X → Y} {consumer : X → Z}
    (f : FactorsThrough proj consumer) : Determines proj consumer := by
  intro a b h
  rw [f.factorisation a, f.factorisation b, h]

/-- Mirror of the Agda `Compression.CompressionFailureWitness` /
`NonFactor.NonFactorabilityWitness`: two states the projection confuses and the
consumer does not. -/
structure ProjectionCollision {X Y Z : Type} (proj : X → Y) (consumer : X → Z) where
  /-- The first state. -/
  left : X
  /-- The second state. -/
  right : X
  /-- The projection confuses them. -/
  sameProjection : proj left = proj right
  /-- The consumer does not. -/
  consumersDiffer : consumer left = consumer right → False

/-- Mirror of `Realization.representationCollisionBlocksRealization`: one
collision refutes every decoder. -/
theorem collision_blocks_factorisation {X Y Z : Type} {proj : X → Y} {consumer : X → Z}
    (col : ProjectionCollision proj consumer) (f : FactorsThrough proj consumer) : False :=
  col.consumersDiffer <| by
    rw [f.factorisation col.left, f.factorisation col.right, col.sameProjection]

theorem not_determines_of_collision {X Y Z : Type} {proj : X → Y} {consumer : X → Z}
    (col : ProjectionCollision proj consumer) : ¬ Determines proj consumer :=
  fun h => col.consumersDiffer (h col.left col.right col.sameProjection)

/-! ## Query-indexed adequacy

The consumer-indexed layer of `Integration.RealisationAdequacy.AdequateFor`,
stated for a family of queries rather than a single consumer. -/

/-- One compressed evaluator per query, agreeing with the fine evaluator. -/
structure QueryIndexedAdequacy {X Y : Type} (Q O : Type) (proj : X → Y)
    (eval : Q → X → O) where
  /-- The compressed evaluator. -/
  evalCompressed : Q → Y → O
  /-- It agrees with the fine evaluator at every query and state. -/
  adequacy : ∀ q x, eval q x = evalCompressed q (proj x)

/-- Query-indexed adequacy factorises each single query. -/
def FactorsThrough.ofQuery {X Y Q O : Type} {proj : X → Y} {eval : Q → X → O}
    (A : QueryIndexedAdequacy Q O proj eval) (q : Q) : FactorsThrough proj (eval q) where
  interpret := A.evalCompressed q
  factorisation := fun x => A.adequacy q x

/-- A collision at one query refutes adequacy for the whole family. -/
theorem query_collision_blocks_adequacy {X Y Q O : Type} {proj : X → Y} {eval : Q → X → O}
    (q : Q) (col : ProjectionCollision proj (eval q))
    (A : QueryIndexedAdequacy Q O proj eval) : False :=
  collision_blocks_factorisation col (FactorsThrough.ofQuery A q)

/-! ## Fibre routing carriers

Transcription of the two records of the Agda overlay module.  `Set₁` becomes
`Type`, which is the same statement with different universe bookkeeping. -/

/-- Mirror of the Agda `FibreRoutingCarrier`. -/
structure FibreRoutingCarrier (Input Fibre Weight : Type) where
  /-- Context-relative routing weight of a fibre for an input. -/
  routeWeight : Input → Fibre → Weight
  /-- Ledger flag: whether overlapping membership is permitted.  A `Bool`
  field, not a theorem. -/
  overlappingMembershipPermitted : Bool
  /-- The owner's bounded reading. -/
  routingReading : String

/-- Mirror of the Agda `FibreCompositionCarrier`. -/
structure FibreCompositionCarrier (Input Fibre Weight Contribution Representation : Type) where
  /-- The routing layer. -/
  routing : FibreRoutingCarrier Input Fibre Weight
  /-- Fibre-local contribution. -/
  localContribution : Input → Fibre → Contribution
  /-- How weights and contributions compose into a representation. -/
  compose : (Fibre → Weight) → (Fibre → Contribution) → Representation
  /-- The representation of an input. -/
  encode : Input → Representation
  /-- The commuting square the owner requires of every instance. -/
  compositionCommutes : ∀ input,
    encode input = compose (routing.routeWeight input) (localContribution input)
  /-- The owner's bounded reading. -/
  compositionReading : String

/-- The pair (routing weights, local contributions) an input induces. -/
def FibreCompositionCarrier.fibreProfile {I F W C R : Type}
    (K : FibreCompositionCarrier I F W C R) : I → (F → W) × (F → C) :=
  fun i => (K.routing.routeWeight i, K.localContribution i)

/-- **The adapter theorem.**  Every fibre-composition carrier exhibits its
representation as factoring through its fibre profile; the commuting square of
the record *is* the factorisation datum. -/
def FibreCompositionCarrier.encodeFactorsThroughProfile {I F W C R : Type}
    (K : FibreCompositionCarrier I F W C R) : FactorsThrough K.fibreProfile K.encode where
  interpret := fun p => K.compose p.1 p.2
  factorisation := K.compositionCommutes

/-- Hence the fibre profile determines the representation: the shape
`Integration.RealisationAdequacy.RepresentationAdequate` asks for. -/
theorem FibreCompositionCarrier.profile_determines_encode {I F W C R : Type}
    (K : FibreCompositionCarrier I F W C R) : Determines K.fibreProfile K.encode :=
  determines_of_factorsThrough K.encodeFactorsThroughProfile

/-! ## The Fly/VFB painted-domain specimen -/

/-- Two painted domains, one nested in the other. -/
inductive PaintedDomain
  | parentDomain
  | childDomain
  deriving DecidableEq, Repr

/-- Three soft membership values; nothing forces them to sum to one. -/
inductive SoftMembership
  | zeroMembership
  | halfMembership
  | fullMembership
  deriving DecidableEq, Repr

/-- Two selected-ROI specimens. -/
inductive SelectedROISpecimen
  | overlappingROI
  | parentOnlyROI
  deriving DecidableEq, Repr

open PaintedDomain SoftMembership SelectedROISpecimen

/-- The soft carrier: the overlapping ROI is active in both domains. -/
def paintedMembership : SelectedROISpecimen → PaintedDomain → SoftMembership
  | overlappingROI, parentDomain => fullMembership
  | overlappingROI, childDomain => halfMembership
  | parentOnlyROI, parentDomain => fullMembership
  | parentOnlyROI, childDomain => zeroMembership

/-- The unique-maximum collapse: one hard winner. -/
inductive HardPaintedIdentity
  | parentWinner
  deriving DecidableEq, Repr

/-- The consumer-relevant overlap profile. -/
inductive PaintedOverlapProfile
  | parentAndChildProfile
  | parentOnlyProfile
  deriving DecidableEq, Repr

open HardPaintedIdentity PaintedOverlapProfile

/-- The hard winner of both specimens is the parent domain. -/
def hardPaintedIdentity : SelectedROISpecimen → HardPaintedIdentity := fun _ => parentWinner

/-- The overlap profile does distinguish them. -/
def paintedOverlapProfile : SelectedROISpecimen → PaintedOverlapProfile
  | overlappingROI => parentAndChildProfile
  | parentOnlyROI => parentOnlyProfile

/-- Mirror of the Agda `hardWinnerLosesOverlapProfile`. -/
def hardWinnerCollision : ProjectionCollision hardPaintedIdentity paintedOverlapProfile where
  left := overlappingROI
  right := parentOnlyROI
  sameProjection := rfl
  consumersDiffer := fun h => by cases h

/-- Mirror of the Agda `hardWinnerCannotRealizeOverlapProfile`: unique-maximum
collapse is a genuine information-loss operation for this consumer. -/
theorem hardWinner_not_factorising :
    FactorsThrough hardPaintedIdentity paintedOverlapProfile → False :=
  collision_blocks_factorisation hardWinnerCollision

theorem hardWinner_not_determines :
    ¬ Determines hardPaintedIdentity paintedOverlapProfile :=
  not_determines_of_collision hardWinnerCollision

/-- The soft membership carrier, by contrast, does determine the overlap
profile: the distinction the hard winner erases is retained. -/
def softMembershipFactorisation : FactorsThrough paintedMembership paintedOverlapProfile where
  interpret := fun m =>
    match m childDomain with
    | zeroMembership => parentOnlyProfile
    | _ => parentAndChildProfile
  factorisation := fun roi => by cases roi <;> rfl

theorem softMembership_determines : Determines paintedMembership paintedOverlapProfile :=
  determines_of_factorsThrough softMembershipFactorisation

/-- The soft carrier packaged as a fibre-composition carrier: routing weights
are the painted memberships, the fibre-local contribution is trivial, and the
composition is the overlap profile.  The commuting square is discharged by case
analysis, so this is an inhabitant, not an interface. -/
def flySoftCompositionCarrier :
    FibreCompositionCarrier SelectedROISpecimen PaintedDomain SoftMembership Unit
      PaintedOverlapProfile where
  routing :=
    { routeWeight := paintedMembership
      overlappingMembershipPermitted := true
      routingReading :=
        "VFB painted domains are retained as overlapping functional fibres; a selected ROI may \
         contribute to more than one painted domain and memberships are not forced to sum to one." }
  localContribution := fun _ _ => ()
  compose := fun w _ =>
    match w childDomain with
    | zeroMembership => parentOnlyProfile
    | _ => parentAndChildProfile
  encode := paintedOverlapProfile
  compositionCommutes := fun roi => by cases roi <;> rfl
  compositionReading :=
    "Finite specimen only: composition of soft painted memberships into an overlap profile. \
     No claim about neuron identity, biological mechanism, or population generalization."

end Proposed.FibreRoutingProjectionAdapter

import Integration.PredictionEnvelope

/-!
# Deliberate falsification of the transport verdict

The Level-III probe concluded that every claim-transport failure it reached
reduces to the frozen owners.  A negative verdict of that kind is only worth
having if it has been attacked, so this file attacks it: it collects the
transport shapes that are **not ordinary total functions** and asks, for each,
whether the existing consumer geometry can state it without distortion.

The shapes probed:

| shape | verdict |
|---|---|
| partial map `X → Option M` | reducible (§1) |
| relation-valued consumer `X → Z → Prop` | reducible, modulo `funext`/`propext` (§2) |
| nondeterministic stage `X → Set M` | reducible (§3) |
| context-indexed admissibility `X → K → Z` | reducible, pointwise (§4) |
| stage defined only on a declared carrier | reducible to the existing `DeterminesOn` (§5) |

In every case the reduction is *proved*, not asserted, and none of them is
generalised: each is an application of `Determines` / `Collision` to a total
function whose codomain happens to be `Option M`, `Z → Prop`, `Set M` or
`K → Z`.

**Honest scope.**  `no_irreducible_shape_found` is a statement about the ledger
of shapes actually probed here.  It is not a proof that no irreducible transport
exists anywhere in the corpus; the falsification metric is a count of what this
search turned up, and it is currently zero.  A nonzero value would be a finding
to inspect, not a defect to suppress.
-/

namespace Integration.TransportFalsification

open Integration.CoordinateSufficiency
open Integration.FactorisationCollision
open Integration.DeclaredCarrier

variable {X Y Z M A K : Type}

/-! ## §1 Partial maps -/

/-- **Definedness is a consumer, and it is determined.**  A partial map's own
domain of definition is a function of the map's value, so partiality introduces
no reading the owner cannot see. -/
theorem definedness_is_determined (p : X → Option M) :
    Determines p (fun x => (p x).isSome) := fun x y h => by
  show (p x).isSome = (p y).isSome
  rw [h]

/-- **Undefinedness is a collision source.**  Two states on which a partial map
is undefined are identified by it; if a consumer separates them, the resulting
obstruction is literally the existing datum, with no new notion of "partial
failure". -/
def undefined_states_collide {p : X → Option M} {C : X → Z} {x y : X}
    (hx : p x = none) (hy : p y = none) (hne : C x ≠ C y) : Collision p C where
  left := x
  right := y
  distinct := fun h => hne (by rw [h])
  collide := by rw [hx, hy]
  separate := hne

/-- **A partial map transports exactly like a total one.**  Splitting it into
"is it defined?" and "what is the value?" changes nothing: the pair reading and
the map itself determine the same consumers. -/
theorem partial_map_pair_reading (p : X → Option M) (C : X → Z) :
    Determines p C ↔ Determines (fun x => ((p x).isSome, p x)) C := by
  constructor
  · exact fun h x y hxy => h x y (congrArg Prod.snd hxy)
  · exact fun h x y hxy => h x y (by show ((p x).isSome, p x) = ((p y).isSome, p y); rw [hxy])

/-! ## §2 Relation-valued consumers -/

/-- **A relation-valued consumer reduces to a function-valued one.**  Asking
that the evidence fix the whole relation pointwise is the same as asking that it
determine the relation as a value.  The reduction needs `funext` and `propext`,
which is why this shape is recorded as *reducible but awkward*: the pointwise
statement is the natural one to write, and the owner sees the packaged one. -/
theorem relational_consumer_reduces (O : X → Y) (C : X → Z → Prop) :
    (∀ x y, O x = O y → ∀ z, (C x z ↔ C y z)) ↔ Determines O C := by
  constructor
  · intro h x y hxy
    funext z
    exact propext (h x y hxy z)
  · intro h x y hxy z
    rw [h x y hxy]

/-- A relation-valued collision is the existing datum, with the separating pair
exhibited by a single argument at which the relations differ. -/
def relational_collision {O : X → Y} {C : X → Z → Prop} {x y : X} {z : Z}
    (hxy : O x = O y) (hne : x ≠ y) (hz : C x z ∧ ¬ C y z) : Collision O C where
  left := x
  right := y
  distinct := hne
  collide := hxy
  separate := fun h => hz.2 (by rw [← h]; exact hz.1)

/-! ## §3 Nondeterministic stages -/

/-- **A nondeterministic stage is a total function into `Set M`.**  Its
downstream answers form a set, and that set is determined by the stage: the
composite reading is again a function, so the warrant theory applies
unchanged. -/
theorem nondeterministic_answers_determined (T : X → Set M) (q : M → A) :
    Determines T (fun x => q '' T x) := fun x y h => by
  show q '' T x = q '' T y
  rw [h]

/-- Hence transport across a nondeterministic stage: if the *set* of downstream
answers determines the claim, so does the stage. -/
theorem nondeterministic_transport {T : X → Set M} {q : M → A} {C : X → Z}
    (w : Determines (fun x => q '' T x) C) : Determines T C :=
  fun x y h => w x y (by show q '' T x = q '' T y; rw [h])

/-- And the obstruction is again a collision — of the set-valued reading against
the claim. -/
theorem nondeterministic_obstruction {T : X → Set M} {C : X → Z}
    (w : Collision T C) : ¬ Determines T C := w.not_determines

/-- The prediction envelope of a nondeterministic stage is exactly the image
set, so §3 and the envelope machinery are the same object seen twice. -/
theorem envelope_of_nondeterministic (T : X → Set M) (q : M → A) (x : X) :
    (fun x => q '' T x) x = q '' T x := rfl

/-! ## §4 Context-indexed admissibility -/

/-- **Context-dependent admissibility reduces pointwise.**  A consumer whose
answer depends on a context is determined exactly when it is determined in each
context separately; no notion of "contextual determination" is needed. -/
theorem context_indexed_reduces (O : X → Y) (C : X → K → Z) :
    (∀ k, Determines O (fun x => C x k)) ↔ Determines O C := by
  constructor
  · intro h x y hxy
    funext k
    exact h k x y hxy
  · intro h k x y hxy
    exact congrFun (h x y hxy) k

/-- **But a context can be the thing that fails.**  Determination in one context
does not give it in another, so an admissibility claim must name its context —
the same consumer-relativity the owner already enforces. -/
theorem context_determination_does_not_transfer :
    ∃ (O : ℕ → ℕ) (C : ℕ → Bool → ℕ),
      Determines O (fun x => C x false) ∧ ¬ Determines O (fun x => C x true) := by
  refine ⟨fun n => n % 2, fun n b => if b then n else n % 2, fun _ _ h => h, ?_⟩
  intro h
  have : (0 : ℕ) = 2 := h 0 2 rfl
  omega

/-! ## §5 Stages defined only on a declared carrier -/

/-- **A stage defined only on a declared carrier is the existing
`DeterminesOn`.**  Restricting attention to the carrier is not a new transport
notion, and the gap between it and global determination is the one the corpus
already records. -/
theorem declared_domain_reduces {S : X → Prop} {O : X → Y} {C : X → Z}
    (h : Determines O C) : DeterminesOn S O C :=
  determinesOn_of_determines h

/-- And the gap is strict, as already proved: local determination on a declared
carrier licenses nothing outside it. -/
theorem declared_domain_gap_is_strict :
    DeterminesOn declared (fun n : ℕ => n % 2) (fun n : ℕ => n) ∧
      ¬ Determines (fun n : ℕ => n % 2) (fun n : ℕ => n) :=
  determinesOn_not_determines

/-! ## §6 The falsification ledger -/

/-- A transport shape probed in this search. -/
inductive TransportShape
  /-- `X → Option M`. -/
  | partialMap
  /-- `X → Z → Prop`. -/
  | relationValuedConsumer
  /-- `X → Set M`. -/
  | nondeterministicStage
  /-- `X → K → Z`. -/
  | contextIndexedAdmissibility
  /-- A stage defined only on a declared carrier. -/
  | declaredDomainStage
  deriving DecidableEq, Repr, Fintype

/-- How the shape fared against the frozen owners. -/
inductive ReductionStatus
  /-- Stated by the existing owners with no distortion. -/
  | reducible
  /-- Reducible, but the natural statement and the owner's statement differ by a
  step (extensionality, packaging). -/
  | awkwardButReducible
  /-- The owners cannot state the object without distortion.  Nothing in this
  search reached this value. -/
  | irreducible
  deriving DecidableEq, Repr, Fintype

/-- One probe. -/
structure Probe where
  /-- The shape probed. -/
  shape : TransportShape
  /-- The verdict. -/
  status : ReductionStatus
  /-- The theorem that justifies the verdict. -/
  witness : String

/-- **The ledger of the search.**  Each row is backed by the named theorem
above. -/
def falsificationLedger : List Probe :=
  [ { shape := .partialMap, status := .reducible
      witness := "definedness_is_determined, undefined_states_collide, \
                  partial_map_pair_reading" }
  , { shape := .relationValuedConsumer, status := .awkwardButReducible
      witness := "relational_consumer_reduces (uses funext and propext), \
                  relational_collision" }
  , { shape := .nondeterministicStage, status := .reducible
      witness := "nondeterministic_answers_determined, nondeterministic_transport, \
                  nondeterministic_obstruction" }
  , { shape := .contextIndexedAdmissibility, status := .reducible
      witness := "context_indexed_reduces, context_determination_does_not_transfer" }
  , { shape := .declaredDomainStage, status := .reducible
      witness := "declared_domain_reduces, declared_domain_gap_is_strict" }
  ]

/-- **Every shape probed here is reducible.**  This is a statement about the
five rows above, proved by computation over them. -/
theorem no_irreducible_shape_found :
    ∀ p ∈ falsificationLedger, p.status ≠ ReductionStatus.irreducible := by decide

/-- The falsification metric: the number of irreducible transport shapes this
search produced.  It is zero — which is a *result of the search*, not a proof
that none exists. -/
theorem irreducible_count :
    (falsificationLedger.filter (fun p =>
      decide (p.status = ReductionStatus.irreducible))).length = 0 := rfl

/-- Every probed shape is classified, and each of the five shapes was probed. -/
theorem ledger_is_complete_over_shapes :
    falsificationLedger.map (fun p => p.shape) =
      [.partialMap, .relationValuedConsumer, .nondeterministicStage,
        .contextIndexedAdmissibility, .declaredDomainStage] := rfl

end Integration.TransportFalsification

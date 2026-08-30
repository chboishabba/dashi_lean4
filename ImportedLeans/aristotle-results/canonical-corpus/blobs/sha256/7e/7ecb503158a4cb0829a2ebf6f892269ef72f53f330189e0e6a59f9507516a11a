import Mathlib

/-!
# The four-level classification of cross-domain claims

This is the vocabulary in which the rest of the `Integration` spine records what
a cross-domain link between two parts of the DASHI corpus actually *is*.  It is
deliberately a Lean datatype rather than a prose table: an entry cannot be
promoted to a higher level without supplying the corresponding Lean object.

The four levels, from weakest to strongest:

1. **`vocabulary`** — the two modules use the same word (`trit`, `fibre`,
   `supervoxel`, `hyperfabric`, `moonshine`, …) and nothing else is shared.  The
   witness is a `String`; it has no formal content, and this is the point.
2. **`recordDependency`** — one module's record *stores* a value produced by the
   other, so there is a field projection `R → F` between the two carriers.  This
   is a genuine import-level dependency but proves nothing about structure.
3. **`sharedType`** — the two carriers are the same type up to a defined
   bijection: an `Equiv A B` that someone actually wrote down.  No operation is
   claimed to be preserved.
4. **`provedTransport`** — an `Equiv` together with a proof that it intertwines
   the two sides' distinguished operations (`Transport`), or more generally a
   preservation theorem.  This is the only level at which "the two domains are
   the same structure" is a theorem.

The negative counterpart is `NoTransport`: a proof that *no* equivalence
intertwines the two operations.  Registry entries that stop at level 3 should
carry one of these whenever the level-4 statement is actually refutable, so that
"we did not prove it" is distinguished from "it is false".
-/

namespace Integration.Levels

/-- The four levels at which a cross-domain claim can hold. -/
inductive BridgeLevel
  /-- Level 1: a shared word. -/
  | vocabulary
  /-- Level 2: one side's record stores the other side's value. -/
  | recordDependency
  /-- Level 3: a defined bijection of carriers. -/
  | sharedType
  /-- Level 4: a bijection proved to preserve the structure. -/
  | provedTransport
  deriving DecidableEq, Repr, Fintype

/-- The levels are linearly ordered by strength. -/
def BridgeLevel.rank : BridgeLevel → ℕ
  | .vocabulary => 1
  | .recordDependency => 2
  | .sharedType => 3
  | .provedTransport => 4

theorem BridgeLevel.rank_injective : Function.Injective BridgeLevel.rank := by decide

/-- A structure-preserving identification of two unary-operation carriers: the
level-4 witness.  `opA`/`opB` are the distinguished operations of the two sides
(in this corpus, almost always a polarity/inversion or a rotation). -/
structure Transport (A B : Type) (opA : A → A) (opB : B → B) where
  /-- The underlying bijection of carriers. -/
  map : A ≃ B
  /-- The bijection intertwines the two operations. -/
  equivariant : ∀ a, map (opA a) = opB (map a)

namespace Transport

variable {A B C : Type} {opA : A → A} {opB : B → B} {opC : C → C}

/-- The identity transport. -/
def refl (A : Type) (op : A → A) : Transport A A op op :=
  ⟨Equiv.refl A, fun _ => rfl⟩

/-- Transports compose. -/
def trans (f : Transport A B opA opB) (g : Transport B C opB opC) :
    Transport A C opA opC :=
  ⟨f.map.trans g.map, fun a => by
    simp [Equiv.trans_apply, f.equivariant a, g.equivariant (f.map a)]⟩

/-- Transports invert. -/
def symm (f : Transport A B opA opB) : Transport B A opB opA :=
  ⟨f.map.symm, fun b => by
    apply f.map.injective
    simp [f.equivariant (f.map.symm b)]⟩

end Transport

/-- The refutation of a level-4 claim: no bijection at all intertwines the two
operations.  This is strictly stronger than "the obvious map does not". -/
structure NoTransport (A B : Type) (opA : A → A) (opB : B → B) : Prop where
  /-- Every candidate bijection fails to be equivariant somewhere. -/
  obstruction : ∀ e : A ≃ B, ¬ ∀ a, e (opA a) = opB (e a)

theorem NoTransport.elim {A B : Type} {opA : A → A} {opB : B → B}
    (h : NoTransport A B opA opB) (t : Transport A B opA opB) : False :=
  h.obstruction t.map t.equivariant

/-- Evidence for a cross-domain claim.  The constructor determines the level, so
a claim cannot be filed at level 3 or 4 without an actual Lean object. -/
inductive Evidence : Type 1
  /-- A shared name and nothing more. -/
  | vocabulary (sharedName : String)
  /-- A record field: the source record stores a value of the target carrier. -/
  | recordDependency {R F : Type} (field : R → F)
  /-- A defined bijection of carriers, with no preservation claim. -/
  | sharedType {A B : Type} (e : A ≃ B)
  /-- A bijection proved to intertwine the distinguished operations. -/
  | provedTransport {A B : Type} {opA : A → A} {opB : B → B} (t : Transport A B opA opB)
  /-- A map proved to preserve a `V`-valued binary invariant — in this corpus,
  always a distance.  Also level 4: it is a preservation theorem, not a
  coincidence of definitions. -/
  | provedPreservation {A B V : Type} (f : A → B) (mA : A → A → V) (mB : B → B → V)
      (h : ∀ x y, mB (f x) (f y) = mA x y)
  /-- A map, not necessarily bijective, proved to intertwine the two sides'
  distinguished operations.  Level 4 as a preservation theorem; the note on the
  row should say what fails to make it an equivalence. -/
  | provedEquivariance {A B : Type} (f : A → B) (opA : A → A) (opB : B → B)
      (h : ∀ a, f (opA a) = opB (f a))

/-- The level an item of evidence certifies. -/
def Evidence.level : Evidence → BridgeLevel
  | .vocabulary _ => .vocabulary
  | .recordDependency _ => .recordDependency
  | .sharedType _ => .sharedType
  | .provedTransport _ => .provedTransport
  | .provedPreservation _ _ _ _ => .provedTransport
  | .provedEquivariance _ _ _ _ => .provedTransport

/-- One row of the global TOE map. -/
structure Entry : Type 1 where
  /-- Source side, as a corpus module or carrier name. -/
  source : String
  /-- Target side. -/
  target : String
  /-- What is actually shared, with its witness. -/
  evidence : Evidence
  /-- Provenance and caveats, in user-facing prose. -/
  note : String

/-- The level of a row is read off its evidence; it is not a separate claim. -/
def Entry.level (e : Entry) : BridgeLevel := e.evidence.level

/-! ## Boundaries and sockets

A map that *fails* to exist is as much a part of the global picture as one that
exists.  A `Boundary` stores the refuted proposition together with its
refutation, so a claimed negative result cannot be filed without a proof; a
`Socket` records a place where the corpus supplies a record or `Bool` field with
no constraint attached, again with a proof of the underdetermination. -/

/-- A refuted cross-domain claim, carrying its refutation. -/
structure Boundary where
  /-- Source side. -/
  source : String
  /-- Target side. -/
  target : String
  /-- What was hoped for, in prose. -/
  statement : String
  /-- The proposition that fails. -/
  claim : Prop
  /-- Its refutation. -/
  refutation : ¬ claim

/-- A place where the corpus supplies an unconstrained record/`Bool` field. -/
structure Socket where
  /-- The corpus module supplying the socket. -/
  site : String
  /-- What the socket is nominally for. -/
  role : String
  /-- A proposition witnessing that the socket constrains nothing. -/
  underdetermined : Prop
  /-- Its proof. -/
  witness : underdetermined

end Integration.Levels

import Integration.Levels
import Integration.ApproximateIntertwiner

/-!
# The seven-class sewing taxonomy, with provenance

`Integration.Levels` classifies a cross-domain claim by *how strong* the link
is (vocabulary → record dependency → shared type → proved transport).  The
sewing round needs a second, orthogonal axis: *what kind of thing* the proposed
relation is, including the kinds that are not links at all — refutations,
deliberately open sockets, and bridges whose hypotheses have not been
discharged.  This file owns that axis.

## The seven classes

Each constructor of `Relation` carries the Lean object that licenses it, so a
row cannot be filed in a class without supplying the corresponding witness.

* `exactInstance` — an `Integration.Levels.Transport`: a bijection of carriers
  proved to intertwine the two sides' distinguished operations.  This is the
  only class that means "the two structures are the same".
* `approximateInstance` — an `IsApproxIntertwiner` with an explicit `ε` in a
  metric target.  The square commutes up to a stated, checked bound.
* `finiteShadow` — a surjection from the general carrier onto a **finite**
  carrier.  The finite side is a faithful image of the general one and nothing
  more: no inverse is claimed.
* `structuralAnalogue` — a predicate `P : Type → Prop` satisfied by both
  carriers, *with no map between them*.  This is the honest home of "these two
  lanes have the same shape"; it is deliberately weaker than `exactInstance`
  and must never be read as an identification.
* `candidateBridge` — an implication `hyp → concl` that **is** proved, together
  with the hypothesis left undischarged.  Implementing a bridge in this class
  means exhibiting the implication; the row stays a candidate exactly until the
  hypothesis is supplied.
* `negativeResult` — a proposition together with its refutation.
* `openSocket` — a proposition witnessing that some corpus field constrains
  nothing (typically: two inhabitants agreeing everywhere except at the field),
  together with its proof.

## Provenance

`Provenance` records, for every row, the corpus module path, the PR/ref the
surface came from (`none` when the surface is in the tracked tree), the
ancestry chain, whether the Lean side is a *source* development or a *mirror*
of Agda text, what validation actually happened, and the claim boundary in
prose.

`Validation.agdaTypecheckStatus` is the point of the whole record: this
repository ships **no Agda checker result**, so every Agda-side row is
`agdaNotChecked`, and `SewnRow.claimsAgdaTypechecked` is proved false for the
whole registry (`Integration.SewingRegistry`).
-/

namespace Integration.SewingTaxonomy

open Integration.Levels
open Integration.ApproximateIntertwiner

/-! ## The classes -/

/-- The seven kinds of proposed relation, as a plain enumeration (the tag). -/
inductive Kind
  | exactInstance | approximateInstance | finiteShadow | structuralAnalogue
  | candidateBridge | negativeResult | openSocket
  deriving DecidableEq, Repr, Fintype

/-- A proposed relation, carrying the witness its class demands. -/
inductive Relation : Type 1
  /-- A bijection proved to intertwine the two sides' distinguished operations. -/
  | exactInstance {A B : Type} {opA : A → A} {opB : B → B} (t : Transport A B opA opB)
  /-- A square commuting up to an explicit, checked bound in a metric target. -/
  | approximateInstance {A B : Type} (mB : PseudoMetricSpace B) (Φ : A → B) (R : A → A)
      (T : B → B) (ε : ℝ) (h : @IsApproxIntertwiner A B mB Φ R T ε)
  /-- A finite faithful image of a general carrier. -/
  | finiteShadow {A B : Type} (fB : Fintype B) (f : A → B) (hf : Function.Surjective f)
  /-- A shared abstract shape, with **no** map between the carriers. -/
  | structuralAnalogue (P : Type → Prop) (A B : Type) (hA : P A) (hB : P B)
  /-- A proved implication whose hypothesis is left open. -/
  | candidateBridge (hyp concl : Prop) (h : hyp → concl)
  /-- A refuted proposition, with its refutation. -/
  | negativeResult (claim : Prop) (refutation : ¬ claim)
  /-- An unconstrained corpus field, with a proof that it constrains nothing. -/
  | openSocket (underdetermined : Prop) (witness : underdetermined)

/-- The tag of a relation. -/
def Relation.kind : Relation → Kind
  | .exactInstance _ => .exactInstance
  | .approximateInstance _ _ _ _ _ _ => .approximateInstance
  | .finiteShadow _ _ _ => .finiteShadow
  | .structuralAnalogue _ _ _ _ _ => .structuralAnalogue
  | .candidateBridge _ _ _ => .candidateBridge
  | .negativeResult _ _ => .negativeResult
  | .openSocket _ _ => .openSocket

/-- Classes that assert an identification of the two carriers.  Only
`exactInstance` does; in particular a `structuralAnalogue` never does. -/
def Kind.identifiesCarriers : Kind → Bool
  | .exactInstance => true
  | _ => false

/-- Classes whose row is a *positive* transported claim. -/
def Kind.isPositiveTransport : Kind → Bool
  | .exactInstance => true
  | .approximateInstance => true
  | _ => false

/-- Classes that record an obligation still owed. -/
def Kind.isOpenObligation : Kind → Bool
  | .candidateBridge => true
  | .openSocket => true
  | _ => false

/-- The map into the four-level scale, where one exists.  A `structuralAnalogue`
is level 1 (a shared word plus a shared shape, no map); a `finiteShadow` is
level 2 (a genuine map, no preservation); the two positive transport classes are
level 4.  The remaining three classes carry no positive level at all, which is
why the function is `Option`-valued. -/
def Kind.toBridgeLevel : Kind → Option BridgeLevel
  | .exactInstance => some .provedTransport
  | .approximateInstance => some .provedTransport
  | .finiteShadow => some .recordDependency
  | .structuralAnalogue => some .vocabulary
  | .candidateBridge => none
  | .negativeResult => none
  | .openSocket => none

theorem toBridgeLevel_eq_none_iff (k : Kind) :
    k.toBridgeLevel = none ↔
      (k = .candidateBridge ∨ k = .negativeResult ∨ k = .openSocket) := by
  cases k <;> simp [Kind.toBridgeLevel]

/-- Only `exactInstance` claims that the two carriers are the same structure. -/
theorem identifiesCarriers_iff (k : Kind) :
    k.identifiesCarriers = true ↔ k = .exactInstance := by
  cases k <;> simp [Kind.identifiesCarriers]

/-- An `exactInstance` really does deliver an equivalence of carriers: the class
is not a label. -/
noncomputable def Relation.carrierEquiv :
    ∀ r : Relation, r.kind = Kind.exactInstance → Σ' A B : Type, A ≃ B
  | .exactInstance (A := A) (B := B) t, _ => ⟨A, B, t.map⟩
  | .approximateInstance _ _ _ _ _ _, h => absurd h (by simp [Relation.kind])
  | .finiteShadow _ _ _, h => absurd h (by simp [Relation.kind])
  | .structuralAnalogue _ _ _ _ _, h => absurd h (by simp [Relation.kind])
  | .candidateBridge _ _ _, h => absurd h (by simp [Relation.kind])
  | .negativeResult _ _, h => absurd h (by simp [Relation.kind])
  | .openSocket _ _, h => absurd h (by simp [Relation.kind])

/-- A `negativeResult` really does deliver a refutation. -/
theorem Relation.negative_sound (P : Prop) (hP : ¬ P) :
    (Relation.negativeResult P hP).kind = Kind.negativeResult := rfl

/-- A `candidateBridge` is only ever the implication; it never asserts its
hypothesis.  Discharging the hypothesis is exactly what promotes it. -/
theorem Relation.candidate_discharge {hyp concl : Prop} (h : hyp → concl) (hh : hyp) :
    concl := h hh

/-! ## Provenance -/

/-- Whether the Lean text is an independent development or a transcription of
Agda text living elsewhere in the corpus. -/
inductive Surface
  /-- Developed in Lean; there is no Agda original. -/
  | leanSource
  /-- A transcription of a named Agda module. -/
  | agdaMirror
  /-- Lean text about an Agda surface that it does not transcribe. -/
  | leanAboutAgda
  deriving DecidableEq, Repr, Fintype

/-- What checking actually happened. -/
inductive AgdaCheck
  /-- No Agda typechecker was run in this environment. -/
  | agdaNotChecked
  /-- An Agda checker result exists and is recorded here.  Unused: this
  repository ships no such result. -/
  | agdaChecked (log : String)
  deriving DecidableEq, Repr

/-- Whether the Lean side is machine-checked. -/
inductive LeanCheck
  /-- Elaborated by `lake build` as part of a default target. -/
  | leanBuilt
  /-- Present in the tree but not in a build target. -/
  | leanNotBuilt
  deriving DecidableEq, Repr, Fintype

/-- Everything the round is required to preserve about a row. -/
structure Provenance where
  /-- The corpus module path the surface comes from. -/
  modulePath : String
  /-- The PR head the surface came from, if it is branch-only.  `none` means
  "present in the tracked tree". -/
  prRef : Option String
  /-- The ancestry chain, most recent first. -/
  ancestry : List String
  /-- Source development or mirror. -/
  surface : Surface
  /-- Agda-side validation status. -/
  agda : AgdaCheck
  /-- Lean-side validation status. -/
  lean : LeanCheck
  /-- The claim boundary: what this row explicitly does **not** assert. -/
  claimBoundary : String
  deriving Repr

/-- A row of the sewing map. -/
structure SewnRow : Type 1 where
  /-- The owner in the small TOE owner set that consumes this surface. -/
  owner : String
  /-- The corpus-side surface. -/
  consumer : String
  /-- The classified relation, with its witness. -/
  relation : Relation
  /-- Provenance. -/
  prov : Provenance

/-- The tag of a row. -/
def SewnRow.kind (r : SewnRow) : Kind := r.relation.kind

/-- A row claims an Agda typecheck exactly when its provenance says so. -/
def SewnRow.claimsAgdaTypechecked (r : SewnRow) : Bool :=
  match r.prov.agda with
  | .agdaNotChecked => false
  | .agdaChecked _ => true

/-- A row carries a non-empty claim boundary. -/
def SewnRow.hasBoundary (r : SewnRow) : Bool := r.prov.claimBoundary ≠ ""

/-- A row is branch-only when its provenance names a PR head. -/
def SewnRow.branchOnly (r : SewnRow) : Bool := r.prov.prRef.isSome

end Integration.SewingTaxonomy

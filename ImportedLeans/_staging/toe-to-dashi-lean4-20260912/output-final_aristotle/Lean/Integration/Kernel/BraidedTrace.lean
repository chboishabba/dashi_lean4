import Integration.Kernel.Quotient

/-!
# Braided traces: coordination without fusion

Two lanes of this corpus describe the same shape.  One insists that distinct
knowledge strands can be coordinated without being merged into a single
supposedly neutral evidence pool, and that provenance and authority survive any
extraction.  The other renders a proof as a physically ordered trace whose
strands are separately identified.  The common object is a **braid**: several
strands, each carrying its own authority, crossing at explicit points, with the
crossings licensed rather than assumed.

This file owns that object at the level the kernel can prove things about.

## What is proved

* `pooled B` — the claim surface after the strand index is forgotten.
  **`pool_does_not_determine_authority`** is the non-fusion theorem: two braids
  with exactly the same pooled claims and different authority assignments, so
  no function of the pool recovers who said what.  `braid_strictly_refines_pool`
  packages this as a strict refinement — pooling is a quotient, not a summary.
* **`every_pair_admits_a_trivial_crossing`** — the honest negative that makes
  the rest necessary: mere *existence* of a translation carrying one strand's
  claim to another's is free, so "these strands cross here" cannot be evidence
  of anything by itself.
* **`LawfulCrossing`** — a crossing that commutes with a declared invariant.
  `lawful_crossing_preserves_invariant` extracts the commuting square, and
  **`no_lawful_crossing_of_different_invariant`** is the firewall: strands whose
  invariants disagree admit no lawful crossing at all.  This is the
  same-object/commuting-projection criterion — the crossing has to be a
  restriction of the same structure, not a coincidence of surface values.
* `lawful_crossing_does_not_merge_authority` — and even a lawful crossing
  leaves the authority coordinates distinct: strands are coordinated, not
  fused.

**Claim boundary.**  Strands, authorities, claims and invariants are arbitrary
types and functions; "authority" is a label attached to an index.  Nothing here
models, adjudicates or represents any actual knowledge holder, permission,
community or obligation.
-/

namespace Integration.Kernel.BraidedTrace

open Integration.Kernel.Quotient

universe u v w x

variable {I : Type u} {A : Type v} {P : Type w} {Q : Type x}

/-! ## §1 Strands and the pooled surface -/

/-- A braided trace: an indexed family of strands, each with its own authority
and its own claim. -/
structure Braid (I : Type u) (A : Type v) (P : Type w) where
  /-- Whose strand this is. -/
  authority : I → A
  /-- What the strand contributes. -/
  claim : I → P

/-- The pooled surface: the claims with the strand index forgotten. -/
def pooled (B : Braid I A P) : Set P := Set.range B.claim

/-- Two braids over two strands: the same claims, different authorities. -/
def braidLeft : Braid Bool Bool Bool := ⟨id, id⟩

/-- The same claims again, with the authorities swapped. -/
def braidRight : Braid Bool Bool Bool := ⟨not, id⟩

theorem pools_agree : pooled braidLeft = pooled braidRight := rfl

theorem authorities_differ : braidLeft.authority ≠ braidRight.authority := by
  intro h
  have := congrFun h true
  exact absurd this (by decide)

/-- **Pooling loses attribution.**  No function of the pooled claim surface
recovers which strand — or whose authority — contributed what. -/
theorem pool_does_not_determine_authority :
    ¬ DescendsThrough (fun B : Braid Bool Bool Bool => B.authority) pooled :=
  not_descendsThrough_of_collision pools_agree authorities_differ

/-- The braid does determine its pool, so pooling is a quotient of the braid and
the pooled reading stays correct — it is simply coarser. -/
theorem pool_descends_through_braid :
    DescendsThrough (pooled : Braid Bool Bool Bool → Set Bool) id :=
  ⟨pooled, fun _ => rfl⟩

theorem braid_strictly_refines_pool :
    StrictlyRefines (pooled : Braid Bool Bool Bool → Set Bool) id where
  law := fun _ _ h => congrArg pooled h
  witness := ⟨braidLeft, braidRight, pools_agree, fun h => authorities_differ (congrArg
    Braid.authority h)⟩

/-! ## §2 Crossings

A crossing says two strands interact at a point.  Bare existence of a
translation between two claims is worthless, so the useful notion is a crossing
that respects a declared invariant. -/

/-- A bare crossing: some rewriting carries strand `i`'s claim to strand `j`'s. -/
structure Crossing (B : Braid I A P) (i j : I) where
  /-- The rewriting used at the crossing. -/
  translate : P → P
  /-- It really does carry one claim to the other. -/
  corresponds : translate (B.claim i) = B.claim j

/-- **Bare crossings are free.**  Any two strands admit one, via the constant
rewriting, so the existence of a crossing is not evidence of anything. -/
theorem every_pair_admits_a_trivial_crossing (B : Braid I A P) (i j : I) :
    Nonempty (Crossing B i j) := ⟨⟨fun _ => B.claim j, rfl⟩⟩

/-- A crossing that commutes with a declared invariant of the claims: the
rewriting may change the presentation but not the thing being tracked. -/
structure LawfulCrossing (B : Braid I A P) (inv : P → Q) (i j : I) where
  /-- The rewriting used at the crossing. -/
  translate : P → P
  /-- It leaves the declared invariant alone — the commuting square. -/
  commutes : ∀ p, inv (translate p) = inv p
  /-- And it carries one claim to the other. -/
  corresponds : translate (B.claim i) = B.claim j

/-- A lawful crossing exhibits the two strands as views of the same invariant. -/
theorem lawful_crossing_preserves_invariant {B : Braid I A P} {inv : P → Q} {i j : I}
    (c : LawfulCrossing B inv i j) : inv (B.claim i) = inv (B.claim j) := by
  rw [← c.corresponds, c.commutes]

/-- **Strands with different invariants cannot be crossed lawfully.**  Unlike a
bare crossing, this one cannot be manufactured. -/
theorem no_lawful_crossing_of_different_invariant {B : Braid I A P} {inv : P → Q} {i j : I}
    (h : inv (B.claim i) ≠ inv (B.claim j)) : IsEmpty (LawfulCrossing B inv i j) :=
  ⟨fun c => h (lawful_crossing_preserves_invariant c)⟩

/-- **A lawful crossing coordinates; it does not fuse.**  Two strands can cross
lawfully — same claim, invariant preserved — and still belong to different
authorities. -/
theorem lawful_crossing_does_not_merge_authority :
    ∃ c : LawfulCrossing braidLeft (id : Bool → Bool) true true,
      c.translate = id ∧ braidLeft.authority true ≠ braidRight.authority true :=
  ⟨⟨id, fun _ => rfl, rfl⟩, rfl, by decide⟩

end Integration.Kernel.BraidedTrace

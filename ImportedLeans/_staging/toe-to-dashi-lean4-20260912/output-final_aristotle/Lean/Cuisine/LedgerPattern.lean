import Mathlib

/-!
# The `Bool`-with-`≡ false` ledger pattern, and exactly what it proves

Throughout the DASHI corpus — and in particular throughout the cuisine lane —
records carry pairs of fields of the shape

```agda
    someClaim         : Bool
    someClaimIsFalse  : someClaim ≡ false
```

for example `CuisinePropositionBoundary.sharedEqualsOwnerless`,
`RepresentationAuthority.universalSpokespersonClaim`,
`SituatedMoleWorld.completeInverseFromPlateClaim`,
`MultiphaseMoleState.permanentSuspensionClaim`,
`AshTransformationReceipt.selectiveAcridityRemovalClaim` and
`AttributedSource.citationCreatesAuthority`.

This file states, once and for all, what such a pair contributes.

* `FalseLedger` — the type of such a pair — has exactly one inhabitant
  (`Unique`), so it is equivalent to `Unit` (`falseLedgerEquivUnit`).
* Consequently a record consisting only of such pairs is itself a singleton
  (`cuisinePropositionBoundaryEquivUnit`): it is always inhabitable, its
  canonical inhabitant is its only inhabitant, and it cannot be used to derive
  anything (`no_information_in_ledger`).

The pattern is therefore *documentation of intent that the typechecker keeps
consistent*: it guarantees that the flag is never flipped to `true` anywhere in
the development.  It is not a proof of the informal statement the field name
describes.  Contrast `Cuisine.Surfaces.SurfaceDistinction.ne`,
`Cuisine.ProcessRoute.orders_are_unmergeable` and
`Cuisine.Provenance.no_source_determined_channel`, which are separations with
actual proof content.
-/

namespace Cuisine.LedgerPattern

/-- One `Bool` field together with its `= false` witness. -/
structure FalseLedger where
  claim : Bool
  claimIsFalse : claim = false

/-- The pair is uniquely inhabited. -/
instance : Unique FalseLedger where
  default := ⟨false, rfl⟩
  uniq := by rintro ⟨b, rfl⟩; rfl

/-- ... hence carries no information. -/
def falseLedgerEquivUnit : FalseLedger ≃ Unit := Equiv.equivPUnit _

/-- The dual `= true` form, used by e.g.
`TraceablePluralWhole.wholeNotReducedToOnePart` and
`CuisineKnowledgeEcology.archiveIsNotPublicViewClaim`. -/
structure TrueLedger where
  claim : Bool
  claimIsTrue : claim = true

instance : Unique TrueLedger where
  default := ⟨true, rfl⟩
  uniq := by rintro ⟨b, rfl⟩; rfl

/-- The Agda record `CuisinePropositionBoundary` of
`DASHI.Culture.Cuisine.ProvenanceRoutingBridge`, transcribed. -/
structure CuisinePropositionBoundary where
  sharedEqualsOwnerless : Bool
  sharedEqualsOwnerlessIsFalse : sharedEqualsOwnerless = false
  adoptedEqualsInvented : Bool
  adoptedEqualsInventedIsFalse : adoptedEqualsInvented = false
  nationalCanonisationEqualsProvenance : Bool
  nationalCanonisationEqualsProvenanceIsFalse : nationalCanonisationEqualsProvenance = false
  visibleAuthenticityImpliesRightsReturn : Bool
  visibleAuthenticityImpliesRightsReturnIsFalse : visibleAuthenticityImpliesRightsReturn = false

/-- The canonical inhabitant supplied in the Agda source. -/
def canonicalCuisinePropositionBoundary : CuisinePropositionBoundary :=
  ⟨false, rfl, false, rfl, false, rfl, false, rfl⟩

instance : Unique CuisinePropositionBoundary where
  default := canonicalCuisinePropositionBoundary
  uniq := by rintro ⟨_, rfl, _, rfl, _, rfl, _, rfl⟩; rfl

/-- The four-flag boundary record is a singleton type. -/
def cuisinePropositionBoundaryEquivUnit : CuisinePropositionBoundary ≃ Unit :=
  Equiv.equivPUnit _

/-- **What the ledger proves.**  Any predicate on the boundary record that holds
of the canonical inhabitant holds of every inhabitant, and conversely; so no
statement can be *separated* using the record.  In particular the record cannot
distinguish a development in which the informal claims hold from one in which
they fail. -/
theorem no_information_in_ledger (P : CuisinePropositionBoundary → Prop) :
    (∃ b, P b) ↔ P canonicalCuisinePropositionBoundary := by
  constructor
  · rintro ⟨b, hb⟩
    rwa [Subsingleton.elim canonicalCuisinePropositionBoundary b]
  · exact fun h => ⟨_, h⟩

end Cuisine.LedgerPattern

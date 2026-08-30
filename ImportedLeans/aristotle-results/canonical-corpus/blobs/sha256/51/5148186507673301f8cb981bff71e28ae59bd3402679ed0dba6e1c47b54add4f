import Mathlib

/-!
# Lean mirror of the DASHI explanation/authority route surfaces

Transcription of three Agda records that together carry the corpus's
**content ≠ competence ≠ permission ≠ authority** vocabulary:

* `DASHI/Promotion/ExplanationAuthorityBoundaryCore.agda` —
  `ExplanationRoute`, `ExplanationStatus`, `ExplanationBoundaryRow` and the
  six-row table `canonicalExplanationRows`;
* `DASHI/Culture/CulturalProvenanceBoundaryCore.agda` — `ProvenanceKind`,
  `ProvenanceRow` (including its `permissionOrAuthorityClaimed` field) and the
  `boundaryHolds`/`boundaryHoldsIsTrue` pair of `CulturalProvenanceBoundary`;
* `DASHI/Philosophy/CulturalProvenanceAdapter.agda` —
  `PhilosophyCulturalAdapter` and `CulturalApplicationPromotion`, the corpus's
  one *promotion* record: three authority receipts (Agda `Set` fields, mirrored
  as `Prop`) and a free `representationPromoted : Bool`.

Only the fields the transcription needs are kept; each omission is a `String`
or `List String` note field with no logical content.  **This is a transcription
of visible Agda text; no Agda module has been typechecked here.**

The facts proved in this file are facts *about the transcribed table*: which
route licenses which use, that the tabulated uses are pairwise exclusive, that
`boundaryHolds` is pinned to `true` by its own companion field, and that the
promotion flag and the permission flag are free.  Their classification against
the Level-II owners is done in `Integration.ClaimTransportLanes`.
-/

namespace AgdaMirror.AuthorityRoutes

/-! ## §1 The explanation/authority route table -/

/-- Agda `data ExplanationRoute`. -/
inductive Route
  | narrativeGuide | metaphor | phenomenologicalDescription
  | typedStructure | empiricalSupport | institutionalAuthority
  deriving DecidableEq, Repr, Fintype

/-- Agda `data ExplanationStatus`. -/
inductive Status
  | guideOnly | structureOnly | supportRequired | authorityExternallyRequired
  deriving DecidableEq, Repr, Fintype

open Route Status

/-- Agda `record ExplanationBoundaryRow`, minus its label. -/
structure Row where
  /-- `rowRoute`. -/
  route : Route
  /-- `rowStatus`. -/
  status : Status
  /-- `mayGuide`. -/
  mayGuide : Bool
  /-- `isTypedProof`. -/
  isTypedProof : Bool
  /-- `isEmpiricalSupport`. -/
  isEmpiricalSupport : Bool
  /-- `isInstitutionalAuthority`. -/
  isInstitutionalAuthority : Bool
  deriving DecidableEq, Repr

/-- Agda `canonicalExplanationRows`, transcribed clause for clause. -/
def canonicalRows : List Row :=
  [ ⟨narrativeGuide, guideOnly, true, false, false, false⟩
  , ⟨metaphor, guideOnly, true, false, false, false⟩
  , ⟨phenomenologicalDescription, guideOnly, true, false, false, false⟩
  , ⟨typedStructure, structureOnly, true, true, false, false⟩
  , ⟨empiricalSupport, supportRequired, false, false, true, false⟩
  , ⟨institutionalAuthority, authorityExternallyRequired, false, false, false, true⟩ ]

/-- The table read as a function of the route. -/
def rowOf : Route → Row
  | narrativeGuide => ⟨narrativeGuide, guideOnly, true, false, false, false⟩
  | metaphor => ⟨metaphor, guideOnly, true, false, false, false⟩
  | phenomenologicalDescription =>
      ⟨phenomenologicalDescription, guideOnly, true, false, false, false⟩
  | typedStructure => ⟨typedStructure, structureOnly, true, true, false, false⟩
  | empiricalSupport => ⟨empiricalSupport, supportRequired, false, false, true, false⟩
  | institutionalAuthority =>
      ⟨institutionalAuthority, authorityExternallyRequired, false, false, false, true⟩

/-- The functional reading agrees with the transcribed list, route by route. -/
theorem canonicalRows_eq_map :
    canonicalRows =
      [rowOf narrativeGuide, rowOf metaphor, rowOf phenomenologicalDescription,
        rowOf typedStructure, rowOf empiricalSupport, rowOf institutionalAuthority] := rfl

/-- The table has exactly one row per route. -/
theorem canonicalRows_length : canonicalRows.length = Fintype.card Route := by decide

/-- Every row's `rowRoute` is the route indexing it. -/
theorem rowOf_route (r : Route) : (rowOf r).route = r := by cases r <;> rfl

/-! ## §2 The four uses, and what the table licenses -/

/-- The four uses the table's Boolean fields name. -/
inductive Use
  | guide | typedProof | empiricalSupport | institutionalAuthority
  deriving DecidableEq, Repr, Fintype

/-- **The corpus's licensing relation**, read off the transcribed table: route
`r` licenses use `u` exactly when the corresponding field of `rowOf r` is
`true`.  This is a table lookup, not a new abstraction. -/
def licenses (r : Route) : Use → Bool
  | .guide => (rowOf r).mayGuide
  | .typedProof => (rowOf r).isTypedProof
  | .empiricalSupport => (rowOf r).isEmpiricalSupport
  | .institutionalAuthority => (rowOf r).isInstitutionalAuthority

/-- **No route licenses two of the three non-guide uses.**  Typed proof,
empirical support and institutional authority are pairwise exclusive across the
whole table. -/
theorem no_route_licenses_two_strong_uses (r : Route) :
    ¬ ((licenses r .typedProof ∧ licenses r .empiricalSupport) ∨
       (licenses r .typedProof ∧ licenses r .institutionalAuthority) ∨
       (licenses r .empiricalSupport ∧ licenses r .institutionalAuthority)) := by
  revert r; decide

/-- **Each strong use is licensed by exactly one route.** -/
theorem strong_uses_are_single_route :
    (∀ r, licenses r .typedProof = true ↔ r = typedStructure) ∧
    (∀ r, licenses r .empiricalSupport = true ↔ r = empiricalSupport) ∧
    (∀ r, licenses r .institutionalAuthority = true ↔ r = institutionalAuthority) := by
  refine ⟨?_, ?_, ?_⟩ <;> (intro r; revert r; decide)

/-- **The uses are not linearly ordered.**  A route may guide without carrying
authority, and a route may carry authority without being permitted to guide, so
there is no "strength" scale along which a licence could be transported. -/
theorem guide_and_authority_are_incomparable :
    licenses narrativeGuide .guide = true ∧
      licenses narrativeGuide .institutionalAuthority = false ∧
      licenses institutionalAuthority .guide = false ∧
      licenses institutionalAuthority .institutionalAuthority = true := by decide

/-- **The guide licence does not separate the proof licence.**  Narrative guide
and typed structure carry the *same* value of `mayGuide` and *different* values
of `isTypedProof`: the corpus's own literal instance of `x ∼_{C₁} y` with
`x ≁_{C₂} y`. -/
theorem guide_agrees_proof_differs :
    licenses narrativeGuide .guide = licenses typedStructure .guide ∧
      licenses narrativeGuide .typedProof ≠ licenses typedStructure .typedProof := by decide

/-! ## §3 The cultural provenance row and its boundary flag -/

/-- Agda `data ProvenanceKind`. -/
inductive ProvenanceKind
  | namedAuthor | namedCommunity | placePractice | comparativeResearch | formalAnalogy
  deriving DecidableEq, Repr, Fintype

/-- Agda `record ProvenanceRow`, with the two `String` description fields
dropped and the two Boolean fields kept. -/
structure ProvenanceRow where
  /-- `sourceName`. -/
  sourceName : String
  /-- `provenanceKind`. -/
  kind : ProvenanceKind
  /-- `permissionOrAuthorityClaimed`. -/
  permissionOrAuthorityClaimed : Bool
  /-- `replaceableByFormalEncoding`. -/
  replaceableByFormalEncoding : Bool
  deriving DecidableEq, Repr

/-- **The permission field is free of the content fields.**  Two provenance
rows naming the same source with the same provenance kind and the same
replaceability, differing only in whether permission or authority is claimed. -/
theorem permission_flag_free :
    ∃ p q : ProvenanceRow,
      p.sourceName = q.sourceName ∧ p.kind = q.kind ∧
        p.replaceableByFormalEncoding = q.replaceableByFormalEncoding ∧
        p.permissionOrAuthorityClaimed ≠ q.permissionOrAuthorityClaimed :=
  ⟨⟨"s", .namedCommunity, true, false⟩, ⟨"s", .namedCommunity, false, false⟩,
    rfl, rfl, rfl, by decide⟩

/-- Agda `record CulturalProvenanceBoundary`, restricted to the fields with
logical content: the provenance rows, the seven anti-extraction flags and the
`boundaryHolds` field **together with its companion proof field**. -/
structure CulturalBoundary where
  /-- `rows`. -/
  rows : List ProvenanceRow
  /-- `provenanceRequired`. -/
  provenanceRequired : Bool
  /-- `noExtraction`. -/
  noExtraction : Bool
  /-- `noSubstitutionForLivingPractice`. -/
  noSubstitution : Bool
  /-- `noUniversalisation`. -/
  noUniversalisation : Bool
  /-- `noRomanticAuthority`. -/
  noRomanticAuthority : Bool
  /-- `noEmpiricalCapture`. -/
  noEmpiricalCapture : Bool
  /-- `formalAnalogyIsLimited`. -/
  formalAnalogyIsLimited : Bool
  /-- `boundaryHolds`. -/
  boundaryHolds : Bool
  /-- `boundaryHoldsIsTrue`: the Agda record pins the previous field. -/
  boundaryHoldsIsTrue : boundaryHolds = true

/-- Agda `canonicalCulturalProvenanceBoundary`: note the empty row list. -/
def canonicalBoundary : CulturalBoundary where
  rows := []
  provenanceRequired := true
  noExtraction := true
  noSubstitution := true
  noUniversalisation := true
  noRomanticAuthority := true
  noEmpiricalCapture := true
  formalAnalogyIsLimited := true
  boundaryHolds := true
  boundaryHoldsIsTrue := rfl

/-- **`boundaryHolds` is a tautology field.**  The record type forces it, so it
is constant on the whole carrier and reports nothing about any other field. -/
theorem boundaryHolds_constant (b c : CulturalBoundary) : b.boundaryHolds = c.boundaryHolds := by
  rw [b.boundaryHoldsIsTrue, c.boundaryHoldsIsTrue]

/-- And the canonical inhabitant asserts the boundary over an **empty**
provenance table. -/
theorem canonicalBoundary_rows_empty : canonicalBoundary.rows = [] := rfl

/-- A second inhabitant with a non-empty row list claiming permission, all
anti-extraction flags off, and the same pinned `boundaryHolds`. -/
def permissiveBoundary : CulturalBoundary where
  rows := [⟨"s", .namedCommunity, true, true⟩]
  provenanceRequired := false
  noExtraction := false
  noSubstitution := false
  noUniversalisation := false
  noRomanticAuthority := false
  noEmpiricalCapture := false
  formalAnalogyIsLimited := false
  boundaryHolds := true
  boundaryHoldsIsTrue := rfl

/-- **The pinned flag cannot report a violation.**  Two boundaries agreeing on
`boundaryHolds` and disagreeing on every flag it purports to summarise. -/
theorem boundaryHolds_does_not_summarise :
    canonicalBoundary.boundaryHolds = permissiveBoundary.boundaryHolds ∧
      canonicalBoundary.noExtraction ≠ permissiveBoundary.noExtraction := by decide

/-! ## §4 The promotion record -/

/-- Agda `record PhilosophyCulturalAdapter`, Boolean fields only. -/
structure Adapter where
  /-- `inspiredBy`. -/
  inspiredBy : Bool
  /-- `representsTradition`. -/
  representsTradition : Bool
  /-- `authorityPresent`. -/
  authorityPresent : Bool
  /-- `explicitNonRepresentationClaim`. -/
  explicitNonRepresentationClaim : Bool
  deriving DecidableEq, Repr

/-- Agda `canonicalPhilosophyCulturalAdapter`. -/
def canonicalAdapter : Adapter :=
  ⟨true, false, false, true⟩

/-- Agda `canonicalInspiredDoesNotRepresent`. -/
theorem canonical_inspired_does_not_represent :
    canonicalAdapter.representsTradition = false := rfl

/-- Agda `record CulturalApplicationPromotion`.  The three receipt fields are
Agda `Set` fields, mirrored as `Prop`; `representationPromoted` is a `Bool` with
no companion proof field. -/
structure Promotion where
  /-- `adapter`. -/
  adapter : Adapter
  /-- `sourceAuthorityReceipt`. -/
  sourceAuthorityReceipt : Prop
  /-- `communityOrSpeakerAuthorityReceipt`. -/
  communityAuthorityReceipt : Prop
  /-- `adaptationBoundaryReceipt`. -/
  adaptationBoundaryReceipt : Prop
  /-- `representationPromoted`. -/
  representationPromoted : Bool

/-- **The receipts do not determine the promotion.**  Two promotions with the
same adapter and the *same three receipts* differing only in whether
representation is promoted: the corpus record states the evidence and the
verdict side by side without linking them. -/
theorem receipts_do_not_determine_promotion :
    ∃ p q : Promotion,
      p.adapter = q.adapter ∧
        p.sourceAuthorityReceipt = q.sourceAuthorityReceipt ∧
        p.communityAuthorityReceipt = q.communityAuthorityReceipt ∧
        p.adaptationBoundaryReceipt = q.adaptationBoundaryReceipt ∧
        p.representationPromoted ≠ q.representationPromoted :=
  ⟨⟨canonicalAdapter, True, True, True, true⟩, ⟨canonicalAdapter, True, True, True, false⟩,
    rfl, rfl, rfl, rfl, by decide⟩

/-- **And the receipts may all be vacuous.**  A promotion whose three receipts
are `True` — inhabited by `trivial` — and whose flag is nevertheless set.  So
"the receipt fields are inhabited" is not evidence either, unless the receipt
types are themselves constrained. -/
theorem vacuous_receipts_admit_promotion :
    ∃ p : Promotion,
      p.sourceAuthorityReceipt ∧ p.communityAuthorityReceipt ∧
        p.adaptationBoundaryReceipt ∧ p.representationPromoted = true :=
  ⟨⟨canonicalAdapter, True, True, True, true⟩, trivial, trivial, trivial, rfl⟩

end AgdaMirror.AuthorityRoutes

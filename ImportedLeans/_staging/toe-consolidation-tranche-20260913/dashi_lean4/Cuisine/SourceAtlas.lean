import Mathlib

/-!
# Cuisine layer 7: the attributed source atlas

Lean mirror of the *counting* content of
`DASHI.Culture.Cuisine.CuisineKnowledgeSourceAtlas` and of the non-promotion
fields of `DASHI.Core.AttributedSourceCore.AttributedSource`.

The Agda side proves `canonicalCuisineKnowledgeSourceCount ≡ 22` by `refl`, and
that receipt is then required as a *field* of both
`MoleProcessArchitecture.MoleProcessArchitectureBoundary` and
`SituatedMoleWorld.SituatedMoleWorld` — one of the few places in the cuisine
lane where a numerical fact is load-bearing for a record's inhabitation.

New content proved here:

* the count, from the same list of identifiers (`sourceCount_eq_22`);
* `sourceIds_nodup` — the twenty-two entries are pairwise distinct, so the count
  really is a count of twenty-two *sources*.  The Agda `sourceCount` is a plain
  list length and does not exclude duplicates; this is a genuine gap closed;
* `citationCreatesAuthority_eq_false` — the non-promotion flag of every
  `AttributedSource` is `false` by construction (see `Cuisine.LedgerPattern` for
  what that does and does not establish).
-/

namespace Cuisine.SourceAtlas

/-- The twenty-two identifiers of `canonicalCuisineKnowledgeSources`, in order. -/
def sourceIds : List String :=
  [ "wovenPalateArchitectureOfAsh"
  , "castilloCisnerosEnMiMeroMole"
  , "hryciukAlquimistaSabores"
  , "hernandezAlbarranCulturaAlimentaria"
  , "buenahoraExperienciasSilenciadas"
  , "pilcherMoleDigitalHistory"
  , "bakGellerCuevasFoodSovereignty"
  , "kimmererBraidingSweetgrass"
  , "yunkaportaSandTalk"
  , "unescoTraditionalMexicanCuisine"
  , "rubinTraditionalCuisineTenYears"
  , "conabioSIAgroBD"
  , "mathijssenCulinaryFluidMechanics"
  , "guyHardParticleSuspensions"
  , "ragouilliauxThixotropicTransition"
  , "dawBatchArrivals"
  , "euGeographicalIndications"
  , "comiteChampagneGovernance"
  , "galapagosVisitorSites"
  , "antarcticVisitorGuidelines"
  , "unescoVisitorManagement"
  , "iachrVoluntaryIsolation" ]

/-- The Agda `sourceCount` is list length. -/
def sourceCount (l : List String) : ℕ := l.length

/-- The receipt required by `MoleProcessArchitectureBoundary` and
`SituatedMoleWorld`. -/
theorem sourceCount_eq_22 : sourceCount sourceIds = 22 := rfl

/-- **Gap closed.**  The twenty-two entries are pairwise distinct, so the
receipt counts twenty-two distinct sources rather than twenty-two list cells. -/
theorem sourceIds_nodup : sourceIds.Nodup := by decide

/-- Hence the underlying finite set also has twenty-two elements. -/
theorem sourceIds_toFinset_card : sourceIds.toFinset.card = 22 := by
  rw [List.toFinset_card_of_nodup sourceIds_nodup]
  rfl

/-! ## Non-promotion flags of an attributed source -/

inductive SourceKind
  | academicArticleSource | academicBookSource | academicChapterSource
  | practitionerSource | communitySource | institutionalSource
  | governmentSource | archivalSource | technicalStandardSource | newsSource
  deriving DecidableEq, Fintype, Repr

/-- The proof-relevant skeleton of `DASHI.Core.AttributedSourceCore.AttributedSource`:
bibliographic strings plus the two non-promotion flags, each pinned to `false`. -/
structure AttributedSource where
  sourceAuthor : String
  sourceTitle : String
  publicationContext : String
  publicationYear : String
  canonicalURL : String
  sourceKind : SourceKind
  formalisationRelationship : String
  citationImportsProof : Bool
  citationImportsProofIsFalse : citationImportsProof = false
  citationCreatesAuthority : Bool
  citationCreatesAuthorityIsFalse : citationCreatesAuthority = false

/-- Citing a source never promotes it to authority: the flag is `false` for
every inhabitant.  Compare the Agda regression
`CuisineFormalismTests.castilloDOIDoesNotCreateAuthority`, which checks a single
source; this is the statement for all of them. -/
theorem citationCreatesAuthority_eq_false (s : AttributedSource) :
    s.citationCreatesAuthority = false := s.citationCreatesAuthorityIsFalse

theorem citationImportsProof_eq_false (s : AttributedSource) :
    s.citationImportsProof = false := s.citationImportsProofIsFalse

end Cuisine.SourceAtlas

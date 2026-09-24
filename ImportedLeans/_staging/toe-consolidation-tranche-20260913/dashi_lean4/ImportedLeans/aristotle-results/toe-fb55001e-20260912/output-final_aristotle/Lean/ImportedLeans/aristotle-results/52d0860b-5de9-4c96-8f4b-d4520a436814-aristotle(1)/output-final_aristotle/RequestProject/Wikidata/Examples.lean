import RequestProject.Epistemic.Repair
import RequestProject.Epistemic.Context

/-!
# Worked example: the artist / painter / sculptor fragment

A concrete knowledge base built from real Wikidata identifiers:

* `Q483501` artist, `Q1028181` painter, `Q1281618` sculptor,
* `Q5592` Michelangelo (a painter *and* a sculptor), `Q762` Leonardo da Vinci,
* `P2737` "union of" is the class-algebra relationship being checked.

Everything below is decided by the executable checkers and transported to the
declarative statements through the exactness theorems, so each example is a
regression test for the engine and a demonstration of the epistemic rules:

* the union is genuine but **not** disjoint (`artist_union_not_disjoint`);
* absence in one knowledge base is not refutation in the world
  (`absence_is_not_world_refutation`);
* deprecated data is invisible to the engine (`deprecated_not_instance`);
* a certified negative alignment really is negative (`badAlignment_refuted`);
* truthy rank data does not determine evidence state
  (`truthy_does_not_determine_evidence`).
-/

namespace Wikidata

namespace Example

open Epistemic

/-- `Q483501`, artist. -/
def artist : Qid := ⟨483501⟩
/-- `Q1028181`, painter. -/
def painter : Qid := ⟨1028181⟩
/-- `Q1281618`, sculptor. -/
def sculptor : Qid := ⟨1281618⟩
/-- An auxiliary class of painter-sculptors. -/
def painterSculptor : Qid := ⟨9999999⟩
/-- `Q5592`, Michelangelo. -/
def michelangelo : Qid := ⟨5592⟩
/-- `Q762`, Leonardo da Vinci. -/
def leonardo : Qid := ⟨762⟩

private def sub (a b : Qid) : Statement := ⟨a, P279, b, Rank.normal⟩
private def inst (x c : Qid) : Statement := ⟨x, P31, c, Rank.normal⟩

/-- The worked knowledge base. -/
def artistKB : KB where
  entities := [artist, painter, sculptor, painterSculptor, michelangelo, leonardo]
  statements :=
    [ sub painter artist
    , sub sculptor artist
    , sub painterSculptor painter
    , sub painterSculptor sculptor
    , inst michelangelo painterSculptor
    , inst leonardo painter ]

/-! ## The subclass and instance engines -/

theorem painter_subclass_artist : SubclassOf artistKB painter artist :=
  (isSubclassOf_iff _ _ _).1 (by decide)

theorem painterSculptor_subclass_artist : SubclassOf artistKB painterSculptor artist :=
  (isSubclassOf_iff _ _ _).1 (by decide)

theorem artist_not_subclass_painter : ¬ SubclassOf artistKB artist painter := by
  intro h
  have := (isSubclassOf_iff artistKB artist painter).2 h
  exact absurd this (by decide)

theorem michelangelo_instance_artist : InstanceOf artistKB michelangelo artist :=
  (isInstanceOf_iff _ _ _).1 (by decide)

theorem leonardo_not_instance_sculptor : ¬ InstanceOf artistKB leonardo sculptor := by
  intro h
  have := (isInstanceOf_iff artistKB leonardo sculptor).2 h
  exact absurd this (by decide)

/-! ## Class algebra: a union that is not a disjoint union -/

theorem artistKB_unionOk : unionOk artistKB artist [painter, sculptor] = true := by decide

/-- Artist is the union of painter and sculptor, as far as this knowledge base
knows. -/
theorem artist_isUnion : IsUnionOn artistKB artist [painter, sculptor] :=
  isUnion_of_unionOk _ _ _ artistKB_unionOk

/-- ... but it is *not* a disjoint union: Michelangelo is both. -/
theorem artist_union_not_disjoint : ¬ IsDisjointUnionOn artistKB artist [painter, sculptor] := by
  intro h
  have := (dunOk_iff artistKB artist [painter, sculptor]).2 h
  exact absurd this (by decide)

theorem painter_sculptor_not_disjoint : ¬ DisjointOn artistKB painter sculptor := by
  intro h
  have := (disjointOk_iff artistKB painter sculptor).2 h
  exact absurd this (by decide)

/-! ## Diagnostics -/

theorem artistKB_valid : Valid artistKB := (valid_iff artistKB).1 (by decide)

theorem artistKB_errors_empty : errors artistKB = [] :=
  (errors_eq_nil_iff_valid artistKB).2 (by decide)

/-! ## Open-world absence

The same claim fails in a smaller knowledge base and holds in a larger one, so a
checker failure must not be exported as a refutation of the world-level claim. -/

/-- The knowledge base with the `painter ⊑ artist` edge missing. -/
def partialKB : KB where
  entities := artistKB.entities
  statements :=
    [ sub sculptor artist
    , sub painterSculptor painter
    , sub painterSculptor sculptor
    , inst michelangelo painterSculptor
    , inst leonardo painter ]

theorem partialKB_sub_artistKB : partialKB.statements ⊆ artistKB.statements := by decide

/-- **Absence is not refutation.**  `painter ⊑ artist` is unprovable from
`partialKB` and provable from the larger `artistKB`. -/
theorem absence_is_not_world_refutation :
    ∃ kb kb' : KB, kb.statements ⊆ kb'.statements ∧
      ¬ SubclassOf kb painter artist ∧ SubclassOf kb' painter artist := by
  refine ⟨partialKB, artistKB, partialKB_sub_artistKB, ?_, painter_subclass_artist⟩
  intro h
  have := (isSubclassOf_iff partialKB painter artist).2 h
  exact absurd this (by decide)

/-! ## Ranks: the truthy projection -/

/-- A knowledge base where Leonardo's "sculptor" statement is deprecated and his
"painter" statement is preferred. -/
def rankedKB : KB where
  entities := artistKB.entities
  statements :=
    [ sub painter artist
    , sub sculptor artist
    , ⟨leonardo, P31, sculptor, Rank.deprecated⟩
    , ⟨leonardo, P31, painter, Rank.preferred⟩
    , ⟨leonardo, P31, artist, Rank.normal⟩ ]

/-- Deprecated statements are invisible to the engine. -/
theorem deprecated_not_instance : ¬ InstanceOf rankedKB leonardo sculptor := by
  intro h
  have := (isInstanceOf_iff rankedKB leonardo sculptor).2 h
  exact absurd this (by decide)

/-- A normal statement is suppressed by a preferred statement on the same
subject and property — but the *derived* fact can survive through the class
hierarchy. -/
theorem normal_statement_suppressed :
    IsTruthy rankedKB ⟨leonardo, P31, artist, Rank.normal⟩ = false := by decide

theorem leonardo_still_artist : InstanceOf rankedKB leonardo artist :=
  (isInstanceOf_iff _ _ _).1 (by decide)

/-! ## Redundancy and review-only repair -/

/-- The redundant edge `painterSculptor ⊑ artist`. -/
def redundantEdge : Statement := sub painterSculptor artist

/-- `artistKB` extended with the redundant edge. -/
def redundantKB : KB where
  entities := artistKB.entities
  statements := redundantEdge :: artistKB.statements

theorem redundantEdge_isRedundant : isRedundant redundantKB redundantEdge = true := by decide

theorem redundantEdge_redundant : Redundant redundantKB redundantEdge :=
  (isRedundant_iff _ _).1 redundantEdge_isRedundant

/-- The proposal generated from the redundancy diagnostic is supported. -/
theorem redundancyProposal_supported :
    (redundancyProposal redundantKB redundantEdge ["Wikidata.Example.redundantEdge"]).evidence
      = Trit.supported :=
  (redundancyProposal_supported_iff _ _ _).2 redundantEdge_redundant

/-- Whatever the review decides, enacting the proposal cannot change what the
ontology says. -/
theorem redundancy_repair_is_meaning_preserving (d : Decision) (a b : Qid) :
    SubclassOf
        (enact redundantKB (redundancyProposal redundantKB redundantEdge
          ["Wikidata.Example.redundantEdge"]) d) a b
      ↔ SubclassOf redundantKB a b :=
  enact_redundancy_proposal_preserves_subclass redundantKB redundantEdge _ rfl
    redundancyProposal_supported d a b

/-! ## Provenance slices

The same claim, evaluated against different provenance slices of the same
knowledge base. -/

/-- Every statement of the worked knowledge base has normal rank. -/
theorem artistKB_allNormal : AllNormal artistKB := by
  show ∀ st ∈ artistKB.statements, st.rank = Rank.normal
  decide

/-- `painter ⊑ artist` is unreferenced; `sculptor ⊑ artist` cites a reliable
source. -/
def artistProvenance : Provenanced where
  base := artistKB
  refs := fun st => if st = sub painter artist then [] else ["catalogue"]
  reliableSource := fun r => r = "catalogue"

theorem artistProvenance_base : artistProvenance.base = artistKB := rfl

/-- Support at the reliable slice transfers up to the full knowledge base. -/
theorem sculptor_support_transfers_up :
    (sliceClaim artistProvenance sculptor artist true ["catalogue"]).stateAt Slice.asserted
      = Trit.supported :=
  sliceClaim_transfers_up artistKB_allNormal Slice.reliable (by decide)

/-- **Support does not transfer down.**  `painter ⊑ artist` is supported by the
asserted knowledge base but unresolved once unreferenced statements are dropped:
restricting to a slice never inherits the authority of the whole. -/
theorem support_does_not_transfer_down :
    (sliceClaim artistProvenance painter artist true []).stateAt Slice.asserted
        = Trit.supported ∧
      (sliceClaim artistProvenance painter artist true []).stateAt Slice.reliable
        = Trit.unresolved := by
  constructor
  · decide
  · decide

/-! ## Cross-ontology alignment -/

/-- A target ontology that splits the visual arts differently: its `painter`
class is not a subclass of its `artist` class. -/
def targetKB : KB where
  entities := [⟨1⟩, ⟨2⟩]
  statements := []

/-- An alignment mapping painter and artist into the target ontology. -/
def badAlignment : Alignment where
  src := artistKB
  tgt := targetKB
  links := [(painter, ⟨1⟩), (artist, ⟨2⟩)]

theorem badAlignment_alignOk_false : Alignment.alignOk badAlignment = false := by decide

/-- **A certified negative.**  The alignment provably fails to preserve the
subclass relation; this is a refutation, not an absence. -/
theorem badAlignment_refuted : ¬ Alignment.PreservesSubclass badAlignment := by
  intro h
  have := (Alignment.alignOk_iff badAlignment).2 h
  rw [badAlignment_alignOk_false] at this
  exact absurd this (by simp)

/-- The certified negative is exactly what may be imported as `contradicted`,
whereas an unobserved alignment stays `unresolved`. -/
theorem badAlignment_evidence :
    verdictState true true ObjectVerdict.certifiedRefuted = Trit.contradicted ∧
      verdictState true true ObjectVerdict.notObserved = Trit.unresolved :=
  ⟨verdictState_certifiedRefuted, rfl⟩

/-! ## Truthy query semantics is not evidence semantics -/

private def unionClaim : ClassClaim := ClassClaim.unionOf artist [painter, sculptor]

/-- A matched source with an accepting checker yields support ... -/
theorem matched_certificate_supported :
    (Certificate.mk artistKB unionClaim SurfaceKind.classFact true []).state = Trit.supported := by
  rw [Certificate.state_eq_supported_iff]
  exact ⟨rfl, artist_isUnion⟩

/-- ... while the identical claim from an unmatched source stays unresolved. -/
theorem unmatched_certificate_unresolved :
    (Certificate.mk artistKB unionClaim SurfaceKind.classFact false []).state
      = Trit.unresolved :=
  Certificate.state_of_source_mismatch rfl

/-- **Truthy rank data does not determine evidence state.**  There is no function
from the truthy projection of the data to the epistemic state of an imported
claim: the two semantics are genuinely different. -/
theorem truthy_does_not_determine_evidence :
    ¬ ∃ f : Bool → Trit, ∀ (cert : Certificate) (st : Statement),
        st ∈ cert.kb.statements → cert.state = f (IsTruthy cert.kb st) := by
  rintro ⟨f, hf⟩
  have hmem : sub painter artist ∈ artistKB.statements := by decide
  have h1 := hf (Certificate.mk artistKB unionClaim SurfaceKind.classFact true [])
    (sub painter artist) hmem
  have h2 := hf (Certificate.mk artistKB unionClaim SurfaceKind.classFact false [])
    (sub painter artist) hmem
  rw [matched_certificate_supported] at h1
  rw [unmatched_certificate_unresolved] at h2
  rw [← h2] at h1
  exact absurd h1 (by simp)

end Example

end Wikidata

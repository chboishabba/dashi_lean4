import RequestProject.TaxaLineage

/-!
# A worked taxon hierarchy: the lineage of *Homo sapiens*

A concrete fragment exercising `RequestProject.Taxa` and `RequestProject.TaxaLineage`.  The
taxa carry their real Wikidata identifiers — *Homo sapiens* (Q15978631), *Homo* (Q171283),
*Primates* (Q7380), *Mammalia* (Q7377), *Chordata* (Q10915), *Animalia* (Q729) and *Aves*
(Q5113) — but the hierarchy is **simplified**: the intermediate ranks that live between
these (families, suborders, subphyla, …) are left out, which the layer permits, since
`taxon rank` values only have to *increase* along `parent taxon`, not to increase by one
step of the scale.

Everything below is decided by computation, including the defects the validator is meant to
catch: a cycle in `parent taxon`, a taxon with two parents, a rank inversion, and a
`parent taxon` statement that duplicates a `subclass of` statement.
-/

namespace Wikidata
namespace TKB

/-! ### The fragment -/

/-- The underlying ontology: seven taxa, each an instance of `taxon` (Q16521). -/
def lifeBase : KB where
  name := "life"
  items := [Qid.wd "Q16521", Qid.wd "Q15978631", Qid.wd "Q171283", Qid.wd "Q7380",
            Qid.wd "Q7377", Qid.wd "Q10915", Qid.wd "Q729", Qid.wd "Q5113"]
  levels := [(Qid.wd "Q16521", 1)]
  inst := [(Qid.wd "Q15978631", Qid.wd "Q16521"), (Qid.wd "Q171283", Qid.wd "Q16521"),
           (Qid.wd "Q7380", Qid.wd "Q16521"), (Qid.wd "Q7377", Qid.wd "Q16521"),
           (Qid.wd "Q10915", Qid.wd "Q16521"), (Qid.wd "Q729", Qid.wd "Q16521"),
           (Qid.wd "Q5113", Qid.wd "Q16521")]

/-- The taxon layer: the `parent taxon` chain from *Homo sapiens* up to *Animalia*, with
*Aves* branching off at *Chordata*. -/
def lifeTKB : TKB where
  base := lifeBase
  parents := [(Qid.wd "Q15978631", Qid.wd "Q171283"), (Qid.wd "Q171283", Qid.wd "Q7380"),
              (Qid.wd "Q7380", Qid.wd "Q7377"), (Qid.wd "Q7377", Qid.wd "Q10915"),
              (Qid.wd "Q10915", Qid.wd "Q729"), (Qid.wd "Q5113", Qid.wd "Q10915")]
  ranks := [(Qid.wd "Q15978631", .species), (Qid.wd "Q171283", .genus),
            (Qid.wd "Q7380", .order), (Qid.wd "Q7377", .class_),
            (Qid.wd "Q10915", .phylum), (Qid.wd "Q729", .kingdom),
            (Qid.wd "Q5113", .class_)]
  names := [(Qid.wd "Q15978631", "Homo sapiens"), (Qid.wd "Q171283", "Homo"),
            (Qid.wd "Q7380", "Primates"), (Qid.wd "Q7377", "Mammalia"),
            (Qid.wd "Q10915", "Chordata"), (Qid.wd "Q729", "Animalia"),
            (Qid.wd "Q5113", "Aves")]

/-! ### What the layer says -/

/-- The worked hierarchy passes every check. -/
theorem life_valid : lifeTKB.tValid = true := by decide

/-- Ranks are *not* total: `taxon` (Q16521) is a class of the ontology, not a taxon, so it
carries no `taxon rank` — exactly as it should be. -/
theorem life_ranks_not_total : lifeTKB.ranksTotal = false := by decide

/-- Humans descend from animals, although nobody said so directly. -/
theorem life_human_descends_from_animalia :
    lifeTKB.isStrictDescendantB (Qid.wd "Q15978631") (Qid.wd "Q729") = true := by decide

/-- …and not the other way round. -/
theorem life_animalia_not_human :
    lifeTKB.isDescendantB (Qid.wd "Q729") (Qid.wd "Q15978631") = false := by decide

/-- The lineage of *Homo sapiens*, in order, up to the root. -/
theorem life_lineage :
    lifeTKB.lineage (Qid.wd "Q15978631") =
      [Qid.wd "Q15978631", Qid.wd "Q171283", Qid.wd "Q7380", Qid.wd "Q7377",
       Qid.wd "Q10915", Qid.wd "Q729"] := by decide

/-- *Animalia* is the one root the fragment has. -/
theorem life_root : lifeTKB.rootsOfL (Qid.wd "Q15978631") = [Qid.wd "Q729"] := by decide

/-- The lowest common ancestor of *Homo sapiens* and *Aves* is *Chordata*: mammals and
birds are both chordates, and nothing below that. -/
theorem life_lca_human_bird :
    lifeTKB.lcaOf? (Qid.wd "Q15978631") (Qid.wd "Q5113") = some (Qid.wd "Q10915") := by decide

/-- The lowest common ancestor of a taxon and one of its own ancestors is that ancestor. -/
theorem life_lca_human_mammalia :
    lifeTKB.lcaOf? (Qid.wd "Q15978631") (Qid.wd "Q7377") = some (Qid.wd "Q7377") := by decide

/-- Scientific names identify taxa. -/
theorem life_name : lifeTKB.nameOf? (Qid.wd "Q171283") = some "Homo" := by decide

/-- …and can be looked up. -/
theorem life_taxon_of_name :
    lifeTKB.taxonOfName? "Chordata" = some (Qid.wd "Q10915") := by decide

/-! ### The defects the checks catch -/

/-- A cycle in `parent taxon` — *Animalia* made a child of *Homo sapiens* — is rejected. -/
theorem life_cycle_rejected :
    { lifeTKB with
        parents := lifeTKB.parents ++ [(Qid.wd "Q729", Qid.wd "Q15978631")] }.tAcyclic
      = false := by decide

/-- A taxon with two parent taxa is rejected: the hierarchy has to be a tree. -/
theorem life_fork_rejected :
    { lifeTKB with
        parents := lifeTKB.parents ++ [(Qid.wd "Q171283", Qid.wd "Q7377")] }.singleParent
      = false := by decide

/-- A rank inversion — *Homo* declared a kingdom, and so ranked above the order it sits
in — is rejected. -/
theorem life_rank_inversion_rejected :
    { lifeTKB with
        ranks := (Qid.wd "Q171283", TaxonRank.kingdom) :: lifeTKB.ranks }.ranksStrict
      = false := by decide

/-- Two taxa sharing a scientific name are rejected. -/
theorem life_duplicate_name_rejected :
    { lifeTKB with names := lifeTKB.names ++ [(Qid.wd "Q5113", "Homo")] }.namesUnique
      = false := by decide

/-- Confusing the taxon hierarchy with the taxonomy of the ontology is rejected: a
`parent taxon` statement may not duplicate a `subclass of` statement. -/
theorem life_taxonomy_confusion_rejected :
    { lifeTKB with
        base := { lifeBase with
          sub := [(Qid.wd "Q15978631", Qid.wd "Q171283")] } }.noTaxonomyConfusion
      = false := by decide

/-! ### The general theorems, instantiated -/

/-- Every taxon of the fragment descends from exactly one root — an instance of
`TKB.tValid_exists_unique_root`. -/
theorem life_exists_unique_root (a : Qid) :
    ∃! b, lifeTKB.isDescendantB a b = true ∧ lifeTKB.isRootB b = true :=
  tValid_exists_unique_root life_valid a

/-- The lineage of *Homo sapiens* consists of exactly the taxa it descends from — an
instance of `TKB.mem_lineage_iff`. -/
theorem life_mem_lineage_iff (x : Qid) :
    x ∈ lifeTKB.lineage (Qid.wd "Q15978631") ↔ lifeTKB.DescendsFrom (Qid.wd "Q15978631") x :=
  mem_lineage_iff (by decide) (by decide) (by decide) _ x

/-- *Chordata* really is a common ancestor of *Homo sapiens* and *Aves*, and every common
ancestor of the two lies above it — an instance of `TKB.lca_sound` and `TKB.lca_least`. -/
theorem life_lca_characterised :
    lifeTKB.DescendsFrom (Qid.wd "Q15978631") (Qid.wd "Q10915") ∧
    lifeTKB.DescendsFrom (Qid.wd "Q5113") (Qid.wd "Q10915") ∧
    ∀ d, lifeTKB.DescendsFrom (Qid.wd "Q15978631") d → lifeTKB.DescendsFrom (Qid.wd "Q5113") d →
      lifeTKB.DescendsFrom (Qid.wd "Q10915") d := by
  refine ⟨(lca_sound (by decide) life_lca_human_bird).1,
    (lca_sound (by decide) life_lca_human_bird).2, fun d hd hd' => ?_⟩
  exact lca_least (by decide) (by decide) life_lca_human_bird hd hd'

end TKB
end Wikidata

import RequestProject.PropertyConstraints

/-!
# A second domain: the Wikidata taxonomy

A further fragment of Wikidata, exercising the same machinery on a different part of
the ontology: taxa (`taxon`, Q16521) organised by `parent taxon` (P171), and their
`taxon rank` (P105) drawn from the class `taxonomic rank` (Q427626).

Two features of the domain are visible in the formalisation:

* `parent taxon` behaves as a transitive containment relation, so the engine derives
  the whole ancestry of a taxon from the individual parent statements, and the
  irreflexivity check certifies that the ancestry relation is a strict order;
* `taxon rank` must *not* be transitive or inherited: the rank of a lion is `species`
  and no other rank, even though its parent taxon has rank `genus`. This is
  `lion_rank_not_inherited` below.

As elsewhere in this development, the identifiers follow Wikidata but the fragment
is a stylised excerpt; the theorems are statements about this fragment.
-/

namespace Wikidata
namespace Taxonomy

open KB PKB

/-- Abbreviation for a Wikidata item. -/
def Q (s : String) : Qid := .wd s

/-- Abbreviation for a Wikidata property. -/
def P (s : String) : Pid := .wd s

/-- English labels for the identifiers used below. -/
def labels : List (Qid × String) :=
  [(Q "Q140", "lion"), (Q "Q127960", "Panthera"), (Q "Q25265", "Felidae"),
   (Q "Q25306", "Carnivora"), (Q "Q7377", "Mammalia"), (Q "Q10915", "Chordata"),
   (Q "Q729", "Animalia"),
   (Q "Q7432", "species"), (Q "Q34740", "genus"), (Q "Q35409", "family"),
   (Q "Q16521", "taxon"), (Q "Q427626", "taxonomic rank"), (Q "Q35120", "entity")]

/-- The label of an identifier, or its raw form if none is recorded. -/
def labelOf (q : Qid) : String := (labels.lookup q).getD (toString (repr q))

/-- The items: seven taxa, three ranks, and the classes they instantiate. -/
def taxonBase : KB where
  name := "wd-taxonomy"
  items := [Q "Q140", Q "Q127960", Q "Q25265", Q "Q25306", Q "Q7377", Q "Q10915", Q "Q729",
            Q "Q7432", Q "Q34740", Q "Q35409",
            Q "Q16521", Q "Q427626", Q "Q35120"]
  levels := [(Q "Q140", 0), (Q "Q127960", 0), (Q "Q25265", 0), (Q "Q25306", 0), (Q "Q7377", 0),
             (Q "Q10915", 0), (Q "Q729", 0),
             (Q "Q7432", 0), (Q "Q34740", 0), (Q "Q35409", 0),
             (Q "Q16521", 1), (Q "Q427626", 1), (Q "Q35120", 1)]
  sub := [(Q "Q16521", Q "Q35120"), (Q "Q427626", Q "Q35120")]
  inst := [(Q "Q140", Q "Q16521"), (Q "Q127960", Q "Q16521"), (Q "Q25265", Q "Q16521"),
           (Q "Q25306", Q "Q16521"), (Q "Q7377", Q "Q16521"), (Q "Q10915", Q "Q16521"),
           (Q "Q729", Q "Q16521"),
           (Q "Q7432", Q "Q427626"), (Q "Q34740", Q "Q427626"), (Q "Q35409", Q "Q427626")]
  disj := [(Q "Q16521", Q "Q427626")]

set_option maxRecDepth 40000 in
theorem taxonBase_valid : taxonBase.valid = true := by decide

/-- The property layer: `parent taxon` (P171), declared transitive with taxa as
subjects and values, and `taxon rank` (P105), which is *not* transitive. -/
def taxonPKB : PKB where
  base := taxonBase
  props := [P "P171", P "P105"]
  stmts := [(P "P171", Q "Q140", Q "Q127960"), (P "P171", Q "Q127960", Q "Q25265"),
            (P "P171", Q "Q25265", Q "Q25306"), (P "P171", Q "Q25306", Q "Q7377"),
            (P "P171", Q "Q7377", Q "Q10915"), (P "P171", Q "Q10915", Q "Q729"),
            (P "P105", Q "Q140", Q "Q7432"), (P "P105", Q "Q127960", Q "Q34740"),
            (P "P105", Q "Q25265", Q "Q35409")]
  transProps := [P "P171"]
  typeC := [(P "P171", Q "Q16521"), (P "P105", Q "Q16521")]
  valueTypeC := [(P "P171", Q "Q16521"), (P "P105", Q "Q427626")]

set_option maxRecDepth 40000 in
/-- The taxonomy passes the full validator, including the type and value-type
constraints of both properties. -/
theorem taxonPKB_pvalid : taxonPKB.pvalid = true := by decide

theorem taxonPKB_pWellFormed : taxonPKB.pWellFormed = true := pvalid_pWellFormed taxonPKB_pvalid

set_option maxRecDepth 40000 in
theorem taxonPKB_transUpwardClosed : taxonPKB.transUpwardClosed = true := by decide

/-- The engine decides derivability in the abstract model exactly for this layer. -/
theorem taxonPKB_relatedB_iff_holds (p : Pid) (s o : Qid) :
    taxonPKB.relatedB p s o = true ↔ taxonPKB.toLayer.Holds p s o :=
  relatedB_iff_holds taxonPKB_pWellFormed rfl rfl taxonPKB_transUpwardClosed p s o

set_option maxRecDepth 40000 in
/-- The whole ancestry of the lion is derived from the six parent statements. -/
theorem lion_ancestry :
    taxonPKB.valuesOf (P "P171") (Q "Q140") =
      [Q "Q127960", Q "Q25265", Q "Q25306", Q "Q7377", Q "Q10915", Q "Q729"] := by decide

set_option maxRecDepth 40000 in
/-- In particular, the lion is a descendant of `Animalia`. -/
theorem lion_in_animalia : taxonPKB.relatedB (P "P171") (Q "Q140") (Q "Q729") = true := by decide

theorem holds_lion_in_animalia : taxonPKB.toLayer.Holds (P "P171") (Q "Q140") (Q "Q729") :=
  (taxonPKB_relatedB_iff_holds _ _ _).1 lion_in_animalia

set_option maxRecDepth 40000 in
/-- The rank of a taxon is not inherited from its parent: the lion has rank
`species`, and not the rank `genus` of its parent taxon `Panthera`. -/
theorem lion_rank_not_inherited :
    taxonPKB.relatedB (P "P105") (Q "Q140") (Q "Q7432") = true ∧
    taxonPKB.relatedB (P "P105") (Q "Q140") (Q "Q34740") = false := by decide

/-- Abstractly: the lion is not of rank `genus`. -/
theorem not_holds_lion_genus :
    ¬ taxonPKB.toLayer.Holds (P "P105") (Q "Q140") (Q "Q34740") := by
  intro h
  have := (taxonPKB_relatedB_iff_holds _ _ _).2 h
  rw [lion_rank_not_inherited.2] at this
  exact Bool.false_ne_true this

set_option maxRecDepth 40000 in
theorem parentTaxon_irreflexiveB : taxonPKB.irreflexiveB (P "P171") = true := by decide

set_option maxRecDepth 40000 in
theorem parentTaxon_isTrans : taxonPKB.isTransB (P "P171") = true := by decide

/-- No taxon is its own ancestor: `parent taxon` is irreflexive ... -/
theorem parentTaxon_irreflexive (s : Qid) : ¬ taxonPKB.toLayer.Holds (P "P171") s s :=
  irreflexive_of_irreflexiveB taxonPKB_pWellFormed rfl rfl taxonPKB_transUpwardClosed
    parentTaxon_irreflexiveB s

/-- ... and acyclic, hence a strict partial order on the taxa. -/
theorem parentTaxon_acyclic (a : Qid) :
    ¬ Relation.TransGen (taxonPKB.toLayer.Holds (P "P171")) a a :=
  acyclic_of_irreflexiveB taxonPKB_pWellFormed rfl rfl taxonPKB_transUpwardClosed
    parentTaxon_isTrans parentTaxon_irreflexiveB a

set_option maxRecDepth 40000 in
theorem taxonRank_singleValueB : taxonPKB.singleValueB (P "P105") = true := by decide

/-- Every taxon has at most one rank. -/
theorem taxonRank_singleValued : taxonPKB.toLayer.SingleValued (P "P105") :=
  singleValued_of_singleValueB taxonPKB_pWellFormed rfl rfl taxonPKB_transUpwardClosed
    taxonRank_singleValueB

/-- A taxon and a rank can never be confused: the two classes are declared disjoint,
and the declaration is respected. -/
theorem taxon_rank_disjoint :
    (taxonBase.toWithDisjointness taxonBase_valid).DisjointWith (Q "Q16521") (Q "Q427626") :=
  Or.inl (by simp [taxonBase])

theorem no_item_is_taxon_and_rank (a : Qid)
    (h1 : (taxonBase.toOntology taxonBase_valid).InstanceOf a (Q "Q16521"))
    (h2 : (taxonBase.toOntology taxonBase_valid).InstanceOf a (Q "Q427626")) : False :=
  (taxonBase.toWithDisjointness taxonBase_valid).disjointWith_spec taxon_rank_disjoint h1 h2

end Taxonomy
end Wikidata

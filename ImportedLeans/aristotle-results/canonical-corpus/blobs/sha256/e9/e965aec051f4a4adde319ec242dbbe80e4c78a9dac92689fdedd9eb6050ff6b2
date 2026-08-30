import RequestProject.Generated.Core
import RequestProject.Generated.DouglasAdams
import RequestProject.Generated.Geography
import RequestProject.Generated.LifeSciences
import RequestProject.Generated.Society
import RequestProject.Generated.Events
import RequestProject.Queries

/-!
# Reasoning with the compiled Wikidata facts

The modules under `RequestProject.Generated` are produced by `wikidata lean` from
data downloaded from the Wikidata API (the `.wdkb` files under `data/`).  This
file is hand-written: it shows what the compiled fragments are *for*, by proving
statements about the real ontology on top of them.

* `Compiled.adams_instanceOf_naturalPerson` and its consequences: inside the
  downloaded Douglas Adams fragment — which passes the validator, hence is an
  abstract `Wikidata.Ontology` — Douglas Adams is a natural person, is not an
  instance of anything he is an instance of in reverse, and sits one metaclass
  level below the class.
* `Compiled.geography_subclass_cycle` and `Compiled.no_ontology_over_geography`:
  the downloaded geography fragment states both `region ⊑ geographical area` and
  `geographical area ⊑ region`.  Live Wikidata therefore has a genuine
  `subclass of` cycle, and **no** `Wikidata.Ontology` can have exactly these
  P279 statements, because the class hierarchy of an ontology is antisymmetric.
* `Compiled.core_knows_more_than_adams`: merging fragments really does add
  knowledge — a fact derivable in the merged corpus that no single fragment
  derives.
* `Compiled.adams_organism_needs_both_downloads`: a *cross-domain* fact.  In the
  merged corpus Douglas Adams is an instance of *organism*, a biological class;
  the derivation runs through statements downloaded for the biography fragment
  and statements downloaded for the life-sciences fragment, and neither of the
  two derives it on its own.
* `Compiled.no_ontology_over_core`: the cycle survives the merge, so the whole
  corpus is not modelled by any abstract `Wikidata.Ontology` either.
* `Compiled.unique_human_of_adamsFragment` and the queries around it: the query
  language of `RequestProject.Queries`, run against the downloaded data — and, by
  completeness of the evaluator, the answers are the only ones there are.
-/

namespace Wikidata
namespace Compiled

open Wikidata.Generated

/-! ### The Douglas Adams fragment, as an abstract ontology -/

/-- Douglas Adams (Q42) is an instance of *natural person* (Q154954): a P31
statement to *human* (Q5) followed by downloaded P279 steps. -/
theorem adams_instanceOf_naturalPerson :
    DouglasAdams.onto.InstanceOf (Qid.wd "Q42") (Qid.wd "Q154954") :=
  (KB.isInstanceOf_iff_instanceOf DouglasAdams.kb_valid _ _).1 (by decide)

/-- Being an instance is asymmetric, so *natural person* is not an instance of
Douglas Adams. -/
theorem naturalPerson_not_instanceOf_adams :
    ¬ DouglasAdams.onto.InstanceOf (Qid.wd "Q154954") (Qid.wd "Q42") :=
  Ontology.instanceOf_asymm adams_instanceOf_naturalPerson

/-- A class sits exactly one metaclass level above its instances. -/
theorem level_naturalPerson :
    DouglasAdams.onto.level (Qid.wd "Q154954") = DouglasAdams.onto.level (Qid.wd "Q42") + 1 :=
  Ontology.level_instanceOf adams_instanceOf_naturalPerson

/-- *Natural person* is a class of the downloaded ontology, since it has an
instance. -/
theorem naturalPerson_isClass : DouglasAdams.onto.IsClass (Qid.wd "Q154954") :=
  Ontology.isClass_of_hasInstance ⟨_, adams_instanceOf_naturalPerson⟩

/-! ### A genuine cycle in the downloaded geography fragment -/

/-- *Region* (Q82794) is stated to be a subclass of *geographical area*
(Q3622002). -/
theorem region_sub_geographicalArea :
    Geography.kb.Sub (Qid.wd "Q82794") (Qid.wd "Q3622002") :=
  show (Qid.wd "Q82794", Qid.wd "Q3622002") ∈ Geography.kb.sub by decide

/-- And *geographical area* is stated to be a subclass of *region*. -/
theorem geographicalArea_sub_region :
    Geography.kb.Sub (Qid.wd "Q3622002") (Qid.wd "Q82794") :=
  show (Qid.wd "Q3622002", Qid.wd "Q82794") ∈ Geography.kb.sub by decide

/-- The two items are different items. -/
theorem region_ne_geographicalArea :
    (Qid.wd "Q82794") ≠ (Qid.wd "Q3622002") := by decide

/-- **The downloaded data contains a `subclass of` cycle**: two distinct items,
each a subclass of the other. -/
theorem geography_subclass_cycle :
    ∃ a b : Qid, a ≠ b ∧ Relation.ReflTransGen Geography.kb.Sub a b ∧
      Relation.ReflTransGen Geography.kb.Sub b a :=
  ⟨_, _, region_ne_geographicalArea,
    Relation.ReflTransGen.single region_sub_geographicalArea,
    Relation.ReflTransGen.single geographicalArea_sub_region⟩

/-- **Consequently no abstract Wikidata ontology has exactly these `subclass of`
statements**: the class hierarchy of an `Ontology` is antisymmetric, and this one
is not.  (This is why `Geography.kb_valid` reports `false`.) -/
theorem no_ontology_over_geography (O : Ontology Qid) (h : O.P279 = Geography.kb.Sub) : False := by
  obtain ⟨a, b, hab, hp, hq⟩ := geography_subclass_cycle
  exact hab (O.P279_antisymm (h ▸ hp) (h ▸ hq))

/-! ### Merging fragments adds knowledge -/

/-- In the merged corpus, *legal form* (Q10541491) is a subclass of *entity*
(Q35120) — a chain that runs through statements downloaded for two different
fragments. -/
theorem core_legalForm_sub_entity :
    Relation.ReflTransGen Core.kb.Sub (Qid.wd "Q10541491") (Qid.wd "Q35120") :=
  (KB.isSubclassOf_iff Core.kb_wellFormed _ _).1 (by native_decide)

/-- The Douglas Adams fragment alone does not derive it. -/
theorem adams_not_legalForm_sub_entity :
    ¬ Relation.ReflTransGen DouglasAdams.kb.Sub (Qid.wd "Q10541491") (Qid.wd "Q35120") := by
  intro h
  have : DouglasAdams.kb.isSubclassOf (Qid.wd "Q10541491") (Qid.wd "Q35120") = true :=
    (KB.isSubclassOf_iff DouglasAdams.kb_wellFormed _ _).2 h
  revert this
  decide

/-- **Importing more Wikidata facts strictly increases what is derivable.** -/
theorem core_knows_more_than_adams :
    Relation.ReflTransGen Core.kb.Sub (Qid.wd "Q10541491") (Qid.wd "Q35120") ∧
      ¬ Relation.ReflTransGen DouglasAdams.kb.Sub (Qid.wd "Q10541491") (Qid.wd "Q35120") :=
  ⟨core_legalForm_sub_entity, adams_not_legalForm_sub_entity⟩

/-! ### Cross-domain reasoning: biography meets biology -/

/-- In the merged corpus, Douglas Adams (Q42) is an instance of *organism*
(Q7239). -/
theorem core_adams_instanceOf_organism :
    ∃ d, Core.kb.Inst (Qid.wd "Q42") d ∧
      Relation.ReflTransGen Core.kb.Sub d (Qid.wd "Q7239") :=
  (KB.isInstanceOf_iff Core.kb_wellFormed _ _).1 (by native_decide)

/-- The first half of the chain comes from the biography download: *human* (Q5)
is a subclass of *animal* (Q729) there. -/
theorem adams_human_sub_animal :
    Relation.ReflTransGen DouglasAdams.kb.Sub (Qid.wd "Q5") (Qid.wd "Q729") :=
  DouglasAdams.sub_Q5_Q729

/-- The second half comes from the life-sciences download: *animal* (Q729) is a
subclass of *organism* (Q7239) there. -/
theorem life_animal_sub_organism :
    Relation.ReflTransGen LifeSciences.kb.Sub (Qid.wd "Q729") (Qid.wd "Q7239") :=
  LifeSciences.sub_Q729_Q7239

/-- The biography fragment alone does not know that Douglas Adams is an
organism: it never downloaded a statement mentioning Q7239. -/
theorem adams_not_instanceOf_organism :
    ¬ ∃ d, DouglasAdams.kb.Inst (Qid.wd "Q42") d ∧
      Relation.ReflTransGen DouglasAdams.kb.Sub d (Qid.wd "Q7239") := by
  intro h
  have : DouglasAdams.kb.isInstanceOf (Qid.wd "Q42") (Qid.wd "Q7239") = true :=
    (KB.isInstanceOf_iff DouglasAdams.kb_wellFormed _ _).2 h
  revert this
  decide

/-- Nor does the life-sciences fragment, which never downloaded Douglas Adams. -/
theorem life_not_instanceOf_organism :
    ¬ ∃ d, LifeSciences.kb.Inst (Qid.wd "Q42") d ∧
      Relation.ReflTransGen LifeSciences.kb.Sub d (Qid.wd "Q7239") := by
  intro h
  have : LifeSciences.kb.isInstanceOf (Qid.wd "Q42") (Qid.wd "Q7239") = true :=
    (KB.isInstanceOf_iff LifeSciences.kb_wellFormed _ _).2 h
  revert this
  native_decide

/-- **A fact that only the merged corpus knows.**  Douglas Adams is an organism
in the merged corpus, and in neither of the two downloads whose statements the
derivation combines. -/
theorem adams_organism_needs_both_downloads :
    (∃ d, Core.kb.Inst (Qid.wd "Q42") d ∧
        Relation.ReflTransGen Core.kb.Sub d (Qid.wd "Q7239")) ∧
      (¬ ∃ d, DouglasAdams.kb.Inst (Qid.wd "Q42") d ∧
        Relation.ReflTransGen DouglasAdams.kb.Sub d (Qid.wd "Q7239")) ∧
      (¬ ∃ d, LifeSciences.kb.Inst (Qid.wd "Q42") d ∧
        Relation.ReflTransGen LifeSciences.kb.Sub d (Qid.wd "Q7239")) :=
  ⟨core_adams_instanceOf_organism, adams_not_instanceOf_organism,
    life_not_instanceOf_organism⟩

/-! ### Facts from the newly imported domains -/

/-- Society: *university* (Q3918) is a subclass of *organization* (Q43229). -/
theorem core_university_sub_organization :
    Relation.ReflTransGen Core.kb.Sub (Qid.wd "Q3918") (Qid.wd "Q43229") :=
  (KB.isSubclassOf_iff Core.kb_wellFormed _ _).1 (by native_decide)

/-- Events: *war* (Q198) is a subclass of *occurrence* (Q1190554). -/
theorem core_war_sub_occurrence :
    Relation.ReflTransGen Core.kb.Sub (Qid.wd "Q198") (Qid.wd "Q1190554") :=
  (KB.isSubclassOf_iff Core.kb_wellFormed _ _).1 (by native_decide)

/-- Life sciences: *animal* (Q729) is a subclass of *organism* (Q7239) in the
merged corpus too. -/
theorem core_animal_sub_organism :
    Relation.ReflTransGen Core.kb.Sub (Qid.wd "Q729") (Qid.wd "Q7239") :=
  (KB.isSubclassOf_iff Core.kb_wellFormed _ _).1 (by native_decide)

/-! ### Querying the downloaded fragments

The certified evaluator of `RequestProject.Queries`, run against real data. -/

/-- "Which items of the fragment are humans?" -/
def qHumans : Query.BGP := [.inst (.var "x") (.item (Qid.wd "Q5"))]

/-- Douglas Adams, and nobody else — computed by the table-based evaluator the
command line tool uses. -/
theorem answers_qHumans :
    Query.answersT DouglasAdams.kb qHumans ["x"] = [[Qid.wd "Q42"]] := by decide

/-- The same, as the single binding the evaluator of the theorems returns. -/
theorem eval_qHumans : Query.eval DouglasAdams.kb qHumans = [[("x", Qid.wd "Q42")]] := by
  rw [← Query.evalT_eq_eval]; decide

/-- **Completeness in action**: this is a fact about the downloaded fragment, not just
about the evaluator.  Any item of the fragment that the biography data makes an
instance of *human* is Douglas Adams. -/
theorem unique_human_of_adamsFragment (g : String → Qid) (hg : g "x" ∈ DouglasAdams.kb.items)
    (hsat : Query.Sat DouglasAdams.kb DouglasAdams.kb_valid g qHumans) : g "x" = Qid.wd "Q42" := by
  have hitems : ∀ n ∈ Query.bgpVars qHumans, g n ∈ DouglasAdams.kb.items := by
    intro n hn
    have : n = "x" := by
      simpa [qHumans, Query.bgpVars, Query.Atom.vars, Query.Tm.vars] using hn
    subst this; exact hg
  obtain ⟨e, he, hag, -⟩ :=
    Query.eval_complete DouglasAdams.kb DouglasAdams.kb_valid qHumans g hsat hitems
  rw [eval_qHumans] at he
  have : e = [("x", Qid.wd "Q42")] := by simpa using he
  subst this
  exact hag "x" (Qid.wd "Q42") (by simp)

/-- "Which items are instances of something and are themselves classes?" — the items of
the fragment that sit one level below a metaclass, with the metaclass. -/
def qClassInstances : Query.BGP :=
  [.inst (.var "x") (.var "c"), .isClass (.var "x")]

/-- The downloaded biography fragment answers it with ten pairs … -/
theorem answers_qClassInstances_length :
    (Query.answersT DouglasAdams.kb qClassInstances ["x", "c"]).length = 10 := by decide

/-- … among them `human` (Q5) and the metaclass *organisms known by a particular common
name* (Q55983715), the pair the hand-built fragment of `RequestProject.Examples` was
modelled on. -/
theorem human_metaclass_mem_answers :
    [Qid.wd "Q5", Qid.wd "Q55983715"] ∈
      Query.answersT DouglasAdams.kb qClassInstances ["x", "c"] := by decide

/-! ### The cycle survives the merge -/

/-- The merged corpus still states `region ⊑ geographical area` … -/
theorem core_region_sub_geographicalArea :
    Core.kb.Sub (Qid.wd "Q82794") (Qid.wd "Q3622002") :=
  show (Qid.wd "Q82794", Qid.wd "Q3622002") ∈ Core.kb.sub by native_decide

/-- … and the converse. -/
theorem core_geographicalArea_sub_region :
    Core.kb.Sub (Qid.wd "Q3622002") (Qid.wd "Q82794") :=
  show (Qid.wd "Q3622002", Qid.wd "Q82794") ∈ Core.kb.sub by native_decide

/-- **No abstract Wikidata ontology has exactly the merged corpus' `subclass of`
statements** — deduplicating and merging eleven downloads does not repair the
cycle, which is why `Core.kb_valid` reports `false`. -/
theorem no_ontology_over_core (O : Ontology Qid) (h : O.P279 = Core.kb.Sub) : False :=
  region_ne_geographicalArea
    (O.P279_antisymm
      (h ▸ Relation.ReflTransGen.single core_region_sub_geographicalArea)
      (h ▸ Relation.ReflTransGen.single core_geographicalArea_sub_region))

end Compiled
end Wikidata

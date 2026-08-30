import Mathlib
import RequestProject.Core
import RequestProject.Engine
import RequestProject.Merge
import RequestProject.SelfDescription
import RequestProject.Examples
import RequestProject.Properties
import RequestProject.PropertyEngine
import RequestProject.PropertyConstraints
import RequestProject.UpperOntology
import RequestProject.Taxonomy
import RequestProject.Ranks
import RequestProject.DisjointUnion
import RequestProject.Alignment
import RequestProject.Semantics
import RequestProject.StatementConstraints
import RequestProject.ItemMerge
import RequestProject.ClassAlgebra
import RequestProject.Temporal
import RequestProject.Paths
import RequestProject.Terms
import RequestProject.Concepts
import RequestProject.Quantities
import RequestProject.Provenance
import RequestProject.Sitelinks
import RequestProject.TimeValues
import RequestProject.Subsumption
import RequestProject.Matching
import RequestProject.ExternalIds
import RequestProject.Snaks
import RequestProject.TypeProperties
import RequestProject.Stratification
import RequestProject.Lexemes
import RequestProject.Schemas
import RequestProject.Rdf
import RequestProject.Mereology
import RequestProject.Kinship
import RequestProject.KinshipDiagnostics
import RequestProject.Parenting
import RequestProject.ParentingDiagnostics
import RequestProject.ParentingExamples
import RequestProject.Redundancy
import RequestProject.Diagnostics

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Overview

A formalisation of the Wikidata ontology layer (`Wikidata:WikiProject Ontology`):

* `RequestProject.Core` — the abstract model: items, `instance of` (P31),
  `subclass of` (P279), metaclass levels, disjointness, and the theorems of the
  ontology layer (the class hierarchy is a partial order, inheritance of
  instances, acyclicity of `instance of`, metaclasses live at level ≥ 2,
  disjointness is inherited by subclasses, ...).
* `RequestProject.Reachability` — a certified executable transitive-closure
  engine.
* `RequestProject.Engine` — `Wikidata.KB`, a finite executable ontology, with
  computable queries (`isSubclassOf`, `isInstanceOf`, `classesOf`,
  `instancesOf`, ...) and a validator, proved to agree with the abstract model.
* `RequestProject.Merge` — importing other ontologies and the entailment
  preorder between ontologies.
* `RequestProject.SelfDescription` — every knowledge base carries a valid
  meta-description of itself (and hence of other knowledge bases, at any depth).
* `RequestProject.Properties` — the property layer: statements, `subproperty of`
  (P1647), transitive, symmetric and inverse properties, and the type
  (Q21503250) and value-type (Q21510865) constraints, with the derived statement
  relation and its minimality.
* `RequestProject.PropertyEngine` — `Wikidata.PKB`, the executable property layer
  on top of a knowledge base, with certified queries (`isSubPropertyOf`,
  `supportsB`, `relatedB`, `valuesOf`, ...) and a validator covering the property
  constraints.
* `RequestProject.PropertyConstraints` — the single-value (Q19474404),
  distinct-values (Q21502410) and irreflexive (Q21510863) constraints, with the
  theorem that an irreflexive transitive property is a strict order, and
  certified executable checks for all three.
* `RequestProject.Examples` — a worked fragment of Wikidata and the checks run
  on it.
* `RequestProject.UpperOntology` — a larger fragment: the upper class hierarchy
  and metaclass tower, the meronomy layer (`part of` P361 and `located in the
  administrative territorial entity` P131) and the social layer (`spouse` P26,
  `relative` P1038, `different from` P1889, `has part(s)` P527), plus the proof
  that a variable-order `class` cannot exist in a strictly stratified ontology.
* `RequestProject.Taxonomy` — a second domain: taxa ordered by `parent taxon`
  (P171) with their `taxon rank` (P105), where the ancestry relation is shown to
  be a strict order and the rank is shown not to be inherited.
* `RequestProject.Alignment` — `equivalent class` (P1709): sound alignments with
  external ontologies, transport of the derived relations along them, composition
  of alignments, import of disjointness, and a certified executable checker for a
  finite table of links.
* `RequestProject.DisjointUnion` — `disjoint union of` (P2738): the abstract
  notion of a class partitioned by subclasses, its consequences (reasoning by
  cases, composition of partitions) and a certified executable checker.
* `RequestProject.Ranks` — statement ranks (`preferred`, `normal`, `deprecated`)
  and qualifiers, the *truthy* fragment they determine, and the certified query
  `truthyValues`; the truthy item-valued statements feed the property engine.
* `RequestProject.Semantics` — the extensional semantics: models of an ontology,
  soundness of the derivation rules, completeness (semantic consequence is
  exactly derivability, via a canonical model), consistency of the disjointness
  layer, pullback of models along alignments, and the matching
  soundness/completeness result for the statement relation of the property
  layer.
* `RequestProject.StatementConstraints` — the statement-level constraints:
  item-requires-statement (Q21503247), value-requires-statement (Q21510864),
  conflicts-with (Q21502838), one-of (Q21510859), none-of (Q52558054) and the
  inverse constraint (Q21510855), together with `properties for this type`
  (P1963), each with a certified executable checker.
* `RequestProject.ItemMerge` — merging items (redirects): renaming identifiers is
  an alignment, so no derived fact is lost, while validity may be destroyed — a
  merge can create a cycle, a level clash or a disjointness violation.
* `RequestProject.ClassAlgebra` — `union of` (P2737) and class intersections: the
  abstract notions, their consequences, certified executable checkers, and a
  fragment where `artist` is the union — but not the disjoint union — of `painter`
  and `sculptor`.
* `RequestProject.Temporal` — time-qualified statements: the qualifiers
  `start time` (P580) and `end time` (P582), validity intervals, and the snapshot
  of a knowledge base at a point in time; every snapshot of a valid base is a
  valid ontology and derives nothing that the whole base does not.
* `RequestProject.Paths` — property paths, the query language: path expressions
  (empty path, atom, inverse, composition, alternation, closure), their
  semantics, the algebra they satisfy, and a certified executable evaluator; the
  Wikidata idiom `wdt:P31/wdt:P279*` is proved to compute exactly the derived
  `instance of` relation.
* `RequestProject.Terms` — the term layer: labels, descriptions and aliases per
  language, the label/description uniqueness constraint (whose checker is proved
  to be exactly the injectivity it expresses), the alias constraint, and search
  by label, term or label-and-description.
* `RequestProject.Concepts` — the extensional view: the Galois connection between
  sets of items and sets of classes, the closure operator it induces, the
  complete lattice of extents, the fact that inheritance is inclusion of
  extents, and a valid knowledge base with two coextensive but unrelated classes.
* `RequestProject.Quantities` — the quantity datatype: amounts with uncertainty
  intervals and units, `conversion to SI unit` (P2370), comparison of quantities
  across units, and the invariance of consistency of two measurements under
  conversion.
* `RequestProject.Provenance` — references and verifiability: `stated in` (P248),
  `reference URL` (P854) and `imported from Wikimedia project` (P143); the
  sourced and the reliable fragment of a knowledge base are valid ontologies
  and derive nothing the whole base does not, and every derived fact rests on a
  finite chain of asserted statements.
* `RequestProject.Sitelinks` — the sitelink layer: an item has at most one page
  per site and a page is linked from at most one item, which together make the
  sitelink table a partial bijection between items and pages of a site; merging
  two items is legitimate exactly when their sitelinks do not clash.
* `RequestProject.TimeValues` — the time datatype: dates recorded to a stated
  precision in a stated calendar model, the coarsening of a date, the set of
  instants a time value denotes, and compatibility of two time values (which is
  exactly overlap of their denotations, and is not transitive).
* `RequestProject.Matching` — the shape common to several layers of the data
  model: a table of ⟨subject, key, value⟩ triples which is functional and
  injective is a partial bijection, and two such tables sharing a key induce a
  matching which is again symmetric, injective and transitive.
* `RequestProject.ExternalIds` — external identifiers (`VIAF ID` P214, `GND ID`
  P227, ...) with their `formatter URL` (P1630): the single-value and
  distinct-values constraints make an identifier property identify the item,
  duplicate items are detected as constraint violations, and two databases
  sharing an identifier property are matched by authority control.
* `RequestProject.Snaks` — the snak types `somevalue` and `novalue`: a model
  theory for them, the decidable consistency criterion (a base has a model
  exactly when no `novalue` snak clashes with another snak for the same item and
  property), and the characterisation of what a consistent base entails.
* `RequestProject.TypeProperties` — `properties for this type` (P1963) as a data
  layer: the properties a class expects of its instances, inherited downwards
  along `subclass of`, the computable `missing properties` report and
  completeness check, the proof that adding statements never destroys
  completeness while adding `instance of` statements adds obligations, and the
  bridge to the abstract soft constraint `Wikidata.PropertiesForType`.
* `RequestProject.Stratification` — the shape of the class hierarchy: the height
  of an item (its number of superclasses), which strictly drops at every proper
  subclass step and so is a linear extension of the subclass order; the
  well-foundedness of the strict superclass relation (induction on classes is
  legitimate); the bound on the length of ascending chains; the executable
  topological sort of the items, proved to place every class before its proper
  superclasses; and the splitting of the items into strata by height, every P279
  edge leading to a strictly lower stratum.
* `RequestProject.Lexemes` — the lexicographical layer: lexemes with their forms
  (addressed by grammatical features) and senses (linked to the ontology by
  `item for this sense`, P5137); a lexeme *means* a class when one of its senses
  denotes an instance of it, translation through a shared denotation preserves
  meaning, sharing a sense is *not* transitive (polysemy), and a lexeme with
  denotations in two disjoint classes provably has at least two senses.
* `RequestProject.Schemas` — entity schemas: cardinality shapes over the property
  layer (minimum and maximum number of statements per property, and closed shapes
  forbidding anything else), with the decidable conformance check; conformance to
  a conjunction of open shapes is conformance to both, shapes without upper
  bounds are monotone under further statements, and the `properties for this
  type` completeness check is exactly conformance to the shape asking for one
  statement per expected property.
* `RequestProject.Rdf` — the RDF rendering: the *truthy* layer (one `wdt:` triple
  per truthy statement) and the *full* layer (every statement reified at its own
  statement node, carrying value, rank and qualifiers).  The reified layer is
  proved lossless — each statement can be read back off the graph, so the export
  is injective — the direct triples are exactly the values a default query
  returns, no deprecated statement ever produces one, and the RDFS-style
  entailment rules on the exported ontology graph derive exactly the `subclass
  of` and `instance of` facts the engine computes.
* `RequestProject.Subsumption` — least common subsumers: uniqueness, their
  behaviour under inheritance, the fact that items at different metaclass levels
  have no common superclass, a certified computation of the candidates, and a
  fragment with multiple inheritance where no least common subsumer exists.
* `RequestProject.Cli.*` — the `wikidata` command line tool (`lake build
  wikidata`): downloading entities from the Wikidata API, a lossless text format
  for local knowledge bases, the construction of the facts a base implies but
  does not state, and checked explanations.  Each command is backed by a theorem
  (faithful import, empty report ⟺ valid, conservative saturation, sound
  explanations, lossless round trip through disk); see `docs/CLI.md`.
-/

section Demo
open Wikidata Wikidata.Examples

/-- info: Bool.true -/
#guard_msgs in
#eval wdCore.valid

/-- info: [Wikidata.Qid.wd "Q5", Wikidata.Qid.wd "Q215627", Wikidata.Qid.wd "Q35120"] -/
#guard_msgs in
#eval wdCore.classesOf (Q "Q42")

/-- info: Bool.true -/
#guard_msgs in
#eval (wdCore.selfDescription.selfDescription).valid

end Demo

section PropertyDemo
open Wikidata Wikidata.Upper

/-- info: Bool.true -/
#guard_msgs in
#eval wdParts.pvalid

/-- info: [Wikidata.Qid.wd "Q21", Wikidata.Qid.wd "Q145", Wikidata.Qid.wd "Q46"] -/
#guard_msgs in
#eval wdParts.valuesOf (P "P361") (Q "Q84")

/-- info: "London" -/
#guard_msgs in
#eval labelOf (Q "Q84")

/-- info: Bool.true -/
#guard_msgs in
#eval wdSocial.relatedB (P "P527") (Q "Q21") (Q "Q84")

end PropertyDemo

section TaxonomyDemo
open Wikidata Wikidata.Taxonomy

/-- info: Bool.true -/
#guard_msgs in
#eval taxonPKB.pvalid

/-- info: ["Panthera", "Felidae", "Carnivora", "Mammalia", "Chordata", "Animalia"] -/
#guard_msgs in
#eval (taxonPKB.valuesOf (P "P171") (Q "Q140")).map labelOf

end TaxonomyDemo

section RankDemo
open Wikidata Wikidata.RankExample

/-- info: [Wikidata.Value.quantity 3644826] -/
#guard_msgs in
#eval Claim.truthyValues berlin (Q "Q64") (P "P1082")

/-- info: [Wikidata.Value.quantity 3644826, Wikidata.Value.quantity 3292365] -/
#guard_msgs in
#eval Claim.truthyValues berlinNoPreferred (Q "Q64") (P "P1082")

/--
info: [(Wikidata.Pid.wd "P17", Wikidata.Qid.wd "Q64", Wikidata.Qid.wd "Q183"),
 (Wikidata.Pid.wd "P1376", Wikidata.Qid.wd "Q64", Wikidata.Qid.wd "Q183")]
-/
#guard_msgs in
#eval Claim.truthyItemStmts berlin

end RankDemo

section DisjointUnionDemo
open Wikidata Wikidata.DisjointUnionExample

/-- info: Bool.true -/
#guard_msgs in
#eval animalKB.dunOk (Q "Q729") [Q "Q25241", Q "Q1082709"]

/-- info: Bool.false -/
#guard_msgs in
#eval animalKB.dunOk (Q "Q729") [Q "Q25241"]

/-- info: ["lion"] -/
#guard_msgs in
#eval (animalKB.instancesOf (Q "Q25241")).map labelOf

end DisjointUnionDemo

section AlignmentDemo
open Wikidata Wikidata.AlignmentExample

/-- info: Bool.true -/
#guard_msgs in
#eval wdFragment.alignOk extOntology links

/-- info: [Wikidata.Qid.wd "E-mammal", Wikidata.Qid.wd "E-animal", Wikidata.Qid.wd "E-thing"] -/
#guard_msgs in
#eval extOntology.classesOf (Q "E-lion")

end AlignmentDemo

section StatementConstraintDemo
open Wikidata Wikidata.StatementConstraintExample

/-- info: Bool.true -/
#guard_msgs in
#eval bio.itemRequiresB (P "P19") (P "P27")

/-- info: Bool.false -/
#guard_msgs in
#eval bio.conflictsWithB (P "P19") (P "P27")

/-- info: [Wikidata.Qid.wd "Q145"] -/
#guard_msgs in
#eval bio.valuesOf (P "P27") (Q "Q42")

end StatementConstraintDemo

section MergeDemo
open Wikidata Wikidata.MergeExample

/-- info: Bool.true -/
#guard_msgs in
#eval mergedKB.valid

/-- info: Bool.true -/
#guard_msgs in
#eval mergedKB.isInstanceOf (Q "Q42") (Q "Q215627")

/-- info: Bool.false -/
#guard_msgs in
#eval (disjKB.mergeItems [(Q "Q11424-x", Q "Q42")]).valid

end MergeDemo

section ClassAlgebraDemo
open Wikidata Wikidata.ClassAlgebraExample

/-- info: Bool.true -/
#guard_msgs in
#eval artistKB.unionOk (Q "Q483501") [Q "Q1028181", Q "Q1281618"]

/-- info: Bool.false -/
#guard_msgs in
#eval artistKB.dunOk (Q "Q483501") [Q "Q1028181", Q "Q1281618"]

/-- info: ["Michelangelo", "Leonardo da Vinci"] -/
#guard_msgs in
#eval (artistKB.instancesOf (Q "Q483501")).map labelOf

end ClassAlgebraDemo

section TemporalDemo
open Wikidata Wikidata.TemporalExample

/-- info: Bool.true -/
#guard_msgs in
#eval (frag.snapshot 1980).isInstanceOf gdr state

/-- info: Bool.false -/
#guard_msgs in
#eval (frag.snapshot 2000).isInstanceOf gdr state

/-- info: [Wikidata.Qid.wd "Q3024240"] -/
#guard_msgs in
#eval fragFixed.instAt 2000 gdr

end TemporalDemo

section PathDemo
open Wikidata Wikidata.PathExample

#guard PathExpr.evalF kbq.allF kbq.linkStep (.seq (.atom .p31) (.star (.atom .p279)))
    (Qid.wd "Q42") = {Qid.wd "Q5", Qid.wd "Q215627", Qid.wd "Q35120"}

#guard PathExpr.evalF kbq.allF kbq.linkStep (.inv (.atom .p279)) (Qid.wd "Q35120") =
    {Qid.wd "Q215627"}

end PathDemo

section TermDemo
open Wikidata Wikidata.TermExample

/-- info: [Wikidata.Qid.wd "Q308", Wikidata.Qid.wd "Q1084"] -/
#guard_msgs in
#eval mercury.byLabel "en" "Mercury"

/-- info: [Wikidata.Qid.wd "Q1084"] -/
#guard_msgs in
#eval mercury.byLabelDesc "en" "Mercury" "Roman god of commerce"

/-- info: Bool.false -/
#guard_msgs in
#eval mercuryBad.uniqueOk "en"

end TermDemo

section QuantityDemo
open Wikidata Wikidata.QuantityExample

/-- info: 1000 -/
#guard_msgs in
#eval lengths.siValue oneKm

/-- info: 1000 -/
#guard_msgs in
#eval lengths.siValue thousandM

/-- info: Bool.true -/
#guard_msgs in
#eval roughKm.wfB

end QuantityDemo

section ProvenanceDemo
open Wikidata Wikidata.ProvenanceExample

/-- info: Bool.true -/
#guard_msgs in
#eval frag.full.valid

/-- info: Bool.true -/
#guard_msgs in
#eval frag.sourced.valid

/-- info: Bool.false -/
#guard_msgs in
#eval frag.verifiableSubclass omnivore person

/-- info: [(Wikidata.Qid.wd "Q164509", Wikidata.Qid.wd "Q215627")] -/
#guard_msgs in
#eval frag.unsourcedStatements

end ProvenanceDemo

section SitelinkDemo
open Wikidata Wikidata.SitelinkExample

/-- info: Option.some "Douglas Adams" -/
#guard_msgs in
#eval frag.pageOf adams "enwiki"

/-- info: some (Wikidata.Qid.wd "Q42") -/
#guard_msgs in
#eval frag.itemOf "enwiki" "Douglas Adams"

/-- info: Bool.false -/
#guard_msgs in
#eval fragBad.pageInjectiveB

end SitelinkDemo

section TimeValueDemo
open Wikidata Wikidata.TimeExample

/-- info: Bool.true -/
#guard_msgs in
#eval TimeValue.compatibleB may1990 y1990

/-- info: Bool.false -/
#guard_msgs in
#eval TimeValue.compatibleB may1990 jul1990

/-- info: Bool.true -/
#guard_msgs in
#eval c20.memB { year := 1905, month := 3, day := 7 }

end TimeValueDemo

section SubsumptionDemo
open Wikidata Wikidata.SubsumptionExample

/-- info: [Wikidata.Qid.wd "Q729", Wikidata.Qid.wd "Q5113", Wikidata.Qid.wd "Q2374463"] -/
#guard_msgs in
#eval frag.commonSupers duck swan

/-- info: [] -/
#guard_msgs in
#eval frag.lcsCandidates duck swan

/-- info: some (Wikidata.Qid.wd "Q5113") -/
#guard_msgs in
#eval frag.lcs? duck bird

end SubsumptionDemo

section ExternalIdDemo
open Wikidata Wikidata.ExternalIdExample

/-- info: Option.some "https://d-nb.info/gnd/119033364" -/
#guard_msgs in
#eval wd.resolve adams gnd

/-- info: some (Wikidata.Qid.wd "DNB-1") -/
#guard_msgs in
#eval wd.matchOn dnb gnd adams

/-- info: [(Wikidata.Qid.wd "Q42", Wikidata.Qid.wd "Q999999"), (Wikidata.Qid.wd "Q999999", Wikidata.Qid.wd "Q42")] -/
#guard_msgs in
#eval wdDup.duplicatesOn viaf

end ExternalIdDemo

section SnakDemo
open Wikidata Wikidata.SnakExample

/-- info: Bool.true -/
#guard_msgs in
#eval Wikidata.SnakBase.clashFreeB frag

/-- info: Bool.false -/
#guard_msgs in
#eval Wikidata.SnakBase.clashFreeB fragBad

/-- info: [] -/
#guard_msgs in
#eval Wikidata.SnakBase.valuesOf frag elizabeth child

/-- info: [Wikidata.Value.item (Wikidata.Qid.wd "Q15873243")] -/
#guard_msgs in
#eval Wikidata.SnakBase.valuesOf frag adams spouse

end SnakDemo

section TypePropertyDemo
open Wikidata Wikidata.TypeProfileExample

/-- info: [Wikidata.Pid.wd "P569", Wikidata.Pid.wd "P27"] -/
#guard_msgs in
#eval profile.expectedOf (Q "Q42")

/-- info: [Wikidata.Pid.wd "P27"] -/
#guard_msgs in
#eval profile.missingOf (Q "Q42")

/-- info: Bool.true -/
#guard_msgs in
#eval (profile.withStmts [(P "P27", Q "Q42", Q "Q145")]).completeB

end TypePropertyDemo

section StratificationDemo
open Wikidata Wikidata.StratumExample

/-- info: 4 -/
#guard_msgs in
#eval tower.height (Q "Q5")

/-- info: [Wikidata.Qid.wd "Q35120"] -/
#guard_msgs in
#eval tower.stratum 1

/-- info: [Wikidata.Qid.wd "Q215627", Wikidata.Qid.wd "Q3305213"] -/
#guard_msgs in
#eval tower.stratum 3

/--
info: [Wikidata.Qid.wd "Q5",
 Wikidata.Qid.wd "Q215627",
 Wikidata.Qid.wd "Q3305213",
 Wikidata.Qid.wd "Q488383",
 Wikidata.Qid.wd "Q35120"]
-/
#guard_msgs in
#eval tower.topoSort

end StratificationDemo

section LexemeDemo
open Wikidata Wikidata.LexemeExample

/-- info: Bool.true -/
#guard_msgs in
#eval lexicon.lexValid

/-- info: Option.some "banks" -/
#guard_msgs in
#eval (bankEn.formByFeatures [Q "Q146786"]).map Form.representation

/-- info: ["Bank"] -/
#guard_msgs in
#eval (lexicon.translationsOf (Q "Q22687") (Q "Q188")).map Lexeme.lemmaForm

/-- info: Bool.true -/
#guard_msgs in
#eval lexicon.meansB bankEn (Q "Q271669")

end LexemeDemo

section SchemaDemo
open Wikidata Wikidata.SchemaExample

/-- info: Bool.true -/
#guard_msgs in
#eval layer.conformsB humanShape (Q "Q42")

/-- info: Bool.false -/
#guard_msgs in
#eval layer.conformsB humanShape (Q "Q7")

/-- info: 2 -/
#guard_msgs in
#eval layer.countOf (P "P569") (Q "Q7")

end SchemaDemo

section RdfDemo
open Wikidata Wikidata.Rdf Wikidata.RankExample

/-- info: 18 -/
#guard_msgs in
#eval (fullGraph berlin).length

/-- info: 3 -/
#guard_msgs in
#eval (truthyGraph berlin).length

/-- info: Bool.true -/
#guard_msgs in
#eval (recoverAt (fullGraph berlin) 2) == some berlin[2]!

end RdfDemo

section MereologyDemo
open Wikidata

/-- info: [Wikidata.Qid.wd "w1", Wikidata.Qid.wd "s1", Wikidata.Qid.wd "r1"] -/
#guard_msgs in
#eval bikeMKB.properPartsOfL (Qid.wd "b1")

/-- info: [Wikidata.Qid.wd "b1", Wikidata.Qid.wd "w1"] -/
#guard_msgs in
#eval bikeMKB.wholesOfL (Qid.wd "r1")

/-- info: Bool.true -/
#guard_msgs in
#eval bikeMKB.mValid

/-- info: [] -/
#guard_msgs in
#eval bikeMKB.missingPartClassesL (Qid.wd "b1")

/-- info: [Wikidata.Qid.wd "Q446"] -/
#guard_msgs in
#eval ({ bikeMKB with parts := [(Qid.wd "s1", Qid.wd "b1")] } : MKB).missingPartClassesL
  (Qid.wd "b1")

end MereologyDemo

section RedundancyDemo
open Wikidata Wikidata.KB

/-- info: [(Wikidata.Qid.wd "Q5", Wikidata.Qid.wd "Q35120")] -/
#guard_msgs in
#eval redundantKB.redundantSubL

/-- info: [] -/
#guard_msgs in
#eval (redundantKB.dropSub (Qid.wd "Q5", Qid.wd "Q35120")).redundantSubL

/-- info: Bool.true -/
#guard_msgs in
#eval (redundantKB.dropSub (Qid.wd "Q5", Qid.wd "Q35120")).valid

end RedundancyDemo

section DiagnosticsDemo
open Wikidata Wikidata.KB

/-- info: 5 -/
#guard_msgs in
#eval brokenKB.errors.length

/-- info: Bool.false -/
#guard_msgs in
#eval brokenKB.clean

/-- info: Bool.true -/
#guard_msgs in
#eval (redundantKB.dropSub (Qid.wd "Q5", Qid.wd "Q35120")).clean

end DiagnosticsDemo

section KinshipDemo
open Wikidata Wikidata.FKB

/-- info: Bool.true -/
#guard_msgs in
#eval family.fValid

/-- info: [Wikidata.Qid.wd "Q1", Wikidata.Qid.wd "Q2", Wikidata.Qid.wd "Q3", Wikidata.Qid.wd "Q4"] -/
#guard_msgs in
#eval family.ancestorsL (Qid.wd "Q1")

/-- info: [Wikidata.Qid.wd "Q1"] -/
#guard_msgs in
#eval family.childrenL (Qid.wd "Q2")

/-- info: some (Wikidata.Qid.wd "Q3") -/
#guard_msgs in
#eval family.motherOf? (Qid.wd "Q2")

/-- info: Bool.false -/
#guard_msgs in
#eval family.relatedB (Qid.wd "Q2") (Qid.wd "Q4")

/-- info: Bool.false -/
#guard_msgs in
#eval cyclicFamily.fValid

/-- info: [] -/
#guard_msgs in
#eval family.fErrors

/-- info: 2 -/
#guard_msgs in
#eval cyclicFamily.fErrors.length

end KinshipDemo

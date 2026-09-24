import RequestProject.Grounding
import RequestProject.Main
import RequestProject.Taxa
import RequestProject.Series
import RequestProject.Queries
import RequestProject.Normalize
import RequestProject.Reachability
import RequestProject.MathResonance
import RequestProject.GrothendieckSite
import RequestProject.OntologyTopology
import RequestProject.PullbackComparison
import RequestProject.CubicalTypes
import RequestProject.OntologyGroups
import RequestProject.OntologyFields

/-!
# The vocabulary of the formalisation, grounded in Wikidata

`RequestProject.Generated.Glossary` grounds every Wikidata **identifier** this
development mentions.  This file grounds the other half: the **notions** the
development defines.  Each entry of `Wikidata.vocabulary` names

* a declaration of this library — written as a name literal, so Lean itself
  rejects an entry that names something which does not exist;
* the Wikidata entity that notion formalises, and
* the English label Wikidata gives that entity.

Some of those entities are Wikidata properties (`Wikidata.MKB.isPartOfB` is
`part of`, P361), some are items of Wikidata's own data model (`Wikidata.Rank` is
`Wikidata statement rank`, Q21044622), and some are the mathematical notions the
formalisation reasons with (`Wikidata.Ontology.subclassPartialOrder` is
`partial order`, Q1069998).

That the entities exist, and that their labels are what the table claims, is
checked against the downloaded glossary in `RequestProject.Grounded`
(`Wikidata.Grounded.vocabulary_checks`).
-/

namespace Wikidata

/-- Every notion of this development, with the Wikidata entity that grounds it.

The order follows the layers of the formalisation: the ontology core, the
knowledge-base engine, the extensional view, the property layer, and then the
layers built on top of it. -/
def vocabulary : List GroundedTerm :=
  [ -- ## The ontology core (`RequestProject.Core`)
    ⟨``Wikidata.Ontology, "Q324254", "ontology"⟩,
    ⟨``Wikidata.Ontology.P279, "P279", "subclass of"⟩,
    ⟨``Wikidata.Ontology.P31, "P31", "instance of"⟩,
    ⟨``Wikidata.Ontology.SubclassOf, "Q93447297", "reflexive transitive closure"⟩,
    ⟨``Wikidata.Ontology.subclassOf_trans, "Q64861", "transitive relation"⟩,
    ⟨``Wikidata.Ontology.subclassOf_antisymm, "Q583760", "antisymmetric relation"⟩,
    ⟨``Wikidata.Ontology.subclassPartialOrder, "Q1069998", "partial order"⟩,
    ⟨``Wikidata.Ontology.IsClass, "Q16889133", "class"⟩,
    ⟨``Wikidata.Ontology.IsIndividual, "Q23958946", "individual entity"⟩,
    ⟨``Wikidata.Ontology.IsMetaclass, "Q19478619", "metaclass"⟩,
    -- ## The executable engine (`RequestProject.Engine`, `Reachability`, …)
    ⟨``Wikidata.KB, "Q593744", "knowledge base"⟩,
    ⟨``Wikidata.Qid, "Q43649390", "Wikidata Q identifier"⟩,
    ⟨``Wikidata.Qid.wd, "Q16222597", "Wikidata item"⟩,
    ⟨``Wikidata.Pid, "Q18616576", "Wikidata property"⟩,
    ⟨``Wikidata.KB.superclasses, "Q1501387", "transitive closure"⟩,
    ⟨``Wikidata.KB.acyclic, "Q1195339", "directed acyclic graph"⟩,
    ⟨``Reach.reach, "Q1361526", "reachability"⟩,
    ⟨``Wikidata.KB.topoSort, "Q753127", "topological sorting"⟩,
    ⟨``Wikidata.KB.stratum, "Q188619", "hierarchy"⟩,
    ⟨``Wikidata.KB.merge, "Q185359", "union"⟩,
    ⟨``Wikidata.KB.normalize, "Q1182260", "data deduplication"⟩,
    ⟨``Wikidata.KB.redundantSubL, "Q3088151", "transitive reduction"⟩,
    ⟨``Wikidata.KB.selfDescription, "Q1129622", "self-reference"⟩,
    ⟨``Wikidata.Issue, "Q3306762", "data validation"⟩,
    -- ## The extensional view (`RequestProject.Concepts`)
    ⟨``Wikidata.Ontology.extension, "Q1189753", "denotation"⟩,
    ⟨``Wikidata.Ontology.commonInstances_subset_iff, "Q1491747", "Galois connection"⟩,
    ⟨``Wikidata.Ontology.extentClosure, "Q10564851", "closure operator"⟩,
    ⟨``Wikidata.Ontology.IsExtent, "Q1437394", "formal concept analysis"⟩,
    ⟨``Wikidata.Ontology.Extent.completeLattice, "Q2362924", "complete lattice"⟩,
    ⟨``Wikidata.Ontology.commonClasses_antitone, "Q194404", "monotonic function"⟩,
    -- ## Models and entailment (`RequestProject.Semantics`, `Snaks`)
    ⟨``Wikidata.Ontology.Model, "Q467606", "model theory"⟩,
    ⟨``Wikidata.SnakBase.Entails, "Q374182", "logical consequence"⟩,
    ⟨``Wikidata.SnakStmt, "Q44292881", "Wikidata statement"⟩,
    ⟨``Wikidata.Snak.someValue, "Q19798648", "concept of unknown value in Wikibase"⟩,
    ⟨``Wikidata.Snak.noValue, "Q19798647", "concept of no-value in Wikibase"⟩,
    -- ## The property layer (`RequestProject.Properties`, `PropertyConstraints`)
    ⟨``Wikidata.PropertyLayer.Stmt, "Q130901", "binary relation"⟩,
    ⟨``Wikidata.PropertyLayer.SubProp, "P1647", "subproperty of"⟩,
    ⟨``Wikidata.PropertyLayer.InverseOf, "P1696", "inverse property"⟩,
    ⟨``Wikidata.PropertyLayer.IsTransitive, "Q18647515", "transitive Wikidata property"⟩,
    ⟨``Wikidata.PropertyLayer.IsSymmetric, "Q18647518", "symmetric property"⟩,
    ⟨``Wikidata.PropertyLayer.Constraints.SubjectTypeOk, "Q21503250", "subject type constraint"⟩,
    ⟨``Wikidata.PropertyLayer.Constraints.ValueTypeOk, "Q21510865", "value-type constraint"⟩,
    -- ## Mereology (`RequestProject.Mereology`)
    ⟨``Wikidata.MKB, "Q1194916", "mereology"⟩,
    ⟨``Wikidata.MKB.isPartOfB, "P361", "part of"⟩,
    ⟨``Wikidata.MKB.properPartsOfL, "P527", "has part(s)"⟩,
    ⟨``Wikidata.MKB.partClasses, "P2670", "has part(s) of the class"⟩,
    -- ## Kinship (`RequestProject.Kinship`)
    ⟨``Wikidata.FKB, "Q171318", "kinship"⟩,
    ⟨``Wikidata.FKB.fatherOf?, "P22", "father"⟩,
    ⟨``Wikidata.FKB.motherOf?, "P25", "mother"⟩,
    ⟨``Wikidata.FKB.spouseB, "P26", "spouse"⟩,
    ⟨``Wikidata.FKB.childrenL, "P40", "child"⟩,
    ⟨``Wikidata.FKB.relatedB, "P1038", "relative"⟩,
    ⟨``Wikidata.FKB.siblingB, "Q31184", "sibling"⟩,
    ⟨``Wikidata.FKB.ancestorsL, "Q402152", "ancestor"⟩,
    -- ## Alternative parenting (`RequestProject.Parenting`)
    ⟨``Wikidata.ParentingKB, "Q1217379", "parenting"⟩,
    ⟨``Wikidata.ParentSlot.parent, "P8810", "parent"⟩,
    ⟨``Wikidata.ParentRole.biological, "Q1502246", "biological parent"⟩,
    ⟨``Wikidata.ParentRole.donor, "Q12338229", "sperm donor"⟩,
    ⟨``Wikidata.ParentRole.surrogate, "Q16547118", "surrogate mother"⟩,
    ⟨``Wikidata.ParentRole.adoptive, "Q20746742", "adoptive parent"⟩,
    ⟨``Wikidata.ParentRole.step, "Q19822352", "stepparent"⟩,
    ⟨``Wikidata.ParentRole.foster, "Q2427941", "foster parent"⟩,
    ⟨``Wikidata.ParentRole.guardian, "Q157509", "legal guardian"⟩,
    ⟨``Wikidata.ParentRole.godparent, "Q223973", "godparent"⟩,
    ⟨``Wikidata.ParentingKB.geneticParentsL, "Q774347", "consanguinity"⟩,
    ⟨``Wikidata.ParentingKB.legalParentsL, "Q66363655", "legal parent"⟩,
    ⟨``Wikidata.ParentingKB.gestationalParent?, "Q136873419", "birth mother"⟩,
    ⟨``Wikidata.ParentingKB.coParentB, "Q2996729", "coparenting"⟩,
    ⟨``Wikidata.ParentingKB.stepConsistent, "P3448", "stepparent"⟩,
    -- ## Series (`RequestProject.Series`)
    ⟨``Wikidata.SKB.series, "P179", "part of the series"⟩,
    ⟨``Wikidata.SKB.predsL, "P155", "follows"⟩,
    ⟨``Wikidata.SKB.nextL, "P156", "followed by"⟩,
    ⟨``Wikidata.SKB.ordinals, "P1545", "series ordinal"⟩,
    -- ## Biological taxa (`RequestProject.Taxa`)
    ⟨``Wikidata.TKB, "Q11398", "biological classification"⟩,
    ⟨``Wikidata.TKB.parents, "P171", "parent taxon"⟩,
    ⟨``Wikidata.TaxonRank, "P105", "taxon rank"⟩,
    ⟨``Wikidata.TKB.names, "P225", "taxon name"⟩,
    -- ## Ranks (`RequestProject.Ranks`)
    ⟨``Wikidata.Rank, "Q21044622", "Wikidata statement rank"⟩,
    ⟨``Wikidata.Rank.preferred, "Q71533031", "preferred rank"⟩,
    ⟨``Wikidata.Rank.normal, "Q73737153", "normal rank"⟩,
    ⟨``Wikidata.Rank.deprecated, "Q73737357", "deprecated rank"⟩,
    -- ## References (`RequestProject.Provenance`)
    ⟨``Wikidata.Ref, "Q44292661", "Wikidata reference"⟩,
    ⟨``Wikidata.RefKind.statedIn, "P248", "stated in"⟩,
    ⟨``Wikidata.RefKind.referenceURL, "P854", "reference URL"⟩,
    ⟨``Wikidata.RefKind.importedFrom, "P143", "imported from Wikimedia project"⟩,
    -- ## Time (`RequestProject.Temporal`, `TimeValues`)
    ⟨``Wikidata.TimeInterval, "Q186081", "time interval"⟩,
    ⟨``Wikidata.TimeInterval.start, "P580", "start time"⟩,
    ⟨``Wikidata.TimeInterval.stop, "P582", "end time"⟩,
    ⟨``Wikidata.Date, "Q186408", "point in time"⟩,
    ⟨``Wikidata.Calendar.gregorian, "Q1985727", "proleptic Gregorian calendar"⟩,
    ⟨``Wikidata.Calendar.julian, "Q1985786", "proleptic Julian calendar"⟩,
    -- ## Quantities (`RequestProject.Quantities`)
    ⟨``Wikidata.Quantity, "Q107715", "physical quantity"⟩,
    ⟨``Wikidata.UnitSystem, "Q47574", "unit of measurement"⟩,
    -- ## Terms, sitelinks and identifiers
    ⟨``Wikidata.TermStore.labelOf, "Q107659597", "Wikidata label"⟩,
    ⟨``Wikidata.TermStore.descOf, "Q107659784", "Wikidata description"⟩,
    ⟨``Wikidata.TermStore.aliasesOf, "Q107659723", "Wikidata alias"⟩,
    ⟨``Wikidata.Sitelink, "Q17587456", "sitelink"⟩,
    ⟨``Wikidata.IdKB, "Q19847637", "Wikidata property for an identifier"⟩,
    ⟨``Wikidata.IdKB.formatUrl, "P1630", "formatter URL"⟩,
    ⟨``Wikidata.KeyTable, "Q1266546", "record linkage"⟩,
    -- ## Lexemes (`RequestProject.Lexemes`)
    ⟨``Wikidata.Lexeme, "Q51885771", "Wikibase lexeme"⟩,
    ⟨``Wikidata.Form, "Q54285143", "Wikibase form"⟩,
    ⟨``Wikidata.Sense, "Q54285715", "Wikibase sense"⟩,
    ⟨``Wikidata.Sense.denotes, "P5137", "item for this sense"⟩,
    -- ## RDF, schemas and queries
    ⟨``Wikidata.Rdf.Triple, "Q3539534", "semantic triple"⟩,
    ⟨``Wikidata.Rdf.Graph, "Q54872", "Resource Description Framework"⟩,
    ⟨``Wikidata.Shape, "Q29377880", "Shape Expressions"⟩,
    ⟨``Wikidata.Query.BGP, "Q1781706", "conjunctive query"⟩,
    -- ## Class algebra and alignment
    ⟨``Wikidata.Ontology.IsUnion, "P2737", "union of"⟩,
    ⟨``Wikidata.Ontology.IsDisjointUnion, "P2738", "disjoint union of"⟩,
    ⟨``Wikidata.Ontology.IsIntersection, "Q185837", "intersection"⟩,
    ⟨``Wikidata.Ontology.WithDisjointness, "Q215382", "disjoint sets"⟩,
    ⟨``Wikidata.Ontology.Alignment, "Q1224764", "ontology alignment"⟩,
    ⟨``Wikidata.KB.alignOk, "P1709", "equivalent class"⟩,
    ⟨``Wikidata.Ontology.IsLCS, "Q4312352", "lowest common ancestor"⟩,
    ⟨``Wikidata.Upper.wdBase, "Q3882785", "upper ontology"⟩,
    -- ## The mathematics the formalisation is made of
    -- (`RequestProject.Reflection`, `MetaFrobenius`, `MathResonance`; each of
    -- these is backed by a theorem stating the construction really is an
    -- instance of the notion, in Mathlib's own vocabulary)
    ⟨``Wikidata.Ontology.Morphism, "Q215111", "homomorphism"⟩,
    ⟨``Wikidata.Ontology.endoSubmonoid, "Q208237", "monoid"⟩,
    ⟨``Wikidata.Ontology.ProperSubclassOf, "Q11077412", "strict order"⟩,
    ⟨``Wikidata.WellFormedKB.instPreorder, "Q1425985", "preorder"⟩,
    ⟨``Wikidata.Ontology.pullback, "Q1397439", "pullback"⟩,
    ⟨``Wikidata.Ontology.pullback.lift, "Q1322614", "limit"⟩,
    ⟨``Wikidata.Ontology.pullback.lift_unique, "Q1417809", "universal property"⟩,
    ⟨``Wikidata.Ontology.pullback.comm, "Q621542", "commutative diagram"⟩,
    ⟨``Wikidata.Ontology.Retract, "Q2141963", "retract"⟩,
    ⟨``Wikidata.Ontology.Retract.idem_isIdempotentElem, "Q44106280", "idempotent function"⟩,
    ⟨``Wikidata.Ontology.Retract.fixedPoints_idem, "Q217608", "fixed point"⟩,
    ⟨``Wikidata.Ontology.Retract.subclassOf_iff, "Q864213", "Conservative extension"⟩,
    ⟨``Wikidata.Ontology.Alignment.pushPull_gc, "Q357858", "adjoint functor"⟩,
    ⟨``Wikidata.Ontology.Alignment.projection_formula, "Q48998319", "Frobenius reciprocity"⟩,
    ⟨``Wikidata.Ontology.IsDisjointUnion.extension_eq_iUnion, "Q381060", "partition of a set"⟩,
    ⟨``Wikidata.KB.metaLift_injective, "Q182003", "injection"⟩,
    ⟨``Wikidata.KB.metaLift_surjective_onto_allMeta, "Q229102", "surjective function"⟩,
    ⟨``Wikidata.KB.metaEquiv_bijective, "Q180907", "bijection"⟩,
    ⟨``Wikidata.KB.metaEquiv, "Q189112", "isomorphism"⟩,
    ⟨``Wikidata.KB.metaCore_isIdempotentElem, "Q368988", "idempotence"⟩,
    ⟨``Wikidata.KB.renameSetoid, "Q130998", "equivalence relation"⟩,
    ⟨``Wikidata.KB.renameQuotientEquiv, "Q3966112", "quotient set"⟩,
    ⟨``Wikidata.FKB.properAncestor_wf, "Q338021", "well-founded relation"⟩,
    ⟨``Wikidata.KB.isSubclassOf, "Q430001", "decidability"⟩,
    ⟨``Wikidata.KB.isSubclassOf_iff, "Q693083", "soundness"⟩,
    ⟨``Wikidata.Query.mem_eval_iff, "Q15846555", "completeness"⟩,
    ⟨``Reach.reach_isLeast, "Q6134913", "Least fixed point"⟩,
    ⟨``Wikidata.Ontology.IsCommonSuperclass, "Q42866132", "upper bound"⟩,
    ⟨``Wikidata.FKB.related_not_transitive, "Q54980267", "intransitivity"⟩,
    ⟨``Wikidata.Ontology.canonicalModel, "Q1609475", "Herbrand structure"⟩,
    ⟨``Wikidata.Ontology.subVocabulary, "Q1308999", "restriction"⟩,
    ⟨``Wikidata.KB.supersL, "Q1137726", "directed graph"⟩,
    -- ## Topology, category theory, and the theories that meet the pullback
    -- (`RequestProject.CategoryOfOntologies`, `OntologyTopology`,
    -- `GrothendieckSite`, `HomotopyTypes`, `CubicalTypes`, `OntologyGroups`,
    -- `OntologyFields`; each entry is backed by a theorem in those files saying
    -- the construction really is an instance of the notion)
    ⟨``Wikidata.Ontology.Ont, "Q719395", "category"⟩,
    ⟨``Wikidata.Ontology.ontCategory, "Q217413", "category theory"⟩,
    ⟨``Wikidata.Ontology.forgetOnt, "Q864475", "functor"⟩,
    ⟨``Wikidata.Ontology.subclassTopology, "Q42989", "topology"⟩,
    ⟨``Wikidata.Ontology.ItemSpace, "Q179899", "topological space"⟩,
    ⟨``Wikidata.Ontology.instAlexandrovDiscreteItemSpace, "Q3532117", "Alexandrov topology"⟩,
    ⟨``Wikidata.Ontology.isOpen_downSet, "Q213363", "open set"⟩,
    ⟨``Wikidata.Ontology.Morphism.continuous_toItemMap, "Q170058", "continuous function"⟩,
    ⟨``Wikidata.Ontology.ontologyTopology, "Q1062242", "Grothendieck topology"⟩,
    ⟨``Wikidata.Ontology.pullbackEquivSigma, "Q5891840", "homotopy type theory"⟩,
    ⟨``Wikidata.Ontology.Fib, "Q493941", "fibration"⟩,
    ⟨``Wikidata.Ontology.pullback_eq_iff, "Q110720714", "Identity type"⟩,
    ⟨``Wikidata.Ontology.cubePullbackEquiv, "Q139761564", "Cubical type theory"⟩,
    ⟨``Wikidata.Ontology.Iv.deMorgan_meet, "Q5244640", "De Morgan algebra"⟩,
    ⟨``Wikidata.Ontology.pbAut, "Q874429", "group theory"⟩,
    ⟨``Wikidata.Ontology.autPerm, "Q60790315", "automorphism group"⟩,
    ⟨``Wikidata.Ontology.autToPerm, "Q83478", "group"⟩,
    ⟨``Wikidata.Ontology.autOverSubgroup, "Q466109", "subgroup"⟩,
    ⟨``Wikidata.Ontology.pbAutMulAction, "Q288465", "group action"⟩,
    ⟨``Wikidata.Ontology.extPullbackSubmodule, "Q903820", "field theory"⟩,
    ⟨``Wikidata.Ontology.GF2, "Q190109", "field"⟩,
    ⟨``Wikidata.Ontology.chi, "Q5513324", "F₂"⟩,
    ⟨``Wikidata.Ontology.ExtSpace, "Q125977", "vector space"⟩,
    ⟨``Wikidata.Ontology.comapLin, "Q207643", "linear map"⟩,
    -- ## The grounding itself
    ⟨``Wikidata.Glossary, "Q2013", "Wikidata"⟩,
    ⟨``Wikidata.Gloss.article, "Q105770631", "English Wikipedia article"⟩ ]

end Wikidata

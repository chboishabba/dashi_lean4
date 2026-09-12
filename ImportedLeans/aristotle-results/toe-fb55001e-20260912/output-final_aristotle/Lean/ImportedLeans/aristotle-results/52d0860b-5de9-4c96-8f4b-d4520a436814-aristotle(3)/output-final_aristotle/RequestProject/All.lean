import RequestProject.Wikidata.Reachability
import RequestProject.Wikidata.Core
import RequestProject.Wikidata.ClassAlgebra
import RequestProject.Wikidata.Redundancy
import RequestProject.Wikidata.Diagnostics
import RequestProject.Wikidata.Alignment
import RequestProject.Wikidata.Provenance
import RequestProject.Wikidata.Slices
import RequestProject.Wikidata.Layers
import RequestProject.Wikidata.Rdf
import RequestProject.Wikidata.Constraints
import RequestProject.Wikidata.Identity
import RequestProject.Wikidata.Values
import RequestProject.Wikidata.Qualifiers
import RequestProject.Wikidata.Sparql
import RequestProject.Wikidata.SparqlPaths
import RequestProject.Wikidata.SparqlAggregation
import RequestProject.Wikidata.SparqlNegation
import RequestProject.Wikidata.ClassExpressions
import RequestProject.Wikidata.NamedGraphs
import RequestProject.Wikidata.Owl
import RequestProject.Wikidata.Lens
import RequestProject.Wikidata.Parenting
import RequestProject.Wikidata.ParentingRoles
import RequestProject.Wikidata.DerivationFibres
import RequestProject.Wikidata.Attribution
import RequestProject.Wikidata.AlignmentSafety
import RequestProject.Wikidata.DisjointUnionDiagnostics
import RequestProject.Wikidata.RdfInformationOrder
import RequestProject.Epistemic.Trit
import RequestProject.Epistemic.Bridge
import RequestProject.Epistemic.Repair
import RequestProject.Epistemic.Context
import RequestProject.Epistemic.Surfaces
import RequestProject.Epistemic.ValueEvidence
import RequestProject.Epistemic.QueryEvidence
import RequestProject.Epistemic.PathEvidence
import RequestProject.Epistemic.Tetralemma
import RequestProject.Epistemic.Lens
import RequestProject.Epistemic.Views
import RequestProject.Epistemic.Observer
import RequestProject.Epistemic.Quotient
import RequestProject.Epistemic.Authority
import RequestProject.Epistemic.FourView
import RequestProject.Epistemic.ObligationAuthority
import RequestProject.Epistemic.ContextErasure
import RequestProject.Wikidata.ParentingFibres
import RequestProject.Wikidata.ParentingAuthority
import RequestProject.Epistemic.ParentingEvidence
import RequestProject.Epistemic.ObserverJoin
import RequestProject.Epistemic.Opposition
import RequestProject.Epistemic.AxisSupport
import RequestProject.Ternary.Balanced
import RequestProject.Ternary.Base369
import RequestProject.Ternary.Aggregate
import RequestProject.Wikidata.ViewJoin
import RequestProject.Wikidata.EvidencePolarity
import RequestProject.Wikidata.Learning
import RequestProject.Wikidata.Examples
import RequestProject.Wikidata.ExamplesLayers
import RequestProject.Wikidata.ExamplesConflict

/-!
# Entry point

Imports the whole development: the executable Wikidata ontology engine
(`RequestProject.Wikidata.*`), the three-valued evidence layer and bridge
(`RequestProject.Epistemic.*`), and the worked artist/painter/sculptor
regressions (`RequestProject.Wikidata.Examples`,
`RequestProject.Wikidata.ExamplesLayers`).

The engine is organised in layers — full statements, the truthy query layer, the
reified RDF layer and the direct RDF layer — and in slices, the sub-bases cut out
by a criterion on statements (provenance, time, or any other).  Evidence is
indexed by both coordinates in `RequestProject.Epistemic.Views`.

The parenting tranche adds a third organising idea: a Wikidata slot is a
*projection* of a richer carrier.  `RequestProject.Wikidata.Parenting` builds the
parent-slot engine and the twelve-coordinate relationship carrier,
`RequestProject.Epistemic.Observer` and `RequestProject.Epistemic.Quotient` supply
the generic theory of observers, hidden motion and exact reopening from a
residual, and `RequestProject.Epistemic.Authority` the theory of acting on a
projection — consumer- and policy-relative future safety, and delegated authority
over time.  `RequestProject.Wikidata.ParentingFibres`,
`RequestProject.Wikidata.ParentingAuthority`,
`RequestProject.Wikidata.ParentingRoles` and
`RequestProject.Epistemic.ParentingEvidence` are the instances.

The evidence-polarity tranche adds a fourth: *what counter-evidence is
counter-evidence against*.  `RequestProject.Epistemic.Opposition` makes
opposition semantic and pools evidence only inside a fibre,
`RequestProject.Epistemic.AxisSupport` requires a claim to resolve every one of
its axes, and `RequestProject.Epistemic.ObserverJoin` supplies the join of two
transverse readings.  `RequestProject.Wikidata.EvidencePolarity` and
`RequestProject.Wikidata.ViewJoin` are the Wikidata instances, and
`RequestProject.Ternary.*` carries the balanced-ternary carrier whose quotient
counts and lossy collapses the tranche is built on.
The value-type tranche closes two gaps of the earlier passes.
`RequestProject.Wikidata.Values` gives Wikidata's literal value types their own
structure — quantities as intervals in a unit, times as timestamps at a precision
in a calendar model, coordinates as points with a tolerance on a globe — each with
an executable comparison and the negative result that says which naive reading is
wrong.  `RequestProject.Wikidata.Qualifiers` makes qualifiers and references
first-class objects of the statement rather than a function on core statements,
and derives the relation to the core layer: the temporal slice cut out by the
qualifiers is a genuine slice, while the core layer forgets qualifiers, erases
expiry, drops `novalue` and `somevalue` snaks, and cannot say which of two
statements with a common projection carries the reference.
`RequestProject.Wikidata.Sparql` adds the query surface: the classical core
fragment of SPARQL evaluated against the truthy projection, with the positive
fragment proved monotone and `OPTIONAL` and `!bound` proved not to be — so an
answer obtained by negation as failure is an absence in the base that was
queried, which is what `RequestProject.Epistemic.QueryEvidence` makes precise for
imported answers.  `RequestProject.Wikidata.Owl` adds the property
characteristics — transitive, symmetric, inverse — as a declarative entailment
relation with a decidable closure check, and proves that each declaration is an
edit to the theory rather than a reading of it, and that class equivalence must
not be encoded as a subclass cycle.

The query surface continues in four further modules.
`RequestProject.Wikidata.SparqlPaths` adds property paths, with `P31/P279*`
proved to be the project's own instance relation and the whole fragment proved
monotone; `RequestProject.Wikidata.NamedGraphs` makes a named graph a slice of a
dataset and shows that a fact derived over the dataset need not hold in any
single graph; `RequestProject.Wikidata.SparqlAggregation` adds `SELECT DISTINCT`,
`GROUP BY`, `COUNT` and `HAVING`, proving that projected answers and group keys
stay monotone while counts and `HAVING` answers do not; and
`RequestProject.Wikidata.SparqlNegation` separates `MINUS` from `FILTER NOT
EXISTS`, which differ exactly on whether the two sides share a variable.
`RequestProject.Wikidata.ClassExpressions` completes the OWL class fragment with
intersection, union, complement and the two restrictions, proving the positive
part monotone, complement and `∀p.C` not, and the class statements Wikidata
records sound for the expression semantics.

`RequestProject.Wikidata.Learning` is the governed-learning boundary: what a
knowledge base may learn about itself from a reviewed cohort, and what a residual
solver may propose without editing anything.
-/

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
-/

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
import RequestProject.Epistemic.Trit
import RequestProject.Epistemic.Bridge
import RequestProject.Epistemic.Repair
import RequestProject.Epistemic.Context
import RequestProject.Epistemic.Surfaces
import RequestProject.Epistemic.Tetralemma
import RequestProject.Epistemic.Lens
import RequestProject.Epistemic.Views
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
-/

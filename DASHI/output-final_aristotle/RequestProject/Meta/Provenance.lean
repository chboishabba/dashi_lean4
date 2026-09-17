/- Attribution: JMD (github.com/meta-introspector) -/
import Mathlib

/-!
# The provenance ledger, machine-checked

This module is **generated** by `tools/provenance.py` from the Lean sources and
from the compiled kernel environment (`tools/DepDump.lean`).  It carries, as
data inside Lean, the numbers that the provenance report and the infographic
state informally:

* for every module of the development, how many of its declarations are traced
  to the DASHI Agda bridge (`chboishabba/dashi_agda` PR #555 / #581 / #582), how many
  render the Wikidata data model, and how many are original to this port;
* the module dependency graph, as it really is in the compiled environment.

The arithmetic claims are then *theorems* (`by decide`), so the ledger cannot
silently disagree with itself, and the dependency graph is proved acyclic.

Regenerate with

```
lake env lean tools/DepDump.lean && python3 tools/provenance.py
```
-/

-- The ledger's `decide` goals fold over the whole development, so the default
-- recursion depth is not enough once the ledger grows.
set_option maxRecDepth 40000

namespace RequestProject.Meta

/-- Where a declaration came from. -/
inductive Src
  | /-- Traced to the DASHI Agda bridge. -/ dashi
  | /-- The Wikidata data model and the standards around it. -/ wikidata
  | /-- Introduced by this Lean port. -/ original
  deriving DecidableEq, Repr

/-- The provenance record of one module: its position in a topological order of
the dependency graph, its declaration counts, and its source mix. -/
structure ModuleProvenance where
  /-- Index of the module in the topological order used by `depEdges`. -/
  index : Nat
  /-- Fully qualified module name. -/
  name : String
  /-- Number of source declarations in the module. -/
  declarations : Nat
  /-- How many of them are theorems. -/
  theorems : Nat
  /-- How many are traced to the DASHI bridge. -/
  dashi : Nat
  /-- How many render the Wikidata data model. -/
  wikidata : Nat
  /-- How many are original to this port. -/
  original : Nat
  deriving DecidableEq, Repr


/-- One record per module of the development, in topological order:
a module only uses modules that appear before it. -/
def ledger : List ModuleProvenance := [
  { index := 0, name := "RequestProject.Agda.Prelude", declarations := 46, theorems := 18,
    dashi := 0, wikidata := 0, original := 46 },
  { index := 1, name := "RequestProject.Agda.Syntax", declarations := 11, theorems := 0,
    dashi := 0, wikidata := 0, original := 11 },
  { index := 2, name := "RequestProject.Agda.Verbatim", declarations := 14, theorems := 0,
    dashi := 0, wikidata := 0, original := 14 },
  { index := 3, name := "RequestProject.Epistemic.ContextErasure", declarations := 19, theorems := 9,
    dashi := 0, wikidata := 0, original := 19 },
  { index := 4, name := "RequestProject.Epistemic.Observer", declarations := 41, theorems := 27,
    dashi := 13, wikidata := 0, original := 28 },
  { index := 5, name := "RequestProject.Epistemic.Trit", declarations := 46, theorems := 34,
    dashi := 12, wikidata := 0, original := 34 },
  { index := 6, name := "RequestProject.Mirror.CRTJFixedPointBridge", declarations := 10, theorems := 8,
    dashi := 0, wikidata := 0, original := 10 },
  { index := 7, name := "RequestProject.Mirror.CRTPeriod", declarations := 23, theorems := 20,
    dashi := 0, wikidata := 0, original := 23 },
  { index := 8, name := "RequestProject.Mirror.Classification", declarations := 34, theorems := 24,
    dashi := 0, wikidata := 0, original := 34 },
  { index := 9, name := "RequestProject.Mirror.Correspondence", declarations := 10, theorems := 8,
    dashi := 0, wikidata := 0, original := 10 },
  { index := 10, name := "RequestProject.Mirror.JFixedPoint", declarations := 21, theorems := 12,
    dashi := 0, wikidata := 0, original := 21 },
  { index := 11, name := "RequestProject.Mirror.Moonshine", declarations := 28, theorems := 16,
    dashi := 0, wikidata := 0, original := 28 },
  { index := 12, name := "RequestProject.Mirror.ProofRelevance", declarations := 11, theorems := 5,
    dashi := 0, wikidata := 0, original := 11 },
  { index := 13, name := "RequestProject.Ternary.Balanced", declarations := 34, theorems := 24,
    dashi := 15, wikidata := 0, original := 19 },
  { index := 14, name := "RequestProject.Wikidata.Coverage", declarations := 25, theorems := 17,
    dashi := 0, wikidata := 14, original := 11 },
  { index := 15, name := "RequestProject.Wikidata.Reachability", declarations := 11, theorems := 8,
    dashi := 0, wikidata := 0, original := 11 },
  { index := 16, name := "RequestProject.Epistemic.Authority", declarations := 36, theorems := 21,
    dashi := 15, wikidata := 0, original := 21 },
  { index := 17, name := "RequestProject.Epistemic.Quotient", declarations := 27, theorems := 15,
    dashi := 14, wikidata := 0, original := 13 },
  { index := 18, name := "RequestProject.Epistemic.Tetralemma", declarations := 48, theorems := 33,
    dashi := 4, wikidata := 0, original := 44 },
  { index := 19, name := "RequestProject.Wikidata.Core", declarations := 32, theorems := 12,
    dashi := 1, wikidata := 31, original := 0 },
  { index := 20, name := "RequestProject.Wikidata.DerivationFibres", declarations := 47, theorems := 23,
    dashi := 0, wikidata := 11, original := 36 },
  { index := 21, name := "RequestProject.Epistemic.FourView", declarations := 27, theorems := 11,
    dashi := 0, wikidata := 0, original := 27 },
  { index := 22, name := "RequestProject.Epistemic.Lens", declarations := 23, theorems := 13,
    dashi := 0, wikidata := 0, original := 23 },
  { index := 23, name := "RequestProject.Epistemic.ObligationAuthority", declarations := 19, theorems := 11,
    dashi := 0, wikidata := 0, original := 19 },
  { index := 24, name := "RequestProject.Epistemic.ObserverJoin", declarations := 10, theorems := 9,
    dashi := 7, wikidata := 0, original := 3 },
  { index := 25, name := "RequestProject.Epistemic.Opposition", declarations := 31, theorems := 16,
    dashi := 14, wikidata := 0, original := 17 },
  { index := 26, name := "RequestProject.Epistemic.OrderDescent", declarations := 12, theorems := 9,
    dashi := 2, wikidata := 0, original := 10 },
  { index := 27, name := "RequestProject.Ternary.Aggregate", declarations := 26, theorems := 15,
    dashi := 12, wikidata := 0, original := 14 },
  { index := 28, name := "RequestProject.Wikidata.Attribution", declarations := 41, theorems := 21,
    dashi := 0, wikidata := 6, original := 35 },
  { index := 29, name := "RequestProject.Wikidata.BFO", declarations := 55, theorems := 29,
    dashi := 0, wikidata := 17, original := 38 },
  { index := 30, name := "RequestProject.Wikidata.ClassAlgebra", declarations := 18, theorems := 10,
    dashi := 0, wikidata := 10, original := 8 },
  { index := 31, name := "RequestProject.Wikidata.ClassOrder", declarations := 35, theorems := 16,
    dashi := 0, wikidata := 16, original := 19 },
  { index := 32, name := "RequestProject.Wikidata.Constraints", declarations := 48, theorems := 25,
    dashi := 0, wikidata := 48, original := 0 },
  { index := 33, name := "RequestProject.Wikidata.Diagnostics", declarations := 8, theorems := 3,
    dashi := 0, wikidata := 8, original := 0 },
  { index := 34, name := "RequestProject.Wikidata.Parenting", declarations := 83, theorems := 29,
    dashi := 20, wikidata := 38, original := 25 },
  { index := 35, name := "RequestProject.Wikidata.Redundancy", declarations := 15, theorems := 12,
    dashi := 0, wikidata := 15, original := 0 },
  { index := 36, name := "RequestProject.Wikidata.Values", declarations := 60, theorems := 37,
    dashi := 8, wikidata := 15, original := 37 },
  { index := 37, name := "RequestProject.Epistemic.AxisSupport", declarations := 26, theorems := 16,
    dashi := 9, wikidata := 0, original := 17 },
  { index := 38, name := "RequestProject.Epistemic.Bridge", declarations := 28, theorems := 16,
    dashi := 3, wikidata := 0, original := 25 },
  { index := 39, name := "RequestProject.Epistemic.Repair", declarations := 15, theorems := 10,
    dashi := 6, wikidata := 0, original := 9 },
  { index := 40, name := "RequestProject.Ternary.Base369", declarations := 39, theorems := 25,
    dashi := 15, wikidata := 0, original := 24 },
  { index := 41, name := "RequestProject.Wikidata.Alignment", declarations := 10, theorems := 4,
    dashi := 2, wikidata := 6, original := 2 },
  { index := 42, name := "RequestProject.Wikidata.Capture", declarations := 19, theorems := 10,
    dashi := 2, wikidata := 0, original := 17 },
  { index := 43, name := "RequestProject.Wikidata.DisjointUnionDiagnostics", declarations := 19, theorems := 9,
    dashi := 0, wikidata := 14, original := 5 },
  { index := 44, name := "RequestProject.Wikidata.EditOrder", declarations := 16, theorems := 6,
    dashi := 1, wikidata := 0, original := 15 },
  { index := 45, name := "RequestProject.Wikidata.Identity", declarations := 27, theorems := 15,
    dashi := 3, wikidata := 15, original := 9 },
  { index := 46, name := "RequestProject.Wikidata.Owl", declarations := 28, theorems := 11,
    dashi := 0, wikidata := 27, original := 1 },
  { index := 47, name := "RequestProject.Wikidata.ParentingAuthority", declarations := 30, theorems := 17,
    dashi := 3, wikidata := 0, original := 27 },
  { index := 48, name := "RequestProject.Wikidata.ParentingFibres", declarations := 46, theorems := 24,
    dashi := 2, wikidata := 9, original := 35 },
  { index := 49, name := "RequestProject.Wikidata.ParentingRoles", declarations := 16, theorems := 8,
    dashi := 5, wikidata := 2, original := 9 },
  { index := 50, name := "RequestProject.Wikidata.Provenance", declarations := 26, theorems := 19,
    dashi := 2, wikidata := 23, original := 1 },
  { index := 51, name := "RequestProject.Wikidata.Retrieval", declarations := 15, theorems := 10,
    dashi := 2, wikidata := 0, original := 13 },
  { index := 52, name := "RequestProject.Epistemic.Commitment", declarations := 20, theorems := 11,
    dashi := 1, wikidata := 0, original := 19 },
  { index := 53, name := "RequestProject.Epistemic.Context", declarations := 7, theorems := 6,
    dashi := 1, wikidata := 0, original := 6 },
  { index := 54, name := "RequestProject.Epistemic.ParentingEvidence", declarations := 16, theorems := 10,
    dashi := 2, wikidata := 0, original := 14 },
  { index := 55, name := "RequestProject.Wikidata.AlignmentSafety", declarations := 22, theorems := 11,
    dashi := 0, wikidata := 4, original := 18 },
  { index := 56, name := "RequestProject.Wikidata.ClassExpressions", declarations := 28, theorems := 18,
    dashi := 0, wikidata := 25, original := 3 },
  { index := 57, name := "RequestProject.Wikidata.Learning", declarations := 61, theorems := 34,
    dashi := 32, wikidata := 22, original := 7 },
  { index := 58, name := "RequestProject.Wikidata.Qualifiers", declarations := 50, theorems := 24,
    dashi := 0, wikidata := 46, original := 4 },
  { index := 59, name := "RequestProject.Wikidata.Slices", declarations := 26, theorems := 23,
    dashi := 0, wikidata := 26, original := 0 },
  { index := 60, name := "RequestProject.Wikidata.Sparql", declarations := 39, theorems := 16,
    dashi := 0, wikidata := 38, original := 1 },
  { index := 61, name := "RequestProject.Epistemic.Independence", declarations := 21, theorems := 12,
    dashi := 0, wikidata := 0, original := 21 },
  { index := 62, name := "RequestProject.Epistemic.QueryEvidence", declarations := 9, theorems := 6,
    dashi := 0, wikidata := 0, original := 9 },
  { index := 63, name := "RequestProject.Epistemic.ValueEvidence", declarations := 17, theorems := 11,
    dashi := 0, wikidata := 0, original := 17 },
  { index := 64, name := "RequestProject.Wikidata.Examples", declarations := 47, theorems := 30,
    dashi := 3, wikidata := 25, original := 19 },
  { index := 65, name := "RequestProject.Wikidata.Layers", declarations := 25, theorems := 22,
    dashi := 1, wikidata := 24, original := 0 },
  { index := 66, name := "RequestProject.Wikidata.OwlCardinality", declarations := 32, theorems := 16,
    dashi := 0, wikidata := 0, original := 32 },
  { index := 67, name := "RequestProject.Wikidata.SparqlAggregation", declarations := 34, theorems := 24,
    dashi := 0, wikidata := 29, original := 5 },
  { index := 68, name := "RequestProject.Wikidata.SparqlExpressions", declarations := 51, theorems := 29,
    dashi := 0, wikidata := 0, original := 51 },
  { index := 69, name := "RequestProject.Wikidata.SparqlNegation", declarations := 26, theorems := 19,
    dashi := 0, wikidata := 15, original := 11 },
  { index := 70, name := "RequestProject.Wikidata.SparqlPaths", declarations := 38, theorems := 24,
    dashi := 0, wikidata := 34, original := 4 },
  { index := 71, name := "RequestProject.Epistemic.Views", declarations := 23, theorems := 17,
    dashi := 1, wikidata := 0, original := 22 },
  { index := 72, name := "RequestProject.Wikidata.EvidencePolarity", declarations := 23, theorems := 15,
    dashi := 9, wikidata := 7, original := 7 },
  { index := 73, name := "RequestProject.Wikidata.NamedGraphs", declarations := 21, theorems := 14,
    dashi := 0, wikidata := 21, original := 0 },
  { index := 74, name := "RequestProject.Wikidata.Rdf", declarations := 33, theorems := 20,
    dashi := 2, wikidata := 31, original := 0 },
  { index := 75, name := "RequestProject.Wikidata.ViewJoin", declarations := 20, theorems := 9,
    dashi := 6, wikidata := 11, original := 3 },
  { index := 76, name := "RequestProject.Epistemic.PathEvidence", declarations := 10, theorems := 7,
    dashi := 0, wikidata := 0, original := 10 },
  { index := 77, name := "RequestProject.Epistemic.Surfaces", declarations := 21, theorems := 13,
    dashi := 1, wikidata := 0, original := 20 },
  { index := 78, name := "RequestProject.Wikidata.BlankNodes", declarations := 67, theorems := 36,
    dashi := 0, wikidata := 38, original := 29 },
  { index := 79, name := "RequestProject.Wikidata.ExamplesLayers", declarations := 32, theorems := 24,
    dashi := 0, wikidata := 27, original := 5 },
  { index := 80, name := "RequestProject.Wikidata.Lens", declarations := 17, theorems := 13,
    dashi := 1, wikidata := 16, original := 0 },
  { index := 81, name := "RequestProject.Wikidata.ExamplesConflict", declarations := 17, theorems := 12,
    dashi := 0, wikidata := 11, original := 6 },
  { index := 82, name := "RequestProject.Wikidata.RdfInformationOrder", declarations := 12, theorems := 7,
    dashi := 0, wikidata := 9, original := 3 }
]

/-- The module dependency graph: `(a, b)` means a declaration of module `a`
uses a declaration of module `b`.  Read off the compiled environment. -/
def depEdges : List (Nat × Nat) := [
  (16, 4), (17, 4), (18, 5), (19, 15), (20, 5), (21, 18),
  (22, 5), (22, 18), (23, 16), (23, 18), (24, 4), (24, 17),
  (25, 18), (26, 4), (26, 17), (27, 4), (27, 5), (27, 13),
  (27, 17), (28, 5), (28, 18), (28, 20), (29, 19), (30, 19),
  (31, 19), (32, 15), (32, 19), (33, 19), (34, 15), (34, 19),
  (35, 19), (36, 19), (37, 16), (37, 18), (37, 23), (38, 5),
  (38, 19), (38, 30), (38, 33), (39, 5), (39, 19), (39, 35),
  (40, 4), (40, 13), (40, 17), (40, 24), (41, 19), (41, 30),
  (42, 15), (42, 17), (42, 19), (42, 26), (43, 19), (43, 30),
  (44, 17), (44, 19), (44, 26), (45, 19), (45, 32), (46, 19),
  (46, 33), (47, 4), (47, 16), (47, 19), (47, 34), (48, 4),
  (48, 17), (48, 19), (48, 34), (49, 19), (49, 34), (50, 19),
  (50, 33), (51, 17), (51, 19), (51, 26), (51, 33), (52, 19),
  (52, 38), (53, 5), (53, 19), (53, 50), (54, 5), (54, 16),
  (54, 17), (54, 19), (54, 34), (54, 47), (54, 48), (55, 19),
  (55, 30), (55, 41), (56, 19), (56, 30), (56, 50), (57, 17),
  (57, 19), (57, 39), (58, 19), (58, 36), (58, 50), (59, 19),
  (59, 33), (59, 50), (60, 19), (60, 50), (61, 19), (61, 52),
  (62, 5), (62, 19), (62, 50), (62, 60), (63, 5), (63, 19),
  (63, 36), (63, 50), (63, 58), (64, 5), (64, 19), (64, 30),
  (64, 33), (64, 35), (64, 38), (64, 39), (64, 41), (64, 50),
  (64, 53), (65, 19), (65, 50), (65, 59), (66, 19), (66, 50),
  (66, 56), (67, 19), (67, 50), (67, 60), (68, 19), (68, 60),
  (69, 19), (69, 60), (70, 15), (70, 19), (70, 50), (70, 60),
  (71, 5), (71, 19), (71, 38), (71, 50), (71, 59), (71, 65),
  (72, 18), (72, 19), (72, 25), (72, 37), (72, 38), (72, 50),
  (72, 64), (73, 19), (73, 50), (73, 59), (73, 70), (74, 19),
  (74, 65), (75, 4), (75, 17), (75, 19), (75, 24), (75, 59),
  (75, 65), (76, 5), (76, 19), (76, 50), (76, 70), (76, 73),
  (77, 5), (77, 19), (77, 32), (77, 38), (77, 74), (78, 19),
  (78, 74), (79, 5), (79, 19), (79, 32), (79, 38), (79, 45),
  (79, 64), (79, 65), (79, 71), (79, 74), (80, 5), (80, 19),
  (80, 22), (80, 65), (80, 74), (81, 5), (81, 18), (81, 19),
  (81, 22), (81, 64), (81, 65), (81, 74), (81, 80), (82, 19),
  (82, 74), (82, 80)
]


/-- Total number of declarations recorded in the ledger. -/
def totalDeclarations : Nat := (ledger.map (·.declarations)).sum

/-- Declarations attributed to a given source. -/
def totalFor : Src → Nat
  | .dashi => (ledger.map (·.dashi)).sum
  | .wikidata => (ledger.map (·.wikidata)).sum
  | .original => (ledger.map (·.original)).sum

/-- The modules that carry at least one bridge-traced declaration. -/
def dashiModules : List ModuleProvenance := ledger.filter (fun m => 0 < m.dashi)

/-- One module uses another: `(a, b) ∈ depEdges` means some declaration of the
module with index `a` uses a declaration of the module with index `b`. -/
def Uses (a b : Nat) : Prop := (a, b) ∈ depEdges

instance (a b : Nat) : Decidable (Uses a b) := inferInstanceAs (Decidable (_ ∈ _))

/-- The ledger is indexed by position: `index` really is the position in the list. -/
theorem ledger_index_eq : ledger.map (·.index) = List.range ledger.length := by decide

/-- Every module's source mix accounts for all of its declarations. -/
theorem module_mix_total : ∀ m ∈ ledger, m.dashi + m.wikidata + m.original = m.declarations := by
  decide

/-- The three sources partition the development. -/
theorem sources_partition :
    totalFor .dashi + totalFor .wikidata + totalFor .original = totalDeclarations := by
  decide

/-- Every dependency edge points from a module to one that is strictly earlier in
the topological order.  This is the ledger's copy of "the graph is layered". -/
theorem depEdges_decreasing : ∀ e ∈ depEdges, e.2 < e.1 := by decide

/-- Both endpoints of every edge are modules of the ledger. -/
theorem depEdges_mem : ∀ e ∈ depEdges, e.1 < ledger.length ∧ e.2 < ledger.length := by decide

/-- A chain of uses strictly decreases the topological index. -/
theorem lt_of_transGen_uses {a b : Nat} (h : Relation.TransGen Uses a b) : b < a := by
  induction h with
  | single hab => exact depEdges_decreasing _ hab
  | tail _ hbc ih => exact lt_trans (depEdges_decreasing _ hbc) ih

/-- **The dependency graph of the development is acyclic.** -/
theorem uses_acyclic (a : Nat) : ¬ Relation.TransGen Uses a a := fun h =>
  absurd (lt_of_transGen_uses h) (lt_irrefl a)

/-- No module uses itself. -/
theorem uses_irrefl (a : Nat) : ¬ Uses a a := fun h => uses_acyclic a (.single h)

/-- The bridge-traced declarations, by fully qualified name.  Each of these is
named in an upstream correspondence row of `PORTING_NOTES.md` or
`RELATED_WORK.md` §1, and carries an `-- @source` comment in its own module. -/
def dashiTraced : List String := [
  "Epistemic.AgreeOn",
  "Epistemic.Authority.currentAuthority",
  "Epistemic.Authority.currentAuthority_append_revoke",
  "Epistemic.Authority.currentAuthority_eq_false_of_no_regrant",
  "Epistemic.Authority.discretionary_act_requires_fresh_grant",
  "Epistemic.Authority.everGranted",
  "Epistemic.Authority.everGranted_append_revoke",
  "Epistemic.Authority.supporter_cannot_self_authorise",
  "Epistemic.Authority.unavoidable_continuation_creates_no_mandate",
  "Epistemic.AxisEvidenceFamily",
  "Epistemic.Certificate",
  "Epistemic.Certificate.holds_of_supported",
  "Epistemic.DescendsToSurface",
  "Epistemic.DynamicSafety",
  "Epistemic.ExactRecoverable",
  "Epistemic.ExactRecoverable.comp",
  "Epistemic.ExactRecoverable.comp_residual_eq",
  "Epistemic.ExactRecoverable.eq_of_project_eq_of_residual_eq",
  "Epistemic.ExactRecoverable.residual_ne_of_hiddenTransition",
  "Epistemic.FactorsThrough",
  "Epistemic.FibreAutomorphism",
  "Epistemic.FibreEvidence",
  "Epistemic.FibreEvidence.pool",
  "Epistemic.FibreEvidence.pool_conflict",
  "Epistemic.FibreEvidence.pool_ignorance",
  "Epistemic.HiddenTransition",
  "Epistemic.Incomparable",
  "Epistemic.MissingRequiredAxis",
  "Epistemic.Observer",
  "Epistemic.OperatorRole",
  "Epistemic.Opposes",
  "Epistemic.Opposition",
  "Epistemic.PluralDynamicSafety",
  "Epistemic.PolicyExposedQuotientDefect",
  "Epistemic.PolicyRelativeSafety",
  "Epistemic.RepairOperation",
  "Epistemic.RequiredAxesResolved",
  "Epistemic.ResidualFibre",
  "Epistemic.ScopedClaim",
  "Epistemic.ScopedClaim.and",
  "Epistemic.ScopedClaim.references_subset_and",
  "Epistemic.SectionedProjection",
  "Epistemic.SectionedProjection.fibreConstant_eq_pullback",
  "Epistemic.Separating",
  "Epistemic.StrictlyRefines",
  "Epistemic.SurfaceClaim.losslessness_always_holds",
  "Epistemic.SurfaceInvariant",
  "Epistemic.TerminalisationDefect",
  "Epistemic.Trit",
  "Epistemic.Trit.neg",
  "Epistemic.collapse_importSquare",
  "Epistemic.commitment_does_not_determine_state",
  "Epistemic.conflict_requires_opposition",
  "Epistemic.conflicting_iff_merge_bothSupported",
  "Epistemic.converse_not_opposes",
  "Epistemic.converse_support_does_not_refute",
  "Epistemic.crossContext_pool_manufactures_conflict",
  "Epistemic.crossRole_pool_manufactures_conflict",
  "Epistemic.enact_eq_of_not_approved",
  "Epistemic.enact_eq_of_unsupported",
  "Epistemic.enact_redundancy_proposal_preserves_subclass",
  "Epistemic.enact_removeBadSuperclass",
  "Epistemic.exists_section_not_injective",
  "Epistemic.factorsThrough_iff_refines",
  "Epistemic.factorsThrough_pairObserver",
  "Epistemic.fibreConstantPred_pullback",
  "Epistemic.importEvidence_eq",
  "Epistemic.importSquare_ne_both",
  "Epistemic.incomparable_of_cross_collisions",
  "Epistemic.merge_then_collapse_ne_collapse_then_merge",
  "Epistemic.no_resolution_from_supportCount",
  "Epistemic.not_factorsThrough",
  "Epistemic.not_factorsThrough_orderedEndpoint",
  "Epistemic.not_factorsThrough_postcomp",
  "Epistemic.not_holds_of_sound_against",
  "Epistemic.not_injective_of_hiddenTransition",
  "Epistemic.not_plural_of_defect",
  "Epistemic.not_resolved_of_missing",
  "Epistemic.not_separating_pairObserver_of_common_collision",
  "Epistemic.obligationOf",
  "Epistemic.pairObserver_least",
  "Epistemic.policyRelativeSafety_of_dynamicSafety",
  "Epistemic.pullbackPred",
  "Epistemic.pullbackPred_join",
  "Epistemic.pullbackPred_meet",
  "Epistemic.receiptState",
  "Epistemic.receiptState_ne_contradicted",
  "Epistemic.redundancyProposal_operation",
  "Epistemic.refines_of_factorsThrough",
  "Epistemic.requiredAxesResolved_iff_no_missing",
  "Epistemic.residualFibre_cons_ssubset",
  "Epistemic.residualFibre_cons_subset",
  "Epistemic.resolved_axes_do_not_open_authority",
  "Epistemic.role_does_not_determine_opposition",
  "Epistemic.separatingFamily_iff_residualFibre_eq",
  "Epistemic.sliceClaim",
  "Epistemic.slot_evidence_cannot_route_authority",
  "Epistemic.sound_ne_bothSupported",
  "Epistemic.strong_support_does_not_compensate",
  "Epistemic.support_does_not_confer_authority",
  "Epistemic.unresolved_left_never_conflicts",
  "Epistemic.verdictState",
  "Epistemic.verdictState_eq_contradicted_iff",
  "Epistemic.verdictState_notObserved",
  "Epistemic.viewClaim_layer_irrelevant",
  "Ternary.BernoulliPoint",
  "Ternary.Block",
  "Ternary.State",
  "Ternary.State.aggregate",
  "Ternary.Trit",
  "Ternary.Trit.antipode",
  "Ternary.Word",
  "Ternary.Word.antipode_eq_self_iff",
  "Ternary.acceptCount",
  "Ternary.acceptCount_erases_direction",
  "Ternary.aggregate_not_factorsThrough_blockObs",
  "Ternary.binaryProject",
  "Ternary.binaryProject_not_separating",
  "Ternary.blockObs",
  "Ternary.blockObs_incomparable_aggregate",
  "Ternary.blockObs_not_factorsThrough_aggregate",
  "Ternary.blockwise_ne_global",
  "Ternary.card_fibre_blockObs",
  "Ternary.card_fibre_blockObs_allPos",
  "Ternary.card_image_blockObs",
  "Ternary.card_orbits_nine",
  "Ternary.card_orbits_three",
  "Ternary.card_orbits_two",
  "Ternary.card_stateOrbits",
  "Ternary.card_sumFibre",
  "Ternary.card_sumFibre_nine_zero",
  "Ternary.card_word",
  "Ternary.card_word_nine",
  "Ternary.centred_complement",
  "Ternary.centred_injective",
  "Ternary.direction_not_factorsThrough_acceptCount",
  "Ternary.encodeWithPolicy",
  "Ternary.encoding_of_unresolved_is_policy",
  "Ternary.half_complement_fixed",
  "Ternary.jointObs",
  "Ternary.jointObs_not_separating",
  "Ternary.jointObs_universal",
  "Ternary.no_canonical_binary_decision",
  "Ternary.rowCount",
  "Ternary.sum_rowCount",
  "Ternary.two_mul_card_orbits",
  "Ternary.two_mul_card_pairImage",
  "Wikidata.Admission",
  "Wikidata.Admission.trains",
  "Wikidata.Alignment",
  "Wikidata.Alignment.alignOk_iff",
  "Wikidata.BiparentalNuclearWitness",
  "Wikidata.ContextStatus",
  "Wikidata.Coordinate.covers_not_symmetric",
  "Wikidata.Coordinate.covers_not_transitive",
  "Wikidata.Coordinate.same_numbers_different_globe_do_not_match",
  "Wikidata.EdgeKind",
  "Wikidata.Example.artistKB",
  "Wikidata.Example.badAlignment_refuted",
  "Wikidata.Example.truthy_does_not_determine_evidence",
  "Wikidata.GenerationEvent",
  "Wikidata.GenerationEvent.progenitorCount",
  "Wikidata.Identity.functional_of_singleValue",
  "Wikidata.Identity.identity_does_not_entail_instance",
  "Wikidata.Identity.injective_of_distinctValue",
  "Wikidata.IsTruthy",
  "Wikidata.MergeCandidate",
  "Wikidata.ParentRole",
  "Wikidata.ParentRole.recorded_tag_is_lossy",
  "Wikidata.ParentRole.refine_preserves_genetic",
  "Wikidata.ParentRole.role_vocabulary_incomplete",
  "Wikidata.ParentRole.step_and_foster_collide",
  "Wikidata.Parenting.childVoiceObserver_not_separating",
  "Wikidata.Parenting.parentObserver_not_separating",
  "Wikidata.Parenting.parent_report_strictly_refined_by_child_voice",
  "Wikidata.Parenting.progressiveReopening_residual",
  "Wikidata.Parenting.route_not_factorsThrough",
  "Wikidata.Polarity.closedWorld_counterSupport_unsound",
  "Wikidata.Polarity.converse_opposition_not_uniform",
  "Wikidata.Polarity.counterposition",
  "Wikidata.Polarity.counterposition_not_opposes",
  "Wikidata.Polarity.crossBase_pool_manufactures_conflict",
  "Wikidata.Polarity.openWorld_pool_is_affirmation",
  "Wikidata.Polarity.painterArtist_has_no_references",
  "Wikidata.Polarity.painterArtist_import_not_resolved",
  "Wikidata.Polarity.requiredImportAxes",
  "Wikidata.Provenanced",
  "Wikidata.Quantity.amount_equality_is_not_quantity_agreement",
  "Wikidata.Quantity.overlaps_not_transitive",
  "Wikidata.Rdf.directTriples",
  "Wikidata.Rdf.reify",
  "Wikidata.RelationVector",
  "Wikidata.SingleGeneticSlots",
  "Wikidata.TimeValue.numeric_equality_is_not_time_agreement",
  "Wikidata.TimeValue.order_is_calendar_blind",
  "Wikidata.TimeValue.year_precision_does_not_determine_the_day",
  "Wikidata.Timed",
  "Wikidata.admitted",
  "Wikidata.answer_not_factorsThrough_unranked",
  "Wikidata.applied_merge_changes_instances",
  "Wikidata.cap_does_not_mean_exactly_two",
  "Wikidata.card_geneticParentsF_le_two",
  "Wikidata.classSurface_cannot_decode_editOrder",
  "Wikidata.classTransition_full_truthy",
  "Wikidata.conditional_distinction_preserved",
  "Wikidata.coverageIncomplete_does_not_train",
  "Wikidata.defect_not_factorsThrough_retrieval",
  "Wikidata.disclosure_is_independent",
  "Wikidata.donorConception_counts",
  "Wikidata.edgeFor",
  "Wikidata.empty_cohort_learns_everything",
  "Wikidata.enactMerge",
  "Wikidata.enactMerge_eq_of_gate_failed",
  "Wikidata.enactMerge_eq_of_not_approved",
  "Wikidata.exactly_two_requires_biparental_witness",
  "Wikidata.gate_not_factorsThrough_geometry",
  "Wikidata.genetic_does_not_confer_parenthood",
  "Wikidata.geometryOnly_fails_gate",
  "Wikidata.geometryOnly_never_edits",
  "Wikidata.gestation_does_not_confer_parenthood",
  "Wikidata.held_does_not_train",
  "Wikidata.inadmissible_context_is_masked",
  "Wikidata.incompatible_blocks_merge",
  "Wikidata.isSubclassOf_submit_shadowed",
  "Wikidata.layerObs",
  "Wikidata.layerObs_incomparable_sliceObs",
  "Wikidata.learned",
  "Wikidata.learned_append_subset",
  "Wikidata.learned_does_not_characterise",
  "Wikidata.learned_has_legitimate_exception",
  "Wikidata.learned_ignores_untrained",
  "Wikidata.mem_learned_iff",
  "Wikidata.membership_not_factorsThrough_signature",
  "Wikidata.mergeGate",
  "Wikidata.mergeMode",
  "Wikidata.mitochondrialReplacement_has_three_progenitors",
  "Wikidata.mitochondrial_does_not_confer_parenthood",
  "Wikidata.parenthood_does_not_require_genetics",
  "Wikidata.progeniture_is_not_parenthood",
  "Wikidata.recordedKB_eq",
  "Wikidata.recorded_statement_forgets_relation",
  "Wikidata.retrieval_not_factorsThrough_defect",
  "Wikidata.similarity_only_from_admissible",
  "Wikidata.sliceObs",
  "Wikidata.slot_does_not_determine_semantics",
  "Wikidata.triparental_has_three_progenitors",
  "Wikidata.truthyLayer",
  "Wikidata.unknown_context_is_not_similarity",
  "Wikidata.unresolved_does_not_train",
  "Wikidata.viewObs",
  "Wikidata.viewObs_not_separating",
  "Wikidata.viewObs_universal"
]

/-- The name list and the per-module counts agree. -/
theorem dashiTraced_length : dashiTraced.length = totalFor .dashi := by decide

end RequestProject.Meta

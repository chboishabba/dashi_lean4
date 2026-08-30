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
  { index := 0, name := "RequestProject.Agda.Prelude", declarations := 40, theorems := 14,
    dashi := 0, wikidata := 0, original := 40 },
  { index := 1, name := "RequestProject.Agda.Syntax", declarations := 11, theorems := 0,
    dashi := 0, wikidata := 0, original := 11 },
  { index := 2, name := "RequestProject.Agda.Verbatim", declarations := 45, theorems := 0,
    dashi := 0, wikidata := 0, original := 45 },
  { index := 3, name := "RequestProject.Epistemic.ContextErasure", declarations := 19, theorems := 9,
    dashi := 0, wikidata := 0, original := 19 },
  { index := 4, name := "RequestProject.Epistemic.Observer", declarations := 41, theorems := 27,
    dashi := 13, wikidata := 0, original := 28 },
  { index := 5, name := "RequestProject.Epistemic.Trit", declarations := 46, theorems := 34,
    dashi := 12, wikidata := 0, original := 34 },
  { index := 6, name := "RequestProject.Ternary.Balanced", declarations := 34, theorems := 24,
    dashi := 15, wikidata := 0, original := 19 },
  { index := 7, name := "RequestProject.Wikidata.Coverage", declarations := 25, theorems := 17,
    dashi := 0, wikidata := 0, original := 25 },
  { index := 8, name := "RequestProject.Wikidata.Reachability", declarations := 11, theorems := 8,
    dashi := 0, wikidata := 0, original := 11 },
  { index := 9, name := "RequestProject.Epistemic.Authority", declarations := 36, theorems := 21,
    dashi := 15, wikidata := 0, original := 21 },
  { index := 10, name := "RequestProject.Epistemic.Quotient", declarations := 27, theorems := 15,
    dashi := 14, wikidata := 0, original := 13 },
  { index := 11, name := "RequestProject.Epistemic.Tetralemma", declarations := 48, theorems := 33,
    dashi := 4, wikidata := 0, original := 44 },
  { index := 12, name := "RequestProject.Wikidata.Core", declarations := 32, theorems := 12,
    dashi := 1, wikidata := 31, original := 0 },
  { index := 13, name := "RequestProject.Wikidata.DerivationFibres", declarations := 47, theorems := 23,
    dashi := 0, wikidata := 11, original := 36 },
  { index := 14, name := "RequestProject.Epistemic.FourView", declarations := 27, theorems := 11,
    dashi := 0, wikidata := 0, original := 27 },
  { index := 15, name := "RequestProject.Epistemic.Lens", declarations := 23, theorems := 13,
    dashi := 0, wikidata := 0, original := 23 },
  { index := 16, name := "RequestProject.Epistemic.ObligationAuthority", declarations := 19, theorems := 11,
    dashi := 0, wikidata := 0, original := 19 },
  { index := 17, name := "RequestProject.Epistemic.ObserverJoin", declarations := 10, theorems := 9,
    dashi := 7, wikidata := 0, original := 3 },
  { index := 18, name := "RequestProject.Epistemic.Opposition", declarations := 31, theorems := 16,
    dashi := 14, wikidata := 0, original := 17 },
  { index := 19, name := "RequestProject.Ternary.Aggregate", declarations := 26, theorems := 15,
    dashi := 12, wikidata := 0, original := 14 },
  { index := 20, name := "RequestProject.Wikidata.Attribution", declarations := 41, theorems := 21,
    dashi := 0, wikidata := 6, original := 35 },
  { index := 21, name := "RequestProject.Wikidata.ClassAlgebra", declarations := 18, theorems := 10,
    dashi := 0, wikidata := 10, original := 8 },
  { index := 22, name := "RequestProject.Wikidata.Constraints", declarations := 48, theorems := 25,
    dashi := 0, wikidata := 48, original := 0 },
  { index := 23, name := "RequestProject.Wikidata.Diagnostics", declarations := 8, theorems := 3,
    dashi := 0, wikidata := 8, original := 0 },
  { index := 24, name := "RequestProject.Wikidata.Parenting", declarations := 83, theorems := 29,
    dashi := 20, wikidata := 38, original := 25 },
  { index := 25, name := "RequestProject.Wikidata.Redundancy", declarations := 15, theorems := 12,
    dashi := 0, wikidata := 15, original := 0 },
  { index := 26, name := "RequestProject.Wikidata.Values", declarations := 60, theorems := 37,
    dashi := 8, wikidata := 15, original := 37 },
  { index := 27, name := "RequestProject.Epistemic.AxisSupport", declarations := 26, theorems := 16,
    dashi := 9, wikidata := 0, original := 17 },
  { index := 28, name := "RequestProject.Epistemic.Bridge", declarations := 28, theorems := 16,
    dashi := 3, wikidata := 0, original := 25 },
  { index := 29, name := "RequestProject.Epistemic.Repair", declarations := 15, theorems := 10,
    dashi := 6, wikidata := 0, original := 9 },
  { index := 30, name := "RequestProject.Ternary.Base369", declarations := 39, theorems := 25,
    dashi := 15, wikidata := 0, original := 24 },
  { index := 31, name := "RequestProject.Wikidata.Alignment", declarations := 10, theorems := 4,
    dashi := 2, wikidata := 6, original := 2 },
  { index := 32, name := "RequestProject.Wikidata.DisjointUnionDiagnostics", declarations := 19, theorems := 9,
    dashi := 0, wikidata := 14, original := 5 },
  { index := 33, name := "RequestProject.Wikidata.Identity", declarations := 27, theorems := 15,
    dashi := 3, wikidata := 15, original := 9 },
  { index := 34, name := "RequestProject.Wikidata.Owl", declarations := 28, theorems := 11,
    dashi := 0, wikidata := 27, original := 1 },
  { index := 35, name := "RequestProject.Wikidata.ParentingAuthority", declarations := 30, theorems := 17,
    dashi := 3, wikidata := 0, original := 27 },
  { index := 36, name := "RequestProject.Wikidata.ParentingFibres", declarations := 46, theorems := 24,
    dashi := 2, wikidata := 9, original := 35 },
  { index := 37, name := "RequestProject.Wikidata.ParentingRoles", declarations := 16, theorems := 8,
    dashi := 5, wikidata := 2, original := 9 },
  { index := 38, name := "RequestProject.Wikidata.Provenance", declarations := 26, theorems := 19,
    dashi := 2, wikidata := 23, original := 1 },
  { index := 39, name := "RequestProject.Epistemic.Context", declarations := 7, theorems := 6,
    dashi := 1, wikidata := 0, original := 6 },
  { index := 40, name := "RequestProject.Epistemic.ParentingEvidence", declarations := 16, theorems := 10,
    dashi := 2, wikidata := 0, original := 14 },
  { index := 41, name := "RequestProject.Wikidata.AlignmentSafety", declarations := 22, theorems := 11,
    dashi := 0, wikidata := 4, original := 18 },
  { index := 42, name := "RequestProject.Wikidata.ClassExpressions", declarations := 28, theorems := 18,
    dashi := 0, wikidata := 0, original := 28 },
  { index := 43, name := "RequestProject.Wikidata.Learning", declarations := 61, theorems := 34,
    dashi := 32, wikidata := 22, original := 7 },
  { index := 44, name := "RequestProject.Wikidata.Qualifiers", declarations := 50, theorems := 24,
    dashi := 0, wikidata := 46, original := 4 },
  { index := 45, name := "RequestProject.Wikidata.Slices", declarations := 26, theorems := 23,
    dashi := 0, wikidata := 26, original := 0 },
  { index := 46, name := "RequestProject.Wikidata.Sparql", declarations := 39, theorems := 16,
    dashi := 0, wikidata := 38, original := 1 },
  { index := 47, name := "RequestProject.Epistemic.QueryEvidence", declarations := 9, theorems := 6,
    dashi := 0, wikidata := 0, original := 9 },
  { index := 48, name := "RequestProject.Epistemic.ValueEvidence", declarations := 17, theorems := 11,
    dashi := 0, wikidata := 0, original := 17 },
  { index := 49, name := "RequestProject.Wikidata.Examples", declarations := 47, theorems := 30,
    dashi := 3, wikidata := 25, original := 19 },
  { index := 50, name := "RequestProject.Wikidata.Layers", declarations := 25, theorems := 22,
    dashi := 1, wikidata := 24, original := 0 },
  { index := 51, name := "RequestProject.Wikidata.SparqlAggregation", declarations := 34, theorems := 24,
    dashi := 0, wikidata := 0, original := 34 },
  { index := 52, name := "RequestProject.Wikidata.SparqlNegation", declarations := 26, theorems := 19,
    dashi := 0, wikidata := 0, original := 26 },
  { index := 53, name := "RequestProject.Wikidata.SparqlPaths", declarations := 38, theorems := 24,
    dashi := 0, wikidata := 0, original := 38 },
  { index := 54, name := "RequestProject.Epistemic.Views", declarations := 23, theorems := 17,
    dashi := 1, wikidata := 0, original := 22 },
  { index := 55, name := "RequestProject.Wikidata.EvidencePolarity", declarations := 23, theorems := 15,
    dashi := 9, wikidata := 7, original := 7 },
  { index := 56, name := "RequestProject.Wikidata.NamedGraphs", declarations := 21, theorems := 14,
    dashi := 0, wikidata := 0, original := 21 },
  { index := 57, name := "RequestProject.Wikidata.Rdf", declarations := 33, theorems := 20,
    dashi := 2, wikidata := 31, original := 0 },
  { index := 58, name := "RequestProject.Wikidata.ViewJoin", declarations := 20, theorems := 9,
    dashi := 6, wikidata := 11, original := 3 },
  { index := 59, name := "RequestProject.Epistemic.PathEvidence", declarations := 10, theorems := 7,
    dashi := 0, wikidata := 0, original := 10 },
  { index := 60, name := "RequestProject.Epistemic.Surfaces", declarations := 21, theorems := 13,
    dashi := 1, wikidata := 0, original := 20 },
  { index := 61, name := "RequestProject.Wikidata.ExamplesLayers", declarations := 32, theorems := 24,
    dashi := 0, wikidata := 27, original := 5 },
  { index := 62, name := "RequestProject.Wikidata.Lens", declarations := 17, theorems := 13,
    dashi := 1, wikidata := 16, original := 0 },
  { index := 63, name := "RequestProject.Wikidata.ExamplesConflict", declarations := 17, theorems := 12,
    dashi := 0, wikidata := 11, original := 6 },
  { index := 64, name := "RequestProject.Wikidata.RdfInformationOrder", declarations := 12, theorems := 7,
    dashi := 0, wikidata := 9, original := 3 }
]

/-- The module dependency graph: `(a, b)` means a declaration of module `a`
uses a declaration of module `b`.  Read off the compiled environment. -/
def depEdges : List (Nat × Nat) := [
  (9, 4), (10, 4), (11, 5), (12, 8), (13, 5), (14, 11),
  (15, 5), (15, 11), (16, 9), (16, 11), (17, 4), (17, 10),
  (18, 11), (19, 4), (19, 5), (19, 6), (19, 10), (20, 5),
  (20, 11), (20, 13), (21, 12), (22, 8), (22, 12), (23, 12),
  (24, 8), (24, 12), (25, 12), (26, 12), (27, 9), (27, 11),
  (27, 16), (28, 5), (28, 12), (28, 21), (28, 23), (29, 5),
  (29, 12), (29, 25), (30, 4), (30, 6), (30, 10), (30, 17),
  (31, 12), (31, 21), (32, 12), (32, 21), (33, 12), (33, 22),
  (34, 12), (34, 23), (35, 4), (35, 9), (35, 12), (35, 24),
  (36, 4), (36, 10), (36, 12), (36, 24), (37, 12), (37, 24),
  (38, 12), (38, 23), (39, 5), (39, 12), (39, 38), (40, 5),
  (40, 9), (40, 10), (40, 12), (40, 24), (40, 35), (40, 36),
  (41, 12), (41, 21), (41, 31), (42, 12), (42, 21), (42, 38),
  (43, 10), (43, 12), (43, 29), (44, 12), (44, 26), (44, 38),
  (45, 12), (45, 23), (45, 38), (46, 12), (46, 38), (47, 5),
  (47, 12), (47, 38), (47, 46), (48, 5), (48, 12), (48, 26),
  (48, 38), (48, 44), (49, 5), (49, 12), (49, 21), (49, 23),
  (49, 25), (49, 28), (49, 29), (49, 31), (49, 38), (49, 39),
  (50, 12), (50, 38), (50, 45), (51, 12), (51, 38), (51, 46),
  (52, 12), (52, 46), (53, 8), (53, 12), (53, 38), (53, 46),
  (54, 5), (54, 12), (54, 28), (54, 38), (54, 45), (54, 50),
  (55, 11), (55, 12), (55, 18), (55, 27), (55, 28), (55, 38),
  (55, 49), (56, 12), (56, 38), (56, 45), (56, 53), (57, 12),
  (57, 50), (58, 4), (58, 10), (58, 12), (58, 17), (58, 45),
  (58, 50), (59, 5), (59, 12), (59, 38), (59, 53), (59, 56),
  (60, 5), (60, 12), (60, 22), (60, 28), (60, 57), (61, 5),
  (61, 12), (61, 22), (61, 28), (61, 33), (61, 49), (61, 50),
  (61, 54), (61, 57), (62, 5), (62, 12), (62, 15), (62, 50),
  (62, 57), (63, 5), (63, 11), (63, 12), (63, 15), (63, 49),
  (63, 50), (63, 57), (63, 62), (64, 12), (64, 57), (64, 62)
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
  "Wikidata.applied_merge_changes_instances",
  "Wikidata.cap_does_not_mean_exactly_two",
  "Wikidata.card_geneticParentsF_le_two",
  "Wikidata.classTransition_full_truthy",
  "Wikidata.conditional_distinction_preserved",
  "Wikidata.coverageIncomplete_does_not_train",
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

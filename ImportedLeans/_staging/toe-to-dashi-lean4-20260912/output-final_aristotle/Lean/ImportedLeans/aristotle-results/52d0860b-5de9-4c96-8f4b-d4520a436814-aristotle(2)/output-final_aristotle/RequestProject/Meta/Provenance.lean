import Mathlib

/-!
# The provenance ledger, machine-checked

This module is **generated** by `tools/provenance.py` from the Lean sources and
from the compiled kernel environment (`tools/DepDump.lean`).  It carries, as
data inside Lean, the numbers that the provenance report and the infographic
state informally:

* for every module of the development, how many of its declarations are traced
  to the DASHI Agda bridge (`chboishabba/dashi_agda` PR #555 / #581), how many
  render the Wikidata data model, and how many are original to this port;
* the module dependency graph, as it really is in the compiled environment.

The arithmetic claims are then *theorems* (`by decide`), so the ledger cannot
silently disagree with itself, and the dependency graph is proved acyclic.

Regenerate with

```
lake env lean tools/DepDump.lean && python3 tools/provenance.py
```
-/

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
  { index := 0, name := "RequestProject.Agda.Prelude", declarations := 24, theorems := 9,
    dashi := 0, wikidata := 0, original := 24 },
  { index := 1, name := "RequestProject.Agda.Syntax", declarations := 6, theorems := 0,
    dashi := 0, wikidata := 0, original := 6 },
  { index := 2, name := "RequestProject.Epistemic.ContextErasure", declarations := 19, theorems := 9,
    dashi := 0, wikidata := 0, original := 19 },
  { index := 3, name := "RequestProject.Epistemic.Observer", declarations := 41, theorems := 27,
    dashi := 13, wikidata := 0, original := 28 },
  { index := 4, name := "RequestProject.Epistemic.Trit", declarations := 46, theorems := 34,
    dashi := 12, wikidata := 0, original := 34 },
  { index := 5, name := "RequestProject.Wikidata.Reachability", declarations := 11, theorems := 8,
    dashi := 0, wikidata := 0, original := 11 },
  { index := 6, name := "RequestProject.Epistemic.Authority", declarations := 36, theorems := 21,
    dashi := 15, wikidata := 0, original := 21 },
  { index := 7, name := "RequestProject.Epistemic.Quotient", declarations := 27, theorems := 15,
    dashi := 14, wikidata := 0, original := 13 },
  { index := 8, name := "RequestProject.Epistemic.Tetralemma", declarations := 48, theorems := 33,
    dashi := 4, wikidata := 0, original := 44 },
  { index := 9, name := "RequestProject.Wikidata.Core", declarations := 32, theorems := 12,
    dashi := 1, wikidata := 31, original := 0 },
  { index := 10, name := "RequestProject.Wikidata.DerivationFibres", declarations := 47, theorems := 23,
    dashi := 0, wikidata := 11, original := 36 },
  { index := 11, name := "RequestProject.Epistemic.FourView", declarations := 27, theorems := 11,
    dashi := 0, wikidata := 0, original := 27 },
  { index := 12, name := "RequestProject.Epistemic.Lens", declarations := 23, theorems := 13,
    dashi := 0, wikidata := 0, original := 23 },
  { index := 13, name := "RequestProject.Epistemic.ObligationAuthority", declarations := 19, theorems := 11,
    dashi := 0, wikidata := 0, original := 19 },
  { index := 14, name := "RequestProject.Wikidata.Attribution", declarations := 41, theorems := 21,
    dashi := 0, wikidata := 6, original := 35 },
  { index := 15, name := "RequestProject.Wikidata.ClassAlgebra", declarations := 18, theorems := 10,
    dashi := 0, wikidata := 10, original := 8 },
  { index := 16, name := "RequestProject.Wikidata.Constraints", declarations := 48, theorems := 25,
    dashi := 0, wikidata := 48, original := 0 },
  { index := 17, name := "RequestProject.Wikidata.Diagnostics", declarations := 8, theorems := 3,
    dashi := 0, wikidata := 8, original := 0 },
  { index := 18, name := "RequestProject.Wikidata.Parenting", declarations := 83, theorems := 29,
    dashi := 20, wikidata := 38, original := 25 },
  { index := 19, name := "RequestProject.Wikidata.Redundancy", declarations := 15, theorems := 12,
    dashi := 0, wikidata := 15, original := 0 },
  { index := 20, name := "RequestProject.Epistemic.Bridge", declarations := 28, theorems := 16,
    dashi := 3, wikidata := 0, original := 25 },
  { index := 21, name := "RequestProject.Epistemic.Repair", declarations := 15, theorems := 10,
    dashi := 6, wikidata := 0, original := 9 },
  { index := 22, name := "RequestProject.Wikidata.Alignment", declarations := 10, theorems := 4,
    dashi := 2, wikidata := 6, original := 2 },
  { index := 23, name := "RequestProject.Wikidata.DisjointUnionDiagnostics", declarations := 19, theorems := 9,
    dashi := 0, wikidata := 14, original := 5 },
  { index := 24, name := "RequestProject.Wikidata.Identity", declarations := 27, theorems := 15,
    dashi := 3, wikidata := 15, original := 9 },
  { index := 25, name := "RequestProject.Wikidata.ParentingAuthority", declarations := 30, theorems := 17,
    dashi := 3, wikidata := 0, original := 27 },
  { index := 26, name := "RequestProject.Wikidata.ParentingFibres", declarations := 46, theorems := 24,
    dashi := 2, wikidata := 9, original := 35 },
  { index := 27, name := "RequestProject.Wikidata.ParentingRoles", declarations := 16, theorems := 8,
    dashi := 5, wikidata := 2, original := 9 },
  { index := 28, name := "RequestProject.Wikidata.Provenance", declarations := 26, theorems := 19,
    dashi := 2, wikidata := 23, original := 1 },
  { index := 29, name := "RequestProject.Epistemic.Context", declarations := 7, theorems := 6,
    dashi := 1, wikidata := 0, original := 6 },
  { index := 30, name := "RequestProject.Epistemic.ParentingEvidence", declarations := 16, theorems := 10,
    dashi := 2, wikidata := 0, original := 14 },
  { index := 31, name := "RequestProject.Wikidata.AlignmentSafety", declarations := 22, theorems := 11,
    dashi := 0, wikidata := 4, original := 18 },
  { index := 32, name := "RequestProject.Wikidata.Slices", declarations := 26, theorems := 23,
    dashi := 0, wikidata := 26, original := 0 },
  { index := 33, name := "RequestProject.Wikidata.Examples", declarations := 47, theorems := 30,
    dashi := 3, wikidata := 25, original := 19 },
  { index := 34, name := "RequestProject.Wikidata.Layers", declarations := 25, theorems := 22,
    dashi := 1, wikidata := 24, original := 0 },
  { index := 35, name := "RequestProject.Epistemic.Views", declarations := 23, theorems := 17,
    dashi := 1, wikidata := 0, original := 22 },
  { index := 36, name := "RequestProject.Wikidata.Rdf", declarations := 33, theorems := 20,
    dashi := 2, wikidata := 31, original := 0 },
  { index := 37, name := "RequestProject.Epistemic.Surfaces", declarations := 21, theorems := 13,
    dashi := 1, wikidata := 0, original := 20 },
  { index := 38, name := "RequestProject.Wikidata.ExamplesLayers", declarations := 32, theorems := 24,
    dashi := 0, wikidata := 27, original := 5 },
  { index := 39, name := "RequestProject.Wikidata.Lens", declarations := 17, theorems := 13,
    dashi := 1, wikidata := 16, original := 0 },
  { index := 40, name := "RequestProject.Wikidata.ExamplesConflict", declarations := 17, theorems := 12,
    dashi := 0, wikidata := 11, original := 6 },
  { index := 41, name := "RequestProject.Wikidata.RdfInformationOrder", declarations := 12, theorems := 7,
    dashi := 0, wikidata := 9, original := 3 }
]

/-- The module dependency graph: `(a, b)` means a declaration of module `a`
uses a declaration of module `b`.  Read off the compiled environment. -/
def depEdges : List (Nat × Nat) := [
  (6, 3), (7, 3), (8, 4), (9, 5), (10, 4), (11, 8),
  (12, 4), (12, 8), (13, 6), (13, 8), (14, 4), (14, 8),
  (14, 10), (15, 9), (16, 5), (16, 9), (17, 9), (18, 5),
  (18, 9), (19, 9), (20, 4), (20, 9), (20, 15), (20, 17),
  (21, 4), (21, 9), (21, 19), (22, 9), (22, 15), (23, 9),
  (23, 15), (24, 9), (24, 16), (25, 3), (25, 6), (25, 9),
  (25, 18), (26, 3), (26, 7), (26, 9), (26, 18), (27, 9),
  (27, 18), (28, 9), (28, 17), (29, 4), (29, 9), (29, 28),
  (30, 4), (30, 6), (30, 7), (30, 9), (30, 18), (30, 25),
  (30, 26), (31, 9), (31, 15), (31, 22), (32, 9), (32, 17),
  (32, 28), (33, 4), (33, 9), (33, 15), (33, 17), (33, 19),
  (33, 20), (33, 21), (33, 22), (33, 28), (33, 29), (34, 9),
  (34, 28), (34, 32), (35, 4), (35, 9), (35, 20), (35, 28),
  (35, 32), (35, 34), (36, 9), (36, 34), (37, 4), (37, 9),
  (37, 16), (37, 20), (37, 36), (38, 4), (38, 9), (38, 16),
  (38, 20), (38, 24), (38, 33), (38, 34), (38, 35), (38, 36),
  (39, 4), (39, 9), (39, 12), (39, 34), (39, 36), (40, 4),
  (40, 8), (40, 9), (40, 12), (40, 33), (40, 34), (40, 36),
  (40, 39), (41, 9), (41, 36), (41, 39)
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
  "Epistemic.HiddenTransition",
  "Epistemic.Observer",
  "Epistemic.PluralDynamicSafety",
  "Epistemic.PolicyExposedQuotientDefect",
  "Epistemic.PolicyRelativeSafety",
  "Epistemic.RepairOperation",
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
  "Epistemic.enact_eq_of_not_approved",
  "Epistemic.enact_eq_of_unsupported",
  "Epistemic.enact_redundancy_proposal_preserves_subclass",
  "Epistemic.enact_removeBadSuperclass",
  "Epistemic.exists_section_not_injective",
  "Epistemic.fibreConstantPred_pullback",
  "Epistemic.importEvidence_eq",
  "Epistemic.importSquare_ne_both",
  "Epistemic.merge_then_collapse_ne_collapse_then_merge",
  "Epistemic.not_factorsThrough",
  "Epistemic.not_injective_of_hiddenTransition",
  "Epistemic.not_plural_of_defect",
  "Epistemic.policyRelativeSafety_of_dynamicSafety",
  "Epistemic.pullbackPred",
  "Epistemic.pullbackPred_join",
  "Epistemic.pullbackPred_meet",
  "Epistemic.receiptState",
  "Epistemic.receiptState_ne_contradicted",
  "Epistemic.redundancyProposal_operation",
  "Epistemic.residualFibre_cons_ssubset",
  "Epistemic.residualFibre_cons_subset",
  "Epistemic.separatingFamily_iff_residualFibre_eq",
  "Epistemic.sliceClaim",
  "Epistemic.slot_evidence_cannot_route_authority",
  "Epistemic.support_does_not_confer_authority",
  "Epistemic.unresolved_left_never_conflicts",
  "Epistemic.verdictState",
  "Epistemic.verdictState_eq_contradicted_iff",
  "Epistemic.verdictState_notObserved",
  "Epistemic.viewClaim_layer_irrelevant",
  "Wikidata.Alignment",
  "Wikidata.Alignment.alignOk_iff",
  "Wikidata.BiparentalNuclearWitness",
  "Wikidata.Example.artistKB",
  "Wikidata.Example.badAlignment_refuted",
  "Wikidata.Example.truthy_does_not_determine_evidence",
  "Wikidata.GenerationEvent",
  "Wikidata.GenerationEvent.progenitorCount",
  "Wikidata.Identity.functional_of_singleValue",
  "Wikidata.Identity.identity_does_not_entail_instance",
  "Wikidata.Identity.injective_of_distinctValue",
  "Wikidata.IsTruthy",
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
  "Wikidata.Provenanced",
  "Wikidata.Rdf.directTriples",
  "Wikidata.Rdf.reify",
  "Wikidata.RelationVector",
  "Wikidata.SingleGeneticSlots",
  "Wikidata.Timed",
  "Wikidata.cap_does_not_mean_exactly_two",
  "Wikidata.card_geneticParentsF_le_two",
  "Wikidata.classTransition_full_truthy",
  "Wikidata.disclosure_is_independent",
  "Wikidata.donorConception_counts",
  "Wikidata.exactly_two_requires_biparental_witness",
  "Wikidata.genetic_does_not_confer_parenthood",
  "Wikidata.gestation_does_not_confer_parenthood",
  "Wikidata.mitochondrialReplacement_has_three_progenitors",
  "Wikidata.mitochondrial_does_not_confer_parenthood",
  "Wikidata.parenthood_does_not_require_genetics",
  "Wikidata.progeniture_is_not_parenthood",
  "Wikidata.recordedKB_eq",
  "Wikidata.recorded_statement_forgets_relation",
  "Wikidata.slot_does_not_determine_semantics",
  "Wikidata.triparental_has_three_progenitors",
  "Wikidata.truthyLayer"
]

/-- The name list and the per-module counts agree. -/
theorem dashiTraced_length : dashiTraced.length = totalFor .dashi := by decide

end RequestProject.Meta

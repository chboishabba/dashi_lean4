# Literal Clay Navier–Stokes terminal project

This nested project is pinned to Lean 4.34.0-rc2, matching the released
OpenAI Navier–Stokes proof, so it does not perturb the parent dashi_lean4
Lean 4.28 environment.

It vendors the independent semantic-gap audit's frozen `ClaySpec.lean`,
`Gap.lean`, and `Adapter.lean` with provenance, then adds
`LiteralABCD.lean`.

Terminal declarations:

- `DASHILiteralClayNS.ClayOptionA`
- `DASHILiteralClayNS.ClayOptionB`
- `DASHILiteralClayNS.ClayOptionC`
- `DASHILiteralClayNS.ClayOptionD`
- `DASHILiteralClayNS.literalClayC`
- `DASHILiteralClayNS.literalClayD`
- `DASHILiteralClayNS.literalAnyOneClayResolution`

Run:

```bash
cd ExternalClayNS
lake update
lake exe cache get
lake build
```

Pinned proof: openai/NavierStokesAndEuler@f9e8bc5b38b6e212696e8a30e3e91517af887bbd

Semantic bridge source:
francescoantoniodeluca/navier-stokes-formal-audit@c2e4f438f7af8bbf222a59801696aca2c3c15b6f


## Goal-1 submission audit

For the Clay-facing mathematical audit, do **not** treat the high-level
\`literalClayC\` / \`literalClayD\` aliases as the end of the provenance check.

\`SubmissionAudit.lean\` rebuilds both endpoints directly from the pinned source
theorem spines:

\`\`\`text
C:
NavierStokesR3.theorem_1_1
  -> NavierStokesR3.comparator_of_breakdown
  -> SemanticGap.ComparatorOptionC_to_ClayOptionC
  -> ClauseAuditC

D:
PeriodicPaper.periodic_corollary
  -> ComparatorBridge.option_D_of_paper_candidate
  -> SemanticGap.ComparatorOptionD_to_ClayOptionD
  -> ClauseAuditD
\`\`\`

It also prints the axioms of the source-level theorems and the direct Clay
endpoints at build time.

This project is an audit/certificate layer. A submission-quality mathematical
proof must still expose the source-specific construction, uniqueness argument,
terminal obstruction, and every official Fefferman hypothesis in readable
mathematics; the proof assistant is not a substitute for that exposition.

The independent A/B statements remain theorem-production targets rather than
being inferred from C/D.


## 15 November 2026 / TOE A/B/C/D source and physical-scope reconciliation

This nested Lean project is the **active C/D direct proof audit**. The
source-written theorem terms `SubmissionAudit.directClayC` and
`SubmissionAudit.directClayD`, their explicit clause audits, and
`LiteralABCD.literalAnyOneClayResolution` were already present before the
new staged auxiliary forced-global corollaries in the Clay rollup. The latter
do not close any new Clay question.

The exact source pin `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`
is one commit *newer* than older comparisons at `8937a8f4...`. Preserve
the manifest and the project-specific Lean `4.34.0-rc2` toolchain.
`lake build` must compile this project, including `SubmissionAudit` and
the printed transitive axioms. Source-text presence, a status Boolean, or
SymPy arithmetic is not this kernel receipt. Review each recovered proof
against the independent original problem statement and the current human
proof, particularly the pressure/periodicity, forcing, finite-energy class,
uniqueness and singular-time step.

The Golden Agda A/B/C/D and TOE (including whole-space ℝ³ Lane A physical
factor payment and periodic B R568/R650/R571/R854) are reconciled in
[ClayNSABCDTOER3OpenAIBidiReconciliation20261115.md](https://github.com/chboishabba/dashi_agda/blob/chatgpt/clay-20261112-four-frontier-fail-closed/Docs/roadmaps/ClayNSABCDTOER3OpenAIBidiReconciliation20261115.md).
The fail-closed paired driver is
`dashi_agda/scripts/check_ns_toe_abcd_pinned_local_20261115.sh`
(with `DASHI_CLAY_LEAN_WORKTREE` set to this repository checkout).

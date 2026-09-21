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

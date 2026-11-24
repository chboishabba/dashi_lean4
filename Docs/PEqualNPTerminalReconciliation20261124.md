# P versus NP: upstream proof corpus and terminal reconciliation (2026-11-24)

Upstream: https://github.com/brilliant-hq/pequalnp-proofs (Apache-2.0, upstream contributors retain attribution), pinned b3787c5889d7039ad509e5cb7306613325b70f49. Submodule: vendor/pequalnp-proofs. Upstream Lean v4.36.0; use its own lean directory, manifest, toolchain and checker. Do not replace DASHI's Lake graph. No kernel run claimed.

Canonical Agda owners: PNotEqualsNPClayCoreExact, PNotEqualsNPDirectSATLowerBoundExact, PNotEqualsNPHaltingResourceClosingTerminalExact, PNotEqualsNPQ1TerminalSemanticsDecisionFailureExact. Canonical roadmap: dashi_agda Docs/roadmaps/ClaySixMillenniumEndpointsExactRoadmap20261115.md. F1 classically closed, native model weld pending. F2 resource-closing compiler remains open; F3 universal SAT failure remains open and follows from universally inhabited F2, or an independent lower bound. Q1 opposite terminal semantics already contains a decision error, so do not use it as an independent premise for hardness.

Import priorities:
- L_meta_1397: projective-plane line OR, fan-in two AND/OR/NOT with at most s NOT gates, bound q*floor(q*(q+1-2^s)/2^(s+1)); truncated subtraction. Not arbitrary circuits or superpolynomial.
- MetaComplexity.L030: query-local parity-to-partial-MCSP obstruction; preserve locality, length and encoding hypotheses.
- Inspect shared computation, gate charging counterexamples and full-basis lifting; distinguish multi-output incidence from a uniform NP decision language.
- Reuse existing Agda Automata/KernelInternal, WetteConstructiveAutomatonExact, WetteFRACTRANCrossPollinationExact, SequentialGameFractranWolframCrossPollinationExact, FractranComputationEquivalence, residual lower bounds and concrete diagonal owners. Imported Agda source is not native Lean theorem authority. Prove exact encoding, simulation and ALL overhead costs before claiming transfer. Universality alone does not close F2.
- Native Lean terminal census currently marks PNP Agda-owned. Establish exact native SAT/standard model bridge from upstream definitions, then transport actual source theorems with their hypotheses; no invented equivalence.
- Acceptance: local submodule checkout at pin, upstream own toolchain/checker, independent DASHI build, axiom audit, same-object cross-model transport. No CI reliance. No P != NP claim.

YM separate: #1444 historical CMP102 donor roadmap read at 3f9c3c9eb3507c2a6ad34afa6f6bf2a4bd231add; points to master-based #1536 for original SU(N) F19 and W3. Preserve separate ownership; physical CMP119/122 T, absolute renormalized CMP116 W3 and same-H OS gap open. Do not merge divergent branches or conflate with PNP.

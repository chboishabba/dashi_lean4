# OpenAI math corpus source-index intake on Lean Clay #108

14 November 2026. Canonical Golden Agda corpus audit: [#1499](https://github.com/chboishabba/dashi_agda/pull/1499) — `Docs/roadmaps/OpenAIMathCorpusCrosswalk20261114.md`. Historical original Lean source and tests: [#78](https://github.com/chboishabba/dashi_lean4/pull/78).

This rollup copied the **original Git blob identities** of `Integration/OpenAIMath/UpstreamPin.lean` and `FullUpstreamMainResultsCatalogue.lean` from the old PR; then adds `Integration/OpenAIMath/ClayCrosswalkSourceIndex20261114.lean` and the dedicated import to `Synthesis/ClaySixFrontierRollup20261114.lean`. It does NOT merge the old PR's build graph, git submodule, or 4.34.1 code into the Lean 4.28 project.

The upstream vendored commit has **200 formalization main-result references** and **719 manuscripts / 372 families**; the later indexed revision has **208 source-qualified declaration references** and **721 manuscripts / 373 families**. Eight declaration references were added (CM Hodge, six local-smoothing comparators, SubexponentialSAT), none removed. This Lean module is a **metadata source-index theorem**, not 208 imported proof bodies.

Full historical source candidate owner routing and six semantic source reviews have been byte-identically transferred to the Golden #1499 branch, with a fail-closed local verifier. The earlier scan has 101/208 lexical candidates and 107 with none, with a **truncated Lean tree**; verified type/scope transports **0**. No claim of completeness of native-owner coverage.

Run locally against pinned Lean 4.28+Mathlib:
```sh
lake env lean Integration/OpenAIMath/FullUpstreamMainResultsCatalogue.lean
lake env lean Integration/OpenAIMath/ClayCrosswalkSourceIndex20261114.lean
lake env lean Synthesis/ClaySixFrontierRollup20261114.lean
```
Check `#print axioms` on new named theorems. Exact branch kernel/axiom acceptance not yet recorded. External 4.34.1 source build and 4.28 original theorem ports remain separate.

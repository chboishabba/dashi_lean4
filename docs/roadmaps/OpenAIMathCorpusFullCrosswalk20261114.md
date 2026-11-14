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


## Original Lean #78 source migration, 14 November

The remaining 35 original PR #78 paths (all **except** the exact
`UpstreamPin.lean` and `FullUpstreamMainResultsCatalogue.lean` already
imported) are now staged in this **same Lean rollup #108**, including
source-level Lean `ListFinsetCNFTransport` proofs, OAI 378 version-gated
finite-CNF/bit-length/fixed-machine adapters, the full five index files,
the original 13 scripts, attribution docs, exact original `.gitmodules`
and **original Git submodule** `vendor/openai-math-src` at its fixed
`1581d4cb...` commit. Historical file SHA IDs are preserved, not
rewritten; any conflicting same-path target must be separately reconciled.

**The source is now available in one PR**, but the older gitlink does not
contain the 8 post-vendor additions. The separate `PIN_378.json` and
`materialize_openai378_toolchain.sh` are required to fetch newer proof
source. `Upstream378FiniteCNFBridge.lean` still imports OAI-specific
source modules absent from the lean-4.28 ambient library and is intentionally
**not** imported by `Synthesis/ClaySixFrontierRollup20261114.lean`.
New safe-ambient source root:
`Integration/OpenAIMath/ClayCrosswalkLeanSourceRollup20261114.lean`.
This stages generic algebraic source, **not a compiler/kernel receipt**.

The historical PR #78 can be retained as provenance rather than serving
as a second active source implementation PR. Agda #1499 holds the full
8 native original Circuit/CNF modules and 3 source tests from donor #1212,
the 721/373/208 machine indices, six exact source-read comparisons and
local fail-closed auditor. The remaining bridge **M00–M05** (actual
Agda source ↔ OAI machine input), primitive time/all-prefix visited space,
and both pinned kernel/axiom checks remain OPEN.


## Exact original terminal theorem types: 14 November independent cross-rollup audit

Golden Agda [Clay #1499](https://github.com/chboishabba/dashi_agda/pull/1499)
now carries a reproducible 13-source theorem-signature audit at
`Docs/roadmaps/ClaySourceVerifiedExistingVsOpen20261114.json`, and a
fail-closed offline checker `scripts/check_clay_existing_vs_open_source_20261114.py`
incorporated into the one six-frontier local acceptance driver. This
is **not a formal absence theorem**, and no current Agda or Lean kernel
receipt is claimed.

The Lean files themselves confirm important paid intermediates:

- `Synthesis/RiemannA2ActualSelectedIntervalDecisionExact.lean` has
  genuine original W/rho/n interval PASS and NO-GO results. Both
  depend on explicit source interval bounds (`hd,hf,hc,hm,hgap`) that
  must come from the actual zeta-zero source. No unconditional RH or A2
  contradiction follows.
- `Synthesis/NavierStokesR854RealTimeIntegratedRateConditionalExact.lean`
  proves a real-time negative integral **given**
  `hOriginalRateEnvelope` for the selected `rate`. A physical
  original R71/R853 real Galerkin rate producer has not been supplied.
- `Synthesis/MillenniumBSDCMOriginalK1Q2H1SameSourceConvergence.lean`
  proves selected E[2]-H1/local fragments. The real/Q2 classical
  Kummer exact sequence remains separate.
- `Synthesis/MillenniumBSDCMActualEBarRestrictedShaTwoTargetExact.lean`
  defines the actual E(Qbar)-coefficient Sha[2] subgroup, but the
  classical Selmer/Sha cokernel identification and original selected
  BSD coefficient theorem remain unproved at this interface.
- `Integration/OpenAIMath/ClayCrosswalkSourceIndex20261114.lean`
  proves an indexed **208-declaration List length**, not 208 imported
  Lean math proof terms.

The Agda consumer audit finds explicit `false` closure flags at R736
and R240, and a conditional physical input `DirectSourceOSLiteralClayInputs`
for the original Yang-Mills literal Clay solution compiler. This
is consistent with the independent review of OpenAI's October 2026
Yang-Mills existence-only candidate, which still needs the original
DASHI F19/R445 Wilson family correspondence before E1 reuse. D1/D2
remain new physical estimates.

The highest-value work is now to produce original carrier hypotheses
for the **existing** theorem consumers, not to build additional
terminal-interface scaffolding. Preserve one rollup PR per repo.

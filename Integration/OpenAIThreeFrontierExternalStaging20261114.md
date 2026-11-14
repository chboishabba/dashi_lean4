# OpenAI / DASHI 2026 cross-pollination: external Lean staging (not native imports)

This directory's foreign-source adapters are deliberately NOT imported by
native DASHI Lean 4.28.0 `Synthesis.lean` or its Clay #108 acceptance root.
They are proof CANDIDATES, not accepted results. Golden source authority and
the 26-row A/B/C ledger (the grouped Karp F1–F4 row contains four gates):
[Agda Clay #1499: ClayOpenAIThreeFrontierBidirectionalSteelman20261114.md](https://github.com/chboishabba/dashi_agda/blob/chatgpt/clay-20261112-four-frontier-fail-closed/Docs/roadmaps/ClayOpenAIThreeFrontierBidirectionalSteelman20261114.md).

## Source-pinned compilation (each independent toolchain)

### OAI YM 28 Oct (Lean 4.32.0)
- Checkout `yang-mills-group/OpenAI-YM-20261028@3456e5e75cf8d4cd558955a5c7638fba2d68f464` and review `yang-mills-group/YM@55ba9fc36293b3f4d52c6b1f813169a0be76ee98`.
- Stage `Integration/OpenAIYangMills32/CombinedA7A8SameWitnessCandidate.lean` into the review's buildable `checks/` import path and run its pinned review Lean toolchain. Check that `Accepted.source` contains `hpublic.ope` at exactly the needed hierarchy `YangMills.hierarchy F Q`.
- Run `#print axioms` for both new theorems, and independently replay original A7/A8 endpoints. Do not mistake a source file for successful compilation.

### OAI NS Sept (Lean 4.34.0-rc2)
- Checkout `openai/NavierStokesAndEuler@8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`.
- Stage `Integration/OpenAINavierStokes34/ForcedGlobalScopeCorollariesCandidate.lean` alongside its root module in the upstream package and run `lake env lean` in that exact toolchain.
- Check C/D theorems and full `ComparatorDefinitions` against the original official statement and the *current* human manuscript; inspect `#print axioms`. Proven C/D implies no universal **forced** regularity in exact comparator classes, not a disproof of unforced B.

### OAI #SAT 25 Oct (Lean 4.34.1)
- Checkout the **later index** `openai/math@7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`. The native DASHI submodule is pinned to the *earlier* `1581d4cb...`; do not silently substitute it.
- Stage `Integration/OpenAIMath34/OriginalListFinsetCountTransportCandidate.lean` in that upstream Lean package's source root and run `lake env lean`, then `#print axioms`.
- Prove list→Finset same literal/index/polarity, CNF semantics, model count, canonical clause sorting and **bitstream equality**. The candidate proves only the first two at the exact OAI SAT type, pending kernel. It does NOT transfer OAI machine runtime into DASHI.

**Causal order:** foreign theorem kernel → exact original semantic equivalence → cost/limit transport → physical or universal Clay endpoint. Never upgrade source-level or finite rational PASS into Lean/Agda checker success.

**Attribution:** OpenAI retains the mathematical results in its source repositories and 2026 papers; FormalConjectures retains comparator definitions; YM committee members retain independent review credit; earlier Cook--Levin/Tseitin, Wilson/Haar and Navier--Stokes/PDE results retain their historical attribution. DASHI here authors only the proposed cross-language/source adapters, independent checks and auditing.


## 15 November: NS external project already pays C/D typed semantic transport

Correction: the older staged `Integration/OpenAINavierStokes34/ForcedGlobalScopeCorollariesCandidate.lean` is now **strictly a redundant logic sidecar**. Our already-existing actual C/D audit project is `ExternalClayNS`, using independent `ClaySpec.lean`, `Gap.lean`, `ClauseAudit.lean`, `ProvenanceAudit.lean`, `SubmissionAudit.lean`, and `LiteralABCD.lean`. That nested project's `lakefile.toml` pins OpenAI `NavierStokesAndEuler@f9e8bc5b38b6e212696e8a30e3e91517af887bbd` and `lean-toolchain` pins `4.34.0-rc2`. The upstream comparator source `8937a8f4...` cited in the earlier staged note is one commit **older**.

The direct source proof route already supplies `SubmissionAudit.directClayC`, `directClayD`, `directClauseAuditC`, `directClauseAuditD`, and `dualRouteReceipt`, and `LiteralABCD.literalAnyOneClayResolution` is an existing source-level theorem. No additional C/D formal declaration is required for the Clay-facing comparison; the remaining P0 is **a clean exact-head nested lake build and transitive #print axioms**, then independent manuscript/source semantic review (the user prefers local verification over CI).

The Agda Golden TOE A/B/C/D and R³ reconciliation ledger is [ClayNSABCDTOER3OpenAIBidiReconciliation20261115.md](https://github.com/chboishabba/dashi_agda/blob/chatgpt/clay-20261112-four-frontier-fail-closed/Docs/roadmaps/ClayNSABCDTOER3OpenAIBidiReconciliation20261115.md), with a strict source + optional-kernel script `scripts/check_ns_toe_abcd_pinned_local_20261115.sh`. Exact SymPy checks are legitimate finite/reference algebra, **never** Lean/Agda kernel acceptance.

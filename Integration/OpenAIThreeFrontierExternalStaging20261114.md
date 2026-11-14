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


## 15 November 2026: recovered original NS and YM donors, source-corrected Clay maximum cut

**Agda Clay #1499** now coalesces 172 exact historical PR #1129 P≠NP machine/quotation/streaming Cook–Levin owners as immutable source blobs, plus the complete PR #1271 original R734 six-mode **physical no-go against unrestricted universal W2** and the historic YM #1440 R320→R313→R333 OS same-source compiler. Neither an impossible universal W2 assumption nor a SAT universal lower-bound witness is to be inserted into Lean as an axiom. See [canonical Agda recovered maxcut](https://github.com/chboishabba/dashi_agda/blob/chatgpt/clay-20261112-four-frontier-fail-closed/Docs/roadmaps/ClayRecoveredProducersW2NoGoR856SourceMaxCut20261115.md).

This canonical Lean rollup #108 adds:
- `Synthesis/NavierStokesR855SharpRealTimeConditionalExact.lean`: **exact optimal integer affine envelope** on the ORIGINAL Agda R829/R854 constants, with next integer failing and a conditional *real-time* rate-negativity consumer; the physical Galerkin solution and actual R853 source derivative estimate remain OPEN. The scalar theorem must be replayed on pinned native Lean 4.28, not substituted for a PDE theorem.
- `Synthesis/YMFiniteRangeGibbsExteriorCancellationExact.lean`: algebraically normalizes a finite *conditional* Gibbs density so any x-independent exterior-only factor cancels exactly, yielding zero distant conditional influence when the bare plaquette locality premise is actually satisfied. This is the finite-sum case, **not** a proof of original compact Haar/SU(N) physical blocked-effective versus renormalized target TV, R320 clustering or a continuum YM gap.

Both source candidates are included from `Synthesis/ClaySixFrontierRollup20261114.lean`. Check `lake env lean` on the exact local native root and inspect `#print axioms`; no kernel receipt was produced in the current runtime. Historic [Lean #7](https://github.com/chboishabba/dashi_lean4/pull/7) `Welds.YMSourceClusteringGap` and `Welds.YMClayAssembly` are already byte-identical in #108 and must not be reintroduced as “new” spectral-gap mathematics. OpenAI external YM 4.32 / NS f9e 4.34.0-rc2 / SAT 4.34.1 staged projects retain foreign-toolchain isolation and original-source attribution.

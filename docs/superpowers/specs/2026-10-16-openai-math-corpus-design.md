# OpenAI Math Corpus Integration Design

## Goal

Integrate OpenAI's October 2026 mathematics corpus into DASHI as a pinned, attribution-preserving upstream theorem source without collapsing manuscript claims, upstream Lean proofs, DASHI Lean ports, or Agda receipts.

## Upstream pin

- Repository: `openai/math`
- Commit: `1581d4cbdd69a0faf34b2089614fe2a814316a6a`
- License: Apache-2.0
- Upstream Lean toolchain: `leanprover/lean4:v4.34.1`
- Upstream formalization catalogue: `lean/formalization.yaml`
- Upstream Lean root: `lean/OAI.lean` / `lean/OAI/`

The pin is immutable evidence. Later upstream updates create a new receipt rather than rewriting the meaning of an older receipt.

## Authority firewall

DASHI must preserve the strict chain

```text
OpenAI manuscript claim
!= OpenAI formalization catalogue entry
!= upstream Lean declaration
!= upstream kernel-check receipt
!= DASHI Lean same-object port
!= DASHI Lean kernel-check receipt
!= Agda imported-formal-source receipt
!= Agda theorem
```

A shared title, theorem statement, mathematical object, identifier, or upstream verification label never collapses these levels.

## Vendor architecture

The complete upstream corpus is represented by a content-addressed vendor pin rather than copied into the ordinary DASHI Lean package. OpenAI's formal library has its own Lean/mathlib/dependency closure and therefore remains hermetic. DASHI records the upstream repository, commit, license, toolchain, manifest/catalogue locations and expected vendor path. A checkout helper may materialize the pinned corpus under `vendor/openai-math/`, but normal DASHI imports do not transitively import or retarget that environment.

This design avoids replacing DASHI's toolchain or mathlib merely to consume the donor corpus.

## Lean ingress

`Integration/OpenAIMath/` owns four layers:

1. `UpstreamPin.lean`: immutable pin/license/toolchain/catalogue constants and authority firewalls.
2. `FormalizationStatus.lean`: proof-relevant status vocabulary separating manuscript, catalogue, upstream declaration, upstream kernel receipt, DASHI port and DASHI kernel receipt.
3. `PriorityAtlas.lean`: a bounded relevance atlas for DASHI's live research programmes. It is routing metadata, not imported theorem authority.
4. `Everything.lean`: focused public rollup.

A future theorem-specific promotion module must identify the exact upstream declaration and exact local statement/object transport before marking a theorem `dashiPorted` or stronger.

## Agda ingress

`DASHI/Research/OpenAIMath/` records the same immutable upstream pin and cross-prover authority boundary. Agda may record an upstream Lean theorem as an imported formal theorem source, but no Lean proof object is treated as an Agda proof. Agda-local theorem promotion requires an Agda proof or an explicitly trusted cross-kernel mechanism defined separately.

The Agda layer should reuse the repository's existing attribution discipline and expose a focused `Everything.agda` rollup.

## Relevance routing

Initial relevance classes are deliberately coarse:

- `directFrontier`: likely to discharge or sharpen a currently named DASHI theorem frontier.
- `lemmaDonor`: useful mathematical infrastructure or local lemmas.
- `independentCrossCheck`: alternate formal treatment useful for comparison but not direct import.
- `backgroundOnly`: no present theorem-level consumer.

Initial named DASHI programmes include RH, BSD, Hodge, Yang-Mills, Navier-Stokes, P versus NP, elliptic/CM arithmetic, exceptional geometry/representation theory, quantum mathematics, Fourier/harmonic analysis and finite/combinatorial mathematics. Classification is revisable and creates no mathematical implication.

## Update receipts

Every future pin advance should record:

```text
old upstream SHA
new upstream SHA
upstream Lean version
formalization catalogue identity
families/declarations added, removed or changed
DASHI theorem-specific promotions affected
```

No current theorem loses its provenance because upstream `main` moves.

## Testing and max-cut

The implementation is test-first at the source boundary: regression owners are created before production owners and initially fail because the production import is absent. Since this execution environment does not provide a local checkout/compiler, this tranche does not claim Lean/Agda kernel success. The max-cut is source architecture, immutable pinning, attribution firewalls, focused rollups, vendor materialization contract, and a prioritized promotion surface.

CI/kernel execution is explicitly not a blocker for this user-requested tranche, but no green claim may be fabricated.

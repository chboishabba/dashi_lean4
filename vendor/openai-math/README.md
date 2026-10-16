# OpenAI Math vendor boundary

The complete upstream repository `openai/math` is vendored as the Git submodule `vendor/openai-math-src`, pinned by the superproject gitlink to one exact upstream commit.

Current pin:

- repository: `https://github.com/openai/math`
- submodule path: `vendor/openai-math-src`
- commit: `1581d4cbdd69a0faf34b2089614fe2a814316a6a`
- license: Apache-2.0
- upstream Lean toolchain: `leanprover/lean4:v4.34.1`
- formalization catalogue: `lean/formalization.yaml`

Materialize and verify the exact pin with:

```bash
bash scripts/materialize_openai_math_vendor.sh
```

The checkout is intentionally hermetic. Do **not** copy its `lean-toolchain`, `lake-manifest.json`, or package graph over DASHI's own Lean environment. Verify upstream formalizations in the upstream checkout, then create theorem-specific DASHI adapters that identify the exact upstream declaration and exact local same-object transport.

The materialized upstream tree retains its own Apache-2.0 `LICENSE` and upstream attribution/notice material. OpenAI and upstream contributors retain authorship of their manuscripts and formalizations; DASHI owns only its pinning, routing, adapters, local theorem transports, and synthesis.

Authority firewall:

```text
manuscript claim
!= formalization catalogue row
!= upstream Lean declaration
!= upstream kernel-check receipt
!= DASHI Lean port
!= DASHI kernel-check receipt
!= Agda imported-formal-source receipt
!= Agda theorem
```

The gitlink is the canonical repository-level vendor receipt. The submodule is deliberately not imported transitively by DASHI Lean source.

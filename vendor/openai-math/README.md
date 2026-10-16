# OpenAI Math vendor boundary

This directory is the designated materialization point for the pinned upstream repository `openai/math`.

Current pin:

- repository: `https://github.com/openai/math`
- commit: `1581d4cbdd69a0faf34b2089614fe2a814316a6a`
- license: Apache-2.0
- upstream Lean toolchain: `leanprover/lean4:v4.34.1`
- formalization catalogue: `lean/formalization.yaml`

Materialize with:

```bash
bash scripts/materialize_openai_math_vendor.sh
```

The checkout is intentionally hermetic. Do **not** copy its `lean-toolchain`, `lake-manifest.json`, or package graph over DASHI's own Lean environment. Verify upstream formalizations in the upstream checkout, then create theorem-specific DASHI adapters that identify the exact upstream declaration and exact local same-object transport.

The materialized upstream tree must retain its Apache-2.0 `LICENSE` and any upstream attribution/notice material. OpenAI and upstream contributors retain authorship of their manuscripts and formalizations; DASHI owns only its pinning, routing, adapters, local theorem transports, and synthesis.

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

This README is tracked; the materialized vendor checkout itself should remain out of ordinary DASHI source imports and should not be committed wholesale without a separate explicit vendoring decision.

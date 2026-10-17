# OpenAI Math integration

This namespace is DASHI's attribution-safe ingress for the pinned `openai/math` corpus.

It does **not** import the upstream Lean project into DASHI's normal package graph. The upstream project is pinned at commit `1581d4cbdd69a0faf34b2089614fe2a814316a6a` and retains its own Lean 4.34.1 environment. Use `scripts/materialize_openai_math_vendor.sh` to create a hermetic checkout when upstream verification or theorem-specific porting is required.

The public boundary is `Integration.OpenAIMath.Everything`.

Promotion order is deliberately explicit:

```text
manuscript -> catalogue -> upstream declaration -> upstream kernel receipt
           -> DASHI same-object port -> DASHI kernel receipt
           -> Agda imported-formal-source receipt -> Agda theorem
```

Arrows are obligations, not automatic conversions.

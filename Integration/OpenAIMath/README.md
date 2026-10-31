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

## 31 October 2026 — Complete indexed upstream inventory, NOT complete theorem ports

Source-audited against **live** `openai/math` README, CONTENTS and `lean/formalization.yaml`: **721 manuscripts, 373 result families**. The upstream machine-readable `status.main_results` list has **208 individual declaration entries across 192 comparator configuration identifiers**; these are not one-to-one family counts and the YAML itself says `scope: Partial progress.` Upstream README warns that not every result is formalized, and not every formalization should be confused with its broader paper.

`FullUpstreamMainResultsCatalogue.lean` now indexes **all 208 actual upstream declarations** with exact comparator, declared symbol and file under current YAML blob `372bcd714cd3a186a9139ac8e0f3318961fb2df1`. An independent same-turn GitHub-source readback compared every row to upstream: **208/208 exact, 0 omissions, 0 extras, identical order**. This does not imply 208 independent DAG-proof ports; the original small `SourceAtlas` remains the curated semantic-routing owner. Do NOT insert the complete index into `Everything.lean` before an exact toolchain build. `scripts/audit_openai_main_result_catalogue.py` runs offline against an explicit upstream `lean/formalization.yaml` checkout and detects drift; its regex parser was checked locally against a representative YAML/Lean pair. The index source itself has not been typechecked.

**Math integration (P3) source-only:** `ListFinsetCNFTransport.lean` generically preserves clause truth, global CNF truth, finite model counts, normalized clause upper count and width. **NEW separate upstream-378 staging** `Upstream378FiniteCNFBridge.lean` binds that generic result to the ACTUAL upstream `SAT.Literal (Fin n)`, `SAT.count`, `SAT.WidthAtMost 3`, and `Encoding.formulaBitLength_upper`, with an explicit bound
`L ≤ n+2+(24*n+28)*(3*g+1)`. This module REQUIRES the newer original OpenAI Lean4.34.1 source; our pinned vendor at `1581d4cb...` predates it and DASHI's mathlib still targets 4.28. This is not imported and has **NO Lean kernel receipt**. Its source does not finish the executable source circuit→Lean normalization adapter, actual fixed-machine time or all-prefix visited space.

**High-alpha existing owners without semantic conflation:** original #1040 Agda circuit semantics, #1212 finite counting + #1212 earlier `OpenAIMathSharedTseitinUniqueExtensionExact` (the canonical uniqueness owner, now reused instead of a duplicate), #1438 native 27-node bipartite grid/54-edge weighted Max-Cut and QID firewall, #1414 distinct 27-functions/11-orbit/7-even+4-odd Fourier chart; external OAI comparators `SubexponentialSAT`, `OptimalMaxCut`, `UniqueGamesTheorem`, `ExactFourier`, `UniformFourier`, `QuasiRiemannHypothesis`, `HodgeConjectureCMAbelianVarieties`, `VlasovMaxwell` are **separate source routes**. Mathematical parallels, numerology, and shared labels do not imply same-object ports, solutions to RH/Clay YM/twin-prime infinitude, or an identified Monster action.

**Attention:** the current upstream YAML now records `HodgeCM.hodge_conjecture_for_cm_abelian_varieties` at `ComparatorChallenges/HodgeConjectureCMAbelianVarieties/Solution.lean`, which was directly inspected. The older pinned `SourceAtlas.hodgeCM` is `manuscript` on that earlier vendor; that historic state should not be silently rewritten as a pinned theorem. Current unpinned upstream proof status is tracked separately pending vendor update and kernel checks.

**Actual missing few-hundred-proof integrations:** the 208 upstream declaration references have been indexed. For each result that matters, still record exact pinned source revision, formalized theorem statement, original author/date, proof dependency/axiom check, in-repo earlier stronger owner comparison, same-object implication, executable/Agda or Lean acceptance receipt, and TOE/QID consumer only when mathematically warranted. The other 373 families have not been individually theorem-ported. This is a programme with real mathematical obligations, not a tally of catalogue names.


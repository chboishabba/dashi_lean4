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


## Executable DAG-to-upstream-378 binary frontend (31 Oct)

`scripts/compile_dashi_circuit_openai378.py` is a **standalone executable** conversion from a JSON serialization of the original DASHI circuit gate carrier to the source-optimized Tseitin clauses and the **actual** current OpenAI `Encoding.lean` structure. Gate sources use `{"type":"input","index":i}` or `{"type":"gate","index":creation_order_id}`, with strictly earlier references. The output wire uses the same format.

Exact source structure: source gate list ⟶ 1/2/3 clause templates ⟶ literal code `2*variable+polarity` ⟶ sets of literal codes / sets of clauses ⟶ ascending sorted numeric clause/literal lists ⟶ unary `encodeNat` and framed nested `encodeList` ⟶ bitstream `Encoding.encodeCNF` style. The frontend reports source/normalized clause counts, width, bit length, the formula `n+2+(24*n+28)*(3*g+1)` upper bound, and the exact bit sequence. This does NOT evaluate a SAT oracle or enumerate assignments, and is not a new Agda semantics owner. It intentionally preserves duplicate/tautological clause syntax in `Finset` semantics instead of applying additional `SAT.normalize` rewriting, so the exact `encodeCNF` target is well defined.

Usage: `python scripts/compile_dashi_circuit_openai378.py circuit.json --out encoding.json`. This source file has **not** been executed from an exact GitHub checkout. An independently written local Python checker passed **1,485 source DAGs**, **104,720 full Boolean assignments** and encoding/decoding round trips; 795 cases had source clauses that collapsed after literal-set normalization. Source-level bound satisfied in all fixtures. These are executed finite checks, not Agda/Lean kernel or fixed-TM step/space certificates.

The outstanding theorem is now exactly the same-object equivalence between this executable frontend, Agda's source `optCircuitCNF` and the updated `OAI.Algorithms.SubexponentialSAT.SAT.CNF` AND a certified cost-preserving compiler into the fixed primitive machine of `SqrtLogSpace.Final`. Lean4 4.28/DASHI old vendor pin versus upstream 4.34.1 remains unresolved; do not import staged `Upstream378FiniteCNFBridge` until compiled with its actual dependencies.


**Last quantitative source cut:** upstream exact encoding bound can be simplified using `g≤n` to
`Encoding.formulaBitLength(toUpstreamCNF clauses) ≤ 72*(n+1)^2` for n = total input+gate variable count, provided `clauses.length≤3*g+1` and width≤3. Source-written Lean declaration: `Upstream378FiniteCNFBridge.upstreamQuadraticBitLengthBound`; **kernel NOT run**. Executable Python frontend now also asserts the quadratic bound for each actual generated bitstring. Independent local audit rerun PASS 1,485 circuits/104,720 full assignments, including exact framing decode. This bounds **input encoding length** only, not the fixed primitive machine's uniform construction time, square-root-log runtime or prefix space.

**Further actual fixed-machine interface**: version-gated `Upstream378FiniteCNFBridge.sourceListExactCountMachine` now source-writes the actual current upstream `SqrtLogSpace.exact_count_and_sat 3` *fixed-machine witness* restricted to source **lists of clauses**, rewrites its output count/SAT tapes to our generic `countedListModels` by `exactUpstreamCount`, and retains the SAME primitive execution trace, exact `runtimeBound` and every-prefix `visitedSpace` constraint. It does NOT assert a new machine, change the exponent, or invent runtime from an oracle. Inspected actual upstream `Computation.lean`, `BinaryArithmetic.lean`, `VisitedTape.lean`, `EncodingBounds.lean` and `Final.lean` to correct namespace spellings. This is SOURCE-WRITTEN, **Lean kernel NOT RUN**. Combining this with DASHI Agda P2 still requires exact type-and-program identity and a formal executable frontend transducer with resource bounds; the Python emitter alone is not an Agda/Lean proof.


## 31 October — fixed comparator budget and native ternary-grid SAT test

The executable original-DAG frontend `scripts/compile_dashi_circuit_openai378.py` now canonicalizes literal lists and clauses using **explicit deterministic ordered insertion**, with no Python hashing/sorting oracle. For `m` source 3-CNF clauses, it reports `literal_comparisons` and `clause_comparisons` and checks their sum is ≤`6m+m(m−1)/2`; each compared tuple has ≤3 codes <`2v`. The actual checkout-native deterministic `scripts/check_openai378_frontend_exact.py` regression now exercises the exact script. That regression was committed but **not executed from GitHub checkout**. Independent local Python PASS compared to canonical `sorted(set())` semantics in 10,735 arbitrary bounded-width CNFs + 2,430 original-source gate-template cases, including matching bitstreams and the same bound. This is a comparison-operation count, not a primitive TM bit-comparison resource proof.

`scripts/check_openai378_27grid_maxcut_bridge.py` is a genuine **cross-owner reuse** fixture: the native #1438 27-vertex / 54-edge `unitNativeGridEdges` adjacency is compiled as a shared original source Boolean DAG (27 inputs, 27 shared NOT gates, 3×54 per-edge XOR gates and 53 shared AND gates), giving 242 gates and 700 three-literal-or-less CNF clauses. Connected bipartiteness gives precisely two proper colourings; the independent local Python check PASS produced 700 normalized clauses, a 1,515,935-bit actual encoded string, 188,225 ordered insertion comparisons (budget 248,850) and two witnessed accepted inputs among 2,502 checked colourings. This is **not** arbitrary graph Max-Cut hardness, nor the unrelated #1414 27-function/11-orbit Fourier carrier. Formal Agda same-object graph→DAG theorem and exact #SAT=2 proof are outstanding.

The newer-upstream-only `Upstream378FiniteCNFBridge` also contains `sourceRuntimeWithinQuadraticInputBudget` and `sourceVisitedSpaceWithinQuadraticInputBudget`, direct source-written envelopes for the **same original 378 machine** with `L≤72(v+1)^2`. No exact 4.34.1 Lean kernel acceptance or fixed-machine frontend preprocessing trace. This source remains excluded from the Lean 4.28 authority spine.

See [Golden Agda exact 39-obligation ledger](https://github.com/chboishabba/dashi_agda/blob/integration/openai-math-corpus/docs/superpowers/plans/2026-10-31-openai-math-exact-lemma-maxcut-ledger.md) for every remaining source proof, kernel, same-object, and analytic terminal certificate.


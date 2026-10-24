# Cross-prover 369 hyperfabric / TOE physical max-cut (2026-10-24)

Scope: `chboishabba/dashi_lean4` integration handoff to [Agda hyperfabric PR #1249](https://github.com/chboishabba/dashi_agda/pull/1249), [Agda TOE PR #1217](https://github.com/chboishabba/dashi_agda/pull/1217) and [Lean TOE PR #80](https://github.com/chboishabba/dashi_lean4/pull/80). This is a **source audit and max-cut**, not a new TOE ontology, a claim that unmerged code is in `main`, or a kernel proof in Lean.

## Existing Lean theorem owners: these already replace generic proposed work

- [Lean #80](https://github.com/chboishabba/dashi_lean4/pull/80), exact inspected head `eafbf232ad74e2dad04db65772434f8151a3907e`: `Integration/DASHITOE/{Core,C3Graph,PrimitiveMaxCut,QuantumInhabitants,GaugeInhabitants,ConcreteInhabitants}.lean`. The partial 369/C3 candidate and *primitive* source ownership are already present. Not a fully physically inhabited TOE.
- [Lean #47](https://github.com/chboishabba/dashi_lean4/pull/47), head `84cec84d4d3afa35a17b6049c7705d8152b207b1`: mathematical finite E6/E8/F4 and generic simple/semisimple/FDRep, isotypic `Hom_E` and normalizer-action compilers. They do **not** supply actual selected Monster full-grade linear action, source-specific zeta restriction or actual 12+78 induced intertwiner.
- [Lean #61](https://github.com/chboishabba/dashi_lean4/pull/61) and [#76](https://github.com/chboishabba/dashi_lean4/pull/76): selected finite quantum atlas, one-global-state marginals, general `*\`-subalgebra/commutant g-TPS source, HS projectors and finite infinitesimal metric. The physical selected Hamiltonian and state/observable same-object identification, minimizer pullback, thermodynamic limit and spacetime recovery remain stronger.
- [Lean #68](https://github.com/chboishabba/dashi_lean4/pull/68), head `1b3772daa785d29f119e1a8ce92764819e12b941`: corrected recursively defined independent Bell-tree RT equality and *nonempty-domain flat* `Lambda=0` Jacobson/Einstein model. These are real declared-benchmark source constructions, **not** nonflat emergent-gravity or AdS/CFT proofs.
- [Lean #69](https://github.com/chboishabba/dashi_lean4/pull/69), head `b4e3dfae0098c6cea800282b6c7f55c126cb1336`: genuine `Z[omega]` norm-shell, `j=0` elliptic CM point-group, inert-prime local Euler factor, selected split-Jacobi compiler. Split-side same-prime Frobenius, Hecke/Groessencharacter and BSD rank/Ш links remain distinct.
- [Agda #1105](https://github.com/chboishabba/dashi_agda/pull/1105), [#1162](https://github.com/chboishabba/dashi_agda/pull/1162), [#1239](https://github.com/chboishabba/dashi_agda/pull/1239): source-specific GF729 selecting action, Monster 3B representation-native and C27 on-cube charge/vertex-mode physical max-cuts. These are **sibling sources**, not local Lean proof terms.
- [Agda #1165](https://github.com/chboishabba/dashi_agda/pull/1165) and [#1241](https://github.com/chboishabba/dashi_agda/pull/1241): selected Casimir/QFT/GR and 5D KK radion source/model spines. Real selected action, common-metric variation, physically compatible matter and final observational constraints remain candidate-dependent.

Attribution: standard finite-product graph/Fourier identities, Heisenberg representation, Hilbert-space quantum walks, Polyakov worldsheet theory, Lorentzian geometry and sourced physics remain prior art. DASHI additions are specific formalizations, counterexamples, transport and provenance constraints. Neither repo's other open PR is promoted to a merged local theorem.

## Critical type/count disambiguation

| Object | Source carrier | Meaning and common false inference |
|---|---|---|
| 27-site hypervoxel | Agda `Base369Ternary27HypervoxelFabricGeometryExact` | `{-1,0,+1}^3` points on path graph `P3^3`, **54 edges** |
| 27 spectral charges | Agda #1239 `Monster27VOACubeWeightedChargeNoGoExact` | 27 eigenspace labels of Monster 27A/B on selected `Vnatural_2`; charge chart is **not** spatial adjacency |
| T^27 relational global section | Agda #1133 `TrialecticT27NativeC3RealizationExact` | **27 trit coordinates**, `3^27` ambient possible values; policy-completed subtype has 18 free coordinates, not 27 physical sites |
| GF729 / `F3^6` / 729-dimensional irrep | Agda #1105, #1162 and Lean #47 | selected field structure and action; no canonical identification with a product of two path Cube27s |
| 729 spatial product pairs | Agda #1249 free path-Laplacian test | `P3^6=P3^3 × P3^3` graph points; `27×27=729`, but not automatically a field or irreducible Monster linear representation |
| 19,683-site product | original 369 interaction/appraisal state count / Agda #1249 selected path-product test | `3^9=27^3=19683`; same count alone does not equate semantic and spatial factor dynamics |

**Signed zero**: `-0/0/+0` are oriented fine states with one scalar-zero observation, **not** alternative complex zero amplitudes, observable outcomes, or canonical physical helicity charges. Preserve the projection fibre when translating to selected quantum algebras.

## Stronger concrete finite operator donor from Agda #1249

For the **original path** graph on n ternary coordinates `P3^n`, define graph Laplacian `L_n`. Between `n=k` and `n=k+3`, define
`I f(x,y)=f(x)` and `R F(x)=3^-3 sum_{y in {-1,0,1}^3} F(x,y)`.
Then the product path edges give exactly
```
R ∘ I = id
L_(k+3) ∘ I = I ∘ L_k
R ∘ L_(k+3) = L_k ∘ R
```
for any real/rational field on the stated grids. The Agda PR records exact-arithmetic tests for `3→6` and `6→9` coordinates, alongside the exact 27-site path standing-wave basis and unitary `exp(-iπL_3)`. This is a *free mathematical operator* commuting-square on actual spatial adjacency, stronger than matching 27/729 cardinalities. It is not automatically a physical renormalization, gauge-invariant QFT, or string/GR construction.

**Negative physical control:** change one added-direction path-edge family to transport sign `-1`; then for constant `1`, the naive coarse pullback/average gives `R L_A I(1)=4/3` while ordinary `L_k 1=0`. To use a selected gauge connection, replace naive scalar restriction with parallel-transport-compatible physical data or explicitly bound that residual. Similarly the periodic `C3^3` Fourier eigenmodes do not diagonalize `P3^3`'s Laplacian; do not confuse representation labels with operators.

Reproduction on Agda PR #1249:
```bash
python3 scripts/check_hyperfabric_wave_geometry_cut.py
python3 scripts/check_hyperfabric_path27_quantum_walk.py
python3 scripts/check_hyperfabric_27_729_19683_refinement.py
```

## Updated physical terminal owners and roadmap phases

| Phase | Deliverable / target | Proof/evidence status and acceptance |
|---|---|---|
| G0 **Genealogy** | exact source/provenance receipt from chosen actual 27,729,T27,Monster and Lean quantum/TOE owners | this audit maps live heads; no implicit branch merge |
| G1 **Finite spectral** | certify original-path standing waves, `C^27` unitary and 27/729/19683 Laplacian restriction | finite arithmetic tests exist; next **Lean/mathlib or Agda kernel term** should encode the actual Laplacian squares and the twisted-link no-go, not create new generic `C3` |
| G2 **Selected matter action** | check finite candidate of Lean #80 against actual source Hamiltonian, Hilbert/g-TPS state, on-site or charged Monster links | *typed exact same-physical-object intertwiner* and observable match; absence must block physical claim |
| G3 **Spacetime** | attach chosen smooth 3+1 metric/causal structure and stress derived by the **same action**; treat #68's flat vacuum as already-closed benchmark | nonflat Einstein-matter solution, conserved renormalized stress, causal/Cauchy and Newtonian recovery; no elevation from flat `Lambda=0` |
| G4 **Strings (optional)** | choose actual `Sigma,h,X` worldsheet, Polyakov sigma-model action, B/dilaton and quantum gauge anomaly/modular/Weyl consistency; controlled target-space low-energy limit | not discharged by 5D KK, a VOA module, braiding, or the 2D toy energy alone. A concrete source model and consistency check required before coupling |
| G5 **YM/NS** | feed operator-specific evidence directly into canonical Agda **source** owners, not cross-domain carrier analogies | YM: CMP109 source and R114/R119/R122/R124/R127 plus cutoff-uniform OS/mass gap; NS: physical A/B, B4 R440, continuation. These are **open** |
| G6 **Arithmetic other Clay** | exploit Lean #69 actual Eisenstein CM in BSD if same curve, RH only with actual zeta and signed estimate; Hodge/P≠NP with original algebraic/complexity claims | source-specific full-theorem obligation needed; ternary analogy proves none |

### Highest-alpha handoffs (do not overindex on quantum/Monster)

1. **Finite exact theorem**: promote `R L_n=L_k R` and `L_n I=I L_k` on the *original* path hypervoxel and the charged-link counterexample to kernel-certified mathematical facts, using existing Lean finite graph/linear-algebra library if feasible. No new abstract 369 framework needed.
2. **Actual matter bridge**: in #80/#1217, try to identify **the selected interacting Coulomb 369 Hamiltonian** with the same 27-site path Hamiltonian or prove a mismatch/residual. A mathematically legal `C^27` basis does not mean the physical Hamiltonian is the graph Laplacian.
3. **Monster charge and spatial locality**: use #1239's proven charged-edge no-go and either build charged VOA modes/compensating links or retain the fully onsite alternative. Actual source-specific 729 irrep/90 multiplicity action requires #1105/#1162/#47 primitives, not `Fin729` coercion.
4. **Direct Clay**: YM and NS remain mathematically higher priority than the optional string branch until their literal source physical estimates or explicit counterexamples are paid. RH/BSD/Hodge/P!=NP are consumers only where an actual same-object theorem is produced.

**Certification**: no Lean/Lake executable was used here; all cross-PR references are *source-reported and inspected*, not newly verified local Lean or Agda kernel receipts. Exact source-head branch drift must be rechecked before merge/rebase. Keep this ledger adjacent to #80's `Integration/DASHITOE/PrimitiveMaxCut.lean`, not in a competing theory ontology.


## 2026-10-24 gauge correction from Agda #1249

The earlier `4/3` defect arises from taking an **ordinary average in a pure-gauge sign-twisted background**. It cannot be called a nontrivial physical flux. The Agda donor now constructs `Z2` site signs `g` and exactly compatible covariant maps `I_A=G I` and `R_A=R G`, so `L_A I_A=I_A L` and `R_A L_A=L R_A`. A *distinct* square with exactly one negative `Z2` edge has gauge-invariant Wilson holonomy `-1`, and an exhaustive four-vertex check rules out a global nonzero parallel `±1` section. This supplies a genuine finite gauge curvature negative control. It does **not** establish SU(2) YM, any continuum mass gap, or a string anomaly.

The exact committed Agda donor `scripts/check_hyperfabric_27_729_19683_refinement.py` (Git blob `e9c2e52af6d986b8aa584ea3f3f5f875a7e14a0b`) was executed locally and all 5 finite checks passed. Lean theorem extraction should target the existing mathlib graph Laplacian, gauge-compatible restrictions and Wilson plaquette product where appropriate; **do not** merely copy boolean test flags as new Lean proofs.

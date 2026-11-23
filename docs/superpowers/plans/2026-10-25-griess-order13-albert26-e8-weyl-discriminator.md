# Max-cut 2026-10-25: Griess order 13 really acts on Albert27 and traceless26; cannot act on E8 Weyl roots
Owner PR: [Lean #52](https://github.com/chboishabba/dashi_lean4/pull/52). Companion [Agda #1239](https://github.com/chboishabba/dashi_agda/pull/1239). Prior positive exceptional-group carrier [Lean #47](https://github.com/chboishabba/dashi_lean4/pull/47), [Agda #1098](https://github.com/chboishabba/dashi_agda/pull/1098).

## Origin / epistemic requirement

The original user prompt was surprise at **883/8** lying near **888/8**, followed by "what algebra actually governs the 512 coefficient triality mismatch?" and requests to cross-pollinate Griess/Monster, Ibrahim, 369, and later the already built **243→240** carriers. The original Peirce-coordinate mismatch is basis-dependent; SO8 rotation by a chosen 60 degrees produces 888/8 but is not canonically selected. The *proper product-preserving related triple* gives **zero** invariant Gram-corrected residual: previous independently checked 512 triality and 729 rational Albert basis products, without Lean kernel status.

The strongest source consequence to date: Griess's original 1990 `g(x,y)` defines a commutative nonassociative 81-element Moufang loop whose associator equals the F3^3 determinant. Its corrected SL3 shears are real source automorphisms, not coordinate-only analogies.

## P0 positive: actual order-13 rational Albert automorphism

Choose the **three source-corrected** Griess M81 shears e01, then e12, then e20. The true order-13 phase lift maps homogeneous original Albert basis elements as `e_x → omega^h(x) e_(Mx)`; the central correction h is required and was verified against the original Griess 1990 product formula. It preserves the original tau-real rational 27D Albert subspace, **not merely 27 complex grade labels**.

Independent exact source-equivalent Python, consuming the existing direct original Griess Q(omega) product checker and the 27×27 rational source-to-native certificate, has actually executed and **PASSED**:

1. All **729 original rational Griess Jordan basis products** under S, plus the unchanged tau-real involution/real-form basis.
2. `S^13=I`; for all k=1..12, `trace(S^k)=1`; `charpoly S=(X−1)^3 Phi13(X)^2`.
3. Transport to literal native rational Cayley-Dickson Albert `N=A*S*A^-1`. All **729 actual native Jordan basis products** under N; `N^13=I`, native Albert unit fixed, and positive trace Gram preserved.

Exact local generator: `/mnt/data/check_griess1990_order13_actual_albert.py`; downloadable finite 27×27 source and native matrices: `/mnt/data/griess1990_actual_albert_order13_certificate.json`.

**Lean source:** `Integration/Griess1990Moufang81ActualAlbertOrder13.lean` reuses existing `Griess1990Moufang81Explicit13Cycle`, `Griess1990OriginalHomogeneousFormula`, `Griess1990RationalTrialityFiniteProduct`, `Griess1990RationalTrialityMatrixWitness`, and literal `RationalAlbertNative`, with source grade→Q(omega) τ-real matrix formula and complete 729 native basis-product proof targets. **Source written, kernel NOT run**. Independent canonical source-equivalent checker added identically to both Lean #52 and Agda #1239: `scripts/check_griess1990_order13_actual_albert_and_traceless26.py`; committed exact blob NOT replayed in local runtime.

## P0 positive: the SAME traceless Albert 26, not another 26-cardinality proxy

Decompose the actual native 27D Albert Q-vector space by its trace:
`J = Q·1 ⊕ J_0`, `dim_Q J_0 = 26`.
Use literal 27×26 traceless column basis `[e0−e1, e1−e2, off12(8),off20(8),off01(8)]`. The order-13 automorphism fixes the actual Albert unit and preserves trace; hence J0 inherits the **same native** action B, with verified coordinate intertwiner `N P=P B`, exact inverse projection QP=I26, and native trace preservation.

Because `χ27=(X−1)^3 Φ13^2` and the unit is one 1-eigenvector, **`χ26=(X−1)^2 Φ13^2`**, fixed dimension2, two 12D irreducible rational cyclotomic blocks, nontrivial powers trace0. The **26=2×13 arithmetic** from Ibrahim is now compared to a *real automorphism module*, but the actual decomposition is `2+12+12`, **NOT two 13-dimensional irreducibles** or a six-dimensional spatial Hamiltonian. This is genuinely stronger than a numerical bridge.

**Lean source:** `Integration/Griess1990AlbertOrder13Traceless26.lean` declares the actual selected native traceless basis, 26D operator, finite trace/transport/order/trace-power targets, **source written, kernel NOT run**. Local `/mnt/data/check_griess1990_order13_traceless26.py` verified the exact 27×26 embedding and B; the 26D cyclotomic formula was DEDUCED using the independently checked 27D charpoly and standard Q-cyclotomic theory, not recomputed through expensive symbolic det26. Native 26 matrix `/mnt/data/griess1990_order13_traceless26_certificate.json`.

## P0 negative: same-action ORIGINAL 240 is not E8 Weyl roots

Earlier T5: `243=3+240`; a reversible original kernel chart `T5≃M81×F3`, diagonal line maps to `{1_M}×F3`. The three-shear source lift acts on old240 and has exact cycles `6×1 + 18×13 = 240`. It is a faithful nontrivial action, not the later structured E8 root carrier. Local exact full six-shear group `|G|=151632=2^4*3^6*13`; the **short 3-shear 13-cycle** suffices.

Classical fixed E8 root-system automorphism/Weyl order: `696729600=2^14*3^5*5^2*7 ≡ 8 (mod 13)`. Hence there can be **NO equivariant bijection** preserving THIS Griess original240 action and the E8 ROOT-WEYL action. This no-go is strong and mathematically complete conditional only on the original source word; neither numerical `240` equality nor F4/Monster sector analogies override it.

Lean #52 `Integration/Griess1990Original240E8WeylPrime13Obstruction.lean` states the numeric nondivisibility and generic Mathlib Lagrange no-injective-group-hom. `Integration/Griess1990Moufang81Explicit13Cycle.lean` states source cycle and original240 finite proof targets. Agda #1239 `DASHI/Moonshine/Griess1990Moufang81ExplicitThirteenCycleExact.agda` gives actual source M81 shear definitions, 81 source constructor cases, charted Kernel5 selected action and exact Weyl quotient/remainder arithmetic. **Lean/Agda kernel UNCHECKED**. Source-equivalent Python **PASSED** exact original M81 cycles `3×1+6×13`, original240 cycles `6×1+18×13`, cochain negative control and W(E8) no13.

NO-GO IS SCOPED: not against arbitrary bijections of cardinal240, not against arbitrary newly chosen operators, not against continuous algebraic E8 elements not preserving a selected root system, not against the actual rational Albert/F4 automorphism constructed above, not against selected Monster/VOA or physical observables.

## Original authorship and source roles (retain individually)

- **Robert L. Griess Jr.** (1990), *A Moufang loop, the exceptional Jordan algebra, and a cubic form in 27 variables*, J. Algebra 131 (1990), 281–293, DOI `10.1016/0021-8693(90)90176-O`: owns original source polynomial, 81-loop, exceptional Albert construction.
- Classical **Cartan/Coxeter/Weyl/Bourbaki** and modern independent source **Rosa Winter & Ronald van Luijk** (2021), *The Action of the Weyl Group on the E8 Root System*, Graphs and Combinatorics 37:1965–2064, DOI `10.1007/s00373-021-02315-8`: root automorphisms/Weyl order; not newly discovered by DASHI.
- **Alsaody–Gille (2019)** and **Barry–Tignol (2023)**: related-triple octonion and triality donors, distinct from the specific algorithm or Griess source polynomial.
- **Chen–Lam–Shimakura (2018)**: published authentic Monster `Vsharp≅Vnatural` Z3-orbifold, a DIFFERENT infinite VOA; no canonical same-object map from 27D Albert to this selected Monster 3B eigensector has been paid.
- **Ibrahim A027907**, N. J. A. Sloane and the original McGarvey/Foster/Riordan contributor provenance: path-cube trinomial row and numerical 13/26/52/78 roles only; not mathematical authority for the Griess automorphism or E8 obstruction.

## Pareto / max-cut after this result

1. **High-value POSITIVE OPEN (formal verification):** kernel compile exact original Griess phase→27D rational source tensor, source→native 729 Jordan map, and concrete order13 automorphism, using the *existing* typed Lean proof owners. Instantiate and kernel-check Agda original source/native same-object transport; no duplicate algebra owners.
2. **High-value NEGATIVE CLOSED computationally:** original old T5-240 ≠ structured E8 Weyl-root SAME SOURCE ACTION because explicit 13-cycle and Weyl lacks 13. Move on; repeated numerical 240 charts have near-zero information gain.
3. **P1 subsequent:** tighter 26D rational cyclotomic unit/fixed eigenspace proof by kernel, and selected genuine Monster VOA 3B action on the same literal VOA, keeping 196884D weight-two VOA Griess separate.
4. **P2:** F4 original-Q group recognition, sources/actors, trialitarian classifications if useful. This order13 *Jordan automorphism* does not by itself prove full Aut_Q(J) classification.
5. **P3:** physical 369 adjacency, KK, AdS3/string or RH remain separate, with user attribution/firewall rules enforced.

**No Lean, Lake or Agda binary available in the runtime**, and no GitHub committed source was falsely promoted to a checked theorem. Independent local Python exact computation (matrices, products, rational trace and unit) is strong, but not a substitute for kernel proof.

## 2026-10-26 actual latest-PR refresh: native punctured27 PG13 ↔ Albert26 C13

**New source discovery (not a new duplicate cube):** Agda crystallography #1261 has `Punctured27NineSheetBridgeExact`, `docs/crystallography_13_in_27_antipodal_diamond_crosspr_20261026.md`, and the existing 13-axis/B3 regression; hyperfabric #1249 ALREADY OWNS the original path-cube antipode/involution/path-edge action, and Ibrahim owns the 1+26/2×13 shape chart. The recent #1261 script was **not executable as first fetched**, because two `\\n` sequences occurred literally outside strings; fixed on #1261 with commit `88848b4e` before adding the directed projective-graph holonomy checks.

**True SAME underlying F3³ grade/projective carrier:** 26 native nonzero cube points `F3³\{0}` have 13 antipodal lines with orientation bit and support strata 3 [100]+6 [110]+4 [111]. A canonical first-nonzero-positive normalisation gives a reversible **26 ↔ (13×Bool) SET** chart. The original graph has 27v/54e; punctured graph 26v/48e; antipodal quotient **13v/24e** (12 edges support1↔2 + 12 edges support2↔3), DIFFERENT from `PG(2,3)` point-line incidence of **52 flags** on the same 13 points. The spatial quotient's edge-sign cocycle has a **four-edge odd XOR holonomy** `[100]→[110]→[010]→[1,-1,0]→[100]` with edge bits 0,0,1,0, so no globally edge-compatible oriented 13-site section. Independent exact local `/mnt/data/check_pg13_cube26_orientation_holonomy.py` PASS. Agda #1249 new `DASHI/Unified/HyperfabricPunctured27Projective13OrientationExact.agda` consumes the actual native antipode, with 26 source-written two-sided `refl` reductions, 26 antipode reductions, four ACTUAL native edge constructors and 16-case XOR no-section proof (**Agda kernel not run**). Existing #1261 graph regression corrected and extended in place.

**Strongest POSITIVE mathematical upgrade:** The selected Griess 1990 order13 automorphism on these 26 nonzero grades has **two genuine 13-cycles**. Its FREE Q-VECTOR SPACE has a two-cycle permutation matrix P. From the *ACTUAL* preexisting 26D traceless native rational Albert operator B, explicit 26×26 cyclic basis X = `[e0,Be0,...,B^12e0 | e1,Be1,...,B^12e1]` satisfies **B X = X P**, exact **det(X) = -729/4096 ≠ 0** (local independent SymPy PASS with intentional B-mutation rejection). Thus these are genuinely isomorphic as **Q[C13] modules**, not just equal dimensions; each 13D permutation module reduces to 1+12 over Q, so Albert J0 decomposes 2+12+12. It does NOT identify the finite 26-site SET with a Q26 VECTOR SPACE, spatial graph adjacency with Jordan multiplication, an actual Monster 3B VOA constituent, a physical bosonic string 26D target, or a different source actor. Lean #52 new `Integration/Griess1990Projective13PuncturedCube27SameGrade.lean` and `Integration/Griess1990Punctured27Albert26Order13Intertwiner.lean` import ACTUAL original Grade and previous B; finite Lean proofs source-written, **no Lean kernel run**. Standalone local exact checker `/mnt/data/check_griess1990_punctured27_albert26_C13_intertwiner.py` PASS against previous 26D rational JSON certificate.

**Sharp negative action discriminator:** same source-actor sends original P3³ edge `(0,0,0)~(0,1,0)` to `(0,0,0),(1,1,1)`, not adjacent; therefore the positive rational C13 module equivalence does not give a graph automorphism or original-Laplacian intertwiner. The older original T5 240 vs structured E8 Weyl fixed-root 13-no-go is separate and remains intact.

**Full focused Pareto/source ledger**: [Lean #52 2026-10-26 punctured27/PG13/Albert26](https://github.com/chboishabba/dashi_lean4/blob/agent/albert-jordan-f4-maxcut-20261007/docs/superpowers/plans/2026-10-26-griess-punctured27-projective13-albert26-equivariant-maxcut.md); [Agda #1261 crystal companion](https://github.com/chboishabba/dashi_agda/blob/feat/tetragonal-d4h-exact-20261025/docs/crystallography_punctured27_pg13_orientation_albert26_C13_maxcut_20261026.md). P0 kernel acceptance of original Griess source→native 729 Jordan product and C13/26 basis plus Agda actual antipoidal codec/holonomy. Source-original Griess Jr. 1990 DOI 10.1016/0021-8693(90)90176-O, classical PG2(3)/B3/Maschke, inherited Ibrahim A027907 Sloane/McGarvey/Foster/Riordan provenance, newer source donor PR #1261 crystal and PR #1249 graph, distinct Chen–Lam–Shimakura Monster Z3 VOA. **Do not collapse source, calculation, source-written proof, kernel receipt, empirical action or physical inference.**

# Griess (1990) Moufang-81 / projective-13 / 883-to-888 max-cut
Date: 2026-10-25. Canonical owner: [Lean PR #52](https://github.com/chboishabba/dashi_lean4/pull/52); original Agda/Ibrahim companion [Agda PR #1239](https://github.com/chboishabba/dashi_agda/pull/1239).

## 0. Recover the actual user trigger and its stop rule

The user was struck that a *selected, nonorthonormal coordinate comparison* of 512 Albert triality coefficients produced `883/8`, only `5/8` below `888/8=111`. They asked **why, what would force exactly 888, and what original source/object controls this**. The accompanying handoff also discovered the EXISTING attributed Chen--Lam--Shimakura actual V#≅Vnatural three-sector Moonshine VOA source owner. Do not replace that question with generalized 369/Monster/KK/RH numerology.

Exact source-selected original map had raw coefficient residual `883/8`. A particular *noncanonical* SO8 rotation produces `R_raw(theta)=(893-10cos(theta))/8`, and `theta=60°` gives 888/8, **without retaining both raw tensor norms or proving a forced overlap 121/16**. Invariant Gram-corrected original residual was 29/2; the explicit Q-rational **related triple** in existing Lean #52 yields **zero**, 512 source triality coefficients and 729 full original-to-native Jordan basis products, from exact source-equivalent local algebra. Product residual zero is the structural acceptance test. No additional 888 fitting remains on the Pareto frontier.

## 1. Source roots, snowball, and noncollapsible independence

| Priority | Original source and date | What it actually supplies | What it DOES NOT supply |
| --- | --- | --- | --- |
| P0 mathematical source | **Robert L. Griess Jr.**, *A Moufang loop, the exceptional Jordan algebra, and a cubic form in 27 variables*, J. Algebra **131** (1990), 281–293, DOI [10.1016/0021-8693(90)90176-O](https://doi.org/10.1016/0021-8693(90)90176-O) | Actual F3³ graded 27D Albert product, polynomial g, commutative Moufang quotient of order81/exponent3, normalizer A⋊SL3(3), associated cubic / 3E6(C) context | Selected Monster VOA 3B same-element action, physical cube adjacency |
| P0 structure donor | **S. Alsaody, P. Gille**, *Isotopes of octonion algebras, G2-torsors and triality*, Adv. Math. **343** (2019), 864–909, DOI [10.1016/j.aim.2018.12.003](https://doi.org/10.1016/j.aim.2018.12.003) | Octonion isotope / rational composition algebra and related-triple background | Specific computed DASHI 27×27 source map or proof imported into Lean |
| P1 targeted follow-up | **D. Barry, J.-P. Tignol**, *Trialitarian triples*, Doc. Math. **28** (2023), 939–1026, DOI [10.4171/DM/926](https://doi.org/10.4171/DM/926) | Explicit rational shift/triality of degree-eight algebras with involution | 888 as invariant or the selected original Griess structure tensor |
| P1 independent VOA root | **H.-Y. Chen, C. H. Lam, H. Shimakura**, *Z3-orbifold construction of the Moonshine vertex operator algebra and some maximal 3-local subgroups of the Monster*, Math. Z. **288** (2018), 75–100, DOI [10.1007/s00209-017-1878-z](https://doi.org/10.1007/s00209-017-1878-z), arXiv 1606.05961 | Genuine V#≅Vnatural with three graded sectors, Monster automorphism group, 3-local subgroup information | Any 27D Albert→infinite-dimensional VOA sector chart, literal selected Monster 3B element, or identification of two Griess products |
| P2 pre-existing Ibrahim/OEIS carrier | [Agda Ibrahim A027907 / path-cube / ternary 13 owner](https://github.com/chboishabba/dashi_agda/blob/chatgpt/c3-nine-site-borromean-braid-20261022/DASHI/Wikimedia/IbrahimA027907PathCubeTernaryExceptionalThirteenSnowballExact.agda). Distinct OEIS contributor priority retained in [convolution attribution owner](https://github.com/chboishabba/dashi_agda/blob/chatgpt/c3-nine-site-borromean-braid-20261022/DASHI/Wikimedia/IbrahimA027907PathCubeConvolutionAttributionProofExact.agda): N. J. A. Sloane; Gerald McGarvey; Tony Foster III; Shapiro et al. Riordan provenance | Exact P3³ trinomial row 1,3,6,7,6,3,1; 13 antipodal pairs; 1+26 and numeric 52,78 decompositions | A projective-geometry action, Moufang loop, Albert product, F4/E6 intertwiner or Moonshine mode by cardinality alone |

**Attribution rule:** source identity, dated publication, local exact computations, source-written Lean/Agda modules, and kernel-certified proof are five different statuses. Do not count a source or cited publication as a local formal proof; do not merge repeated source echoes into independent primary confirmations.

## 2. NEW original-source finite mathematical theorem

Griess's source polynomial
`g(x,y) = -x0*x1*y2-x2*y0*y1+x1*x2*y0+x0*y1*y2 mod3`
defines on `F3³×F3` the central-phase product
`(x,a)⋆(y,b)=(x+y,a+b+g(x,y))`.

An independent exact local script `/mnt/data/check_griess1990_M81_associator_moufang.py` executed PASS with all 81 elements and 27³=19683 grade triples:
`δg(x,y,z):=g(x,y)+g(x+y,z)-g(y,z)-g(x,y+z)=det(x,y,z) mod3`.
Associator value counts: 0→8451, 1→5616, 2→5616. The quotient is commutative with identity and every element has third power identity; Moufang identity exhaustively checked on all grade triples; a concrete nonassociativity witness is retained. Symbolic algebra confirmed the integer-polynomial δg−det = `3*y1*(-x0*z2+x2*z0)` before passage to F3. The Moufang law phase difference also has an explicit factor3, so these are source formulas rather than pattern fits.

**New Lean source** `Integration/Griess1990Moufang81Determinant.lean` reuses `ZMod 3`, states a ring-theoretic associator determinant proof, commutative loop, identity and Moufang phase/loop laws. **SOURCE WRITTEN; Lean kernel not run.**

## 3. NEW genuine projective geometry, Ibrahim same-number versus same-carrier

There are 13 points and 13 dual lines in `PG(2,3)` formed from 26 nonzero grades modulo ±. The incidence relation for projective representative a, dual normal b is the **actual invariant** `a·b=0 mod3`, not an arbitrary 13-element bijection.

Independent source-specific script `/mnt/data/check_griess1990_pg23_incidence.py` executed PASS:
- 13 points and 13 lines; four points on each line and four lines per point; 52 **actual incidence flags**.
- Each of `C(13,2)=78` point pairs lies on a **unique** projective line.
- Exactly 52 of `C(13,3)=286` point triples are collinear; 234 are noncollinear. `δg=det` vanishes for distinct representatives exactly on collinear triples.
- `13`, `52`, `78` share integer values with the Ibrahim A027907 and exceptional-module decompositions, but **incidence flags and point pairs are not by themselves F4 or E6 Lie algebras or selected physical observables**.

**New Agda source** `DASHI/Moonshine/Griess1990Moufang81IbrahimProjective13Exact.agda` directly REUSES `SSPTritCarrier`, the original `Base369Ternary27HypervoxelFabricGeometryExact` 27-point carrier, and the canonical Ibrahim Thirteen arithmetic theorem owner. It implements the source phase g and an 81-carrier loop operation and explicit basis determinant/associator receipts; **not Agda kernel checked**. Independent Agda #1239 script `scripts/check_griess1990_M81_ibrahim_pg23_source_weld.py` reads the ORIGINAL Agda #1249 homogeneous Griess fixture and tests source M81 and PG23; the exact independently implemented local Python equivalents executed PASS.

## 4. NEW source-specific open-cube discriminator: complete finite GL3 enumeration

The **actual original** open P3³ graph has balanced coordinates -1↔0↔+1 (no -1↔+1 edge). Independent local `/mnt/data/check_griess1990_pg23_open_cube_symmetry_intersection.py` enumerated ALL GL3(3) matrices with 54 edges:
- |GL3(3)| =11232, |SL3(3)|=5616.
- EXACTLY 48 invertible linear transformations preserve the original open cube edge set. They are **the signed coordinate permutations**, equivalently the stabilizer of the projective coordinate triangle.
- Exactly 24 of these matrices have determinant +1 and thus lie in original Griess SL3(3).
- Their effective action on projective PG23 has order24, since global inversion is projectively trivial.
- Index `5616/24=234`, agreeing with the **234 noncollinear unordered triples**, because all noncollinear projective coordinate triangles form one SL3(3) orbit. The orientation/full-group identification must retain the distinction between GL3(3) and SL3(3).

This is a **real same-label mathematical explanation** of why the original open spatial graph loses almost all Griess label normalizer symmetry; it is NOT an action-preserving physical F4/Monster correspondence. Source-equivalent Agda #1239 `scripts/check_griess_pg23_exact_open_cube_symmetry_intersection.py` is committed. A symbolic determinant calculation additionally confirms `det(Mx,My,Mz)=det(M) det(x,y,z)` over the integers, hence source associator is orientation-preserving under SL3(3) and reverses sign under determinant −1 unless the central phase is correspondingly transformed.

## 5. Reproducibility audit and repairs (no inflated receipts)

At the start of this continuation, user-provided historical local checks `check_13_c3_source_equivalent.py` and `check_griess1990_formula_to_table_source_equivalent.py` FAILED when called in this runtime because two imported helper scripts were absent from /mnt/data. Also the committed Lean #52 13-line regression accidentally used `Q=(s.eye(27),R,R**2)` for 2×2 phase blocks. **BUG REPAIRED** on the existing PR: `Q=(s.eye(2),R,R**2)` (commit 3343298e). These do NOT refute the arithmetic, but they do refute claiming that these specific stale local files are presently standalone green.

To remove missing-helper dependence, new standalone current-turn local executable `/mnt/data/check_griess1990_standalone_crossprover.py` consumes only the already saved 27×27 rational certificate JSON and SymPy:
- PASS source-authored Q(omega) 729/729 basis products versus literal Lean-native rational octonion Jordan formula, correct off20-conjugation convention.
- PASS exact left/right inverse, trace Gram, unit and **3×729 source product equivariance** for true Griess F3³ action generators.
- PASS adversarial mutation rejection (deliberately change one rational matrix coefficient; Gram fails).
- Executed in ~3.4 seconds, without any repository-local script imports.
The Agda #1239 `scripts/check_griess1990_rational_triality_crossprover_certificate.py` was upgraded to check inverse/3×729 source actor equations/negative-control; the upgraded source was copied verbatim as Lean #52 `scripts/check_griess1990_crossprover_standalone_certificate.py`. The newly committed GitHub bytes were NOT themselves replayed in this runtime; locally executed implementation is source-equivalent.
- Lean, Lake, Agda remain unavailable: **NO kernel certificate**.
- GH PRs unmerged/open and may change concurrently; read HEAD on each follow-up.

## 6. Pareto and hard acceptance gates

| Rank | Candidate | Utility / cost and accepted finish line |
| --- | --- | --- |
| P0 (highest) | Compile the ACTUAL Lean #52 source formula `Griess1990OriginalHomogeneousFormula` and the 1839-entry tensor-to-native 729-product proof | If Lean kernel passes, the source-to-native product map is a genuine same-object theorem. Do not settle for a hard-coded 27D dimension or script PASS. Split big `native_decide` into chunked finite 27-column tables if resource-limited. |
| P0 | Instantiate the Agda `Griess1990RationalAlbertTrialityTransportExact` record from actual 27×27 rational map and source action, compile Agda | Native algebra, actual Actor and trace pairing must be *the same* on both sides. Use existing Agda octonion/Jordan owners; don't create second J3(O). |
| P1 | Compile source `Griess1990Moufang81Determinant` and scoped 13-line/PG23 module | Mathematical proof of δg=det and the source's ternary incidence, importable into more than one repo. This is a small polynomial identity and likely cheap relative to 729 native octonion products. |
| P1 | Validate exact GitHub blob scripts against source certificate and 81-loop/GL enumeration | All test scripts runnable with genuine inputs, mutation fails; no missing helpers, no false SUCCESS. |
| P2 | The published Chen--Lam--Shimakura actual V# three-sector VOA / repo selected Monster 3B recognition | Obtain a concrete same-literal-VOA selected element/eigenspace/mode chart. An analogous 9+9+9 split of the finite Albert action is NOT this chart. |
| P3 | Original-Q F4/E6 algebraic-group recognition | Needs action/group/stabilizer witness, not 52/78 arithmetic or an automorphism's finite character. |
| P4 | 369 graph Hamiltonian, physical KK/AdS3/string, RH | Require selected measured/source Hamiltonian or physical action and exact same-operator observables; past open-P3³ graph and 26D K27 no-gos remain unaffected. |

The exact trigger `888/8` is mathematically explained as an adjustable coordinate residual; no basis-invariant or original-source-force for 888 has been shown. The structural explanatory result is the **determinant associator of Griess's ORIGINAL Moufang81** and its projective/open-cube symmetry implications.

## 7. Attribution and proof-status checklist

Original author and dated source `Griess 1990` must accompany the phase polynomial and 81-loop. Source code and computational reconstruction are *local implementation*, not original discovery. Barry--Tignol and Alsaody--Gille remain independent mathematical donors. Chen--Lam--Shimakura is original authority for Moonshine orbifold, not the Albert multiplication. OEIS author/contributor dates and Riordan provenance belong only to the A027907 arithmetic observation. All present exact tests are local executable calculations, and new Lean/Agda modules are **source-written unverified**; no kernel or physical evidence is claimed.


## 2026-10-25 continuation: ORIGINAL 240/243 is now related to actual Griess M81 by a reversible chart and source-correct automorphisms

**Canonical, implementation-level 12K provenance and acceptance ledger:** [Lean #52 Griess M81 / original T5 243-240 / E6–E8 actual-action max-cut](https://github.com/chboishabba/dashi_lean4/blob/agent/albert-jordan-f4-maxcut-20261007/docs/superpowers/plans/2026-10-25-griess-m81-original-t5-243240-e6e8-actual-action-maxcut.md).

The user explicitly reminded us of PRE-EXISTING 240/243 prior art. Original owners: Lean #43 / Agda #1094 (literal 243=T5 and 240=T5 minus constant diagonal); Lean #47 / Agda #1098 (E6 standard quadratic 243=1+80+90+72; formal noninvariance of old 240 under original E6 simple s3); Lean #47's **already advanced** intrinsic structured E8 240 root datum, glue reflection, full Coxeter action and locally computed |W(E8)|=696729600, plus Agda #1093 E8 order-three origin. Distinct 240 referents in Casimir pressure, YM interval boxes, and QCD remain separate typed objects.

**New explicit same-carrier chart:**
\`(z0,z1,z2,z3,z4) ↔ (((z0−z4,z1−z4,z2−z4),a=z3−z4),t=z4)\` in F3. The first four digits are the **underlying carrier**, but NOT the coordinatewise-additive algebra, of original Griess (1990) M81; the fifth remains extra. The old deleted diagonal becomes literally \`{M81 identity}×F3\`. So old 240 is **explicitly bijective as a selected-chart set** to \`(M81 minus identity)×F3\`, decomposing \`240=3×80=6+234\` by central/noncentral source grade. The inherited E6 Q stratification on the SAME old carrier instead gives \`(Q0,Q1,Q2)=(80,90,70)\` because the deleted diagonal removes one origin Q0 and two Q2; the formal E6 reflection obstruction is unchanged. Original M81 set chart is not the STRUCTURED E8 240 (72+6+6×27).

**New ACTUAL source g-corrected Griess automorphism lift:** for each of 6 elementary SL3(3) shears \`Tij\`, solve \`h(x+y)-h(x)-h(y)=g(Tx,Ty)-g(x,y)\`. Explicit correction polynomials \`h01=x2(1−x1²), h02=0, h10=x2(1−x0²), h12=x0(x2²−1), h20=0, h21=x0(x1²−1)\` make literal \`(x,a)↦(Tij x,a+hij(x))\` a loop automorphism of source Griess M81. Original uncorrected phase action demonstrably fails. Local exact independent Python verifies **4,374** cocycle equations, **39,366** M81 product laws, six cube identities, and generated permutation-group order **151,632=27×5,616**, separately checks projected grade group order 5,616 and ALL 27 linear central character shifts in the kernel. Griess M81 orbit sizes \`1,1,1,78\`. Conjugate each actual lift through the old240 bijection to obtain an ACTUAL action on that original 240; old240 orbit sizes \`1×6,78×3\`. Thus \`234\` noncentral states are three 78-orbits, not the original PG(2,3) 234 noncollinear-triple transitive orbit: shared 234 DOES NOT pay an equivariant identification.

Lean #52 **source-written** new owners: \`Integration/Griess1990OriginalT5Moufang243240Chart.lean\`; \`Integration/Griess1990Moufang81ElementaryLift.lean\`; \`Integration/Griess1990MoufangOriginal240Action.lean\`. Branch-specific missing PR47 \`T5RelativeE6ActionRestrictionObstruction\` import corrected by consuming already available real \`E6Mod3WeylAction.reflectStandard\` and reproducing selected s3 counterexample. Agda #1239 **source-written** original Kernel5/actual Griess M81 chart: \`DASHI/Moonshine/Griess1990OriginalKernel5M81243240ChartExact.agda\`; dependent two-sided Agda proof record still uninhabited; #1094 relative owner is on another unmerged branch. Independent portable no-helper test \`scripts/check_griess_m81_t5_243240_actual_cocycle_action.py\` committed to BOTH repos (remote bytes not replayed). Local counterpart \`/mnt/data/check_griess_M81_243_240_cocycle_full_maxcut.py\` executed all acceptance cases PASS; receipt \`/mnt/data/griess_M81_243_240_cocycle_receipt.json\`. No Lean/Agda executables installed, so **NOT kernel-certified**.

**Source-role snowball and original authorship:** Robert L. Griess Jr. (1990), J Algebra 131:281–293, DOI 10.1016/0021-8693(90)90176-O original M81 g phase, Albert Jordan and local finite normalizer. For general commutative Moufang-loop automorphism theory **Lucien Bénéteau and J. Lacaze (1980)** European J Combinatorics 1:299–309 DOI 10.1016/S0195-6698(80)80029-1; **Lucien Bénéteau (1981)** 81-loop classification DOI 10.5802/afst.561; separately Alsaody–Gille, Barry–Tignol octonion donors; Chen–Lam–Shimakura independent Monster VOA source; original Ibrahim/OEIS contributor attribution retained. New code and specific finite checks are DASHI formalisation; not original mathematics, not literature theorem imported into a kernel. A source-written \`native_decide\` theorem is still just a proof target until independently run and accepted. No physics, RH, original T5=W(E8), or selected Monster 3B same-object promotion.

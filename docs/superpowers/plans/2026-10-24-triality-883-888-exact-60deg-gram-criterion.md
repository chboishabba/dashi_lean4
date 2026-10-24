# Why 883/8 almost equals 888/8: exact Spin(8) triality alignment audit
Date: 2026-10-24. Canonical owner Lean PR #52.

## Source/author attribution
* Robert L. Griess Jr., *A Moufang loop, the exceptional Jordan algebra, and a cubic form in 27 variables*, Journal of Algebra 131 (1990), 281–293, DOI 10.1016/0021-8693(90)90176-O: the A=F3³ homogeneous **Albert** (not Moonshine Griess VOA) product, its exceptional cubic.
* John Baez, *The Octonions*, Bull. AMS 39 (2002), §Spinors and Trialities, https://math.ucr.edu/home/baez/octonions/node7.html: the nondegenerate trilinear normed triality for three 8-dimensional modules; and Alsaody–Gille (2019), *Isotopes of Octonion Algebras, G2-Torsors and Triality*, Adv. Math. 343, 864–909, DOI 10.1016/j.aim.2018.12.003: the related-triple/isotope machinery and important field-vs-ring distinctions.
* Existing Lean PR #52 `RationalAlbertNative`, `RationalAlbertTrialityBasis`, `TernaryAlbertLinearBasisWeld`, `AlbertStructureTransport` and `check_griess1990_native_albert_rational_peirce_isometry.py`: original in-repo owners of the rational H3(O) product, homogeneous source model, Peirce 3+8+8+8 and the earlier selected full metric isometry. This audit neither reinvents a new Albert algebra nor pretends that all products already match.

## Core question and its exact answer
Our earlier comparison used 512 entries S_{ijk}, T_{ijk} of Griess1990 and native-octonionic triality **in a selected nonorthonormal Peirce basis** and the coordinate squared residual
`R_coord=Σ_{ijk}(S_{ijk}-T_{ijk})²`.
Initial exact numbers:
* `ΣS²=251/4=502/8`;
* `ΣT²=507/8`;
* `ΣST=63/8`;
* therefore `R_coord=(502+507−126)/8=883/8`.
Making `R_coord=888/8=111` **WHILE FREEZING THESE TWO COORDINATE NORMS** would require `ΣST=121/16`, down by 5/16 from 63/8. That is a constraint on an arbitrary chosen coordinate alignment, **not a known sourced triality identity**.

## A precise way to force 888, which exposes its noncanonicity
Act on the *third* Peirce-space target by the standard real `SO(8)` planar rotation of octonion coordinates (0,6), keeping all other coordinates fixed. Let c=cos θ, s=sin θ. Exact symbolic contraction of the actual 512 tensors gives:
* source coefficient norm² `=251/4` independent of θ;
* target coefficient norm² `=(511−4c+2s)/8`;
* source–target overlap `=(60+3c+s)/8`;
* after using c²+s²=1, `R_coord(θ)=(893−10c)/8`.
Thus **θ=60°** gives exactly `888/8=111`: (893−10×(1/2))/8. It is an explicit exact algebraic point, not an approximate numerical fit. BUT at 60°, the target coordinate norm changes to `(509+sqrt(3))/8` and overlap to `(123+sqrt(3))/16`, so it **does not realize the user's separate fixed-norm demand ΣST=121/16**. It is also not a Q-linear octonion-coordinate transformation: its entries contain sqrt(3). Its single-slot action was NOT accompanied by the related Spin8 transformations of the other two slots and does not preserve the cross-slot product.

Why 60° was a promising trial is mathematically understandable: the source chosen Peirce gram is A2^4; A2 root geometry has order-six hexagonal rotations. But the root-lattice 60° map is rational in **its A2 root basis**, not the same as an arbitrary 60° plane rotation between octonion coordinate axes 0 and 6.

## Exhaustive actual A2^4 rational sixfold subgroup test
For each A2 block with `G2=[[2,-1],[-1,2]]`, the integral order-six map `R2=[[1,-1],[1,0]]` satisfies `R2^T G2 R2=G2` and `R2^6=I`. Exact exhaustive test of all `6^4=1296` independent block rotations on the selected third Peirce-space isometry gives **zero choices with R_coord=111**. The closest has `R_coord=887/8`, distance 1/8. The earlier independent 256 native-octonion-coordinate sign choices also gave zero exact 111 and nearest values 887/8 and 889/8. These are subgroup audits, NOT a proof no general rational Spin8/triality map could yield 111.

## The correct normed-triality inner product changes the question
The source 8D Peirce basis is NOT orthonormal. Its rational positive Gram is `G=diag(G2,G2,G2,G2)`. The basis-INVARIANT tensor inner product for a fixed candidate map is
`<S,T>_G= S_{ijk}(G^-1)^{ii'}(G^-1)^{jj'}(G^-1)^{kk'}T_{i'j'k'}`.
The exact inverse blocks are `G2^-1=(1/3)[[2,1],[1,2]]`.
The fully checked invariant contractions for the original candidate are:
* `||S||_G²=8`;
* `||T||_G²=8`;
* `<S,T>_G=3/4`;
* **`R_G=||S−T||_G²=29/2`**.
The equality `8=8` is a genuine normed-octonion triality property, rather than a coincidence involving 883 or 888. With the chosen 60° SO8 rotation, the metric-corrected overlap is `13/16−sqrt(3)/48` and the residual is `115/8+sqrt(3)/24`, NOT 111. The corrected norm is independent of *basis changes* but its overlap still varies under independently changing the candidate source-to-target map.

A true `Spin(8)` related triple that actually preserves/matches the two products must attain `<S,T>_G=8`, so R_G=0. Positive definiteness makes this the actual full product-equivalence gate. Nothing presently sources a canonical value 121/16 for the unweighted coordinate overlap. The target's 888 is constructible by selecting a convenient noncanonical rotation, but it is not derived from an invariant.

## Verification and next Pareto cut
Locally ACTUALLY EXECUTED exact Python: 
`/mnt/data/audit_888_triality_alignment_search.py` (256 signs),
`/mnt/data/audit_888_triality_planar_rotations.py` (28 planes symbolic),
`/mnt/data/audit_888_triality_exact_60deg.py`,
`/mnt/data/audit_888_triality_invariant_norm.py`,
`/mnt/data/audit_888_triality_weighted_60deg.py`,
`/mnt/data/audit_888_A2_root_rotations.py` (1296 rational isometries).
All exact assertions PASS and py_compile PASS.
New portable regression sources on Lean PR #52: `scripts/check_griess1990_triality_888_gram_rotation_exact.py`, `scripts/check_griess1990_triality_A2_lattice_888_exhaustive.py`. No exact-GitHub-blob replay or Lean kernel compilation claimed.

**P0**: Freeze Peirce 3+8+8+8 and use Gram-corrected `R_G`, not raw Σ coefficient squares, as optimizer/proof acceptance measure. **P1**: solve the three mutually related slot maps using Spin(8)/octonion isotope compatibility (G2 stabilizer); test all 512 cubic entries exactly. Over fields, octonion norm-classification can inform existence, but producing the actual Q-rational source frame still requires a SAME-OBJECT map. **P2**: only on exact R_G=0, transport a genuine Albert Jordan algebra isomorphism to Lean's native product and selfadjoint Hamiltonians; Monster 196884D VOA/KK/AdS3/RH remain separate lanes. Always distinguish published originals, finite Python, source-written Lean, kernel-verified proofs and physical claims.


## Further EXACT Pareto result: optimize the correct Gram-metric residual, not the 888 numerator

New local independently executed `/mnt/data/audit_triality_A2_best_metric_alignment.py` and committed portable regression `scripts/check_griess1990_triality_A2_best_invariant_alignment.py`: the **correct** tensor metric norm satisfies `||S||_G²=||T||_G²=8` for every rational root rotation, so `R_G=16−2<S,T>_G`. On the 6^4 finite rational A2-root subgroup acting on target Peirce slot 02, the global maximum can be computed by four independent two-dimensional block optimisations. For blocks 0,1,2,3 the best source/target weighted overlaps are `3/8, 1/4, 1/8, 1/4` attained at powers `(5,1,1,5)` of the source-integer hexagonal matrix `R=[[1,-1],[1,0]]`. Hence `<S,T>_G` increases **3/4→1**, and squared product residual decreases **29/2→14**. These new slot maps are ACTUAL Q-linear Gram-isometries and preserve diagonal-plus-one-slot products, unlike the auxiliary irrational native-coordinate 60-degree rotation that engineered 888. But weighted residual14 is still nonzero and the full three-slot Spin8-related map is NOT constructed. Do not call the source-selected subgroup optimum an invariant of Albert algebras; it is a controlled finite-search result for an explicitly chosen subgroup and starting chart.


## Direct fixed-norm version of user's question (stronger test, not the same as hitting 888 by 60°)
The 60° example **changes** raw target norm `507/8 → (509+√3)/8`, hence does NOT realize the specific counterfactual `T²=507/8` and `<S,T>=121/16` simultaneously. To test that condition independently, write an SO8 coordinate-plane rotation via rational tangent-half-angle `c=(1−t²)/(1+t²)`, `s=2t/(1+t²)`; for each of 28 coordinate pairs form exact polynomial equations `T'(t)²−507/8=0`, `<S,T'(t)>−121/16=0`. Exact polynomial GCD computations over Q for ALL 28 cases find **no common root**, including algebraic half-angle parameters, for any single coordinate-plane rotation. This is a narrowly scoped rigorous no-go for the selected one-plane family, NOT for all 2-plane rotations or SO8. Actually executed exact local Python `/mnt/data/audit_888_fixed_norm_oneplane.py` PASS; committed portable owner `scripts/check_griess1990_triality_888_frozen_norm_oneplane_no_go.py`. Any claim that source-root Griess1990/Spin8 **forces** 121/16 remains unsupported.


## 2026-10-24 NEW MAX-CUT: explicit rational related triple closes the selected full-product seam (Python exact, Lean open)

**Supersedes the earlier "A3 open" status IN THE LOCAL EXACT PYTHON LANE.** New executable owner:
\`scripts/check_griess1990_triality_rational_related_triple_recovery.py\`
(commit \`56607795a65e9a0d70931f8aae306eab974d6a30\`).
Source provenance: Griess (1990), *J. Algebra* 131:281–293, DOI 10.1016/0021-8693(90)90176-O; standard Hurwitz octonion coordinatization; Alsaody–Gille (2019), *Isotopes of Octonion Algebras, G2-Torsors and Triality*, DOI 10.1016/j.aim.2018.12.003; Barry–Tignol (2023), *Trialitarian triples*, DOI 10.4171/DM/926. These are the **original source authors**, not DASHI discovery claims.

**Actual source-object construction**, not just a dimension match or arbitrary norm isometry:
1. Read the SAME Griess1990 \`S01, S12, S02\` source slots and original product. Form \`S_ijk = 3 B(S01_i ∘ S12_j,S02_k)\`. Set \`q=G/2\` with the repository's rational \`G=A2^4\`; recover source composition \`mu(x,y)=q^{-1}S(x,y,-)\`.
2. Verify the complete polarization \`L_i^T q L_k + L_k^T q L_i=2q_ik q\` for all \`i,k\`. This is the full **bilinear norm-composition identity**, not a set of selected numerical examples.
3. Select \`a=b=W^{-1}e0\`, \`c=mu(a,b)\`, \`R_b(x)=mu(x,b)\`, \`L_a(y)=mu(a,y)\`. They are rational norm isometries. The unital isotope on the same third slot is \`x*y=mu(R_b^{-1}x,L_a^{-1}y)\` with unit \`c\`.
4. Two exact rational Householder reflections build a Cayley basis \`(c,u,v,uv,w,uw,vw,(uv)w)\`. Exhaustively check its 64 products equal **the same** rational Cayley–Dickson octonion basis used by \`RationalAlbertNative\`. With \`Phi=D^{-1}\`, the explicit maps are \`g01=Phi R_b\`, \`g12=Phi L_a\`, \`g02=Phi\`. Each satisfies \`g^T g=q\` in the native coordinate norm and \`g02(mu(x,y))=g01(x)*g12(y)\` on all 64 basis products.
5. Verify all 512 source/target trilinear coefficients **exactly equal** and then assemble the full rational 27x27 linear map, fixing the three frame idempotents and applying each matching 8x8 map to its correct native slot. Exhaustive exact check: **729/729 Jordan products**, the actual unit and all 729 full-basis trace pairings match. The new selected-map Gram residual is exactly **ZERO**, \`<S,T>_G=8\`, rather than the old 29/2 or optimized single-slot-subgroup 14.

**Execution receipt:** independent source-equivalent local Python/SymPy in \`/mnt/data/triality_related_triple_recovery.py\` executed **PASS** for a synthetic rotated octonion tensor and the reconstructed Griess1990/Peirce/native-source equations: 512/512 cubic comparisons, 729/729 actual Jordan product table, unit and trace metric. The GitHub script has been committed but its exact uploaded bytes have NOT been independently replayed, and neither Lean/Lake nor Agda kernel was run. The local source copies were reconstructed from the PR equations, so the exact HEAD still needs replay.

**Roadmap gates after this advance:**
- **A3 local exact:** PASS on reconstructed source-equivalent equations, explicit rational same-object 27D product isomorphism. Execute newly committed script at exact GitHub HEAD to upgrade to exact-head Python receipt.
- **A4 Lean:** OPEN. Export the three explicit 8x8 rational matrices (script prints them), native 27x27 block transport, prove all 64 mixed bilinear identities plus frame/trace/unit in the existing Lean rational carrier, then compile the full product through existing \`AlbertTrialityCubicCompiler\` / \`AlbertStructureTransport\`. Kernel green is still a separate claim.
- **Original-Q F4/E6 classification:** the pre-existing separate same-object external classification witness remains OPEN; source-level product equivalence is not by itself a classification of a rational algebraic group.
- **Monster VOA, C27, 369 physical grid, KK/AdS3, RH/zeta:** all retain their independent operator/action and empirical/analytic gates. No physical inference is made from this algebraic certificate.

**888 arithmetic remains a map-dependent curiosity:** the previous 60° one-plane raw-residual identity, the one-plane frozen-norm no-go, and the 1296-element subgroup optimum are correct *for their explicitly chosen families*; none obstructs the constructed rational three-slot product isomorphism, and none canonically forces the unweighted overlap 121/16.


## 2026-10-25 return to original question: why 883/8 nearly 888/8, and where the Monster Z3 owner fits

**Recover the user's actual prompt before treating the work as a generic TOE/Monster programme.** The prompt was the surprise that one *chosen* 512-component cross-slot Albert comparison returned \`883/8=110.375\`, so close to \`888/8=111\`; the user asked what mathematical object governs it, what would make it exactly 888, and whether that would be a structural result. The initial handoff additionally identified the existing **Chen--Lam--Shimakura V#=Vnatural Z3 orbifold** source owner, \`DASHI/Wikimedia/IbrahimMonster3BZ3OrbifoldPhaseRecognitionSnowballExact.agda\`, and asked that it not be bypassed by toy three-charge constructions.

**The answer on the literal question is no longer open.** The original source-selected comparison, in NONORTHONORMAL Peirce basis, has coefficient residual \`883/8\`. An arbitrarily selected real SO8 plane-rotation changes it as \`R_raw(theta)=(893-10cos(theta))/8\`; \`theta=60deg\` produces exactly \`888/8\`, but it also changes the raw target norm, is not a Q-rational source-prescribed triality triple, and does not satisfy the user's *separate* fixed-norm \`121/16\` overlap hypothesis. The correct Gram tensor objective started at \`29/2\` and reached **zero** after the explicit rational three-slot related-triple map. That zero product residual, verified independently for all 512 triality and 729 Jordan basis identities, is the meaningful exact mathematical success. It makes *further optimization toward 888* counterproductive.

**NEW legitimate cyclotomic three-sector contact to the user's Chen--Lam--Shimakura prior art:** The **original 27D Griess Albert** \`A=(Z/3)^3\` has exactly \`(3³-1)/(3-1)=13\` cyclic order-three subgroups. Restrict its actual Q-rational representation along any nonzero direction: the trace of each nonidentity phase operator is zero, the rational fixed projector \`(I+U+U²)/3\` has rank9, and its cyclotomic complement rank18. Over Q(omega), the source phase eigenspace dimensions are **9,9,9**. For two distinct cyclic directions, their common fixed space has dimension3; three independent directions leave the 1D actual Albert identity. The full label \`SL(3,3)\` (order5616) acts transitively on all 13 lines: no original-source-canonical distinguished C3/Peirce-plane direction. The original Chen--Lam--Shimakura \`V#=Vnatural\` three-way VOA grading is an ACTUAL published, separate infinite-dimensional VOA; shared phase eigenvalues do **not** give a same-VOA source-sector chart, Monster 3B selected-element recognition, native Griess-mode multiplication, or any 27D Albert→VOA embedding.

**New concrete checks/Lean owners on PR #52**:
- \`scripts/check_griess1990_13_cyclic_phase_restrictions.py\` is the exact source-specific 13-line rational projector/SL3 transitivity regression (GitHub source-written, exact downloaded blob not replayed).
- \`Integration/Griess1990ThirteenCyclicPhaseRestrictions.lean\` imports the ACTUAL previous \`Griess1990RationalF3CubedActualAction\` matrices and declares finite \`native_decide\` payment targets for 13 order-three subgroups, fixed-projector idempotents/trace9, intersection trace3, triple identity-line projection and native transported rank9. No redundant octonions/cube generated. This is **source-written, NOT Lean kernel verified**.
- Independent local \`/mnt/data/check_13_c3_source_equivalent.py\` executed PASS on all thirteen actual source-character rational matrices, 78 pair intersections, independent three-axis identity projector, and all 5616 SL3(3) label matrices. Python compile PASS.
- Agda #1239 \`scripts/check_griess1990_albert_13_c3_vs_monster_z3_source_cut.py\` independently builds the finite 13-line phase/projector discriminator, reuses original Griess and CLS attribution; source-written script, not the separate original Agda/Lean kernel.

**Stop-rule/roadmap correction:** What the user originally found surprising was a *coordinate-level close call*, not a physical prediction. The strongest steelman is the verified rational product isomorphism and source-selected 3^3 action/Fourier intertwiner, plus the genuine literature-backed Moonshine VOA Z3-phase side **without** a false same-object weld. The next mathematical gate is Lean kernel compilation of literal Griess source tensor→native Jordan multiplication and source-selected actor plus Agda transport inhabitant. The independent Monster 3B literal VOA-mode/sector chart and F4 original-Q classification are distinct. No KK/AdS3, RH, string, quantum observer, or measured 369 dynamics result is smuggled in via equal cardinalities or shared zeta symbols.

**Source attribution:** R. L. Griess Jr., *A Moufang loop, the exceptional Jordan algebra, and a cubic form in 27 variables*, J. Algebra **131** (1990), 281–293, DOI 10.1016/0021-8693(90)90176-O; H.-Y. Chen, C. H. Lam, H. Shimakura, *Z3-orbifold construction of the Moonshine vertex operator algebra and some maximal 3-local subgroups of the Monster*, Math. Z. **288** (2018), 75–100, DOI 10.1007/s00209-017-1878-z; S. Alsaody and P. Gille (2019) on octonion isotopes/triality, DOI 10.1016/j.aim.2018.12.003. Original authorship is theirs, while finite source-specific scripts and conditional formal transport are DASHI implementation only.

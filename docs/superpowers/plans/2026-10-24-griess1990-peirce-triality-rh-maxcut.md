# Griess 1990 homogeneous Albert -> native H3(O_Q): exact Peirce/real-form max-cut, RH half audit (2026-10-24)

## Original source and in-repo attribution

**External original mathematical source:** Robert L. Griess Jr., *A Moufang loop, the exceptional Jordan algebra, and a cubic form in 27 variables*, J. Algebra 131 (1990), 281–293, DOI [10.1016/0021-8693(90)90176-O](https://doi.org/10.1016/0021-8693(90)90176-O). Source owns the elementary-abelian A=F3³ homogeneous Albert Jordan product with e_x ∘ e_y = (-2)^(-c(x,y)) ω^g(x,y)e_(x+y). Standard Peirce decomposition, primitive idempotents, rational E8 roots, and Hadamard identity are established mathematics, not newly invented by DASHI.

**Existing Lean owners:** #52 `Integration/RationalAlbertNative.lean` original-Q Hermitian octonions and actual Jordan product/unit; `RationalAlbertTrialityBasis.lean` 3+8+8+8 native coordinate basis; `RationalAlbertS3Native.lean` source Jordan S3 action; `RationalAlbertJordanHamiltonianSymmetry.lean` selected real diagonal h and operator conjugacy; `TernaryAlbertLinearBasisWeld.lean` noncanonical 1+26 coordinate equivalence **without product**; `AlbertStructureTransport.lean` generic structure transport requiring an actual isomorphism; existing `scripts/check_griess1990_albert_f3cubed_homogeneous_product.py` exact external 1990 multiplication. `dashi_agda` #1249 owns a distinct real nonperiodic cube 26-mode zero-mean graph quotient, not the Albert tracefree space. `dashi_agda` #1239 owns separate cyclic Monster C27 / VOA Griess grade-two operator questions (dimension196884). Don't conflate A=F3³ (exponent3), cyclic Monster C27 (exponent27), or literal spatial Cube27.

## 1. Exact primitive idempotents reveal why +1/2 occurs

For fixed nonzero a in F3³, the subalgebra span(e0,e_a,e_-a) is Q(ω)[C3], since e_a²=e_-a, e_a e_-a=e0. Its primitive idempotents are

`p_j = (e0 + ω^(-j)e_a + ω^(-2j)e_-a)/3` for j=0,1,2.

All three satisfy `p_j∘p_k=δ_jk p_j`, `sum p_j=e0`, and are fixed by the **anti-linear Jordan real form** `τ(e_x)=e_-x`, `τ(ω)=ω²`. Under positive definite Hermitian `H(u,v)=3 B(u,τ(v))`, `H(p_j,p_k)=δ_jk` and `H(e0,e0)=3`. (The trace normalization factor3 matches Lean's native rational Albert trace form.)

For `p0=(e0+e_a+e_-a)/3`, `H_a=L_(e_a+e_-a)=3L_p0−I`; the known spectrum 2:1, −1:10, +1/2:16 arises from universal primitive-idempotent Peirce spectrum 1:1, 0:10, 1/2:16. There is no extraneous 'RH spectral half' mechanism.

The source primitive Jordan frame has 3 scalar diagonal directions and **three off-diagonal 8-dimensional Peirce spaces**. Exact polynomial projections:

`D_j=2 L_pj²−L_pj` and `O_jk=4 L_pj L_pk`.

Verified for all source 27 basis vectors: D/O are pairwise orthogonal idempotent projections, their sum equals I, ranks [1,1,1,8,8,8]; complete Peirce product fusion rules hold on all 27×27 basis-pair combinations. Thus source `p_j -> Lean-native E_jj` is a REAL-STRUCTURE/TRACED/JORDAN-PRODUCT preserving isomorphism on the ENTIRE 3-dimensional diagonal subalgebra, not merely a 1+26 shape bijection.

## 2. New actual 27D rational full-space form isometry

For each of the three 8D Peirce slots, select eight explicit τ-fixed source vectors (images of the 13 conjugate charge pairs) whose **native trace-normalised** Gram is `G = diag(B2,B2,B2,B2)`, `B2=[[2,-1],[-1,2]]`; exact determinant `81`. Native octonion-slot trace form is `2 I8`.

Build eight explicit rational E8 roots forming an `A2^4` subsystem: rational matrix `R` has `Rᵀ R=G`. The classical Sylvester 8×8 Hadamard matrix `H8` has `H8ᵀ H8=8 I8`. Hence `W=H8 R / 4` is fully rational and obeys **`Wᵀ (2I8) W=G`**, without a hidden √2 or field extension. Use W on each Peirce slot, and send source p0,p1,p2 to the corresponding native 3 diagonal idempotents.

The resulting EXPLICIT 27×27 Q-linear operator on the source τ-fixed Q-space is invertible, transports the positive trace-pairing, unit, and Peirce projectors correctly onto Lean's native Hermitian-octonion coordinate space. Against literal **rational Cayley–Dickson octonionic multiplication** (not a mock target tensor), every pair of basis vectors from **each diagonal+8-offdiagonal-slot Jordan subalgebra** has exactly the SAME image product. This is a strict advance over a dimension-only map.

**Source product still not fully transported.** One cubic across two different slots gives actual source Frobenius cubic=1 and target cubic=0; the native trace-norm-square of the product residual is **1**. Exhaustive source-vs-target triality comparison on `8×8×8=512` scalar entries has **341 nonmatching entries** and sum of squared coefficient residuals **883/8** for this SELECTED rational W and Peirce basis. This proves only that the obvious independent metric isometry on all three slots is NOT a Jordan algebra homomorphism. No global no-go for all possible triality-compatible isomorphisms is asserted.

**New exact completion target:** three 8×8 rational isometries `U01,U12,U02` obeying one triality tensor equality `Tr((U01 x ∘ U12 y) U02 z)=Tr((x ∘ y)z)` for all 512 basis triples. Given already checked Peirce fusion/trace form and same-slot multiplication, this is sufficient for all 27D basis products by Frobenius nondegeneracy. Check preservation of the Griess τ real form and Lean-native trace/unit on the SAME selected operators, not a separate arbitrary finrank27 equivalence.

## 3. RH cross-pollination: useful NEGATIVE control, no proof payment

The critical line in Riemann hypothesis is **Re(s)=1/2**. In Hilbert–Pólya type proposals a self-adjoint operator's REAL eigenvalues are intended to encode the IMAGINARY ORDINATES γ of zeros `1/2+iγ`, not have eigenvalue `+1/2` by itself. The Peirce half is present in generic Jordan algebras, independent of any Dirichlet series, Weil positivity or ξ functional equation.

Selected Albert charpoly `P(s)=(s−2)(s+1)^10(s−1/2)^16` has exact reflection ratio
`P(1−s)/P(s)=−((s−2)/(s+1))^9`,
not ±1. Even a shift cannot make multiplicities at 2 and −1 equal. A manufactured **finite** entire function `Xi_toy(s)=((s−1/2)^2+4)((s−1/2)^2+1)^10((s−1/2)^2+1/4)^16` satisfies Xi_toy(s)=Xi_toy(1−s) and has 54 zeros on that line **by definition**, but does not match the completed Riemann zeta function or source zero ordinates. This is a **negative-control fixture** for RH proof claims, not a new independent positive estimate, same-object zero encoding or kernel RH theorem.

Native RH owners: Lean PR #50 A1 inverse-square-shell partition / A2 signed quartic sixth/eighth leading debt and FarHorizontal curvature / B signed fifth boundary-gap-convergence; PR #77 G21 selected actual-zeta pole/off-line a=|β−1/2| and p=1/2. No RH leaf is discharged by an unrelated Peirce eigenvalue, and the formal G21 pole p=1/2 is likewise a zeta-derived kernel parameter, not a Jordan idempotent.

## 4. Executed receipts, committed source, and next cut

**Executed locally**:
- `/mnt/data/check_griess1990_peirce_frame_rh_audit.py` (PASS 3 Jordan idempotents; all 27D Peirce projectors and fusion; RH reflection negative control).
- `/mnt/data/check_griess1990_peirce_rational_norm.py` (PASS all three source 8D rational Gram matrices each A2⁴, det81).
- `/mnt/data/find_e8_a2_fourframe.py` (PASS 8 exact E8 rational roots and Gram).
- `/mnt/data/check_griess1990_native_albert_27_peirce_isometry.py` (PASS full 27D Q isometry, all same-slot native products, exact 341/512 tensor discrepancy and residual 883/8).
- local SymPy RH polynomial/functional-equation negative controls PASS; Python byte-compile PASS.
**Committed Lean #52 scripts** `scripts/check_griess1990_albert_peirce_rh_frame.py` and `scripts/check_griess1990_native_albert_rational_peirce_isometry.py`; committed Lean RH #50 `scripts/check_rh_albert_peirce_critical_half_negative_control.py`. Equivalent actual local source executed, **exact committed Git blob not independently executed**, and no Lean/Lake or Agda kernel receipt. Existing previous native Lean structure-owner PR #52 remains open/draft and not silently merged.

**Pareto P0**: solve the explicit 512-scalar tensor identity with product-compatible Q8 slot maps (or prove an exact original-Q form obstruction using its cubic triality invariants). **P1**: formalize the concrete selected same-object algebra map in Lean #52 only after P0, reusing `RationalAlbertNative`, `RationalAlbertTrialityBasis`, `AlbertStructureTransport`. **P2**: return to separate Monster VOA Vnatural_2 C27 genuine Griess projected mode, and its selected KK/AdS3 observable, without substituting Albert operators. **P3 RH**: retain adversarial finite Peirce fixture in RH #50/#77 only; prioritize actual signed/far analytic inputs, not spectral half numerology.

**Scientific boundary:** none of these finite algebraic facts identifies a physical Hamiltonian, string/KK source, Moonshine VOA state or zero of ζ. Preserve original source attribution and exact proof method.

## Exact 2026-10-24 phase/orbifold and 883/8 correction
The in-repo `DASHI/Wikimedia/IbrahimMonster3BZ3OrbifoldPhaseRecognitionSnowballExact.agda` owns the Chen–Lam–Shimakura `V#` / `V^sharp` source and records its three phase summands V0,V1,V2, natural Z3 automorphism and Moonshine VOA identification (DOI 10.1007/s00209-017-1878-z; arXiv:1606.05961). Do not claim exact `Vb` or `Vneutral` exports without located declarations; nor replace its 3-summand orbifold with the 27D Albert A=F3^3 grading or the Monster C27 charge chart. The selected Griess-1990-to-native-Albert rational Peirce isometry has a mapped-triality squared discrepancy 883/8, but a *single slot sign reversal* preserves real structure, trace, Gram form and all same-slot products while changing it to 1135/8. Exact local `/mnt/data/audit_883_over_8_basis_dependence.py` executed PASS and the Lean #52 regression now verifies this; therefore 883/8 is not an algebraic invariant, only a candidate-map dependent error measure. The only decisive gate is all 512 cubic triality equations zero for a single compatible three-slot map; one failed map does not prove no full isomorphism exists.


## 2026-10-24 EXACT 883/8 ↔ 888/8 triality algebra, correct metric norm, and 6^4 Pareto result
Source-anchored canonical ledger: `chboishabba/dashi_lean4` PR #52 `docs/superpowers/plans/2026-10-24-triality-883-888-exact-60deg-gram-criterion.md`. Published owners: Griess 1990 A=F3³ Albert Jordan; Baez octonion/Spin8 triality; Alsaody–Gille 2019 normed octonion isotope/triality. Actual source + native 512 cubic tensor comparison has **raw coordinate norm** `S²=251/4`, `T²=507/8`, overlap `63/8`, residual `883/8`. Direct exact SO(8) rotation of octonion coordinate plane (0,6) yields `R_raw(θ)=(893−10cosθ)/8`; at **θ=60°**, `R_raw=888/8=111` EXACT. This is NOT a canonical or Q-rational A2 lattice action: native plane uses √3 and the raw target coordinate norm changes to `(509+√3)/8`, so it does NOT establish previous counterfactual fixed-norm overlap `121/16`.
The real Peirce Gram is `G=A2^4`, so correct tensor contraction uses THREE inverse Gram factors. Exact **basis-independent for a FIXED candidate map** norms are `||S||_G²=||T||_G²=8`, weighted overlap `3/4`, weighted squared residual **29/2**, not 883/8. Under auxiliary 60° plane rotation the weighted error is `115/8+√3/24`, not 111. A full product isomorphism requires weighted overlap8 and residual0.
Exhausted **all 1296 Q-rational 60° A2^4 root rotations** on one chosen Peirce slot: none gives raw R=111 (nearest 887/8). Optimizing the ACTUAL Gram residual over the same finite subgroup instead gives exact best powers `(5,1,1,5)`, overlap `3/4→1`, invariant-metric squared error **29/2→14**. This is genuine source-informed local Pareto improvement, NOT full Spin8 related triple or canonical 888. Executed locally Python exact assertions PASS; committed Lean #52 `check_griess1990_triality_888_gram_rotation_exact.py`, `check_griess1990_triality_A2_lattice_888_exhaustive.py`, `check_griess1990_triality_A2_best_invariant_alignment.py`; exact committed blobs/Lean kernel not run. Separate 196884-D Monster Griess VOA/KK/AdS3/RH content not identified with this selected 27D Albert tensor.


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

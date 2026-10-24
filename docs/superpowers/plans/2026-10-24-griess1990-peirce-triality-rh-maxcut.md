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

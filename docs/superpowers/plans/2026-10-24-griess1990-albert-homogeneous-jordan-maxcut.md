# Griess 1990 source-specific Albert F3³ multiplication and Hamiltonian max-cut — 2026-10-24

## Source, primary attribution and original owners

**Original primary source:** Robert L. Griess Jr., *A Moufang loop, the exceptional Jordan algebra, and a cubic form in 27 variables*, Journal of Algebra 131 (1990), 281–293, DOI 10.1016/0021-8693(90)90176-O ([paper](https://www.sciencedirect.com/science/article/pii/002186939090176O)). Griess describes an elementary abelian A=(Z/3)^3 subgroup of Aut(J_3(O_C)), normalizing SL3(3), and a decomposition into 27 one-dimensional character spaces. The **source's** homogeneous multiplication formula, basis construction and Jordan result remain Griess's original theorem, not original DASHI mathematics.

**Existing Lean-native repository theorem owners:** `Integration/RationalCayleyDicksonOctonion.lean`, `RationalAlbertNative.lean` (full original-Q Jordan product and unit), `RationalAlbertS3Native.lean` (actual native order3 Jordan automorphism), `RationalAlbertCubicNormStructure.lean`, `RationalAlbertTracePairNondegenerate.lean`, `AlbertScalarTraceless.lean`, `TernaryAlbertLinearBasisWeld.lean`, and `RationalAlbertF4E6IrreducibleFrontier.lean` all predate this source cut. Existing finite ternary geometry has its separate actual Cube27 graph and 54 edges. The Monster Griess algebra Vnatural_2 is a different algebra of dimension196884, and cyclic Monster C27 has exponent27, not exponent3 like A.

## Explicit homogeneous complex Albert product (checked)

Use A^ = F3³; for x=(x1,x2,x3), y=(y1,y2,y3), set
`c(x,y)=0` when linearly dependent and `1` otherwise,
`g(x,y) = -x1*x2*y3 - x3*y1*y2 + x2*x3*y1 + x1*y2*y3 mod 3`.
In the source-normalized basis over Q(ω), ω³=1 and 1+ω+ω²=0,
`e_x∘e_y = (-2)^(-c(x,y)) * ω^(g(x,y)) * e_(x+y)`.

**Do not miss the NEGATIVE exponent**: the coefficient is **-1/2** for independent pairs, and 1 for dependent pairs. A superficially plausible +1 exponent FAILS the Jordan polynomial identity in exact arithmetic. This was caught in the independent adversarial test before committing the corrected formula.

Source-reproducing complete local Python `/mnt/data/check_griess1990_albert_homogeneous_exact.py` executed PASS:
- 27 homogeneous basis characters; 729/729 nonzero basis products; true unit e_0; commutativity for all 729 pairs.
- Frobenius-invariant pairing via e_0 coefficient for all 27³=19683 basis triples.
- FULL polarization of the degree-(3 in X,1 in Y) Jordan identity `((X²∘Y)∘X)=(X²∘(Y∘X))` for all `C(29,3)×27=98,658` independent monomial coefficients using exact `Q(ω)` arithmetic; hence the identity on all linear combinations over characteristic zero. This is an exhaustive computation, not an Agda/Lean kernel theorem.
- Explicit nonzero homogeneous cubic: `<e_(1,0,0)∘e_(0,1,0),e_(2,2,0)> = -1/2`.
- Explicit nonassociativity: `(e_(0,0,1)²)∘e_(0,1,0)=-1/2 e_(0,1,2)` while `e_(0,0,1)∘(e_(0,0,1)∘e_(0,1,0))=+1/4 e_(0,1,2)`.

Portable same-mathematics checker committed as `scripts/check_griess1990_albert_f3cubed_homogeneous_product.py` with full polarized Jordan and 26 homogeneous Hamiltonian cycles. The local long-form full checker executed and `py_compile` passed; no Lean/Lake kernel run or execution of the newly committed GitHub blob on this head is claimed.

## Actual nontrivial left-Jordan operator spectrum, not just numbers

For each NONZERO a∈F3³, the 27×27 left-Jordan multiplication operator `L_(e_a):e_x ↦ C(a,x)e_(x+a)` is monomial with exactly NINE cycles of length3. Along the dependent line {0,a,2a}, the product of three edge coefficients is **1**; on each of the other eight cycles it is **-1/8**. Exact calculation repeated for ALL 26 nontrivial a.

Therefore the characteristic polynomial is
`(λ³−1)(λ³+1/8)^8`, giving spectral triples
`{1,ω,ω²}` each multiplicity1 and `{−1/2,−ω/2,−ω²/2}` each multiplicity8.
These eigenvalues are generally **nonreal**, so `L_(e_a)` is NOT selfadjoint in a positive-definite complex Hilbert inner product. It is still a genuine Jordan multiplication operator and invariant under the algebra's bilinear Frobenius form, which is not the same thing as a positive Hermitian physical energy pairing. A real/Hermitian linear combination of homogeneous modes would be a new selected operator and require its own dynamics.

Contrast the SOURCE-NATIVE *compact rational* Albert choice `h=diag(1,0,-1)` on Lean #52. The new `Integration/RationalAlbertJordanHamiltonianSymmetry.lean` shows actual order3 S3 conjugacy, commutation iff h fixed, native tracefree scalar→26 amplitude2 and exact Python tests for rank27 nonzero S3 commutator with squared norm18. The diagonal `L_h` has *REAL* spectrum ±1:1, ±1/2:8 and 0:9. Both are genuine Albert-related algebraic Hamiltonian candidates, but the coordinate convention, scalar extension and positive form are not identified.

## Exact types and 27−1 roles

1. **F3³ character labels:** 1 trivial character +26 nontrivial characters, each a 1D eigenspace of A in the Griess 1990 *complex Albert* algebra. All nonzero A characters have order3.
2. **Spatial 3×3×3 path cube:** 27 sites, 54 nearest-neighbour edges. A chosen label set bijection to A^ does NOT preserve geometry; the full source Jordan multiplication is nonlocal relative to the cube graph (every one of 729 products is nonzero).
3. **Lean native compact rational Albert J3(O_Q):** 27-dimensional Jordan algebra with trace-unit linear equivalence J≃ℝ⊕ker(tr), 26D traceless part; exact complex homogeneous basis transition remains unpaid. Extending ℚ to ℚ(ω) does NOT automatically prove it is isomorphic to the specific Griess 1990 Q(ω)-form.
4. **Monster Vnatural_2 C27:** 196884-dimensional Monster Griess algebra with cyclic order27 automorphism and nonuniform eigenspace ranks; NOT this A-grading.
5. **Agda #1249 path-Cube27 zero-mean 26:** graph-wave 26D reduction with `A=D+1*b^T`, metric `G=I−J/27`; NOT the 26-dimensional Albert representation or bosonic string target.

## Pareto residual and acceptance

P0: run pinned Lake compilation on `Integration/RationalAlbertJordanHamiltonianSymmetry.lean` and new script (repo uses Lean v4.35.0-rc3 with mathlib rev v4.28.0; resolve pin compatibility as needed). P1: construct and source-certify an actual scalar-extended isomorphism between the Griess 1990 Q(ω) homogeneous Jordan multiplication and the repository's ORIGINAL rational compact Albert form after extension, comparing cubic norm and trace form. THIS is the same-algebra producer; random basis identification is not enough. P2: compare chosen selfadjoint operators with actual physical Hamiltonian and the original spatial adjacency under an explicit norm/observable-preserving map; do not use an arbitrary complex non-Hermitian L_(e_a) as a physical Hamiltonian. P3: only with source-native realization consider a Monster-VOA/Griess operator map or KK/AdS3 physical connection.

No result here proves the bosonic 26D string theory, 27D Bosonic M, quantum field Hamiltonian, Monster-AdS3 correspondence, or general YM/Clay theorem.


## 2026-10-24 exact Griess1990 positive real form and homogeneous Hamiltonian (new max-cut)
**Original source authority**: Griess (1990), J. Algebra 131, 281–293, DOI 10.1016/0021-8693(90)90176-O. Existing Lean #52 source already implements and checks his complex 27D Albert product `e_x∘e_y = (-2)^(-c(x,y)) ω^g(x,y) e_(x+y)`. The following is a *new exact consequence / local computation on that ORIGINAL selected product*, not a new Jordan algebra, not the Monster Griess VOA, and not an isomorphism with native rational Albert.

Define antilinear `τ(ω)=ω²`, `τ(e_x)=e_(-x)`. Exact coefficient checks of all 729 products establish `τ(e_x∘e_y)=τ(e_x)∘τ(e_y)`. The original invariant symmetric form `B(e_x,e_y)=δ_(x+y,0)` yields **positive Hermitian** `H(u,v)=B(u,τ(v))`, with `H(e_x,e_y)=δ_xy`. The 26 nonzero homogeneous grades form 13 τ-conjugate pairs. Each `h_a=e_a+e_-a` is τ-real, and `L_(e_a)†=L_(e_-a)`; hence `H_a=L_(h_a)` is positive-form SELFADJOINT for all 26 nonzero a, giving 13 distinct operators indexed by opposite pairs.

Exact local Python: `/mnt/data/check_griess1990_realform_hamiltonian.py` ran PASS across all 729 product identities, 26 adjoint-pair families, all 27 basis vectors for each a, polynomial annihilator `(H_a−2I)(H_a+I)(2H_a−I)=0`, trace `0` and squared trace `18`. Hermitian diagonalizability + these moments yield COMPLETE real spectrum **2:1, −1:10, +1/2:16**. Each a retains the order-9 kernel of its nontrivial F3³ character and acts on the CHOSEN 27 character-chart as nine disjoint triangle chains (27 bonds). For x-axis a=(1,0,0), 18 of these edges are original spatial cube grid bonds and 9 are PERIODIC WRAP bonds; NOT the full original 54-edge grid Hamiltonian. This is a selected source algebraic operator, not empirical quantum dynamics.

**Precise 27−1 operator cut:** `H_a(e0)=e_a+e_-a`, so the 26 nontrivial *homogeneous* grades are NOT invariant under full H_a. Source-orthogonal compression `K_a=Q H_a Q` (Q=I−|e0><e0|) has exact spectrum **+1:1, −1:9, +1/2:16** and trace-square14 (vs full18). Agda #1249's actual original open P3³ cube zero-mean Laplacian has 26 nonzero modes and EIGHT distinct eigenvalues {1,2,3,4,5,6,7,9}. Any affine scale `λK_a+μ I` with λ≠0 has only THREE distinct eigenvalues. Therefore these selected 26-D Albert and spatial-graph operators are provably **not unitary-equivalent even up to shift/rescaling**. Earlier geometric-origin plus26 set codec, constant-mode spatial quotient and Albert grade-unit decomposition are three separate constructions.

**New committed executable owner**: `scripts/check_griess1990_albert_positive_realform_hamiltonian.py` on Lean #52, plus local independently executed full script `/mnt/data/check_griess1990_realform_hamiltonian.py`. No Lean/Lake/Agda kernel run, no explicit same-source `H3(O_Q)≅J_{Griess1990}` matrix, and NO selected Monster weight-two action or AdS3/KK physical interpretation. This advances the original source homogeneous spectral programme without replacing its F4/E6 classification leaf or current native rational-Albert Hamiltonian proof.

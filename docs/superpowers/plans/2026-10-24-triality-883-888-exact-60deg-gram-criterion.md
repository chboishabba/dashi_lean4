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

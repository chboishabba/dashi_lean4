# BSD selected curve — exact K0–K5 correction and max-cut (2026-11-12)

## Original curve and authoritative external cross-check

E: y²=x³−x is LMFDB 32.a3 / Cremona 32a2:
https://www.lmfdb.org/EllipticCurve/Q/32/a/3

- Minimal discriminant 64, conductor 32, j=1728, CM by Z[i].
- E(Q) abstract Mordell–Weil group Z/2×Z/2, four torsion
  points and rank zero in the external curve database.
- STANDARD full real period Omega_std=5.2441151085842396...
  (two real components); Tamagawa c_2=2; Kodaira III.
- L(E,1)=0.65551438857302995... in the external database.
- Standard rank-zero BSD RHS, taking Sha order=1 and
  regulator=1: Omega_std*2/4² = Omega_std/8.
- If Omega_half=Omega_std/2=2.62205755429..., the same
  numerical value is Omega_half/4. PERIOD CONVENTIONS MUST
  BE LABELED. Tamagawa c_2=4 and Kodaira I_3^* belong to
  the isogenous 32.a4 / Cremona 32a1, not this curve.
- These database values are EXTERNAL EVIDENCE, not local
  Lean or Agda theorem proofs.

## Essential corrections to the attached K0–K5 plan

1. E[2](Qbar)=(Z/2)^2 has trivial Galois action. The full
   group E(Qbar) is not E(Q), is not four-element, and does
   not have the asserted trivial Galois action.
2. The genuine geometric [2] sequence is
     0 → E[2] → E(Qbar) --[2]→ E(Qbar) → 0.
   The connecting homomorphism lands in H¹(G_Q,E[2]).
   The following map is H¹(G_Q,E[2])→H¹(G_Q,E(Qbar)).
3. The exact 2-Selmer sequence is
     0 → E(Q)/2E(Q) → Sel²(E/Q) → Sha(E/Q)[2] → 0.
   Vanishing of an explicit square-class Kummer cokernel is
   not the vanishing of all of Sha(E/Q), even after K1
   and K2 have been proved: only Sha(E/Q)[2] follows.
4. The local real Kummer condition is image-membership,
   INCLUDING the trivial class, not restriction to the
   single nontrivial real connected component.
5. Mordell–Weil rank zero requires actual finite generation,
   the rank/mod-two theorem, and actual rational 2-torsion
   identification. A mere four-class quotient is not enough.
6. Rubin or Coates–Wiles cannot be invoked to eliminate ALL
   odd-primary Sha without explicit applicable theorem
   hypotheses, exact local factors, and proof of inputs.
7. A universal Clay BSD axiom is NOT a theorem and must
   not be introduced into the authoritative proof chain.
8. The Bishop Riemann-zeta commuting square is a convergence
   method donor, not an elliptic L-function identity.

## Current exact owners and separate acceptance

K0 — SOURCE WRITTEN; LOCAL KERNEL PENDING:
- scripts/bsd_local_maxcut_verify.sh now builds Lean
  dependency modules with lake build, then performs
  axiom inspection and optional full Synthesis build.
- lean-toolchain v4.35.0-rc3 vs mathlib v4.28.0 needs
  exact compatibility audit and pinned local receipt.
- No CI dependency; absence of sorry is NOT typechecking.

K1 — GLOBAL PART SOURCE WRITTEN, LOCAL PART OPEN:
- Original geometric selected-curve quarter-point owner:
  cmRationalCohomologicalKummerXT_eq_totalGlobalKummer_paid.
- Genuine global H¹(E[2]) square-class carrier:
  rationalGenericTwoTorsionH1MulEquivSquareClassPair,
  explicitSelmerToGenericTwoTorsionH1.
- New proof owner
  MillenniumBSDCMActualE2H1ExplicitImageWeldExact:
  cmExplicitSelmerToActualE2H1_injective;
  cmActualE2H1ExplicitSelmerImage_eq_torsion;
  cmGlobalGeometricXTKummer_toActualE2H1_square.
- UNPAID: source-realized PadicQuadraticKummerCompatibility
  and PadicEllipticKummerExactness at every p, real
  cohomological Kummer matching and all local naturality.
  Existing typed records are NOT inhabited producers.

K2 — CLASSICAL E-VALUED SHA[2] OPEN:
- The selected original E(Qbar) continuous Galois TopRep
  ALREADY EXISTS as cmEllipticPointRepresentation, with
  globalGenericE2ToEllipticPoint and global E[2]→E H¹
  cohomology arrow in MillenniumBSDLocalKummerCohomologyReduction.
- New MillenniumBSDCMActualEBarRestrictedShaTwoTargetExact
  specializes rationalTateShafarevichOne and its 2-torsion
  to the genuine cmEllipticPointRepresentation, and proves
  the literal all-place localization-kernel membership test.
- UNPAID: prove local E(Qbar_v) coefficient identification,
  equivariant geometric doubling LES, connecting morphisms,
  global/local naturality and exact cokernel comparison.
  The restricted-global E(Qbar) coefficients alone are NOT
  automatically classical local E(Qbar_v) coefficients.
- Compare actual continuous Selmer with original explicit
  group and identify explicit cokernel with classical
  Sha(E/Q)[2].
- Existing EllipticShaTwoComparisonBoundary is E[2]-
  coefficient typed and therefore MUST NOT be relabeled
  classical E(Qbar)-valued Sha.
- ExplicitTwoSelmerCokernel_subsingleton is EXPLICIT only.

K3 — CARDINALITY PART SOURCE WRITTEN, RANK OPEN:
- MillenniumBSDCMOriginalMordellWeilModTwoCardExact
  gives original E(Q)/2E(Q) equivalence and four-card
  theorem using original four torsion constructors.
- Still pay actual finitely-generated rank formula and
  full selected E(Q)[2] same-object identification.

K4 — ANALYTIC OPEN:
- New MillenniumBSDCMSelectedPeriodNormalizationExact
  proves the original-curve arithmetic ratio Omega_std*2/16
  = Omega_half/4, with Omega_half=Omega_std/2. This is a
  normalization IDENTITY, not a proof of original L(E,1).
- All-n original curve Hecke coefficients, Euler factors,
  Bishop Dirichlet majorant/limit, modular/Mellin same
  object, functional equation, continuation to s=1,
  and source-checked exact positive central value.
- Do NOT replace the proof with the LMFDB decimal value.

K5 — ODD-PRIMARY/FULL BSD/UNIVERSAL OPEN:
- Explicit odd-primary Sha, full rank-zero coefficient
  formula, Tamagawa/period exact transport, and
  universal rank/leading-coefficient assertions remain
  separate obligations.

## Highest-information continuation order

K0 exact-head LOCAL kernel and axiom audit FIRST;
K1 actual finite-place and real-place H1 local matching;
K2 full E-valued classical Kummer exactness;
K3 finitely generated MW rank theorem;
K4 same-curve analytic central nonvanishing;
K5 odd-primary and full/universal BSD last.

No flag automatically promotes source-written to local
checked, kernel accepted, or physically verified.
Agda remains golden for Agda owners; local verification
rather than CI is authoritative; attribution to Mathlib,
LMFDB, Agda and other primary owners is preserved.


## 2026-11-12 K1–K5 continuation and corrected original-owner accounting

Source-written (not local-kernel-checked):
* K3 MillenniumBSDCMOriginalMWTwoTorsionRepresentativesExact.lean:
  cmRationalTorsionCode_double_zero,
  cmOriginalMWModTwo_everyClass_has_twoTorsionLift,
  cmOriginalMWModTwo_has_actual_twoTorsion_representative,
  cmEveryRationalPoint_modDoubles_eq_actual_twoTorsion.
  These prove that EVERY original E(Q)/2E(Q) class can be
  represented by a genuine rational point annihilated by [2].
  The original full E(Q)[2] four-point classification is ALREADY
  SOURCE-WRITTEN in the preexisting
  MillenniumBSDRationalTwoTorsionExact.lean; DO NOT label this
  part unpaid. The remaining missing rank step is formal
  Mordell–Weil finite generation and a rank-vs-mod-two theorem
  on the actual E(Q) carrier; the quotient calculation alone
  does not establish that rank theorem.
* K5 MillenniumBSDCMShaTwoNotFullShaNegativeControlExact.lean:
  constructive finite counterexample ZMod 3 where
  A[2] = 0 but A is nontrivial. This is NOT a claim
  that the selected E has nonzero odd-primary Sha.
  It forbids a logically invalid promoted full-Sha inference.
* K4 MillenniumBSDCMLevel32EtaFinitePositivityExact.lean:
  finite truncations of the ORIGINAL selected modular
  newform eta(4z)^2 eta(8z)^2 (q-product) are positive
  for 0<q<1. This is a literal q-product donor, not
  proof of nonzero infinite product or Mellin integral.

New concrete K4 proof path, with external academic attribution:
Huber–Liu–McLaughlin–Ye–Yuan–Zhang,
Computing Special L-Values of Certain Modular Forms with Complex
Multiplication (https://emis.de/ft/24022), Lemma 3.1,
states the exact original modular form equality
  f_32(z)=eta(4z)^2 eta(8z)^2
and
  L(f_32,1)=2^(-7/2)*Beta(1/4,1/4)>0.
Next K4 genuine producers:
  (i) original finite q-product -> strictly positive
      infinite product / rigorous positive Mellin integrand
      via Bishop uniform product tails;
 (ii) original eta-product newform and all-n Fourier
      coefficients; modularity same-object f_32 ↔ E(32.a3);
(iii) justified Mellin transform, analytic continuation,
      and positive Beta integral at s=1.
This avoids a gratuitous unverified L-value decimal or a
fabricated exact period. It also avoids treating the Riemann-zeta
commuting square as if it were an elliptic L-function theorem.

K1 unpaid: all-place actual local scalar quadratic Kummer
isomorphisms, actual elliptic local image exactness and
localization naturality; the existing global E[2] H1 map
is source-written but not sufficient.

K2 unpaid: exact original E(Qbar) doubling sequence
cohomology + comparison of restricted coefficient
localizations to original E(Qbar_v), Sha(E)[2]
cokernel equivalence. The original E(Qbar)
coefficient representation is already present in
MillenniumBSDLocalKummerCohomologyReduction.

K3 unpaid: original MW finite-generation and rank
transport only (rational E(Q)[2] classification is present).

K4 unpaid: the original eta-product's infinite convergence,
modular same-object and Mellin/central-value theorem.

K5 unpaid: odd-primary Sha and full leading coefficient,
and universal Clay BSD. The universal conjecture cannot be
pronounced closed by an interface, declaration, or assertion.

K0 acceptance: script includes these new modules in local
Lake dependency builds and #print axioms. STILL PENDING
actual local execution and original golden Agda validation.


## 2026-11-12 K2/K3/K4 next max-cut source continuation

NEW source owners on THIS main-based PR branch, all still
unverified against the local Lean kernel:

K3: MillenniumBSDCMOriginalMWTwoTorsionRepresentativesExact now
has cmEveryRationalPoint_eq_twoTorsion_add_double: for every
original P:E(Q), actual original T,U:E(Q) with [2]T=O and
P=T+[2]U. This is a literal group equation, not quotient code
or dimension receipt.

K3: MillenniumBSDCMFGAbelianRankZeroFromModTwoExact:
- cmFGAbelian_finite_of_modDoubles_twoTorsion takes ANY
  genuinely finitely generated abelian G with literal
  g=t+[2]u and [2]t=0, and proves G FINITE via Mathlib
  AddCommGroup.equiv_free_prod_directSum_zmod (v4.28.0).
  It rules out a free Z coordinate by observing 1 cannot
  equal a 2-torsion coordinate plus an even integer.
- cmSelectedRationalPoints_finite_of_MW_finiteGeneration
  reuses the actual P=T+2U theorem, with ONLY the
  independently needed AddGroup.FG RationalProjectivePoint.
- cmSelectedOriginalMordellWeil_ZRank_zero derives
  Module.rank ℤ RationalProjectivePoint=0 using pinned
  Mathlib AddMonoid.isTorsion_iff_isTorsion_int and
  rank_eq_zero_iff_isTorsion.
THIS IS A CONDITIONAL *GENUINE RANK THEOREM*, but the
selected original Mordell–Weil finite-generation instance
is UNPROVED; never claim K3 selected rank zero kernel-accepted.

K2: MillenniumBSDCMOriginalGeometricKummerGroupExact:
- actual E[2](Qbar) inclusion is injective;
- its image is kernel of the actual [2] point-group
  homomorphism;
- actual [2] is surjective by selected curve's existing
  constructive algebraic-closure halves;
- cmSelectedGeometricKummerShortExact_group packages
  unconditional selected GROUP-level
  0→E[2](Qbar)→E(Qbar)→[2]E(Qbar)→0.
Remaining K2 is the continuous equivariant TopRep exact
sequence, global/local H1 connecting LES and coefficient
comparison with E(Qbar_v), especially at the real place.

K4: MillenniumBSDCMLevel32ActualEtaInfiniteNonzeroExact:
- uses Mathlib v4.28.0 ModularForm.eta and its proved
  infinite tprod nonzero throughout the upper half-plane,
  not a finite truncation limit assumed positive;
- cmLevel32EtaAnalyticExpression_ne_zero proves
  eta(4z)^2 eta(8z)^2 ≠ 0 for Im z>0;
- cmLevel32EtaAnalyticExpression_differentiableAt
  proves complex-differentiability (holomorphy) there.
This closes the true infinite eta-expression nonvanishing
and analyticity subgate. It does NOT prove positive Mellin
integral or identified L(E,1): a nonzero holomorphic
function may have a zero central Mellin value.
Exact next: prove this expression = original normalized
level-32 newform; build its q→0 and modular cusp bounds,
positive integral on imaginary axis, Mellin/Dirichlet
same-object and original curve L(E,1)=Mellin(f32,1).
External academic formula is not a Lean theorem.

K1 remains OPEN: local continuous H1 quadratic Kummer
equivalence and full original elliptic local image
naturality at Qp and R. No new scalar compatibility proof
was inserted and none is marked complete.

K5 remains OPEN: selected odd-primary Sha and full BSD
leading formula; universal arbitrary-curve/higher-rank
Clay BSD is unsolved and not representable by an axiom
in the accepted source world.

K0 is mandatory on exact HEAD:
bash scripts/bsd_local_maxcut_verify.sh --full
Script now includes all new modules and #print axioms.
Source git-readback != kernel elaboration; no Lean/Lake
is executable in the current attached execution context.

Attribution: Mathlib authors of the finite abelian structure
theorem and Birkbeck/Loeffler eta library retain their
original credit. GitHub PR is source-written only.


## 2026-11-12 next max-cut: actual Galois equivariance, TopRep [2], and congruent-one triangle bridge

THIS APPENDIX SUPERSEDES OUTDATED CLAIMS THAT THE ENTIRE CONTINUOUS
COHOMOLOGICAL K2 SHORT EXACT SEQUENCE OR SELECTED RANK 0 IS PROVED.

NEW source-written owners, all imported into Synthesis.lean:
- MillenniumBSDCMOriginalGeometricKummerGaloisEquivariantExact.lean
  cmSelectedGeometricE2Inclusion_galois_equivariant,
  cmSelectedGeometricDoubling_galois_equivariant,
  cmSelectedGeometricKummerShortExact_galois_equivariant.
  These consume BSDCohomology.galoisPointMap_double and
  galoisTwoTorsionMap_coe. Thus the REAL selected group maps
  [2] and E[2] inclusion commute with the literal G_Q action.
  This is stronger than group exactness alone but is NOT the H1 LES.

- MillenniumBSDCMOriginalEbarDoublingTopRepExact.lean
  cmEbarDoublingCLM, cmEbarDoublingTopRepHom,
  cmEbarDoublingTopRepHom_surjective,
  cmEbarDoublingTopRepHom_kernel_iff_actualE2,
  cmEbarDoublingTopRepHom_kernel_and_surjective.
  The ACTUAL cmEllipticPointRepresentation uses genuine E(Qbar).
  It is an actual continuous TopRep morphism, with the kernel
  identified elementwise to cmAlgClosureTwoTorsionSubgroup.
  Still construct E[2] inclusion as a coherent TopRep morphism,
  categorical short exactness, continuous connecting LES,
  completion coefficients E(Qbar_v), and Sha(E)[2] cokernel.

- MillenniumBSDCMUnitAreaTriangleCurveWeldExact.lean
  cmCurveTriangle_pythagorean,
  cmCurveTriangle_area_one,
  cmSelectedCurvePoint_implies_unitAreaTriangle,
  cmUnitTriangle_curve_equation,
  cmUnitAreaTriangle_implies_selected_nonTorsionPoint,
  cmSelectedCongruentOne_iff_curve_nonTorsion.
  Maps original rational affine y!=0 points on y²=x³-x
  ↔ actual signed rational right triangles with a*b=2
  and a²+b²=c²; all equations written literally over Q.

- MillenniumBSDCMCongruentOneRankReductionExact.lean
  cmNoUnitAreaTriangle_forces_affineY_zero,
  cmNoUnitAreaTriangle_forces_allRationalTwoTorsion,
  cmOriginalMordellWeil_ZRank_zero_of_noUnitAreaTriangle.
  Independent rank-zero deduction under the EXACT arithmetic
  hypothesis ¬CMHasRationalRightTriangleAreaOne, without a
  general Mordell–Weil finite-generation instance.
  The hypothesis is NOT inhabited: the missing step is a
  formal integer infinite descent proving no rational
  right triangle of square area. The pinned mathlib theorem
  Fermat42.not_fermat_42 (FLT/Four.lean) forbids a⁴+b⁴=c²;
  a formally verified bridge from primitive Pythagorean
  area-square integer triples to that F42 witness is still
  required. Do not silently use a theorem name of a different
  type or confuse nonzero finite q-product with elliptic L(1).

EXACT K0 VERSION GATE: root lean-toolchain is
  leanprover/lean4:v4.35.0-rc3
while the repository's mathlib v4.28.0 tag has
  leanprover/lean4:v4.28.0.
The fail-closed local script now detects this mismatch BEFORE
checking any BSD module; it refuses to claim a kernel receipt
with an incompatible pair. The explicit isolated override
  BSD_USE_MATHLIB_TOOLCHAIN=1 bash scripts/bsd_local_maxcut_verify.sh --full
selects v4.28.0 FOR THAT SHELL PROCESS ONLY via LEAN_TOOLCHAIN,
without mutating root pins or manifest.
This override does NOT claim the 4.35-written surrounding
repository modules compile under 4.28; every imported theorem
still requires an actual pinned local Lean acceptance receipt.
No local Lean/lake/nix executable is present in this tool session.

Remaining gate names, precisely:
K1: genuine scalar quadratic Kummer equivalence at every Qp and R,
    E[2]-cohomological local Kummer image equality and localisation.
K2: exact continuous TopRep inclusion of literal E[2], derived
    cohomological LES, local E(Qbar_v) comparison, classical Sha[2].
K3: either genuine formal finite-generation input for
    RationalProjectivePoint and pinned structure theorem, OR
    the original rational-square-area triangle infinite descent
    linked to Mathlib.Fermat42.not_fermat_42.
K4: prove eta(4τ)^2 eta(8τ)^2 is THE original level-32 newform,
    Mellin identity with cmLSeries, period and central positivity.
K5: odd-primary actual Sha and all-primary leading coefficient;
    universal BSD remains a Millennium problem and cannot be
    closed by finite selected-curve computations.
NONE of K1–K5 is fully kernel-accepted or mathematically closed.

Attribution: Mathlib elliptic point and FLT(4) theorem owners,
the original Galois/TopRep project owners, and the prior
Agda-Bishop analytical owners remain separate. No new axiom,
uninhabited record, or asserted metadata substitutes for proofs.

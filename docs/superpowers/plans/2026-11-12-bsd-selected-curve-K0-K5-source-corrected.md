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
- Construct original E(Qbar) continuous Galois TopRep,
  equivariant geometric doubling, connecting LES and
  localization naturality in the SAME coefficients.
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

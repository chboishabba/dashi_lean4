# BSD exact max-cut roadmap — 2026-11-11

## Mathematical authority firewall

No Clay BSD theorem is claimed. The classical exact sequence is:

    0 -> E(Q)/2E(Q) -> Sel^2(E/Q) -> Sha(E/Q)[2] -> 0.

The Selmer group belongs to H^1(G_Q,E[2]); the right term belongs to
classical Sha(E)=ker(H^1(G_Q,E(Qbar)) -> product_v H^1(G_Qv,E(Qbar))).
An E[2]-coefficient local-triviality kernel is NOT by definition Sha(E)[2].
In particular the existing owner
Synthesis/MillenniumBSDActualE2ShaSameObjectMaxCut.lean
defines a representation-level E[2] localization kernel, not automatically
the classical Weil–Châtelet obstruction. The missing H^1(E[2])->H^1(E)
long-exact-sequence comparison must be constructed.

The geometric Kummer connecting morphism sends a rational P to
the class of sigma(Q)-Q (with 2Q=P) in H^1(G_Q,E[2]), not H^1(G_Q,E).
For the selected curve, the Galois action is trivial ON E[2], not on E.
Full rational two-torsion has dimension 2.

Minimal two-Selmer dimension 2 entails rank(E(Q))=0 and Sha(E)[2]=0
ONLY after proving the genuine exact sequence and an actual Selmer
dimension calculation. It does NOT establish all of Sha(E)=0, since
odd-primary Sha can persist.

## Live PR #39 source owners

- Synthesis/MillenniumBSDCMGeometricKummerContinuousH1Exact.lean:
  selected geometric continuous 1-cocycle.
- Synthesis/MillenniumBSDCMGlobalToPadicKummerCompatibilityExact.lean:
  global rational-point x-T localization, with
  PadicQuadraticKummerCompatibility p still explicit for H^1 naturality.
- Synthesis/MillenniumBSDActualE2ShaSameObjectMaxCut.lean:
  E[2]-representation localization and conditional cokernel comparator.
- BSDCohomology/GenuineDegreeOneShaTwoTorsion.lean:
  generic representation-level localization kernels.
- Synthesis/MillenniumBSDTwoSelmerDimensionArithmeticMaxCut.lean:
  newly added numerical rank/defect consequences from an explicitly
  supplied genuine dimension formula, NOT an actual curve-level calculation.

All are source-level observations; no Lean kernel run in this tranche.

## P0 — selected-curve highest-alpha gates

C0. Construct the genuine classical E(Qbar) continuous Galois module,
E[2] inclusion, exact multiplication-by-two sequence, and induced
H^1 long-exact-sequence maps. Separate H^1(E[2]) from H^1(E).

C1. Prove PadicQuadraticKummerCompatibility at every prime and the
whole-local-point Kummer image compatibility, not merely restriction
of rational global points. Include the real place.

C2. Complete same-object localization commuting squares and equate
explicit Stoll x-T Selmer to cohomological 2-Selmer.

C3. Descend the global Kummer image by the genuine E-valued
long exact sequence to prove
ExplicitSelmer / image(E(Q)/2E(Q)) equiv Sha(E)[2].
Do not promote an arbitrary equivalence to an E[2]-Sha kernel.

C4. Certify by concrete local criteria that
dim_F2 Sel^2(y^2=x^3-x)=2, and certify dim_F2 E(Q)[2]=2.
Then derive rank=0 and Sha(E)[2]=0. Do not infer full Sha=0.

C5. Supply a same-curve exact nonvanishing L(E,1) receipt and the
analytic L-function normalization. Nonvanishing plus rank zero proves
the selected rank formula, not the universal Clay theorem.

## P1 — universal BSD

Generalize C0-C3 to every elliptic curve over Q; build compatible
higher p^n Selmer towers and arithmetic rank controls; establish
same-curve analytic continuation, functional equation and analytic rank;
close rank equality including analytic ranks >=2 via a NONCIRCULAR
argument. Arbitrary mediator definitions do not close it.

## P2 — complete leading coefficient

Establish period, regulator, Tamagawa, torsion, full Sha finiteness,
and leading-coefficient identity, all with exact normalization for
the same curve. Sha[2]=0 neither proves Sha=0 nor its finiteness.

## Acceptance

Use pinned local Lean kernel on exact head, inspect #print axioms and
reject sorryAx for pivots. Record source-write, kernel receipt and
actual Clay theorem separately. Negative controls must explicitly
reject E[2]-Sha = classical Sha[2] by definition and
Sha[2]=0 => Sha=0.

Related: Lean PRs #27, #39, #53, #78 and Agda
DASHI/Mathematics/Arithmetic/BirchSwinnertonDyerBoundary.agda.

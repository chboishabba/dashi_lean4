import Synthesis.MillenniumBSDActualE2TopRepSameObject
import Synthesis.MillenniumBSDActualEllipticPointTopRep
import Synthesis.MillenniumBSDSelmerShaCohomologicalBoundary
import Synthesis.MillenniumBSDExplicitSelmerCokernelExact
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Correct classical Sha[2] boundary for the CM curve

The finite Galois module `E[2]` is now completely identified in the repo, but
`Sha¹(E[2])` is not the classical Tate--Shafarevich group of the elliptic
curve.  The classical two-descent exact sequence is

  0 → E(Q)/2E(Q) → Sel₂(E/Q) → Sha(E/Q)[2] → 0,

and its right-hand term is the two-torsion in the localization kernel for the
*full elliptic point module* `E(Qbar)`, reached from `H¹(G_Q,E[2])` through
the Kummer long exact sequence.

This file records that prize-facing target correctly.  It deliberately does
not replace the missing continuous Kummer theorem by an E[2]-Sha surrogate.
-/

namespace Synthesis.Millennium.BSD

/-- The finite-module Sha target is useful cohomology, but is not classical Sha(E)[2]. -/
noncomputable abbrev cmE2FiniteModuleShaOne :=
  rationalTateShafarevichOne cmActualE2Representation

noncomputable abbrev cmE2FiniteModuleShaTwo :=
  rationalTateShafarevichTwoTorsion cmActualE2Representation

/--
For any actual continuous representation of the full elliptic point group,
this is the correct classical degree-one Sha localization kernel.
-/
noncomputable def classicalEllipticShaOne
    (Ebar : TopRep ℤ RationalAbsoluteGalois) :=
  rationalTateShafarevichOne Ebar

/-- The literal two-torsion subgroup of the classical elliptic Sha target. -/
noncomputable def classicalEllipticShaTwo
    (Ebar : TopRep ℤ RationalAbsoluteGalois) :=
  rationalTateShafarevichTwoTorsion Ebar

/--
Canonical exact-map form of the remaining classical two-descent theorem.

Rather than asking for the final quotient equivalence as a black box, this
records exactly what continuous Kummer exactness and localization must
produce on the already-built explicit Selmer subgroup:

* a homomorphism from the explicit Selmer group to classical Sha(E)[2];
* kernel equal to the already-paid global Kummer image E(Q)/2E(Q);
* surjectivity.

Noether's first isomorphism theorem then constructs the desired cokernel
equivalence automatically.
-/
structure ClassicalTwoDescentExactMapBoundary where
  selmerToSha :
    explicitTwoSelmerSubgroup →*
      Multiplicative (classicalEllipticShaTwo cmEllipticPointRepresentation)
  kernel_eq_globalKummerImage :
    selmerToSha.ker = globalKummerImageSubgroup
  surjective : Function.Surjective selmerToSha

/-- The exact-map boundary compiles to the literal explicit Selmer cokernel
equivalence by the first isomorphism theorem. -/
noncomputable def explicitSelmerCokernelEquivClassicalShaTwo_of_exactMap
    (h : ClassicalTwoDescentExactMapBoundary) :
    ExplicitTwoSelmerCokernel ≃
      classicalEllipticShaTwo cmEllipticPointRepresentation := by
  let eKer :
      ExplicitTwoSelmerCokernel ≃*
        (explicitTwoSelmerSubgroup ⧸ h.selmerToSha.ker) :=
    QuotientGroup.quotientMulEquivOfEq h.kernel_eq_globalKummerImage
  let eSha :
      (explicitTwoSelmerSubgroup ⧸ h.selmerToSha.ker) ≃*
        Multiplicative (classicalEllipticShaTwo cmEllipticPointRepresentation) :=
    QuotientGroup.quotientKerEquivOfSurjective h.selmerToSha h.surjective
  let e := eKer.trans eSha
  exact
    { toFun := fun q => (e q).toAdd
      invFun := fun s => e.symm (Multiplicative.ofAdd s)
      left_inv := by
        intro q
        simp [e]
      right_inv := by
        intro s
        simp [e] }

/--
Exact remaining arithmetic producer after the explicit 2-descent work.

`ellipticPointRepresentation` must be the full `E(Qbar)` Galois module, not
`E[2]`.  The equivalence is precisely what continuous Kummer + local Kummer
compatibility prove in the classical descent argument.
-/
structure ClassicalTwoDescentShaComparison where
  ellipticPointRepresentation : TopRep ℤ RationalAbsoluteGalois
  explicitCokernelEquivClassicalShaTwo :
    ExplicitTwoSelmerCokernel ≃
      classicalEllipticShaTwo ellipticPointRepresentation

noncomputable def explicitSelmerCokernelEquivClassicalShaTwo
    (comparison : ClassicalTwoDescentShaComparison) :
    ExplicitTwoSelmerCokernel ≃
      classicalEllipticShaTwo comparison.ellipticPointRepresentation :=
  comparison.explicitCokernelEquivClassicalShaTwo

/--
The prize-facing BA4--BA6 boundary: continuous Kummer must construct the
comparison above from the already-paid actual E[2] representation and the
explicit local square-class Selmer conditions.
-/
def ContinuousKummerTwoDescentProducer : Prop :=
  Nonempty ClassicalTwoDescentShaComparison

/--
Sharpened prize-facing boundary with the full elliptic-point representation
already fixed internally.  The only remaining datum is the actual continuous
Kummer/localization equivalence from the explicit Selmer cokernel to
classical Sha(E)[2].
-/
def ActualClassicalTwoDescentShaComparison : Prop :=
  Nonempty
    (ExplicitTwoSelmerCokernel ≃
      classicalEllipticShaTwo cmEllipticPointRepresentation)

/-- Exact-map data therefore pays the older fixed-representation comparison
boundary without asking for an independent equivalence producer. -/
theorem actualClassicalTwoDescentShaComparison_of_exactMap
    (h : ClassicalTwoDescentExactMapBoundary) :
    ActualClassicalTwoDescentShaComparison :=
  ⟨explicitSelmerCokernelEquivClassicalShaTwo_of_exactMap h⟩


/-- The fixed-representation comparison compiles back to the older
structure-shaped producer. -/
theorem continuousKummerTwoDescentProducer_of_actualComparison
    (h : ActualClassicalTwoDescentShaComparison) :
    ContinuousKummerTwoDescentProducer := by
  rcases h with ⟨e⟩
  exact ⟨
    { ellipticPointRepresentation := cmEllipticPointRepresentation
      explicitCokernelEquivClassicalShaTwo := e }⟩

/-- Machine-readable sharpening of the classical Sha boundary. -/
structure ClassicalShaTwoBoundaryStatus where
  fullEllipticPointCarrierPaid : Bool
  coordinateGaloisActionPaid : Bool
  additiveGaloisActionPaid : Bool
  fullEllipticPointTopRepPaid : Bool
  continuousKummerLocalizationComparisonPaid : Bool
  deriving DecidableEq, Repr

def classicalShaTwoBoundaryStatus : ClassicalShaTwoBoundaryStatus :=
  ⟨true, true, true, true, false⟩


end Synthesis.Millennium.BSD

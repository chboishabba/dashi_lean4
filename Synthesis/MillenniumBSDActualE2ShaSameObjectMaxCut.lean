import Synthesis.MillenniumBSDSelmerShaCohomologicalBoundary
import Synthesis.MillenniumBSDActualE2H1LowDegreeReduction

/-!
# BSD max-cut: specialize the rational Sha kernel to the literal geometric E[2]

The repository already contains the actual two-torsion subgroup of the selected
CM elliptic curve over Qbar, its continuous absolute-Galois TopRep, and the
continuous H¹ comparison with the literal rational square-class pair.

Accordingly the cohomological Sha boundary should no longer leave the E[2]
representation as free data.  This module fixes the coefficient object to
`cmActualE2Representation` and isolates only the genuinely missing
same-object localization/Kummer comparison with the explicit Stoll-style
2-descent cokernel.
-/

namespace Synthesis.Millennium.BSD

open CategoryTheory

/-- Literal degree-one Sha kernel for the actual geometric E[2] representation
of the selected CM test curve. -/
noncomputable abbrev cmActualE2ShaOne :
    AddSubgroup
      (ContinuousCohomology.continuousCohomology 1 cmActualE2Representation) :=
  rationalTateShafarevichOne cmActualE2Representation

/-- Its literal 2-torsion subgroup. -/
noncomputable abbrev cmActualE2ShaTwo :
    AddSubgroup cmActualE2ShaOne :=
  rationalTateShafarevichTwoTorsion cmActualE2Representation

/-- Membership in the actual E[2] Sha kernel is exactly vanishing under every
real/p-adic localization map used by the rational-place owner. -/
theorem mem_cmActualE2ShaOne_iff
    (x : ContinuousCohomology.continuousCohomology 1 cmActualE2Representation) :
    x ∈ cmActualE2ShaOne ↔
      ∀ v : RationalPlace,
        (ContinuousCohomology.map
          (Field.absoluteGaloisGroup.map
            (algebraMap ℚ (rationalLocalField v)))
          (𝟙 _) 1).hom x = 0 := by
  exact mem_rationalTateShafarevichOne_iff cmActualE2Representation x

/-- The actual geometric E[2] coefficient object has therefore already paid
the representation part of the older comparison boundary.  What remains is
ONLY a mutually inverse comparison between the explicit 2-Selmer cokernel and
this fixed cohomological target. -/
structure CMExplicitCokernelShaTwoComparisonBoundary where
  explicitToShaTwo : ExplicitTwoSelmerCokernel → cmActualE2ShaTwo
  shaTwoToExplicit : cmActualE2ShaTwo → ExplicitTwoSelmerCokernel
  leftInverse : Function.LeftInverse shaTwoToExplicit explicitToShaTwo
  rightInverse : Function.RightInverse shaTwoToExplicit explicitToShaTwo

/-- Any discharge of the narrowed boundary gives the exact same-object
equivalence wanted at the finite 2-descent stage. -/
noncomputable def cmExplicitSelmerCokernelEquivActualE2ShaTwo
    (comparison : CMExplicitCokernelShaTwoComparisonBoundary) :
    ExplicitTwoSelmerCokernel ≃ cmActualE2ShaTwo where
  toFun := comparison.explicitToShaTwo
  invFun := comparison.shaTwoToExplicit
  left_inv := comparison.leftInverse
  right_inv := comparison.rightInverse

/-- The narrowed boundary canonically inhabits the older, more permissive
boundary, fixing its previously-free representation field to the actual E[2]
TopRep. -/
noncomputable def cmComparisonToLegacyBoundary
    (comparison : CMExplicitCokernelShaTwoComparisonBoundary) :
    EllipticShaTwoComparisonBoundary where
  ellipticTwoTorsionRepresentation := cmActualE2Representation
  explicitCokernelToCohomologicalShaTwo := comparison.explicitToShaTwo
  cohomologicalShaTwoToExplicitCokernel := comparison.shaTwoToExplicit
  leftInverse := comparison.leftInverse
  rightInverse := comparison.rightInverse

/-!
MAX-CUT STATUS

PAID BEFORE THIS FILE:
* actual elliptic E[2] over Qbar;
* continuous G_Q action / TopRep on that same subgroup;
* H¹_cont(G_Q,E[2]) on the same coefficient object;
* equivalence of that H¹ with the literal rational square-class pair;
* genuine rational-place Sha localization kernel.

PAID HERE:
* the Sha target is specialized to the literal `cmActualE2Representation`;
* the obsolete free-representation field is eliminated from the active
  comparison boundary.

STILL OPEN:
* prove localization compatibility of the paid H¹ <-> square-class comparison;
* prove that the explicit local Kummer conditions are exactly the kernels of
  those continuous-cohomology localization maps;
* descend the resulting Selmer equivalence through the global Kummer image;
* thereby inhabit `CMExplicitCokernelShaTwoComparisonBoundary`.

No equivalence with classical elliptic Sha[2] is asserted merely from an
interface field.
-/

end Synthesis.Millennium.BSD

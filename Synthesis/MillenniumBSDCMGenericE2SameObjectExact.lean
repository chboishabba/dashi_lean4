import Synthesis.MillenniumBSDActualE2TopRepSameObject
import BSDCohomology.EllipticPointTopRep
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Tactic

/-!
# Selected CM curve: generic Kummer E[2] is the paid actual E[2] same object

Two independently-developed exact lanes meet here:

* `cmActualE2Representation` uses the explicit CM algebraic-closure point
  carrier and already supports the paid H¹ <-> rational square-class theorem;
* `BSDCohomology.ellipticTwoTorsionTopRep cmWeierstrass` is the literal kernel
  of doubling inside the generic geometric-point Galois representation used by
  the genuine Kummer/Sha lane.

This file identifies those carriers through the existing additive equivalence
between the custom CM point carrier and Mathlib's actual affine point group,
and proves Galois equivariance.  Downstream Kummer classes can therefore land
in the exact coefficient object whose H¹ comparison is already paid.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

noncomputable section

------------------------------------------------------------------------
-- The custom CM point action is literally Mathlib base-change point transport.
------------------------------------------------------------------------

theorem cmAlgClosurePointEquiv_galois_commutes
    (σ : RationalAbsoluteGalois)
    (P : CMAlgClosureProjectivePoint) :
    cmAlgClosurePointAddEquivMathlib (cmAlgClosureGaloisAction σ P) =
      BSDCohomology.galoisPointMap cmWeierstrass σ
        (cmAlgClosurePointAddEquivMathlib P) := by
  cases P with
  | infinity =>
      simp [cmAlgClosureGaloisAction, cmAlgClosurePointAddEquivMathlib,
        cmAlgClosurePointEquivMathlib, BSDCohomology.galoisPointMap]
  | affine x y h =>
      simp [cmAlgClosureGaloisAction, cmAlgClosurePointAddEquivMathlib,
        cmAlgClosurePointEquivMathlib, BSDCohomology.galoisPointMap]

------------------------------------------------------------------------
-- Restrict the point equivalence to the literal kernels of doubling.
------------------------------------------------------------------------

noncomputable def cmActualE2ToGenericKummerE2 :
    cmAlgClosureTwoTorsionSubgroup ≃+
      BSDCohomology.EllipticTwoTorsion cmWeierstrass where
  toFun P := by
    refine ⟨cmAlgClosurePointAddEquivMathlib P.1, ?_⟩
    change (2 : ℕ) • cmAlgClosurePointAddEquivMathlib P.1 = 0
    rw [← map_nsmul]
    simp [P.2]
  invFun P := by
    refine ⟨cmAlgClosurePointAddEquivMathlib.symm P.1, ?_⟩
    change (2 : ℕ) • cmAlgClosurePointAddEquivMathlib.symm P.1 = 0
    rw [← map_nsmul]
    simp [P.2]
  left_inv P := by
    apply Subtype.ext
    simp
  right_inv P := by
    apply Subtype.ext
    simp
  map_add' P Q := by
    apply Subtype.ext
    exact map_add cmAlgClosurePointAddEquivMathlib P.1 Q.1

@[simp] theorem cmActualE2ToGenericKummerE2_coe
    (P : cmAlgClosureTwoTorsionSubgroup) :
    (cmActualE2ToGenericKummerE2 P).1 =
      cmAlgClosurePointAddEquivMathlib P.1 := rfl

------------------------------------------------------------------------
-- Generic E[2] action is pointwise fixed, hence agrees with the paid trivial
-- actual-E[2] representation.
------------------------------------------------------------------------

theorem cmGenericKummerE2_pointwise_fixed
    (σ : RationalAbsoluteGalois)
    (P : BSDCohomology.EllipticTwoTorsion cmWeierstrass) :
    BSDCohomology.galoisTwoTorsionMap cmWeierstrass σ P = P := by
  let Q : cmAlgClosureTwoTorsionSubgroup :=
    cmActualE2ToGenericKummerE2.symm P
  apply Subtype.ext
  change BSDCohomology.galoisPointMap cmWeierstrass σ P.1 = P.1
  have hcomm := cmAlgClosurePointEquiv_galois_commutes σ Q.1
  have hfix := cmAlgClosure_twoTorsionSubgroup_pointwise_fixed σ Q
  rw [hfix] at hcomm
  simpa [Q] using hcomm.symm

------------------------------------------------------------------------
-- Upgrade to an isomorphism of the exact continuous Galois representations.
------------------------------------------------------------------------

local instance : TopologicalSpace cmAlgClosureTwoTorsionSubgroup := ⊥
local instance : DiscreteTopology cmAlgClosureTwoTorsionSubgroup :=
  discreteTopology_bot _
local instance : TopologicalSpace
    (BSDCohomology.EllipticTwoTorsion cmWeierstrass) := ⊥
local instance : DiscreteTopology
    (BSDCohomology.EllipticTwoTorsion cmWeierstrass) :=
  discreteTopology_bot _

noncomputable def cmActualE2ToGenericKummerE2ContinuousLinear :
    cmAlgClosureTwoTorsionSubgroup ≃L[ℤ]
      BSDCohomology.EllipticTwoTorsion cmWeierstrass :=
  ContinuousLinearEquiv.mk
    cmActualE2ToGenericKummerE2.toIntLinearEquiv
    continuous_of_discreteTopology
    continuous_of_discreteTopology

noncomputable def cmActualE2GenericKummerContRepEquiv :
    cmActualE2Representation.ρ.Equiv
      (BSDCohomology.ellipticTwoTorsionContRepresentation cmWeierstrass) :=
  ContRepresentation.Equiv.mk
    cmActualE2ToGenericKummerE2ContinuousLinear
    (by
      intro σ
      ext P
      change cmActualE2ToGenericKummerE2 P =
        BSDCohomology.galoisTwoTorsionMap cmWeierstrass σ
          (cmActualE2ToGenericKummerE2 P)
      symm
      exact cmGenericKummerE2_pointwise_fixed σ
        (cmActualE2ToGenericKummerE2 P))

noncomputable def cmActualE2ToGenericKummerTopRep :
    cmActualE2Representation ⟶
      BSDCohomology.ellipticTwoTorsionTopRep cmWeierstrass :=
  TopRep.ofHom cmActualE2GenericKummerContRepEquiv.toContIntertwiningMap

noncomputable def cmGenericKummerE2ToActualTopRep :
    BSDCohomology.ellipticTwoTorsionTopRep cmWeierstrass ⟶
      cmActualE2Representation :=
  TopRep.ofHom cmActualE2GenericKummerContRepEquiv.symm.toContIntertwiningMap

noncomputable def cmActualE2GenericKummerTopRepIso :
    cmActualE2Representation ≅
      BSDCohomology.ellipticTwoTorsionTopRep cmWeierstrass where
  hom := cmActualE2ToGenericKummerTopRep
  inv := cmGenericKummerE2ToActualTopRep
  hom_inv_id := by
    ext P
    rfl
  inv_hom_id := by
    ext P
    rfl

/-!
MAX-CUT STATUS

PAID IN THIS OWNER:
* the explicit CM E[2] subgroup and the generic Kummer kernel E[2] subgroup are
  additively equivalent on actual Mathlib elliptic points;
* the custom coordinate Galois action commutes with the generic point action;
* generic E[2] is pointwise fixed for this selected full-rational-2-torsion
  curve;
* the two coefficient representations are TopRep-isomorphic.

NEXT:
* transport the already-paid actual-E[2] H¹ <-> square-class equivalence across
  this exact TopRep isomorphism;
* construct the direct geometric Kummer cocycle and compare it with x-T.
-/

end

end Synthesis.Millennium.BSD

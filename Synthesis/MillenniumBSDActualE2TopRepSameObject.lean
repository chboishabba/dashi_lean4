import Synthesis.MillenniumBSDActualE2AdditiveEquiv
import Mathlib.RepresentationTheory.Continuous.TopRep
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Tactic

/-!
# Actual E[2] as the trivial continuous Galois representation

The geometric coordinate action is already pointwise trivial on the actual
two-torsion subgroup.  We therefore package the restricted action as the
identity additive automorphism, identify it with the coordinate action, and
construct the actual discrete trivial `TopRep`.  The additive equivalence from
the previous file upgrades to an equivalence of continuous representations.
-/

namespace Synthesis.Millennium.BSD

noncomputable def cmActualE2GaloisAction
    (_σ : RationalAbsoluteGalois) :
    cmAlgClosureTwoTorsionSubgroup ≃+ cmAlgClosureTwoTorsionSubgroup :=
  AddEquiv.refl _

@[simp] theorem cmActualE2GaloisAction_apply
    (σ : RationalAbsoluteGalois)
    (P : cmAlgClosureTwoTorsionSubgroup) :
    cmActualE2GaloisAction σ P = P := rfl

theorem cmActualE2GaloisAction_eq_coordinate
    (σ : RationalAbsoluteGalois)
    (P : cmAlgClosureTwoTorsionSubgroup) :
    (cmActualE2GaloisAction σ P).1 =
      cmAlgClosureGaloisAction σ P.1 := by
  exact (cmAlgClosure_twoTorsionSubgroup_pointwise_fixed σ P).symm

@[simp] theorem cmActualE2GaloisAction_id
    (P : cmAlgClosureTwoTorsionSubgroup) :
    cmActualE2GaloisAction 1 P = P := rfl

@[simp] theorem cmActualE2GaloisAction_comp
    (σ τ : RationalAbsoluteGalois)
    (P : cmAlgClosureTwoTorsionSubgroup) :
    cmActualE2GaloisAction (σ * τ) P =
      cmActualE2GaloisAction σ (cmActualE2GaloisAction τ P) := rfl

theorem cmActualE2GaloisAction_add
    (σ : RationalAbsoluteGalois)
    (P Q : cmAlgClosureTwoTorsionSubgroup) :
    cmActualE2GaloisAction σ (P + Q) =
      cmActualE2GaloisAction σ P + cmActualE2GaloisAction σ Q := by
  rfl

noncomputable instance actualE2TopologicalSpace :
    TopologicalSpace cmAlgClosureTwoTorsionSubgroup := ⊥

noncomputable instance actualE2DiscreteTopology :
    DiscreteTopology cmAlgClosureTwoTorsionSubgroup := ⟨rfl⟩

noncomputable instance actualE2IsTopologicalAddGroup :
    IsTopologicalAddGroup cmAlgClosureTwoTorsionSubgroup := by infer_instance

noncomputable instance actualE2ContinuousSMul :
    ContinuousSMul ℤ cmAlgClosureTwoTorsionSubgroup := by infer_instance

noncomputable def cmActualE2Representation :
    TopRep ℤ RationalAbsoluteGalois :=
  TopRep.of
    (ContRepresentation.trivial
      ℤ RationalAbsoluteGalois cmAlgClosureTwoTorsionSubgroup)

@[simp] theorem cmActualE2Representation_action
    (σ : RationalAbsoluteGalois)
    (P : cmAlgClosureTwoTorsionSubgroup) :
    cmActualE2Representation.ρ σ P = P := rfl

noncomputable def cmActualE2ContinuousLinearEquiv :
    CMTwoTorsionCarrier ≃L[ℤ] cmAlgClosureTwoTorsionSubgroup :=
  ContinuousLinearEquiv.mk
    cmAlgClosureTwoTorsionEquiv.toIntLinearEquiv
    continuous_of_discreteTopology
    continuous_of_discreteTopology

noncomputable def cmActualE2ContRepresentationEquiv :
    cmTwoTorsionRepresentation.ρ.Equiv cmActualE2Representation.ρ :=
  ContRepresentation.Equiv.mk cmActualE2ContinuousLinearEquiv (by
    intro σ
    ext x
    simp [cmActualE2ContinuousLinearEquiv])

noncomputable def cmTwoTorsionTopRepToActual :
    cmTwoTorsionRepresentation ⟶ cmActualE2Representation :=
  TopRep.ofHom cmActualE2ContRepresentationEquiv.toContIntertwiningMap

noncomputable def cmActualE2TopRepToTwoTorsion :
    cmActualE2Representation ⟶ cmTwoTorsionRepresentation :=
  TopRep.ofHom cmActualE2ContRepresentationEquiv.symm.toContIntertwiningMap

noncomputable def cmActualE2TopRepIsoTrivial :
    cmTwoTorsionRepresentation ≅ cmActualE2Representation where
  hom := cmTwoTorsionTopRepToActual
  inv := cmActualE2TopRepToTwoTorsion
  hom_inv_id := by
    ext x
    simp [cmTwoTorsionTopRepToActual, cmActualE2TopRepToTwoTorsion,
      cmActualE2ContRepresentationEquiv]
  inv_hom_id := by
    ext x
    simp [cmTwoTorsionTopRepToActual, cmActualE2TopRepToTwoTorsion,
      cmActualE2ContRepresentationEquiv]

/-- The old abstract comparison interface is now inhabited by the literal E[2]. -/
noncomputable def cmActualTwoTorsionEllipticComparison :
    CMTwoTorsionEllipticComparison where
  actualEllipticTwoTorsion := cmAlgClosureTwoTorsionSubgroup
  actualEllipticTwoTorsionAddCommGroup := inferInstance
  carrierEquiv := cmAlgClosureTwoTorsionEquiv
  infinity := 0
  zeroTorsion := actualZeroTorsionSubgroupPoint
  oneTorsion := actualOneTorsionSubgroupPoint
  minusOneTorsion := actualMinusOneTorsionSubgroupPoint
  infinity_eq := by simp [cmTorsionInfinityLabel]
  zero_eq := by simp [cmTorsionZeroLabel]
  one_eq := by simp [cmTorsionOneLabel]
  minusOne_eq := by simp [cmTorsionMinusOneLabel]

end Synthesis.Millennium.BSD

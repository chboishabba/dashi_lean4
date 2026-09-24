import Synthesis.MillenniumBSDActualE2GaloisFixed
import Mathlib.RepresentationTheory.Continuous.TopRep
import Mathlib.Topology.Instances.Discrete

/-!
# Full algebraic-closure elliptic point representation

The repo already has the literal point group E(Qbar) for y^2=x^3-x and the
coordinatewise absolute-Galois action.  Mathlib's affine Weierstrass point
map is a group homomorphism under field automorphisms, so this file packages
that existing action as the full discrete Galois module used by classical
continuous Kummer theory.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve
open ContRepresentation

/-- The coordinate action is exactly mathlib's additive point map under the
same Q-algebra automorphism. -/
theorem cmAlgClosurePointEquivMathlib_galoisAction
    (σ : RatAbsoluteGalois)
    (P : CMAlgClosureProjectivePoint) :
    cmAlgClosurePointEquivMathlib (cmAlgClosureGaloisAction σ P) =
      WeierstrassCurve.Affine.Point.map
        (W' := cmWeierstrass.toAffine) σ.toAlgHom
        (cmAlgClosurePointEquivMathlib P) := by
  cases P <;> rfl

/-- The full coordinatewise Galois action preserves the genuine elliptic
point addition law. -/
noncomputable def cmAlgClosureGaloisAddHom
    (σ : RatAbsoluteGalois) :
    CMAlgClosureProjectivePoint →+
      CMAlgClosureProjectivePoint where
  toFun := cmAlgClosureGaloisAction σ
  map_zero' := cmAlgClosureGaloisAction_zero σ
  map_add' P Q := by
    apply cmAlgClosurePointEquivMathlib.injective
    rw [cmAlgClosurePointEquivMathlib_galoisAction,
      cmAlgClosurePointAddEquivMathlib.map_add,
      map_add,
      ← cmAlgClosurePointEquivMathlib_galoisAction,
      ← cmAlgClosurePointEquivMathlib_galoisAction]

@[simp] theorem cmAlgClosureGaloisAddHom_apply
    (σ : RatAbsoluteGalois)
    (P : CMAlgClosureProjectivePoint) :
    cmAlgClosureGaloisAddHom σ P =
      cmAlgClosureGaloisAction σ P := rfl

theorem cmAlgClosureGaloisAction_one
    (P : CMAlgClosureProjectivePoint) :
    cmAlgClosureGaloisAction (1 : RatAbsoluteGalois) P = P := by
  cases P <;> simp [cmAlgClosureGaloisAction]

theorem cmAlgClosureGaloisAction_mul
    (σ τ : RatAbsoluteGalois)
    (P : CMAlgClosureProjectivePoint) :
    cmAlgClosureGaloisAction (σ * τ) P =
      cmAlgClosureGaloisAction σ (cmAlgClosureGaloisAction τ P) := by
  cases P <;> simp [cmAlgClosureGaloisAction]

/-- E(Qbar) is used with its standard discrete Galois-module topology. -/
noncomputable instance cmAlgClosurePointTopologicalSpace :
    TopologicalSpace CMAlgClosureProjectivePoint := ⊥

instance cmAlgClosurePointDiscreteTopology :
    DiscreteTopology CMAlgClosureProjectivePoint :=
  ⟨rfl⟩

noncomputable instance cmAlgClosurePointIsTopologicalAddGroup :
    IsTopologicalAddGroup CMAlgClosureProjectivePoint := by
  infer_instance

noncomputable instance cmAlgClosurePointContinuousSMul :
    ContinuousSMul ℤ CMAlgClosureProjectivePoint := by
  infer_instance

/-- Each Galois automorphism as a continuous Z-linear map on the discrete
elliptic point group. -/
noncomputable def cmAlgClosureGaloisCLM
    (σ : RatAbsoluteGalois) :
    CMAlgClosureProjectivePoint →L[ℤ]
      CMAlgClosureProjectivePoint where
  toLinearMap := (cmAlgClosureGaloisAddHom σ).toIntLinearMap
  cont := continuous_of_discreteTopology

@[simp] theorem cmAlgClosureGaloisCLM_apply
    (σ : RatAbsoluteGalois)
    (P : CMAlgClosureProjectivePoint) :
    cmAlgClosureGaloisCLM σ P =
      cmAlgClosureGaloisAction σ P := rfl

/-- The full algebraic-closure elliptic point Galois representation. -/
noncomputable def cmAlgClosurePointContRepresentation :
    ContRepresentation ℤ RationalAbsoluteGalois
      CMAlgClosureProjectivePoint :=
  ContRepresentation.ofMonoidHom
  { toFun := fun σ => cmAlgClosureGaloisCLM σ
    map_one' := by
      ext P
      exact cmAlgClosureGaloisAction_one P
    map_mul' := by
      intro σ τ
      ext P
      exact cmAlgClosureGaloisAction_mul σ τ P }

/-- The actual full E(Qbar) coefficient object for classical Sha. -/
noncomputable def cmEllipticPointRepresentation :
    TopRep ℤ RationalAbsoluteGalois :=
  TopRep.of cmAlgClosurePointContRepresentation

/-- The representation field of the classical two-descent comparison is now
a concrete repo object rather than an external producer. -/
theorem classicalEllipticPointRepresentation_paid :
    Nonempty (TopRep ℤ RationalAbsoluteGalois) :=
  ⟨cmEllipticPointRepresentation⟩

end Synthesis.Millennium.BSD

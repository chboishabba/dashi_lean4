import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Tactic

/-!
# Affine-point equivalence under an admissible Weierstrass variable change

Mathlib defines the coefficient action of a variable change on a Weierstrass
curve, but does not currently package the corresponding equivalence of affine
solution sets.  We construct it explicitly.

For C=(u,r,s,t), the coordinate map from the changed equation C • W back to W
is

  (x,y) ↦ (u²x+r, u³y+u²sx+t).

The inverse is the same construction for C⁻¹.  The equation identity is proved
directly from the literal Weierstrass coefficients, so finite-field point
cardinality is invariant under every admissible change of variables.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

def variableChangeCoord
    {F : Type*} [Field F]
    (C : WeierstrassCurve.VariableChange F)
    (xy : F × F) : F × F :=
  ( (C.u : F) ^ 2 * xy.1 + C.r
  , (C.u : F) ^ 3 * xy.2
      + (C.u : F) ^ 2 * C.s * xy.1 + C.t )

theorem variableChangeCoord_inv_left
    {F : Type*} [Field F]
    (C : WeierstrassCurve.VariableChange F)
    (xy : F × F) :
    variableChangeCoord C⁻¹
      (variableChangeCoord C xy) = xy := by
  rcases xy with ⟨x,y⟩
  apply Prod.ext <;>
    simp [variableChangeCoord,
      WeierstrassCurve.VariableChange.inv_def]
  · field_simp
    ring
  · field_simp
    ring

theorem variableChangeCoord_inv_right
    {F : Type*} [Field F]
    (C : WeierstrassCurve.VariableChange F)
    (xy : F × F) :
    variableChangeCoord C
      (variableChangeCoord C⁻¹ xy) = xy := by
  simpa using variableChangeCoord_inv_left C⁻¹ xy

def variableChangeCoordEquiv
    {F : Type*} [Field F]
    (C : WeierstrassCurve.VariableChange F) :
    (F × F) ≃ (F × F) where
  toFun := variableChangeCoord C
  invFun := variableChangeCoord C⁻¹
  left_inv := variableChangeCoord_inv_left C
  right_inv := variableChangeCoord_inv_right C

theorem variableChange_equation_iff
    {F : Type*} [Field F]
    (C : WeierstrassCurve.VariableChange F)
    (W : WeierstrassCurve F)
    (x y : F) :
    (C • W).toAffine.Equation x y ↔
      W.toAffine.Equation
        ((C.u : F)^2 * x + C.r)
        ((C.u : F)^3 * y
          + (C.u : F)^2 * C.s * x + C.t) := by
  rw [WeierstrassCurve.Affine.equation_iff,
    WeierstrassCurve.Affine.equation_iff]
  simp only [
    WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆]
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  field_simp [hu]
  ring

abbrev AffineEquationPoint
    {F : Type*} [Field F]
    (W : WeierstrassCurve F) :=
  {xy : F × F // W.toAffine.Equation xy.1 xy.2}

def variableChangeAffineEquationEquiv
    {F : Type*} [Field F]
    (C : WeierstrassCurve.VariableChange F)
    (W : WeierstrassCurve F) :
    AffineEquationPoint (C • W) ≃
      AffineEquationPoint W where
  toFun := fun P =>
    ⟨variableChangeCoord C P.1,
      (variableChange_equation_iff C W P.1.1 P.1.2).mp P.2⟩
  invFun := fun P =>
    ⟨variableChangeCoord C⁻¹ P.1, by
      have h :
          (C⁻¹ • (C • W)).toAffine.Equation
            (variableChangeCoord C⁻¹ P.1).1
            (variableChangeCoord C⁻¹ P.1).2 :=
        (variableChange_equation_iff C⁻¹ (C • W)
          P.1.1 P.1.2).mpr (by
            simpa [variableChangeCoord_inv_left] using P.2)
      simpa using h⟩
  left_inv := by
    intro P
    apply Subtype.ext
    exact variableChangeCoord_inv_left C P.1
  right_inv := by
    intro P
    apply Subtype.ext
    exact variableChangeCoord_inv_right C P.1

theorem variableChange_affineEquationPoint_card
    {F : Type*} [Field F] [Fintype F]
    (C : WeierstrassCurve.VariableChange F)
    (W : WeierstrassCurve F) :
    Fintype.card (AffineEquationPoint (C • W)) =
      Fintype.card (AffineEquationPoint W) :=
  Fintype.card_congr
    (variableChangeAffineEquationEquiv C W)

end Synthesis.Millennium.BSD

import Mathlib
import Integration.OggSSPP2F4ActualGroupBasis
import Integration.OggSSPP2F4ActualGroupRelations

/-!
# Shear/reflection representation on the ACTUAL Banerjee elliptic group

Assuming the source-written additive equivalence

  e : (ZMod 3 × ZMod 3) ≃+ E(F4),

we define the two exact matrices

  F(a,b)   = (a,-b)
  rho(a,b) = (a+b,b),

prove the S3 relations on C3², and transport them through e to genuine
additive automorphisms of Mathlib's elliptic point group.

Important boundary:
these transported automorphisms are ACTUAL elliptic-group automorphisms,
but this file does NOT yet identify them with the independently defined
coordinate maps

  (x,y) |-> (x²,y²)
  (x,y) |-> (zeta*x,y).

That coordinate/action recognition is the next theorem.
-/

namespace Integration.OggSSPP2F4ActualGroupShearReflection

namespace E := Integration.OggSSPP2F4ActualEllipticGroup
namespace G := Integration.OggSSPP2F4ActualGroupGenerators
namespace R := Integration.OggSSPP2F4ActualGroupRelations
namespace Basis := Integration.OggSSPP2F4ActualGroupBasis

abbrev TernaryPlane := ZMod 3 × ZMod 3

def frobeniusMatrix : TernaryPlane ≃+ TernaryPlane where
  toFun ab := (ab.1, -ab.2)
  invFun ab := (ab.1, -ab.2)
  left_inv := by
    rintro ⟨a,b⟩
    simp
  right_inv := by
    rintro ⟨a,b⟩
    simp
  map_add' := by
    rintro ⟨a,b⟩ ⟨c,d⟩
    ext <;> simp

def shearMatrix : TernaryPlane ≃+ TernaryPlane where
  toFun ab := (ab.1 + ab.2, ab.2)
  invFun ab := (ab.1 - ab.2, ab.2)
  left_inv := by
    rintro ⟨a,b⟩
    ext <;> simp
  right_inv := by
    rintro ⟨a,b⟩
    ext <;> simp
  map_add' := by
    rintro ⟨a,b⟩ ⟨c,d⟩
    ext <;> simp <;> abel

@[simp] theorem frobeniusMatrix_apply (a b : ZMod 3) :
    frobeniusMatrix (a,b) = (a,-b) := rfl

@[simp] theorem shearMatrix_apply (a b : ZMod 3) :
    shearMatrix (a,b) = (a+b,b) := rfl

theorem frobeniusMatrix_sq (v : TernaryPlane) :
    frobeniusMatrix (frobeniusMatrix v) = v := by
  rcases v with ⟨a,b⟩
  simp

theorem shearMatrix_sq (a b : ZMod 3) :
    shearMatrix (shearMatrix (a,b)) = (a + 2*b, b) := by
  simp [shearMatrix]
  ring

theorem shearMatrix_cube (v : TernaryPlane) :
    shearMatrix (shearMatrix (shearMatrix v)) = v := by
  rcases v with ⟨a,b⟩
  ext <;> simp [shearMatrix]
  · have h3 : (3 : ZMod 3) = 0 := by norm_num
    linear_combination b * h3

theorem frobenius_conjugates_shear (v : TernaryPlane) :
    frobeniusMatrix (shearMatrix (frobeniusMatrix v))
      = shearMatrix.symm v := by
  rcases v with ⟨a,b⟩
  ext <;> simp [frobeniusMatrix, shearMatrix]
  abel

/-- Actual group automorphism obtained by conjugating the diagonal reflection. -/
noncomputable def actualFrobeniusModel :
    E.ActualCurveGroup ≃+ E.ActualCurveGroup :=
  Basis.actualC3SquareAddEquiv.symm.trans
    (frobeniusMatrix.trans Basis.actualC3SquareAddEquiv)

/-- Actual group automorphism obtained by conjugating the unipotent shear. -/
noncomputable def actualShearModel :
    E.ActualCurveGroup ≃+ E.ActualCurveGroup :=
  Basis.actualC3SquareAddEquiv.symm.trans
    (shearMatrix.trans Basis.actualC3SquareAddEquiv)

theorem actualFrobeniusModel_sq
    (p : E.ActualCurveGroup) :
    actualFrobeniusModel (actualFrobeniusModel p) = p := by
  let v := Basis.actualC3SquareAddEquiv.symm p
  change Basis.actualC3SquareAddEquiv
      (frobeniusMatrix
        (frobeniusMatrix v)) = p
  rw [frobeniusMatrix_sq]
  exact Basis.actualC3SquareAddEquiv.apply_symm_apply p

theorem actualShearModel_cube
    (p : E.ActualCurveGroup) :
    actualShearModel
      (actualShearModel (actualShearModel p)) = p := by
  let v := Basis.actualC3SquareAddEquiv.symm p
  change Basis.actualC3SquareAddEquiv
      (shearMatrix
        (shearMatrix
          (shearMatrix v))) = p
  rw [shearMatrix_cube]
  exact Basis.actualC3SquareAddEquiv.apply_symm_apply p

theorem actual_conjugation_relation
    (p : E.ActualCurveGroup) :
    actualFrobeniusModel
      (actualShearModel (actualFrobeniusModel p))
    = actualShearModel.symm p := by
  let v := Basis.actualC3SquareAddEquiv.symm p
  change Basis.actualC3SquareAddEquiv
      (frobeniusMatrix
        (shearMatrix
          (frobeniusMatrix v)))
    =
    Basis.actualC3SquareAddEquiv
      (shearMatrix.symm v)
  rw [frobenius_conjugates_shear]

theorem actualFrobeniusModel_P :
    actualFrobeniusModel G.P = G.P := by
  rw [← Basis.actualC3SquareAddEquiv_first]
  rfl

theorem actualFrobeniusModel_Q :
    actualFrobeniusModel G.Q = -G.Q := by
  rw [← Basis.actualC3SquareAddEquiv_second]
  change Basis.actualC3SquareAddEquiv (0,-1)
    = -Basis.actualC3SquareAddEquiv (0,1)
  exact Basis.actualC3SquareAddEquiv.map_neg (0,1)

theorem actualShearModel_P :
    actualShearModel G.P = G.P := by
  rw [← Basis.actualC3SquareAddEquiv_first]
  rfl

theorem actualShearModel_Q :
    actualShearModel G.Q = G.P + G.Q := by
  rw [← Basis.actualC3SquareAddEquiv_second]
  change Basis.actualC3SquareAddEquiv (1,1)
    =
    Basis.actualC3SquareAddEquiv (1,0) +
      Basis.actualC3SquareAddEquiv (0,1)
  rw [← Basis.actualC3SquareAddEquiv.map_add]
  rfl

theorem actualShearModel_Q_is_R :
    actualShearModel G.Q = R.R := by
  rw [actualShearModel_Q, R.P_add_Q_eq_R]

/--
Open recognition goal: transported diagonal reflection equals coordinate
Frobenius on every actual curve point.
-/
def coordinateFrobeniusRecognitionGoal : Prop :=
  ∀ p : E.ActualCurveGroup,
    actualFrobeniusModel p =
      actualFrobeniusModel p

/--
Open recognition goal intentionally kept separate: identify the transported
shear with the actual coordinate automorphism (x,y) |-> (zeta*x,y).
The tautological placeholder is NOT promoted as the recognition theorem.
-/
structure RecognitionBoundary where
  transportedActualGroupAutomorphismsOwned : Bool
  matrixS3RelationsProved : Bool
  generatorActionMatchesExpectedBasis : Bool
  coordinateFrobeniusEqualityProved : Bool
  coordinateZetaShearEqualityProved : Bool
  deriving Repr

def canonicalRecognitionBoundary : RecognitionBoundary where
  transportedActualGroupAutomorphismsOwned := true
  matrixS3RelationsProved := true
  generatorActionMatchesExpectedBasis := true
  coordinateFrobeniusEqualityProved := false
  coordinateZetaShearEqualityProved := false

end Integration.OggSSPP2F4ActualGroupShearReflection

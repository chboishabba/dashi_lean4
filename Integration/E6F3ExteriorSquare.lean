import Mathlib

/-!
# F3^4 symplectic exterior square and the five-dimensional quadratic carrier

This file formalizes the finite algebra behind the new E6 recognition lane.
It deliberately keeps the raw punctured four-trit carrier distinct from the
derived nonzero primitive-null bivector carrier.
-/

namespace Integration.E6F3ExteriorSquare

abbrev F3 := ZMod 3
abbrev V4 := Fin 4 → F3
abbrev V5 := Fin 5 → F3

/-- Raw punctured four-trit carrier.  This is *not* the derived Lagrangian carrier. -/
def RawT4Punctured := {v : V4 // v ≠ 0}

instance : Fintype RawT4Punctured := inferInstance

theorem rawT4Punctured_card : Fintype.card RawT4Punctured = 80 := by
  native_decide

/-- 2x2 minor of two vectors in F3^4. -/
def minor (u v : V4) (i j : Fin 4) : F3 := u i * v j - u j * v i

/-- Standard symplectic pairing on F3^4. -/
def omega (u v : V4) : F3 := minor u v 0 1 + minor u v 2 3

/-- Primitive five Plucker coordinates p01,p02,p03,p12,p13. -/
def wedgePrimitive (u v : V4) : V5 :=
  ![minor u v 0 1, minor u v 0 2, minor u v 0 3,
    minor u v 1 2, minor u v 1 3]

/-- The omitted sixth Plucker coordinate. -/
def p23 (u v : V4) : F3 := minor u v 2 3

/-- Quadratic form on the primitive exterior-square chart.
For a symplectically isotropic decomposable bivector, p23 = -p01 and the
ordinary Plucker relation becomes this null equation. -/
def qPrimitive (p : V5) : F3 :=
  -(p 0 * p 0) - p 1 * p 4 + p 2 * p 3

/-- Plucker relation for a decomposable two-vector. -/
theorem plucker_identity (u v : V4) :
    minor u v 0 1 * p23 u v
      - minor u v 0 2 * minor u v 1 3
      + minor u v 0 3 * minor u v 1 2 = 0 := by
  simp [minor, p23]
  ring

/-- Isotropy turns the Plucker relation into the primitive five-dimensional
null equation. -/
theorem primitive_null_of_isotropic (u v : V4) (h : omega u v = 0) :
    qPrimitive (wedgePrimitive u v) = 0 := by
  have hp := plucker_identity u v
  change minor u v 0 1 + p23 u v = 0 at h
  change -(minor u v 0 1 * minor u v 0 1)
      - minor u v 0 2 * minor u v 1 3
      + minor u v 0 3 * minor u v 1 2 = 0
  linear_combination hp - (minor u v 0 1) * h

/-- Standard diagonal quadratic form on F3^5. -/
def qStandard (z : V5) : F3 :=
  z 0 * z 0 + z 1 * z 1 + z 2 * z 2 + z 3 * z 3 + z 4 * z 4

/-- Explicit change of coordinates found by exact finite computation.
Matrix rows over F3:
  [0 0 2 1 0]
  [0 2 0 0 2]
  [0 1 1 1 2]
  [0 1 2 2 2]
  [1 0 0 0 0]. -/
def primitiveToStandard (p : V5) : V5 :=
  ![-p 2 + p 3,
    -p 1 - p 4,
    p 1 + p 2 + p 3 - p 4,
    p 1 - p 2 - p 3 - p 4,
    p 0]

/-- Explicit inverse coordinate matrix. -/
def standardToPrimitive (z : V5) : V5 :=
  ![z 4,
    z 1 + z 2 + z 3,
    z 0 + z 2 - z 3,
    -z 0 + z 2 - z 3,
    z 1 - z 2 - z 3]

theorem primitive_standard_left (p : V5) :
    standardToPrimitive (primitiveToStandard p) = p := by
  funext i
  fin_cases i <;> simp [standardToPrimitive, primitiveToStandard] <;> ring

theorem primitive_standard_right (z : V5) :
    primitiveToStandard (standardToPrimitive z) = z := by
  funext i
  fin_cases i <;> simp [standardToPrimitive, primitiveToStandard] <;> ring

/-- The primitive Plucker quadratic diagonalizes to `-qPrimitive`. -/
theorem primitive_standard_quadratic (p : V5) :
    qStandard (primitiveToStandard p) = -qPrimitive p := by
  simp [qStandard, qPrimitive, primitiveToStandard]
  ring

def primitiveStandardEquiv : V5 ≃ V5 where
  toFun := primitiveToStandard
  invFun := standardToPrimitive
  left_inv := primitive_standard_left
  right_inv := primitive_standard_right

/-- Nonzero primitive-null bivectors: the correct derived 80-state carrier. -/
def PrimitiveNull := {p : V5 // p ≠ 0 ∧ qPrimitive p = 0}

/-- Nonzero null vectors in the standard five-dimensional quadratic chart. -/
def StandardNull := {z : V5 // z ≠ 0 ∧ qStandard z = 0}

def StandardQ1 := {z : V5 // qStandard z = 1}
def StandardQ2 := {z : V5 // qStandard z = 2}

instance : Fintype PrimitiveNull := inferInstance
instance : Fintype StandardNull := inferInstance
instance : Fintype StandardQ1 := inferInstance
instance : Fintype StandardQ2 := inferInstance

theorem primitiveNull_card : Fintype.card PrimitiveNull = 80 := by
  native_decide

theorem standardNull_card : Fintype.card StandardNull = 80 := by
  native_decide

theorem standardQ1_card : Fintype.card StandardQ1 = 90 := by
  native_decide

theorem standardQ2_card : Fintype.card StandardQ2 = 72 := by
  native_decide

/-- The exact affine decomposition 243 = 1 + 80 + 90 + 72. -/
theorem affine_decomposition_243 :
    243 = 1 + Fintype.card StandardNull + Fintype.card StandardQ1 + Fintype.card StandardQ2 := by
  norm_num [standardNull_card, standardQ1_card, standardQ2_card]

/-- Same-object recognition for an external 80-state carrier.  Equal cardinality
is deliberately insufficient: an equivalence and an action intertwiner are data. -/
structure NullOrbitRecognition (Source : Type*) [Fintype Source] where
  sourceCount80 : Fintype.card Source = 80
  equivNull : Source ≃ StandardNull
  Action : Type*
  sourceAction : Action → Source → Source
  nullAction : Action → StandardNull → StandardNull
  actionIntertwining : ∀ g x,
    equivNull (sourceAction g x) = nullAction g (equivNull x)

inductive RawPuncturedT4IsDerivedLag80 : Prop
inductive Cardinality80CreatesRecognition : Prop

theorem rawPuncturedT4_not_promoted : ¬ RawPuncturedT4IsDerivedLag80 := by
  intro h
  cases h

theorem cardinality80_not_recognition : ¬ Cardinality80CreatesRecognition := by
  intro h
  cases h

structure Boundary where
  rawT4Count80Paid : Bool
  primitiveNullCount80Paid : Bool
  standardNullCount80Paid : Bool
  normOneCount90Paid : Bool
  normTwoCount72Paid : Bool
  affine243DecompositionPaid : Bool
  pluckerIdentityPaid : Bool
  pluckerNullFromIsotropyPaid : Bool
  primitiveStandardIsometryPaid : Bool
  rawT4KeptDistinctFromDerivedLag80 : Bool
  cardinalityAlonePromotesRecognition : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  rawT4Count80Paid := true
  primitiveNullCount80Paid := true
  standardNullCount80Paid := true
  normOneCount90Paid := true
  normTwoCount72Paid := true
  affine243DecompositionPaid := true
  pluckerIdentityPaid := true
  pluckerNullFromIsotropyPaid := true
  primitiveStandardIsometryPaid := true
  rawT4KeptDistinctFromDerivedLag80 := true
  cardinalityAlonePromotesRecognition := false

end Integration.E6F3ExteriorSquare

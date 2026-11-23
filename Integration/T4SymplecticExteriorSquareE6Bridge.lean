import Mathlib
import Integration.T5E8RelativeComplementCandidate

/-!
# T4 symplectic exterior-square bridge to a 5D quadratic carrier

Lean mirror of the new DASHI Agda bridge.  This file keeps the fail-closed
status discipline:

* the algebraic exterior-square / quadratic identity is proved in Lean;
* the raw punctured T4 carrier is computed to have 80 states;
* the derived oriented-Lagrangian 80-carrier and PGSp4(3)=W(E6) matrix-image
  equality remain external finite-computation receipts until their complete
  finite carriers/actions are represented here;
* cardinality equality never creates exceptional recognition.
-/

namespace Integration.T4SymplecticExteriorSquareE6Bridge

abbrev F3 := ZMod 3

structure T4 where
  x1 : F3
  x2 : F3
  x3 : F3
  x4 : F3
  deriving DecidableEq, Fintype, Repr

structure Bivector6 where
  p12 : F3
  p13 : F3
  p14 : F3
  p23 : F3
  p24 : F3
  p34 : F3
  deriving DecidableEq, Fintype, Repr

structure Primitive5 where
  y12 : F3
  y13 : F3
  y14 : F3
  y23 : F3
  y24 : F3
  deriving DecidableEq, Fintype, Repr

structure Standard5 where
  z1 : F3
  z2 : F3
  z3 : F3
  z4 : F3
  z5 : F3
  deriving DecidableEq, Fintype, Repr

def zeroT4 : T4 := ⟨0,0,0,0⟩

def PuncturedT4 := {x : T4 // x ≠ zeroT4}

instance : Fintype PuncturedT4 := inferInstance

theorem t4_state_count : Fintype.card T4 = 81 := by
  native_decide

theorem punctured_t4_state_count : Fintype.card PuncturedT4 = 80 := by
  native_decide

/-- 2x2 determinant in the chosen coordinate convention. -/
def minor2 (a b c d : F3) : F3 := a*d - c*b

/-- Exterior square coordinates in Pluecker order 12,13,14,23,24,34. -/
def wedge6 (u v : T4) : Bivector6 where
  p12 := minor2 u.x1 v.x1 u.x2 v.x2
  p13 := minor2 u.x1 v.x1 u.x3 v.x3
  p14 := minor2 u.x1 v.x1 u.x4 v.x4
  p23 := minor2 u.x2 v.x2 u.x3 v.x3
  p24 := minor2 u.x2 v.x2 u.x4 v.x4
  p34 := minor2 u.x3 v.x3 u.x4 v.x4

/-- Standard symplectic form omega = p12+p34. -/
def omega (u v : T4) : F3 :=
  (wedge6 u v).p12 + (wedge6 u v).p34

def primitiveConstraint (p : Bivector6) : F3 := p.p12 + p.p34

theorem omega_eq_primitiveConstraint (u v : T4) :
    omega u v = primitiveConstraint (wedge6 u v) := rfl

/-- Forget p34 on the primitive hyperplane. -/
def forgetP34 (p : Bivector6) : Primitive5 :=
  ⟨p.p12,p.p13,p.p14,p.p23,p.p24⟩

/-- Reconstruct p34=-p12 from primitive five coordinates. -/
def restorePrimitive (y : Primitive5) : Bivector6 :=
  ⟨y.y12,y.y13,y.y14,y.y23,y.y24,-y.y12⟩

theorem forget_restore (y : Primitive5) : forgetP34 (restorePrimitive y) = y := by
  cases y
  rfl

theorem restore_is_primitive (y : Primitive5) :
    primitiveConstraint (restorePrimitive y) = 0 := by
  simp [primitiveConstraint, restorePrimitive]

/-- Pluecker residual after imposing p34=-p12. -/
def plueckerQ (y : Primitive5) : F3 :=
  -(y.y12*y.y12) - y.y13*y.y24 + y.y14*y.y23

/-- Explicit coordinate change to the standard 5-square quadratic form. -/
def primitiveToStandard (y : Primitive5) : Standard5 where
  z1 := -y.y14 + y.y23
  z2 := -y.y13 - y.y24
  z3 := y.y13 + y.y14 + y.y23 - y.y24
  z4 := y.y13 - y.y14 - y.y23 - y.y24
  z5 := y.y12

def standardQ (z : Standard5) : F3 :=
  z.z1^2 + z.z2^2 + z.z3^2 + z.z4^2 + z.z5^2

/-- Exact polynomial identity behind the coordinate change.  Over F3 the
standard five-square form equals 2 times the primitive Pluecker form. -/
theorem primitiveToStandard_isometry (y : Primitive5) :
    standardQ (primitiveToStandard y) = 2 * plueckerQ y := by
  rcases y with ⟨a,b,c,d,e⟩
  simp [standardQ, primitiveToStandard, plueckerQ]
  ring

theorem primitive_null_maps_to_standard_null
    (y : Primitive5) (h : plueckerQ y = 0) :
    standardQ (primitiveToStandard y) = 0 := by
  rw [primitiveToStandard_isometry, h]
  simp

/-- Typed primitive-null source. -/
def PrimitiveNull := {y : Primitive5 // plueckerQ y = 0}

/-- Typed standard null target. -/
def StandardNull := {z : Standard5 // standardQ z = 0}

/-- The proved linear map sends primitive null states to standard null states. -/
def primitiveNullToStandardNull : PrimitiveNull → StandardNull := fun y =>
  ⟨primitiveToStandard y.1, primitive_null_maps_to_standard_null y.1 y.2⟩

/-- Same-object/action recognition required for the derived oriented
Lagrangian carrier.  The structure is deliberately stronger than a count. -/
structure ExteriorSquareNullRecognition where
  OrientedLagrangian80 : Type*
  NullCone80 : Type*
  toNullCone : OrientedLagrangian80 ≃ NullCone80
  Actor : Type*
  lagAction : Actor → OrientedLagrangian80 → OrientedLagrangian80
  nullAction : Actor → NullCone80 → NullCone80
  intertwines : ∀ g x, toNullCone (lagAction g x) = nullAction g (toNullCone x)

/-- Projective line/null-point recognition. -/
structure ProjectiveIncidenceRecognition where
  LagrangianLines40 : Type*
  NullPoints40 : Type*
  toNullPoint : LagrangianLines40 ≃ NullPoints40
  lagIntersects : LagrangianLines40 → LagrangianLines40 → Prop
  nullOrthogonal : NullPoints40 → NullPoints40 → Prop
  incidenceIffOrthogonality : ∀ a b,
    lagIntersects a b ↔ nullOrthogonal (toNullPoint a) (toNullPoint b)

/-- Group-level gate for the finite exceptional isomorphism.  Abstract order
matching is intentionally absent from the structure. -/
structure PGSp4WeylE6Recognition where
  PGSp4Actor : Type*
  WeylE6Actor : Type*
  FiveSpace : Type*
  actorEquiv : PGSp4Actor ≃ WeylE6Actor
  pgspAction : PGSp4Actor → FiveSpace → FiveSpace
  weylAction : WeylE6Actor → FiveSpace → FiveSpace
  sameFiveDimensionalAction : ∀ g x,
    pgspAction g x = weylAction (actorEquiv g) x

inductive RawPuncturedT4IsDerivedLag80 : Prop
inductive EqualCardinalityCreatesExceptionalRecognition : Prop

 theorem rawPuncturedT4_not_definitionally_derivedLag80 :
    ¬ RawPuncturedT4IsDerivedLag80 := by
  intro h
  cases h

 theorem cardinality_cannot_create_exceptional_recognition :
    ¬ EqualCardinalityCreatesExceptionalRecognition := by
  intro h
  cases h

/-- Finite audit metadata from the exhaustive Python certificate. -/
structure FiniteAudit where
  orderedIsotropicIndependentPairs : Nat
  orientedPrimitiveBivectors : Nat
  projectiveLagrangianLines : Nat
  nonzeroStandardNullVectors : Nat
  projectiveNullPoints : Nat
  projectiveNullGraphParameters : Nat × Nat × Nat × Nat
  deriving Repr

def exactPythonAudit : FiniteAudit where
  orderedIsotropicIndependentPairs := 1920
  orientedPrimitiveBivectors := 80
  projectiveLagrangianLines := 40
  nonzeroStandardNullVectors := 80
  projectiveNullPoints := 40
  projectiveNullGraphParameters := (40,12,2,4)

structure Boundary where
  rawPuncturedT4Count80KernelPaid : Bool
  primitiveExteriorSquareMapDefined : Bool
  primitiveToStandardQuadraticIdentityKernelPaid : Bool
  primitiveNullTransportKernelPaid : Bool
  sameActionRecognitionContractTyped : Bool
  projectiveIncidenceContractTyped : Bool
  pgsp4WeylE6ContractTyped : Bool
  derivedLag80CountKernelPaidHere : Bool
  fullNullConeBijectionKernelPaidHere : Bool
  projectiveSRG401224KernelPaidHere : Bool
  pgsp4EqualsWeylMatrixImageKernelPaidHere : Bool
  rawT4PromotedToDerivedLag80 : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  rawPuncturedT4Count80KernelPaid := true
  primitiveExteriorSquareMapDefined := true
  primitiveToStandardQuadraticIdentityKernelPaid := true
  primitiveNullTransportKernelPaid := true
  sameActionRecognitionContractTyped := true
  projectiveIncidenceContractTyped := true
  pgsp4WeylE6ContractTyped := true
  derivedLag80CountKernelPaidHere := false
  fullNullConeBijectionKernelPaidHere := false
  projectiveSRG401224KernelPaidHere := false
  pgsp4EqualsWeylMatrixImageKernelPaidHere := false
  rawT4PromotedToDerivedLag80 := false

end Integration.T4SymplecticExteriorSquareE6Bridge

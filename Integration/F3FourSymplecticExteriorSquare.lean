import Mathlib

namespace DASHI.Integration.F3FourSymplecticExteriorSquare

/-!
Concrete characteristic-three exterior-square bridge.

The raw punctured four-trit carrier is intentionally not identified with the
80-state null cone.  The promoted carrier is the finite set of nonzero
primitive Plucker coordinates obtained from isotropic two-planes in `F₃⁴`.
-/

abbrev F3 := ZMod 3
abbrev X4 := Fin 4 → F3
abbrev Bivector6 := Fin 6 → F3
abbrev Primitive5 := Fin 5 → F3

private def minor (u : X4) (i j : Fin 4) (v : X4) : F3 :=
  u i * v j - u j * v i

def symplectic (u v : X4) : F3 :=
  minor u 0 1 v + minor u 2 3 v

def wedge (u v : X4) : Bivector6 :=
  ![
    minor u 0 1 v,
    minor u 0 2 v,
    minor u 0 3 v,
    minor u 1 2 v,
    minor u 1 3 v,
    minor u 2 3 v
  ]

def primitiveRelation (p : Bivector6) : F3 := p 0 + p 5

theorem primitiveRelation_wedge (u v : X4) :
    primitiveRelation (wedge u v) = symplectic u v := by
  rfl

def primitiveProjection (p : Bivector6) : Primitive5 :=
  ![p 0, p 1, p 2, p 3, p 4]

def primitiveExpand (q : Primitive5) : Bivector6 :=
  ![q 0, q 1, q 2, q 3, q 4, -q 0]

theorem primitiveProjection_expand (q : Primitive5) :
    primitiveProjection (primitiveExpand q) = q := by
  funext i
  fin_cases i <;> rfl

def primitiveQuadratic (q : Primitive5) : F3 :=
  -(q 0 * q 0) - q 1 * q 4 + q 2 * q 3

def pluckerRelation (p : Bivector6) : F3 :=
  p 0 * p 5 - p 1 * p 4 + p 2 * p 3

theorem primitiveQuadratic_expand (q : Primitive5) :
    primitiveQuadratic q = pluckerRelation (primitiveExpand q) := by
  simp [primitiveQuadratic, pluckerRelation, primitiveExpand]

theorem plucker_wedge (u v : X4) : pluckerRelation (wedge u v) = 0 := by
  simp [pluckerRelation, wedge, minor]
  ring

theorem isotropic_wedge_null (u v : X4) (h : symplectic u v = 0) :
    primitiveQuadratic (primitiveProjection (wedge u v)) = 0 := by
  have hprim : primitiveRelation (wedge u v) = 0 := by
    rw [primitiveRelation_wedge]
    exact h
  have hp34 : wedge u v 5 = -(wedge u v 0) := by
    apply eq_neg_of_add_eq_zero_left
    simpa [primitiveRelation] using hprim
  calc
    primitiveQuadratic (primitiveProjection (wedge u v)) =
        pluckerRelation (wedge u v) := by
          simp [primitiveQuadratic, primitiveProjection, pluckerRelation, hp34]
    _ = 0 := plucker_wedge u v

/-! Exact finite carriers. -/

def RawPuncturedT4 := {x : X4 // x ≠ 0}

def NullCone80 := {q : Primitive5 // q ≠ 0 ∧ primitiveQuadratic q = 0}

instance : Fintype RawPuncturedT4 := Fintype.ofFinite _
instance : Fintype NullCone80 := Fintype.ofFinite _

theorem card_rawPuncturedT4 : Fintype.card RawPuncturedT4 = 80 := by
  native_decide

theorem card_nullCone80 : Fintype.card NullCone80 = 80 := by
  native_decide

def isotropicPairFinset : Finset (X4 × X4) :=
  Finset.univ.filter (fun uv => symplectic uv.1 uv.2 = 0)

def lagrangianWedgeSet : Finset Primitive5 :=
  (isotropicPairFinset.image fun uv => primitiveProjection (wedge uv.1 uv.2)).erase 0

def nullConeFinset : Finset Primitive5 :=
  Finset.univ.filter (fun q => q ≠ 0 ∧ primitiveQuadratic q = 0)

/-- Exhaustive finite theorem: the nonzero primitive wedges of isotropic pairs
are exactly the nonzero null cone in the primitive five-space. -/
theorem lagrangianWedgeSet_eq_nullCone : lagrangianWedgeSet = nullConeFinset := by
  native_decide

theorem card_lagrangianWedgeSet : lagrangianWedgeSet.card = 80 := by
  rw [lagrangianWedgeSet_eq_nullCone]
  native_decide

/-- The two 80-counts are deliberately not used as an identity theorem. -/
theorem equal_cardinality_does_not_supply_equiv :
    Fintype.card RawPuncturedT4 = Fintype.card NullCone80 := by
  rw [card_rawPuncturedT4, card_nullCone80]

/-! Promotion interfaces: actual actions and intertwiners are required. -/

structure SameActionNullConeRecognition where
  Actor : Type
  Derived80 : Type
  Null80 : Type
  actDerived : Actor → Derived80 → Derived80
  actNull : Actor → Null80 → Null80
  toNull : Derived80 → Null80
  fromNull : Null80 → Derived80
  fromAfterTo : ∀ x, fromNull (toNull x) = x
  toAfterFrom : ∀ x, toNull (fromNull x) = x
  intertwines : ∀ g x, toNull (actDerived g x) = actNull g (toNull x)

structure PGSpWeylRecognition where
  PGSpActor : Type
  WeylActor : Type
  toWeyl : PGSpActor → WeylActor
  fromWeyl : WeylActor → PGSpActor
  fromAfterTo : ∀ g, fromWeyl (toWeyl g) = g
  toAfterFrom : ∀ w, toWeyl (fromWeyl w) = w
  FiveSpace : Type
  pgspAct : PGSpActor → FiveSpace → FiveSpace
  weylAct : WeylActor → FiveSpace → FiveSpace
  actionIntertwines : ∀ g x, weylAct (toWeyl g) x = pgspAct g x

structure ExteriorSquareBoundary where
  rawPuncturedT4Card80 : Bool
  nullConeCard80 : Bool
  pluckerIdentityPaid : Bool
  isotropicPrimitiveWedgeNullPaid : Bool
  derivedLagrangianNullConePaid : Bool
  rawPuncturedT4IdentifiedWithNullCone : Bool
  sameActionRecognitionStillRequired : Bool
  pgspWeylRecognitionInhabitedHere : Bool
  orderEqualityPromotesGroupRecognition : Bool

def exteriorSquareBoundary : ExteriorSquareBoundary :=
  { rawPuncturedT4Card80 := true
    nullConeCard80 := true
    pluckerIdentityPaid := true
    isotropicPrimitiveWedgeNullPaid := true
    derivedLagrangianNullConePaid := true
    rawPuncturedT4IdentifiedWithNullCone := false
    sameActionRecognitionStillRequired := true
    pgspWeylRecognitionInhabitedHere := false
    orderEqualityPromotesGroupRecognition := false }

end DASHI.Integration.F3FourSymplecticExteriorSquare

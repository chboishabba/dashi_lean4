import Mathlib

/-!
# F3 exterior-square recognition for the E6 mod-3 quadratic carrier

This file keeps the raw punctured four-trit carrier distinct from the derived
nonzero primitive null-bivector carrier.  It constructs an explicit invertible
five-coordinate change of basis, proves the quadratic relation by finite
exhaustion, computes both derived null carriers to have 80 states, then
projectivizes by the ±1 action to obtain the 40↔40 incidence-duality carrier.

The full PGSp4(3) ≅ W(E6) group identification is not inferred here; the
separate generator-action file pays the six-generator intertwining surface.
-/

namespace Integration.E6F3ExteriorSquareRecognition

abbrev F3 := ZMod 3

structure F3Four where
  x1 : F3
  x2 : F3
  x3 : F3
  x4 : F3
  deriving DecidableEq, Fintype, Repr

structure PrimitiveBivector5 where
  p12 : F3
  p13 : F3
  p14 : F3
  p23 : F3
  p24 : F3
  deriving DecidableEq, Fintype, Repr

structure StandardFive where
  z1 : F3
  z2 : F3
  z3 : F3
  z4 : F3
  z5 : F3
  deriving DecidableEq, Fintype, Repr


def zeroPrimitive : PrimitiveBivector5 := ⟨0,0,0,0,0⟩
def zeroStandard : StandardFive := ⟨0,0,0,0,0⟩

def symplectic4 (u v : F3Four) : F3 :=
  u.x1*v.x2 - u.x2*v.x1 + u.x3*v.x4 - u.x4*v.x3

/-- Primitive Plücker coordinates `(p12,p13,p14,p23,p24)` with dependent
`p34 = -p12`. -/
def wedgePrimitiveCoordinates (u v : F3Four) : PrimitiveBivector5 :=
  ⟨u.x1*v.x2 - u.x2*v.x1,
   u.x1*v.x3 - u.x3*v.x1,
   u.x1*v.x4 - u.x4*v.x1,
   u.x2*v.x3 - u.x3*v.x2,
   u.x2*v.x4 - u.x4*v.x2⟩

def pluckerQ (p : PrimitiveBivector5) : F3 :=
  -(p.p12*p.p12) - p.p13*p.p24 + p.p14*p.p23

def standardQ (z : StandardFive) : F3 :=
  z.z1*z.z1 + z.z2*z.z2 + z.z3*z.z3 + z.z4*z.z4 + z.z5*z.z5

/-- Explicit diagonalizing map found by exact F3 computation. -/
def primitiveToStandard (p : PrimitiveBivector5) : StandardFive :=
  ⟨-p.p14 + p.p23,
   -p.p13 - p.p24,
   p.p13 + p.p14 + p.p23 - p.p24,
   p.p13 - p.p14 - p.p23 - p.p24,
   p.p12⟩

/-- Explicit inverse matrix over F3. -/
def standardToPrimitive (z : StandardFive) : PrimitiveBivector5 :=
  ⟨z.z5,
   z.z2 + z.z3 + z.z4,
   z.z1 + z.z3 - z.z4,
   -z.z1 + z.z3 - z.z4,
   z.z2 - z.z3 - z.z4⟩

theorem primitive_roundtrip_all :
    ∀ p : PrimitiveBivector5, standardToPrimitive (primitiveToStandard p) = p := by
  native_decide

theorem standard_roundtrip_all :
    ∀ z : StandardFive, primitiveToStandard (standardToPrimitive z) = z := by
  native_decide

/-- The chosen standard quadratic form is `-1` times the primitive Plücker
quadratic form.  Over F3 this is the same scalar `2` found computationally. -/
theorem quadratic_intertwining_all :
    ∀ p : PrimitiveBivector5, standardQ (primitiveToStandard p) = -(pluckerQ p) := by
  native_decide


def PrimitiveNull80 := {p : PrimitiveBivector5 // pluckerQ p = 0 ∧ p ≠ zeroPrimitive}
def StandardNull80 := {z : StandardFive // standardQ z = 0 ∧ z ≠ zeroStandard}

instance : Fintype PrimitiveNull80 := inferInstance
instance : Fintype StandardNull80 := inferInstance

theorem primitiveNull80_card : Fintype.card PrimitiveNull80 = 80 := by
  native_decide

theorem standardNull80_card : Fintype.card StandardNull80 = 80 := by
  native_decide

theorem primitiveToStandard_nonzero_null :
    ∀ p : PrimitiveNull80,
      standardQ (primitiveToStandard p.1) = 0 ∧ primitiveToStandard p.1 ≠ zeroStandard := by
  native_decide

theorem standardToPrimitive_nonzero_null :
    ∀ z : StandardNull80,
      pluckerQ (standardToPrimitive z.1) = 0 ∧ standardToPrimitive z.1 ≠ zeroPrimitive := by
  native_decide

/-- Exact equivalence of the derived 80-state null carriers. -/
def null80Equiv : PrimitiveNull80 ≃ StandardNull80 where
  toFun p := ⟨primitiveToStandard p.1, primitiveToStandard_nonzero_null p⟩
  invFun z := ⟨standardToPrimitive z.1, standardToPrimitive_nonzero_null z⟩
  left_inv p := Subtype.ext (primitive_roundtrip_all p.1)
  right_inv z := Subtype.ext (standard_roundtrip_all z.1)

/-- Canonical representative of a nonzero ±1 projective class: first nonzero
coordinate equals 1. -/
def canonical5 (a b c d e : F3) : Bool :=
  if a ≠ 0 then decide (a = 1)
  else if b ≠ 0 then decide (b = 1)
  else if c ≠ 0 then decide (c = 1)
  else if d ≠ 0 then decide (d = 1)
  else if e ≠ 0 then decide (e = 1)
  else false

def primitiveCanonical (p : PrimitiveBivector5) : Bool :=
  canonical5 p.p12 p.p13 p.p14 p.p23 p.p24

def standardCanonical (z : StandardFive) : Bool :=
  canonical5 z.z1 z.z2 z.z3 z.z4 z.z5

def negPrimitive (p : PrimitiveBivector5) : PrimitiveBivector5 :=
  ⟨-p.p12,-p.p13,-p.p14,-p.p23,-p.p24⟩

def negStandard (z : StandardFive) : StandardFive :=
  ⟨-z.z1,-z.z2,-z.z3,-z.z4,-z.z5⟩

def canonicalizePrimitive (p : PrimitiveBivector5) : PrimitiveBivector5 :=
  if primitiveCanonical p then p else negPrimitive p

def canonicalizeStandard (z : StandardFive) : StandardFive :=
  if standardCanonical z then z else negStandard z


def PrimitiveProjectiveNull :=
  {p : PrimitiveBivector5 // pluckerQ p = 0 ∧ p ≠ zeroPrimitive ∧ primitiveCanonical p = true}

def StandardProjectiveNull :=
  {z : StandardFive // standardQ z = 0 ∧ z ≠ zeroStandard ∧ standardCanonical z = true}

instance : Fintype PrimitiveProjectiveNull := inferInstance
instance : Fintype StandardProjectiveNull := inferInstance

theorem primitiveProjectiveNull_card : Fintype.card PrimitiveProjectiveNull = 40 := by
  native_decide

theorem standardProjectiveNull_card : Fintype.card StandardProjectiveNull = 40 := by
  native_decide


def projectiveToStandardRaw (p : PrimitiveBivector5) : StandardFive :=
  canonicalizeStandard (primitiveToStandard p)

def projectiveToPrimitiveRaw (z : StandardFive) : PrimitiveBivector5 :=
  canonicalizePrimitive (standardToPrimitive z)

theorem projectiveToStandard_mem :
    ∀ p : PrimitiveProjectiveNull,
      standardQ (projectiveToStandardRaw p.1) = 0 ∧
      projectiveToStandardRaw p.1 ≠ zeroStandard ∧
      standardCanonical (projectiveToStandardRaw p.1) = true := by
  native_decide

theorem projectiveToPrimitive_mem :
    ∀ z : StandardProjectiveNull,
      pluckerQ (projectiveToPrimitiveRaw z.1) = 0 ∧
      projectiveToPrimitiveRaw z.1 ≠ zeroPrimitive ∧
      primitiveCanonical (projectiveToPrimitiveRaw z.1) = true := by
  native_decide

theorem projective_primitive_roundtrip_all :
    ∀ p : PrimitiveProjectiveNull,
      projectiveToPrimitiveRaw (projectiveToStandardRaw p.1) = p.1 := by
  native_decide

theorem projective_standard_roundtrip_all :
    ∀ z : StandardProjectiveNull,
      projectiveToStandardRaw (projectiveToPrimitiveRaw z.1) = z.1 := by
  native_decide

/-- Exact 40↔40 projective recognition. -/
def projectiveEquiv : PrimitiveProjectiveNull ≃ StandardProjectiveNull where
  toFun p := ⟨projectiveToStandardRaw p.1, projectiveToStandard_mem p⟩
  invFun z := ⟨projectiveToPrimitiveRaw z.1, projectiveToPrimitive_mem z⟩
  left_inv p := Subtype.ext (projective_primitive_roundtrip_all p)
  right_inv z := Subtype.ext (projective_standard_roundtrip_all z)


def pluckerPolar (p q : PrimitiveBivector5) : F3 :=
  p.p12*q.p12 - p.p13*q.p24 - q.p13*p.p24 + p.p14*q.p23 + q.p14*p.p23

def standardDot (z w : StandardFive) : F3 :=
  z.z1*w.z1 + z.z2*w.z2 + z.z3*w.z3 + z.z4*w.z4 + z.z5*w.z5

def LinesIntersect (p q : PrimitiveProjectiveNull) : Prop := pluckerPolar p.1 q.1 = 0
def NullPointsOrthogonal (z w : StandardProjectiveNull) : Prop := standardDot z.1 w.1 = 0

theorem projective_incidence_orthogonality_all :
    ∀ p q : PrimitiveProjectiveNull,
      LinesIntersect p q ↔ NullPointsOrthogonal (projectiveEquiv p) (projectiveEquiv q) := by
  native_decide

/-- Same-action socket for the full projective similitude/Weyl promotion. -/
structure PGSp4WeylRecognition where
  PGSp4Actor : Type
  WeylE6Actor : Type
  actorToWeyl : PGSp4Actor → WeylE6Actor
  fourAction : PGSp4Actor → F3Four → F3Four
  fiveAction : WeylE6Actor → StandardFive → StandardFive
  inducedPrimitiveAction : PGSp4Actor → PrimitiveBivector5 → PrimitiveBivector5
  exteriorSquareCovariance : ∀ g u v,
    symplectic4 u v = 0 →
    wedgePrimitiveCoordinates (fourAction g u) (fourAction g v) =
      inducedPrimitiveAction g (wedgePrimitiveCoordinates u v)
  standardIntertwining : ∀ g p,
    primitiveToStandard (inducedPrimitiveAction g p) =
      fiveAction (actorToWeyl g) (primitiveToStandard p)

inductive RawPuncturedT4IsDerivedNull80 : Prop

theorem raw_punctured_t4_not_promoted : ¬ RawPuncturedT4IsDerivedNull80 := by
  intro h
  cases h

structure Boundary where
  ambientFiveCoordinateEquivalencePaid : Bool
  quadraticIntertwiningPaid : Bool
  primitiveNullCount80Paid : Bool
  standardNullCount80Paid : Bool
  null80EquivalencePaid : Bool
  primitiveProjectiveCount40Paid : Bool
  standardProjectiveCount40Paid : Bool
  projectiveEquivalencePaid : Bool
  incidenceOrthogonalityPaid : Bool
  rawPuncturedT4IdentifiedWithDerived80 : Bool
  literalPGSp4WeylGroupEqualityPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  ambientFiveCoordinateEquivalencePaid := true
  quadraticIntertwiningPaid := true
  primitiveNullCount80Paid := true
  standardNullCount80Paid := true
  null80EquivalencePaid := true
  primitiveProjectiveCount40Paid := true
  standardProjectiveCount40Paid := true
  projectiveEquivalencePaid := true
  incidenceOrthogonalityPaid := true
  rawPuncturedT4IdentifiedWithDerived80 := false
  literalPGSp4WeylGroupEqualityPaid := false

end Integration.E6F3ExteriorSquareRecognition

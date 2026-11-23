import Integration.E6Mod3QuadraticBridge
import Mathlib

/-!
# Projective E6 root-line graph over F3

The 72 norm-two vectors in the standard five-dimensional E6 mod-3 quadratic
space occur in antipodal pairs.  Choosing the unique representative whose first
nonzero coordinate is 1 gives a literal 36-element root-line carrier.

Orthogonality in the standard bilinear form gives a graph with exact parameters
SRG(36,15,6,6).  Since lambda = mu = 6, every pair of distinct projective root
lines has exactly six common neighbors; the adjacent/nonadjacent cases are
therefore immediate specializations.
-/

namespace DASHI.Integration.E6ProjectiveRootLineSRG

open Integration.E6Mod3QuadraticBridge

/-- Canonical representative of an antipodal projective point: the first
nonzero coordinate is 1.  On a norm-two vector the zero case is impossible. -/
def canonicalLineRep (z : F3Five) : Prop :=
  z.z0 = 1 ∨
  (z.z0 = 0 ∧ z.z1 = 1) ∨
  (z.z0 = 0 ∧ z.z1 = 0 ∧ z.z2 = 1) ∨
  (z.z0 = 0 ∧ z.z1 = 0 ∧ z.z2 = 0 ∧ z.z3 = 1) ∨
  (z.z0 = 0 ∧ z.z1 = 0 ∧ z.z2 = 0 ∧ z.z3 = 0 ∧ z.z4 = 1)

/-- Literal projective norm-two/root-line carrier. -/
def QTwoRootLine := {z : F3Five // standardQuadratic z = 2 ∧ canonicalLineRep z}

instance : Fintype QTwoRootLine := Fintype.ofFinite _
instance : DecidableEq QTwoRootLine := inferInstance

/-- Standard polar dot product for q(z)=sum z_i^2.  In characteristic 3 the
usual scalar factor in polarization is invertible, so zero dot product is the
orthogonality relation needed here. -/
def dot5 (x y : F3Five) : ZMod 3 :=
  x.z0*y.z0 + x.z1*y.z1 + x.z2*y.z2 + x.z3*y.z3 + x.z4*y.z4

/-- Orthogonality neighbors of one projective root line. -/
def neighbors (x : QTwoRootLine) : Finset QTwoRootLine :=
  Finset.univ.filter (fun y => y ≠ x ∧ dot5 x.1 y.1 = 0)

/-- Common orthogonality neighbors. -/
def commonNeighbors (x y : QTwoRootLine) : Finset QTwoRootLine :=
  Finset.univ.filter (fun z =>
    z ≠ x ∧ z ≠ y ∧ dot5 x.1 z.1 = 0 ∧ dot5 y.1 z.1 = 0)

/-- Exactly one representative from each of the 36 antipodal E6 root lines. -/
theorem qtwoRootLine_card : Fintype.card QTwoRootLine = 36 := by
  native_decide

/-- The projective root-line orthogonality graph is 15-regular. -/
theorem qtwoRootLine_degree15 :
    ∀ x : QTwoRootLine, (neighbors x).card = 15 := by
  native_decide

/-- Stronger than splitting lambda/mu: every two distinct vertices have exactly
six common neighbors. -/
theorem qtwoRootLine_common6 :
    ∀ x y : QTwoRootLine, x ≠ y → (commonNeighbors x y).card = 6 := by
  native_decide

/-- Adjacent-pair parameter lambda = 6. -/
theorem qtwoRootLine_adjacent_common6 :
    ∀ x y : QTwoRootLine,
      x ≠ y → dot5 x.1 y.1 = 0 → (commonNeighbors x y).card = 6 := by
  intro x y hxy _
  exact qtwoRootLine_common6 x y hxy

/-- Nonadjacent-pair parameter mu = 6. -/
theorem qtwoRootLine_nonAdjacent_common6 :
    ∀ x y : QTwoRootLine,
      x ≠ y → dot5 x.1 y.1 ≠ 0 → (commonNeighbors x y).card = 6 := by
  intro x y hxy _
  exact qtwoRootLine_common6 x y hxy

structure RootLineSRGBoundary where
  antipodalProjectiveRepresentativeTyped : Bool
  vertexCount36Paid : Bool
  degree15Paid : Bool
  adjacentCommon6Paid : Bool
  nonAdjacentCommon6Paid : Bool
  srg361566Paid : Bool
  rootLineGraphIdentifiedWithPhysicalMechanism : Bool
  deriving Repr

def rootLineBoundary : RootLineSRGBoundary where
  antipodalProjectiveRepresentativeTyped := true
  vertexCount36Paid := true
  degree15Paid := true
  adjacentCommon6Paid := true
  nonAdjacentCommon6Paid := true
  srg361566Paid := true
  rootLineGraphIdentifiedWithPhysicalMechanism := false

end DASHI.Integration.E6ProjectiveRootLineSRG

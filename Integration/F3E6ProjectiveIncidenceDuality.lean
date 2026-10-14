import Integration.F3E6PGSpSameObjectBridge
import Mathlib

/-!
# Projective Lagrangian / E6-null incidence duality over F3

The raw punctured four-trit carrier has 80 vectors but is not the exceptional
80-state object. The exceptional source object is the set of nonzero primitive
decomposable bivectors coming from isotropic two-planes in F3^4. Projectivizing
by ±1 gives 40 Lagrangian lines.

This owner closes the projective geometric seam. It chooses canonical
first-nonzero-coordinate-one representatives, transports them through the
existing primitive-to-standard five-space isometry, and proves:

* 40 canonical Lagrangian Plucker representatives;
* 40 canonical primitive null representatives;
* 40 canonical standard-E6 null representatives;
* explicit two-sided projective transport to the standard E6 null quadric;
* Plucker meet-incidence is equivalent to quadratic orthogonality after that
  transport;
* the resulting projective graph is SRG(40,12,2,4).

No equality with raw `T4^×` is introduced.
-/

namespace DASHI.Integration.F3E6ProjectiveIncidenceDuality

open F3FourSymplecticExteriorSquare
open F3E6PGSpSameObjectBridge

private def primitiveAdd (p q : Primitive5) : Primitive5 := fun i => p i + q i
private def primitiveNeg (p : Primitive5) : Primitive5 := fun i => -p i

/-- Polarization of the primitive Plucker quadratic form. -/
def primitivePolar (p q : Primitive5) : F3 :=
  primitiveQuadratic (primitiveAdd p q) - primitiveQuadratic p - primitiveQuadratic q

/-- Coefficient of the top exterior form in the wedge of two primitive
2-vectors. On decomposable bivectors its vanishing is the Plucker incidence
criterion for the corresponding projective lines to meet. -/
def pluckerMeet (p q : Primitive5) : F3 :=
  let P := primitiveExpand p
  let Q := primitiveExpand q
  P 0 * Q 5 + P 5 * Q 0 - P 1 * Q 4 - P 4 * Q 1 + P 2 * Q 3 + P 3 * Q 2

/-- The Grassmann meet pairing is exactly the polar form of the primitive
quadratic equation. -/
theorem pluckerMeet_eq_primitivePolar :
    ∀ p q : Primitive5, pluckerMeet p q = primitivePolar p q := by
  native_decide

/-- Canonical projective sign convention over F3: the first nonzero coordinate
is 1. Since the only nonzero scalars are ±1, this chooses one representative
from every projective ± pair. -/
def firstNonzeroOne (q : Primitive5) : Prop :=
  if q 0 ≠ 0 then q 0 = 1
  else if q 1 ≠ 0 then q 1 = 1
  else if q 2 ≠ 0 then q 2 = 1
  else if q 3 ≠ 0 then q 3 = 1
  else q 4 = 1

def projectiveLagrangianFinset : Finset Primitive5 :=
  lagrangianWedgeSet.filter firstNonzeroOne

def projectiveNullFinset : Finset Primitive5 :=
  nullConeFinset.filter firstNonzeroOne

/-- Same-object projectivization: the derived Lagrangian carrier and primitive
null cone are literally the same canonical 40 representatives. -/
theorem projective_lagrangian_eq_null :
    projectiveLagrangianFinset = projectiveNullFinset := by
  rw [projectiveLagrangianFinset, projectiveNullFinset, lagrangianWedgeSet_eq_nullCone]

theorem projectiveLagrangian_card : projectiveLagrangianFinset.card = 40 := by
  native_decide

theorem projectiveNull_card : projectiveNullFinset.card = 40 := by
  rw [← projective_lagrangian_eq_null]
  exact projectiveLagrangian_card

def ProjectiveLagPoint := {q : Primitive5 // q ∈ projectiveLagrangianFinset}
def ProjectiveNullPoint := {q : Primitive5 // q ∈ projectiveNullFinset}

instance : Fintype ProjectiveLagPoint := projectiveLagrangianFinset.fintypeCoeSort
instance : Fintype ProjectiveNullPoint := projectiveNullFinset.fintypeCoeSort

def toProjectiveNull (p : ProjectiveLagPoint) : ProjectiveNullPoint :=
  ⟨p.1, by
    rw [← projective_lagrangian_eq_null]
    exact p.2⟩

def fromProjectiveNull (p : ProjectiveNullPoint) : ProjectiveLagPoint :=
  ⟨p.1, by
    rw [projective_lagrangian_eq_null]
    exact p.2⟩

theorem projectiveNull_from_to (p : ProjectiveLagPoint) :
    fromProjectiveNull (toProjectiveNull p) = p := by
  apply Subtype.ext
  rfl

theorem projectiveNull_to_from (p : ProjectiveNullPoint) :
    toProjectiveNull (fromProjectiveNull p) = p := by
  apply Subtype.ext
  rfl

/-- Plucker incidence on the source Lagrangian projective carrier. -/
def lagIncidence (p q : ProjectiveLagPoint) : Prop := pluckerMeet p.1 q.1 = 0

/-- Primitive-null orthogonality before the standard E6 coordinate change. -/
def nullOrthogonal (p q : ProjectiveNullPoint) : Prop := primitivePolar p.1 q.1 = 0

theorem lagIncidence_iff_nullOrthogonal (p q : ProjectiveLagPoint) :
    lagIncidence p q ↔ nullOrthogonal (toProjectiveNull p) (toProjectiveNull q) := by
  simp only [lagIncidence, nullOrthogonal, toProjectiveNull]
  rw [pluckerMeet_eq_primitivePolar]

/-! ## Standard E6 null quadric

The existing same-object bridge supplies an explicit scaled isometry from the
primitive Plucker five-space into the repository's standard E6 F3^5 carrier.
The projective normalization below removes the possible output sign.
-/

private def standardNeg (z : E6Bridge.F3Five) : E6Bridge.F3Five :=
  ⟨-z.z0, -z.z1, -z.z2, -z.z3, -z.z4⟩

private def standardFirstNonzeroOne (z : E6Bridge.F3Five) : Prop :=
  if z.z0 ≠ 0 then z.z0 = 1
  else if z.z1 ≠ 0 then z.z1 = 1
  else if z.z2 ≠ 0 then z.z2 = 1
  else if z.z3 ≠ 0 then z.z3 = 1
  else z.z4 = 1

private def normalizePrimitive (q : Primitive5) : Primitive5 :=
  if q 0 = 2 then primitiveNeg q
  else if q 0 = 1 then q
  else if q 1 = 2 then primitiveNeg q
  else if q 1 = 1 then q
  else if q 2 = 2 then primitiveNeg q
  else if q 2 = 1 then q
  else if q 3 = 2 then primitiveNeg q
  else if q 3 = 1 then q
  else if q 4 = 2 then primitiveNeg q
  else q

private def normalizeStandard (z : E6Bridge.F3Five) : E6Bridge.F3Five :=
  if z.z0 = 2 then standardNeg z
  else if z.z0 = 1 then z
  else if z.z1 = 2 then standardNeg z
  else if z.z1 = 1 then z
  else if z.z2 = 2 then standardNeg z
  else if z.z2 = 1 then z
  else if z.z3 = 2 then standardNeg z
  else if z.z3 = 1 then z
  else if z.z4 = 2 then standardNeg z
  else z

def standardProjectiveNullFinset : Finset E6Bridge.F3Five :=
  Finset.univ.filter fun z =>
    E6Bridge.standardQuadratic z = 0 ∧ standardFirstNonzeroOne z

theorem standardProjectiveNull_card : standardProjectiveNullFinset.card = 40 := by
  native_decide

def StandardProjectiveNullPoint :=
  {z : E6Bridge.F3Five // z ∈ standardProjectiveNullFinset}

instance : Fintype StandardProjectiveNullPoint := standardProjectiveNullFinset.fintypeCoeSort

private def lagToStandardValue (p : ProjectiveLagPoint) : E6Bridge.F3Five :=
  normalizeStandard (primitiveToStandard p.1)

private theorem lagToStandardValue_mem :
    ∀ p : ProjectiveLagPoint, lagToStandardValue p ∈ standardProjectiveNullFinset := by
  native_decide

def lagToStandardNull (p : ProjectiveLagPoint) : StandardProjectiveNullPoint :=
  ⟨lagToStandardValue p, lagToStandardValue_mem p⟩

private def standardToLagValue (z : StandardProjectiveNullPoint) : Primitive5 :=
  normalizePrimitive (standardToPrimitive z.1)

private theorem standardToLagValue_mem :
    ∀ z : StandardProjectiveNullPoint,
      standardToLagValue z ∈ projectiveLagrangianFinset := by
  native_decide

def standardNullToLag (z : StandardProjectiveNullPoint) : ProjectiveLagPoint :=
  ⟨standardToLagValue z, standardToLagValue_mem z⟩

/-- Exact projective two-sided recovery across the explicit E6 standard chart. -/
theorem standardNull_lag_roundTrip :
    ∀ p : ProjectiveLagPoint, standardNullToLag (lagToStandardNull p) = p := by
  native_decide

theorem lag_standardNull_roundTrip :
    ∀ z : StandardProjectiveNullPoint, lagToStandardNull (standardNullToLag z) = z := by
  native_decide

def lagEquivStandardNull : ProjectiveLagPoint ≃ StandardProjectiveNullPoint where
  toFun := lagToStandardNull
  invFun := standardNullToLag
  left_inv := standardNull_lag_roundTrip
  right_inv := lag_standardNull_roundTrip

private def standardAdd (x y : E6Bridge.F3Five) : E6Bridge.F3Five :=
  ⟨x.z0 + y.z0, x.z1 + y.z1, x.z2 + y.z2, x.z3 + y.z3, x.z4 + y.z4⟩

def standardPolar (x y : E6Bridge.F3Five) : F3 :=
  E6Bridge.standardQuadratic (standardAdd x y) -
    E6Bridge.standardQuadratic x - E6Bridge.standardQuadratic y

def standardNullOrthogonal (x y : StandardProjectiveNullPoint) : Prop :=
  standardPolar x.1 y.1 = 0

/-- Final projective duality theorem: Plucker incidence of the Lagrangian lines
is exactly orthogonality of the corresponding standard E6 null points. -/
theorem lagIncidence_iff_standardNullOrthogonal :
    ∀ p q : ProjectiveLagPoint,
      lagIncidence p q ↔ standardNullOrthogonal (lagToStandardNull p) (lagToStandardNull q) := by
  native_decide

/-! ## Exact projective association graph

Remove the reflexive isotropic relation and use orthogonality as adjacency.
The standard-E6 null-point graph has the exact strongly-regular parameters
(40,12,2,4).  Through `lagEquivStandardNull`, the source Lagrangian incidence
graph is the same graph.
-/

def standardAdjacent (x y : StandardProjectiveNullPoint) : Prop :=
  x ≠ y ∧ standardNullOrthogonal x y

def standardNeighbors (x : StandardProjectiveNullPoint) : Finset StandardProjectiveNullPoint :=
  Finset.univ.filter (standardAdjacent x)

def standardCommonNeighbors
    (x y : StandardProjectiveNullPoint) : Finset StandardProjectiveNullPoint :=
  Finset.univ.filter fun z => standardAdjacent x z ∧ standardAdjacent y z

theorem standard_degree12 :
    ∀ z : StandardProjectiveNullPoint, (standardNeighbors z).card = 12 := by
  native_decide

theorem standard_adjacent_common2 :
    ∀ x y : StandardProjectiveNullPoint,
      x ≠ y → standardAdjacent x y → (standardCommonNeighbors x y).card = 2 := by
  native_decide

theorem standard_nonadjacent_common4 :
    ∀ x y : StandardProjectiveNullPoint,
      x ≠ y → ¬ standardAdjacent x y → (standardCommonNeighbors x y).card = 4 := by
  native_decide

def lagAdjacent (x y : ProjectiveLagPoint) : Prop :=
  x ≠ y ∧ lagIncidence x y

theorem lagAdjacent_iff_standardAdjacent :
    ∀ x y : ProjectiveLagPoint,
      lagAdjacent x y ↔ standardAdjacent (lagToStandardNull x) (lagToStandardNull y) := by
  native_decide

structure IncidenceBoundary where
  projectiveLagCount40Paid : Bool
  projectiveNullCount40Paid : Bool
  standardE6ProjectiveNullCount40Paid : Bool
  lagNullProjectiveSameObjectPaid : Bool
  standardE6ProjectiveEquivalencePaid : Bool
  incidenceOrthogonalityEquivalencePaid : Bool
  projectiveSRG401224Paid : Bool
  sourceTargetAdjacencyIntertwiningPaid : Bool
  rawPuncturedT4PromotedToLagCarrier : Bool
  cardinalityAlonePromotesProjectiveRecognition : Bool
  deriving Repr

def incidenceBoundary : IncidenceBoundary where
  projectiveLagCount40Paid := true
  projectiveNullCount40Paid := true
  standardE6ProjectiveNullCount40Paid := true
  lagNullProjectiveSameObjectPaid := true
  standardE6ProjectiveEquivalencePaid := true
  incidenceOrthogonalityEquivalencePaid := true
  projectiveSRG401224Paid := true
  sourceTargetAdjacencyIntertwiningPaid := true
  rawPuncturedT4PromotedToLagCarrier := false
  cardinalityAlonePromotesProjectiveRecognition := false

end DASHI.Integration.F3E6ProjectiveIncidenceDuality

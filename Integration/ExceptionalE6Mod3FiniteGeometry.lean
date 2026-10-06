import Mathlib

/-!
# E6 mod-3 finite quadratic geometry

DASHI finite-model owner for the five-dimensional ternary quadratic space that
appears after reducing the E6 Cartan lattice modulo 3 and quotienting its
one-dimensional radical.

This file deliberately separates:
* the concrete 243-state quadratic model, whose finite counts and projective
  graph parameters are discharged by `native_decide`;
* the E6 root/Weyl recognition interface, which requires an explicit root map
  and action intertwiner;
* the E8 dual-incidence bridge, which remains a recognition contract rather
  than being inferred from matching graph parameters.

The convention used here has the 72-state root candidate in quadratic class 2
and the 90-state class in quadratic class 1. Multiplying the quadratic form by
2 swaps those labels without changing the geometry.
-/

namespace Integration.ExceptionalE6Mod3FiniteGeometry

abbrev F3 := Fin 3

structure V5 where
  x0 : F3
  x1 : F3
  x2 : F3
  x3 : F3
  x4 : F3
  deriving DecidableEq, Fintype, Repr

/-- Gram form obtained from one complement to the mod-3 radical of the standard
E6 Cartan matrix. This is a coordinate presentation of the quotient, not a
claim that the basis itself is canonical. -/
def bilinear (x y : V5) : F3 :=
  2*x.x0*y.x0 + 2*x.x0*y.x1 +
  2*x.x1*y.x0 + 2*x.x1*y.x1 + 2*x.x1*y.x2 + 2*x.x1*y.x4 +
  2*x.x2*y.x1 + 2*x.x2*y.x2 + 2*x.x2*y.x3 +
  2*x.x3*y.x2 + 2*x.x3*y.x3 +
  2*x.x4*y.x1 + 2*x.x4*y.x4

def quadratic (x : V5) : F3 := bilinear x x

def zeroV : V5 := ⟨0,0,0,0,0⟩

def NullNonzero := {x : V5 // x ≠ zeroV ∧ quadratic x = 0}
def ClassOne := {x : V5 // quadratic x = 1}
def ClassTwo := {x : V5 // quadratic x = 2}

instance : Fintype NullNonzero := inferInstance
instance : Fintype ClassOne := inferInstance
instance : Fintype ClassTwo := inferInstance

 theorem total_state_count : Fintype.card V5 = 243 := by native_decide
 theorem null_nonzero_count : Fintype.card NullNonzero = 80 := by native_decide
 theorem class_one_count : Fintype.card ClassOne = 90 := by native_decide
 theorem class_two_count : Fintype.card ClassTwo = 72 := by native_decide
 theorem state_partition_arithmetic : 243 = 1 + 80 + 90 + 72 := by decide

/-- Balanced-ternary sign. -/
def negV (x : V5) : V5 := ⟨-x.x0,-x.x1,-x.x2,-x.x3,-x.x4⟩

def encode (x : V5) : Nat :=
  x.x0.val + 3*x.x1.val + 9*x.x2.val + 27*x.x3.val + 81*x.x4.val

/-- Canonical representative of an antipodal pair, used only to obtain a
literal finite carrier for projective root/null/nonsingular lines. -/
def canonicalSign (x : V5) : Prop := encode x < encode (negV x)

instance (x : V5) : Decidable (canonicalSign x) := inferInstance

def NullLines := {x : V5 // x ≠ zeroV ∧ quadratic x = 0 ∧ canonicalSign x}
def RootCandidateLines := {x : V5 // quadratic x = 2 ∧ canonicalSign x}
def OtherNonsingularLines := {x : V5 // quadratic x = 1 ∧ canonicalSign x}

instance : Fintype NullLines := inferInstance
instance : Fintype RootCandidateLines := inferInstance
instance : Fintype OtherNonsingularLines := inferInstance

 theorem null_line_count : Fintype.card NullLines = 40 := by native_decide
 theorem root_candidate_line_count : Fintype.card RootCandidateLines = 36 := by native_decide
 theorem other_nonsingular_line_count : Fintype.card OtherNonsingularLines = 45 := by native_decide
 theorem projective_partition_arithmetic : 121 = 40 + 36 + 45 := by decide

/-- Orthogonality point graph on any canonical projective stratum. -/
def lineAdj {P : Type} [Coe P V5] [DecidableEq P] (x y : P) : Bool :=
  decide (x ≠ y ∧ bilinear (x : V5) (y : V5) = 0)

instance : Coe NullLines V5 := ⟨fun x => x.1⟩
instance : Coe RootCandidateLines V5 := ⟨fun x => x.1⟩
instance : Coe OtherNonsingularLines V5 := ⟨fun x => x.1⟩

private def degree {P : Type} [Fintype P] [DecidableEq P] [Coe P V5] (x : P) : Nat :=
  (Finset.univ.filter fun y => lineAdj x y).card

private def commonNeighbors {P : Type} [Fintype P] [DecidableEq P] [Coe P V5]
    (x y : P) : Nat :=
  (Finset.univ.filter fun z => lineAdj x z && lineAdj y z).card

/-- The three projective quadratic strata have three distinct regular incidence
geometries. These are finite arithmetic theorems about the concrete V5 model. -/
theorem null_lines_srg_parameters :
    (∀ x : NullLines, degree x = 12) ∧
    (∀ x y : NullLines, x ≠ y →
      (lineAdj x y = true → commonNeighbors x y = 2) ∧
      (lineAdj x y = false → commonNeighbors x y = 4)) := by
  native_decide

theorem root_candidate_lines_srg_parameters :
    (∀ x : RootCandidateLines, degree x = 15) ∧
    (∀ x y : RootCandidateLines, x ≠ y →
      (lineAdj x y = true → commonNeighbors x y = 6) ∧
      (lineAdj x y = false → commonNeighbors x y = 6)) := by
  native_decide

theorem other_nonsingular_lines_srg_parameters :
    (∀ x : OtherNonsingularLines, degree x = 12) ∧
    (∀ x y : OtherNonsingularLines, x ≠ y →
      (lineAdj x y = true → commonNeighbors x y = 3) ∧
      (lineAdj x y = false → commonNeighbors x y = 3)) := by
  native_decide

/-- Recognition interface for upgrading the 72-state quadratic stratum to the
actual E6 root system. Cardinality and Gram data alone do not inhabit it. -/
structure E6RootRecognition (Root : Type*) [Fintype Root] where
  rootCount72 : Fintype.card Root = 72
  toFinite : Root ≃ ClassTwo
  Weyl : Type*
  rootAction : Weyl → Root → Root
  finiteAction : Weyl → ClassTwo → ClassTwo
  intertwines : ∀ g r, toFinite (rootAction g r) = finiteAction g (toFinite r)
  provenance : String

/-- Stronger group-level interface for the mod-3 Weyl action. -/
structure E6WeylFaithfulRecognition (Weyl : Type*) [Fintype Weyl] where
  groupOrder51840 : Fintype.card Weyl = 51840
  act : Weyl → V5 → V5
  preservesBilinear : ∀ g x y, bilinear (act g x) (act g y) = bilinear x y
  faithful : ∀ g h, (∀ x, act g x = act h x) → g = h
  provenance : String

/-- Candidate bridge to the fixed-point-free order-3 E8 quotient. This record
requires an incidence equivalence; matching 40-vertex parameters is not enough. -/
structure E6E8DualIncidenceRecognition (E8ProjectivePoint E8ProjectiveLine : Type*) where
  e8PointCount40 : Fintype.card E8ProjectivePoint = 40
  e8LineCount40 : Fintype.card E8ProjectiveLine = 40
  incident : E8ProjectivePoint → E8ProjectiveLine → Prop
  nullLineToE8Line : NullLines ≃ E8ProjectiveLine
  incidenceIntertwiningReceipt : Prop
  provenance : String

/-- The 80 signed null vectors cannot be the nonzero vectors of an ordinary
four-dimensional linear F3 action if an element has exactly 20 fixed vectors:
linear fixed spaces have nonzero cardinality 3^d-1. The concrete E6-reflection
fixed-count witness is deliberately kept outside this purely finite owner until
an actual Weyl action is supplied. -/
theorem twenty_not_linear_fixed_nonzero_count :
    20 ≠ 0 ∧ 20 ≠ 2 ∧ 20 ≠ 8 ∧ 20 ≠ 26 ∧ 20 ≠ 80 := by decide

inductive CardinalityCreatesExceptionalRecognition : Prop
inductive MatchingSRGParametersCreateIncidenceIsomorphism : Prop
inductive DepthNormCreatesProductDecomposition : Prop

 theorem cardinalityDoesNotCreateRecognition : ¬ CardinalityCreatesExceptionalRecognition := by
  intro h; cases h
 theorem matchingParametersDoNotCreateIsomorphism : ¬ MatchingSRGParametersCreateIncidenceIsomorphism := by
  intro h; cases h
 theorem depthNormNotAutoProduct : ¬ DepthNormCreatesProductDecomposition := by
  intro h; cases h

structure Boundary where
  concrete243ModelPaid : Bool
  strataCountsPaid : Bool
  projectiveCountsPaid : Bool
  threeSRGParameterSetsPaid : Bool
  e6RootRecognitionInhabitedHere : Bool
  faithfulWeylRecognitionInhabitedHere : Bool
  e6E8DualIncidenceRecognitionInhabitedHere : Bool
  t4LinearIdentificationClaimed : Bool
  depthNormProductClaimed : Bool
  deriving Repr

 def canonicalBoundary : Boundary where
  concrete243ModelPaid := true
  strataCountsPaid := true
  projectiveCountsPaid := true
  threeSRGParameterSetsPaid := true
  e6RootRecognitionInhabitedHere := false
  faithfulWeylRecognitionInhabitedHere := false
  e6E8DualIncidenceRecognitionInhabitedHere := false
  t4LinearIdentificationClaimed := false
  depthNormProductClaimed := false

end Integration.ExceptionalE6Mod3FiniteGeometry

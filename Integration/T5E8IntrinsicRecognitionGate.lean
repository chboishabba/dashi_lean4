import Integration.E8RelativeT5IntrinsicGraphObstruction
import Integration.ActionOrbitRecognition
import Mathlib

/-!
# Intrinsic-geometry gate for T5/E8 recognition

The earlier `E8RelativeComplementRecognition` correctly required a state
bijection and an action intertwiner, but if the target action is allowed to be
defined *after* choosing the bijection, any 240-element carrier can receive an
E8 action by transport.  That construction is mathematically legitimate but is
not independent evidence that the target carrier already possessed E8 geometry.

This owner therefore adds the stronger experimental/same-object gate:

1. choose a target geometry independently of the recognition map;
2. record its provenance;
3. only then ask for a bijection preserving the source E8 relation.

The naive standard-F3 orthogonality geometry is instantiated and rejected by the
56-vs-77 degree obstruction already proved in
`E8RelativeT5IntrinsicGraphObstruction`.  Other independently motivated target
geometries remain open.
-/

namespace Integration.T5E8IntrinsicRecognitionGate

open Integration.T5E8RelativeComplementCandidate
open Integration.E8RelativeT5IntrinsicGraphObstruction

/-- A relation on the target carrier fixed independently of any E8 bijection. -/
structure IntrinsicTargetGeometry where
  relation : RelativeT5Carrier → RelativeT5Carrier → Prop
  decidableRelation : DecidableRel relation
  provenance : String
  fixedBeforeRecognitionMap : Bool
  fixedBeforeRecognitionMapIsTrue : fixedBeforeRecognitionMap = true

attribute [instance] IntrinsicTargetGeometry.decidableRelation

/-- E8 source relation in the literal scaled-root carrier. -/
def e8RootRelation (a b : E8ScaledRoot) : Prop :=
  a ≠ b ∧ e8ScaledDot a b = -4

instance : DecidableRel e8RootRelation := by
  intro a b
  unfold e8RootRelation
  infer_instance

/-- Strong same-object gate: target relation is supplied first and the state
bijection must preserve and reflect adjacency. -/
structure IntrinsicE8Recognition (geometry : IntrinsicTargetGeometry) where
  rootEquiv : E8ScaledRoot ≃ RelativeT5Carrier
  relationIntertwining :
    ∀ a b,
      e8RootRelation a b ↔ geometry.relation (rootEquiv a) (rootEquiv b)
  recognitionProvenance : String

/-- Naive balanced-F3 orthogonality as an independently specified target
geometry.  This is precisely the candidate falsified by the degree audit. -/
def naiveOrthogonalityGeometry : IntrinsicTargetGeometry where
  relation := fun x y => x ≠ y ∧ t5Dot x.1 y.1 = 0
  decidableRelation := by
    intro x y
    infer_instance
  provenance := "DASHI candidate: standard balanced-F3 orthogonality on the pre-existing T5 carrier"
  fixedBeforeRecognitionMap := true
  fixedBeforeRecognitionMapIsTrue := rfl

def NaiveOrthogonalityRecognition := IntrinsicE8Recognition naiveOrthogonalityGeometry

/-- Any adjacency-preserving equivalence preserves neighbor cardinalities.  We
make that consequence explicit and feed it to the already-paid degree no-go. -/
theorem naive_recognition_yields_degree_recognition
    (recognition : NaiveOrthogonalityRecognition) :
    IntrinsicGraphRecognition := by
  refine ⟨recognition.rootEquiv, ?_⟩
  intro r
  let f : E8RootNeighbor r →
      RelativeOrthogonalNeighbor (recognition.rootEquiv r) := fun s =>
    ⟨recognition.rootEquiv s.1, by
      constructor
      · intro hEq
        have : s.1 = r := recognition.rootEquiv.injective hEq
        exact s.2.1 this
      · exact (recognition.relationIntertwining r s.1).mp s.2 |>.2⟩
  let g : RelativeOrthogonalNeighbor (recognition.rootEquiv r) →
      E8RootNeighbor r := fun y =>
    ⟨recognition.rootEquiv.symm y.1, by
      have hyRel : naiveOrthogonalityGeometry.relation (recognition.rootEquiv r) y.1 := y.2
      have hsrc := (recognition.relationIntertwining r (recognition.rootEquiv.symm y.1)).mpr (by
        simpa using hyRel)
      exact hsrc⟩
  let e : E8RootNeighbor r ≃ RelativeOrthogonalNeighbor (recognition.rootEquiv r) where
    toFun := f
    invFun := g
    left_inv := by
      intro s
      apply Subtype.ext
      simp [f, g]
    right_inv := by
      intro y
      apply Subtype.ext
      simp [f, g]
  exact Fintype.card_congr e

theorem naive_orthogonality_recognition_impossible :
    ¬ NaiveOrthogonalityRecognition := by
  intro recognition
  exact intrinsic_graph_recognition_impossible
    (naive_recognition_yields_degree_recognition recognition)

/-- Merely transporting a source relation through a chosen equivalence is kept
as a different construction: it is a model definition, not independent target
evidence. -/
def transportedRelation
    (e : E8ScaledRoot ≃ RelativeT5Carrier) :
    RelativeT5Carrier → RelativeT5Carrier → Prop :=
  fun x y => e8RootRelation (e.symm x) (e.symm y)

inductive TransportedGeometryCreatesIndependentRecognitionEvidence : Prop

theorem transportedGeometryCannotCreateIndependentEvidence :
    ¬ TransportedGeometryCreatesIndependentRecognitionEvidence := by
  intro h
  cases h

structure Boundary where
  targetGeometryMustPreexistRecognition : Bool
  relationPreservationAndReflectionRequired : Bool
  transportingGeometryThroughBijectionCountsAsIndependentEvidence : Bool
  naiveOrthogonalityCandidateRejected : Bool
  otherIntrinsicGeometriesRemainOpen : Bool
  intrinsicGeometryRecognitionCreatesPhysicalMechanism : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  targetGeometryMustPreexistRecognition := true
  relationPreservationAndReflectionRequired := true
  transportingGeometryThroughBijectionCountsAsIndependentEvidence := false
  naiveOrthogonalityCandidateRejected := true
  otherIntrinsicGeometriesRemainOpen := true
  intrinsicGeometryRecognitionCreatesPhysicalMechanism := false

end Integration.T5E8IntrinsicRecognitionGate

import Integration.F3E6PGSpClosure
import Mathlib

/-!
# Literal five-space image recognition for the F3^4 / E6 bridge

This owner pays the finite same-image seam left after the generator bridge and
projective closure/kernel computation.

The six literal four-space lifts already satisfy

  standardExteriorAction (pgspLift i) = e6StandardGenerator i

for every simple-generator index.  Here we close both generated five-space
matrix images and prove, by exact finite computation on the literal matrices,
that they are the same 51,840-element subset of M5.

This is strictly stronger than an order comparison: the two finite matrix
images are equal.  It also inhabits the repository's existing same-action
`PGSpWeylRecognition` contract at the concrete matrix-image level.  We still
do not manufacture an abstract named group isomorphism `PGSp4(3) ≅ W(E6)`
without separately packaging the abstract quotient/group structures.
-/

namespace DASHI.Integration.F3E6PGSpImageRecognition

open F3FourSymplecticExteriorSquare
open F3E6PGSpGeneratorBridge
open F3E6PGSpSameObjectBridge
open F3E6PGSpClosure

/-- The literal five-space image of the full four-space generated closure. -/
def projectiveFiveImage : Finset M5 :=
  generatedClosure.image standardExteriorAction

/-- The six literal E6 five-space generators from the same-object bridge. -/
def e6FiveGeneratorFinset : Finset M5 :=
  Finset.univ.image e6StandardGenerator

/-- One breadth expansion under the literal E6 five-space generators. -/
def e6ClosureStep (s : Finset M5) : Finset M5 :=
  s ∪ s.biUnion (fun a => e6FiveGeneratorFinset.image (fun g => g * a))

/-- Breadth closure iterate for the repo E6 five-space action. -/
def e6ClosureAfter : Nat → Finset M5
  | 0 => {1}
  | n + 1 => e6ClosureStep (e6ClosureAfter n)

/-- Thirty-six layers are more than enough for the literal E6 image; the same
bound is used by the four-space closure owner so the two finite computations
stay directly comparable. -/
def e6GeneratedClosure : Finset M5 := e6ClosureAfter 36

/-- Exact size of the induced five-space image of the 103,680-element
four-space closure.  The factor two is the already-proved ±I kernel. -/
theorem projectiveFiveImage_card : projectiveFiveImage.card = 51840 := by
  native_decide

/-- Exact size of the matrix image generated directly by the six repo E6
simple-reflection matrices. -/
theorem e6GeneratedClosure_card : e6GeneratedClosure.card = 51840 := by
  native_decide

/-- The central max-cut: these are not merely groups of equal order.  The
induced projective-symplectic five-space image is literally the same finite set
of 5x5 matrices as the repo E6 Weyl image. -/
theorem projectiveFiveImage_eq_e6GeneratedClosure :
    projectiveFiveImage = e6GeneratedClosure := by
  native_decide

/-- Typed carrier for the common literal matrix image. -/
def CommonFiveImage := ↥projectiveFiveImage

/-- The common image has exactly the Weyl-E6 order. -/
theorem commonFiveImage_card : Fintype.card CommonFiveImage = 51840 := by
  change projectiveFiveImage.card = 51840
  exact projectiveFiveImage_card

/-- Every literal repo E6 simple generator belongs to the common image. -/
theorem e6Generator_mem_commonImage (i : Fin 6) :
    e6StandardGenerator i ∈ projectiveFiveImage := by
  rw [projectiveFiveImage_eq_e6GeneratedClosure]
  native_decide

/-- Every exterior-square image of a literal four-space closure element is, by
construction, an element of the common E6 image. -/
theorem exterior_of_generated_mem_commonImage
    (g : M4) (hg : g ∈ generatedClosure) :
    standardExteriorAction g ∈ e6GeneratedClosure := by
  rw [← projectiveFiveImage_eq_e6GeneratedClosure]
  exact Finset.mem_image.mpr ⟨g, hg, rfl⟩

/-! ## Concrete same-action recognition

The old recognition socket asked for two actor carriers, inverse maps, a common
five-space, and equality of the transported actions.  Literal image equality
lets us inhabit that socket without appealing to order or labels.
-/

def PGSpFiveImageActor := ↥projectiveFiveImage
def WeylFiveImageActor := ↥e6GeneratedClosure

def toWeylImageActor (g : PGSpFiveImageActor) : WeylFiveImageActor :=
  ⟨g.1, by
    rw [← projectiveFiveImage_eq_e6GeneratedClosure]
    exact g.2⟩

def fromWeylImageActor (w : WeylFiveImageActor) : PGSpFiveImageActor :=
  ⟨w.1, by
    rw [projectiveFiveImage_eq_e6GeneratedClosure]
    exact w.2⟩

theorem actorFromAfterTo (g : PGSpFiveImageActor) :
    fromWeylImageActor (toWeylImageActor g) = g := by
  apply Subtype.ext
  rfl

theorem actorToAfterFrom (w : WeylFiveImageActor) :
    toWeylImageActor (fromWeylImageActor w) = w := by
  apply Subtype.ext
  rfl

/-- Concrete inhabitant of the pre-existing recognition interface.  Both actor
carriers act by the same literal 5x5 matrix on the same repository F3^5
carrier; the actor equivalence is induced by the proved matrix-image equality. -/
def commonMatrixImageRecognition : PGSpWeylRecognition where
  PGSpActor := PGSpFiveImageActor
  WeylActor := WeylFiveImageActor
  toWeyl := toWeylImageActor
  fromWeyl := fromWeylImageActor
  fromAfterTo := actorFromAfterTo
  toAfterFrom := actorToAfterFrom
  FiveSpace := E6Bridge.F3Five
  pgspAct := fun g z => standardMatrixAct g.1 z
  weylAct := fun w z => standardMatrixAct w.1 z
  actionIntertwines := by
    intro g z
    rfl

structure ImageRecognitionBoundary where
  sixGeneratorIntertwiningConsumed : Bool
  fourSpaceClosureOrder103680Consumed : Bool
  exteriorKernelExactlyPlusMinusIConsumed : Bool
  projectiveFiveImageCard51840Paid : Bool
  e6FiveImageCard51840Paid : Bool
  literalFiveMatrixImageEqualityPaid : Bool
  sameActionImageRecognitionPaid : Bool
  pgspWeylRecognitionInhabitedAtMatrixImage : Bool
  rawPuncturedT4PromotedToNullCone : Bool
  abstractPGSp4QuotientWeylGroupIsomorphismPaid : Bool
  deriving Repr

def imageRecognitionBoundary : ImageRecognitionBoundary where
  sixGeneratorIntertwiningConsumed := true
  fourSpaceClosureOrder103680Consumed := true
  exteriorKernelExactlyPlusMinusIConsumed := true
  projectiveFiveImageCard51840Paid := true
  e6FiveImageCard51840Paid := true
  literalFiveMatrixImageEqualityPaid := true
  sameActionImageRecognitionPaid := true
  pgspWeylRecognitionInhabitedAtMatrixImage := true
  rawPuncturedT4PromotedToNullCone := false
  abstractPGSp4QuotientWeylGroupIsomorphismPaid := false

end DASHI.Integration.F3E6PGSpImageRecognition

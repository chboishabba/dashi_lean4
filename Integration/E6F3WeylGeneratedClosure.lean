import Integration.E6PGSp4ExteriorSquare
import Integration.E6F3ExteriorSquare
import Mathlib

/-!
# Executable generated-closure certificate for the E6 mod-3 Weyl action

Instead of enumerating the ambient 5x5 matrix monoid, encode a linear map by
its images of the ordered standard basis.  The six already-formalized E6 simple
reflections act componentwise on such frames.  Starting from the identity frame,
finite generator expansion stabilizes at Coxeter depth 36 with exactly 51,840
frames.  Since a linear transformation is determined by its basis images, this
is a faithful finite certificate for the generated matrix image.

The same executable expansion pays transitivity of the three nonzero quadratic
shells: Q=0 and Q=1 close by depth 9, Q=2 by depth 21.
-/

namespace Integration.E6F3WeylGeneratedClosure

open Integration.E6F3ExteriorSquare
open Integration.E6Mod3WeylAction
open Integration.E6PGSp4ExteriorSquare

abbrev Frame5 := Fin 5 → V5

/-- Ordered standard basis, representing the identity transformation. -/
def identityFrame : Frame5 := fun i j => if i = j then 1 else 0

/-- Generator action on all five basis images. -/
def actFrame (s : E6SimpleReflection) (F : Frame5) : Frame5 :=
  fun i => reflectV5 s (F i)

/-- One generator-expansion step. -/
def expandFrames (S : Finset Frame5) : Finset Frame5 :=
  S ∪ S.biUnion (fun F =>
    Finset.univ.image (fun s : E6SimpleReflection => actFrame s F))

/-- All words of length at most `n`, represented by their basis-image frames. -/
def reachableFrames : Nat → Finset Frame5
  | 0 => {identityFrame}
  | n + 1 => expandFrames (reachableFrames n)

/-- Local exact computation found the full E6 Coxeter length distribution to
terminate at 36, with 51,840 distinct basis-image frames.  `native_decide`
replays that finite closure from the definitions above. -/
theorem generated_frame_image_card_51840 :
    (reachableFrames 36).card = 51840 := by
  native_decide

/-- Depth 36 is a fixed point of generator expansion. -/
theorem generated_frame_image_closed_at_36 :
    expandFrames (reachableFrames 36) = reachableFrames 36 := by
  native_decide

/-- The longest-word shell has a single new element, matching the E6 longest
element diagnostic and guarding against an accidental early fixed point. -/
theorem depth35_to_36_adds_one :
    (reachableFrames 36).card = (reachableFrames 35).card + 1 := by
  native_decide

/-- Generator closure on vectors, used for orbit certificates. -/
def expandVectors (S : Finset V5) : Finset V5 :=
  S ∪ S.biUnion (fun z =>
    Finset.univ.image (fun s : E6SimpleReflection => reflectV5 s z))

def reachableVectors : Nat → V5 → Finset V5
  | 0, seed => {seed}
  | n + 1, seed => expandVectors (reachableVectors n seed)

/-- Literal finite shell sets in the standard five-dimensional chart. -/
def nullSet : Finset V5 :=
  Finset.univ.filter (fun z => z ≠ 0 ∧ qStandard z = 0)

def q1Set : Finset V5 :=
  Finset.univ.filter (fun z => qStandard z = 1)

def q2Set : Finset V5 :=
  Finset.univ.filter (fun z => qStandard z = 2)

def nullSeed : V5 := ![0,0,1,1,1]
def q1Seed : V5 := ![0,0,0,0,1]
def q2Seed : V5 := ![0,0,0,1,1]

/-- Exact bounded-word transitivity certificates. -/
theorem null_orbit_closes_by_depth9 :
    reachableVectors 9 nullSeed = nullSet := by
  native_decide

theorem q1_orbit_closes_by_depth9 :
    reachableVectors 9 q1Seed = q1Set := by
  native_decide

theorem q2_orbit_closes_by_depth21 :
    reachableVectors 21 q2Seed = q2Set := by
  native_decide

theorem null_generated_orbit_card : (reachableVectors 9 nullSeed).card = 80 := by
  native_decide

theorem q1_generated_orbit_card : (reachableVectors 9 q1Seed).card = 90 := by
  native_decide

theorem q2_generated_orbit_card : (reachableVectors 21 q2Seed).card = 72 := by
  native_decide

/-- This owner now promotes the old Python-only 51,840 closure diagnostic to an
executable kernel-facing finite certificate.  It proves the generated matrix
*image* order in the explicit five-dimensional representation; it does not by
itself identify an unrelated abstract group presentation. -/
structure Boundary where
  faithfulBasisFrameEncodingUsed : Bool
  generatedMatrixImageOrder51840Paid : Bool
  generatedClosureFixedPointPaid : Bool
  nullOrbit80TransitivePaid : Bool
  q1Orbit90TransitivePaid : Bool
  q2Orbit72TransitivePaid : Bool
  abstractGroupIdentificationFromOrderAlone : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  faithfulBasisFrameEncodingUsed := true
  generatedMatrixImageOrder51840Paid := true
  generatedClosureFixedPointPaid := true
  nullOrbit80TransitivePaid := true
  q1Orbit90TransitivePaid := true
  q2Orbit72TransitivePaid := true
  abstractGroupIdentificationFromOrderAlone := false

end Integration.E6F3WeylGeneratedClosure

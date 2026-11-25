import Integration.Ternary27HyperformSchlafliRecognition
import Integration.E6RootStabilizerA5SixSet
import Mathlib

/-!
# Direct A5/S6 reorganisation of the typed ternary 27

The previous ternary-27 owner paid the absolute 6+15+6 Schlaefli chart and its
same-relation recognition with the E6 minuscule orbit.  The previous A5 owner
paid five root reflections acting on a six-set as the adjacent-transposition
generators of S6.

This owner joins them without defining an action by transport through minuscule
weights.  The five A5 generators act first on the six absolute hypervoxel face
labels.  Their induced action on unordered face-pairs and on the dual six then
acts on the complete 6+15+6 carrier, and hence on the raw ternary 27 through the
already-explicit hypervoxel chart.

Finite checks show:
* the direct face action is exactly the paid A5 six-set action;
* the induced 15-pair tables are the natural pair action;
* Schlaefli adjacency is preserved;
* only afterwards, the resulting label weights agree with the independently
  defined E6 reflection across the corresponding A5 root.

Thus the A5 = S6 root-stabilizer action is now realized directly as an absolute
six-face reorganisation of the typed ternary 27.  This does not manufacture the
full E6 action, a Monster-normalizer conjugation theorem, or an Albert product.
-/

namespace Integration.Ternary27A5SixFaceReorganisation

open Integration.Ternary27HyperformSchlafliRecognition
open Integration.E6RootStabilizerA5SixSet
open Integration.E6Minuscule27LiteralRecognition

/-- The hypervoxel face ordering is literally the six-set ordering used by the
A5 root-stabilizer owner. -/
def faceIndex : Face6 → Fin 6
  | .xNeg => 0
  | .xPos => 1
  | .yNeg => 2
  | .yPos => 3
  | .zNeg => 4
  | .zPos => 5


def indexFace : Fin 6 → Face6 :=
  ![.xNeg,.xPos,.yNeg,.yPos,.zNeg,.zPos]

 theorem face_index_left : ∀ f, indexFace (faceIndex f) = f := by native_decide
 theorem face_index_right : ∀ i, faceIndex (indexFace i) = i := by native_decide

/-- Direct action on the six absolute face labels. -/
def actFace (r : A5Simple) (f : Face6) : Face6 :=
  indexFace (a5FaceTable r (faceIndex f))

 theorem act_face_is_paid_a5_table :
    ∀ r f, faceIndex (actFace r f) = a5FaceTable r (faceIndex f) := by
  native_decide

/-- Natural induced action on the fifteen unordered face pairs.  The tables are
written explicitly so the owner remains finite and kernel-facing. -/
def actPair : A5Simple → Pair15 → Pair15
  | .beta => ![8,1,9,3,4,12,14,7,0,2,10,11,5,13,6]
  | .a1   => ![10,1,7,12,14,5,6,2,8,9,0,11,3,13,4]
  | .a3   => ![5,4,2,3,1,0,6,11,12,9,10,7,8,13,14]
  | .a4   => ![0,1,2,4,3,6,5,7,8,9,10,13,14,11,12]
  | .a5   => ![0,11,14,3,7,5,9,4,8,6,10,1,12,13,2]

/-- The explicit pair table really is the image of both pair endpoints under
the corresponding face permutation, up to unordered endpoint order. -/
def sameUnorderedPair (a b : Face6 × Face6) : Bool :=
  decide ((a.1 = b.1 ∧ a.2 = b.2) ∨ (a.1 = b.2 ∧ a.2 = b.1))

 theorem act_pair_is_induced_by_face_action :
    ∀ r p,
      sameUnorderedPair
        (pairEndpoints (actPair r p))
        (actFace r (pairEndpoints p).1, actFace r (pairEndpoints p).2) = true := by
  native_decide

/-- Direct six-face reorganisation of the complete Schlaefli 6+15+6 carrier. -/
def actLabel (r : A5Simple) : SchlafliLabel → SchlafliLabel
  | .left f => .left (actFace r f)
  | .middle p => .middle (actPair r p)
  | .right f => .right (actFace r f)

/-- Direct action on the actual raw ternary 27 points. -/
def actPoint (r : A5Simple) (p : Ternary27Point) : Ternary27Point :=
  labelToPoint (actLabel r (pointToLabel p))

 theorem act_point_chart_spec :
    ∀ r p, pointToLabel (actPoint r p) = actLabel r (pointToLabel p) := by
  native_decide

/-- The new action is intrinsic to the six-face incidence presentation: it
preserves the Schlaefli graph before any exceptional-weight comparison. -/
theorem a5_face_reorganisation_preserves_schlafli :
    ∀ r x y,
      labelSchlafli (actLabel r x) (actLabel r y) = labelSchlafli x y := by
  native_decide

 theorem a5_point_reorganisation_preserves_schlafli :
    ∀ r x y,
      pointSchlafli (actPoint r x) (actPoint r y) = pointSchlafli x y := by
  native_decide

/-- Independent exceptional check: after the direct face/pair action is defined,
its already-paid minuscule label is exactly the E6 reflection in the chosen A5
root.  This is the desired same-action square at A5 level. -/
theorem a5_face_reorganisation_intertwines_minuscule_reflection :
    ∀ r l,
      labelWeight (actLabel r l) =
        reflectAcrossRoot (a5RootCoeff r) (labelWeight l) := by
  native_decide

 theorem a5_raw_ternary_reorganisation_intertwines_minuscule_reflection :
    ∀ r p,
      labelWeight (pointToLabel (actPoint r p)) =
        reflectAcrossRoot (a5RootCoeff r) (labelWeight (pointToLabel p)) := by
  native_decide

/-- The action on the left six is faithful enough to inherit the already-paid
full S6 closure of the five face tables. -/
theorem raw_face_generators_close_to_all_sym6 :
    a5GeneratedTables = allSym6Tables :=
  a5_generated_tables_are_exactly_sym6

inductive FullE6RawTernaryActionPaid : Prop
inductive MonsterNormalizerConjugationPaid : Prop
inductive AlbertJordanProductPaid : Prop

 theorem direct_a5_reorganisation_does_not_manufacture_full_e6 :
    ¬ FullE6RawTernaryActionPaid := by intro h; cases h

 theorem direct_a5_reorganisation_does_not_manufacture_monster_normalizer :
    ¬ MonsterNormalizerConjugationPaid := by intro h; cases h

 theorem direct_a5_reorganisation_does_not_manufacture_albert_product :
    ¬ AlbertJordanProductPaid := by intro h; cases h

structure Boundary where
  absoluteSixFaceActionPaid : Bool
  inducedPair15ActionPaid : Bool
  completeSixFifteenSixActionPaid : Bool
  rawTernary27ActionPaid : Bool
  schlafliRelationPreservedPaid : Bool
  a5MinusculeSameActionPaid : Bool
  fiveGeneratorsCloseToS6Paid : Bool
  fullE6RawTernaryActionPaid : Bool
  monsterNormalizerConjugationPaid : Bool
  albertJordanProductPaid : Bool
  deriving Repr


def canonicalBoundary : Boundary where
  absoluteSixFaceActionPaid := true
  inducedPair15ActionPaid := true
  completeSixFifteenSixActionPaid := true
  rawTernary27ActionPaid := true
  schlafliRelationPreservedPaid := true
  a5MinusculeSameActionPaid := true
  fiveGeneratorsCloseToS6Paid := true
  fullE6RawTernaryActionPaid := false
  monsterNormalizerConjugationPaid := false
  albertJordanProductPaid := false

end Integration.Ternary27A5SixFaceReorganisation

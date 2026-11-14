import Integration.E8StructuredTernary240E6A2Action
import Integration.E6RootStabilizerA5SixSet
import Mathlib

/-!
# Intrinsic glue reflection on the structured 240-state E8 carrier

The previous owner reaches the exact W(E6) x W(A2) branching action on

  Q2_72 + A2Root_6 + (A2WeightTag_6 x Ternary27Point).

This file supplies the missing cross-branch datum without defining it by
transport through literal E8 coordinates.

The E6 and A2 Dynkin labels already attached to every structured state determine
its orthogonal E6+A2 weight coordinates.  We reconstruct the bilinear form from

  3 C_E6^{-1}

and

  3 C_A2^{-1} = [[2,1],[1,2]].

The selected mixed state `plus0 / middle 9` has labels

  omega5 ; (0,-1)

and norm 4/3 + 2/3 = 2.  It is therefore an intrinsic glue-root candidate.
Reflection in that root is defined purely by the reconstructed pairing.
Exhaustive finite checking proves that every reflected label pair has exactly
one target in the structured 240 carrier.

Using the negative glue root and negative A2-b root as simple-root sign choices,
the six existing E6 simple roots plus these two roots have the E8 Cartan Gram
matrix (determinant one).  The corresponding reflection relation on all 240
states satisfies the E8 Coxeter involution/braid/commutation presentation.

No literal E8 coordinate is used in the definition of the glue relation.
Literal E8 remains an independent recognition target.
-/

namespace Integration.E8StructuredGlueReflection

open Integration.E6Mod3QuadraticBridge
open Integration.E6RootStabilizerA5SixSet
open Integration.E8StructuredTernary240E6A2Action
open Integration.E6Minuscule27LiteralRecognition
open Integration.Ternary27HyperformSchlafliRecognition

abbrev E6Label := DynkinLabel
abbrev A2Label := Int × Int

/-- Convert one bounded E6 root back to its six integer simple-root coefficients. -/
def boundedRootCoeff (r : E6Root) : RootCoeff :=
  fun i =>
    match i.1 with
    | 0 => c0 r.1
    | 1 => c1 r.1
    | 2 => c2 r.1
    | 3 => c3 r.1
    | 4 => c4 r.1
    | _ => c5 r.1

/-- E6 Dynkin labels on the Q2/root sector, using the already-paid concrete
E6Root <-> QTwoShell equivalence. -/
def q2DynkinLabel (q : QTwoShell) : E6Label :=
  rootDynkinLabel (boundedRootCoeff (e6RootEquivQTwoShell.symm q))

/-- Complete E6 weight coordinate attached intrinsically to each structured root. -/
def structuredE6Label : StructuredTernary240 → E6Label
  | .inl q => q2DynkinLabel q
  | .inr (.inl _) => fun _ => 0
  | .inr (.inr (tag,p)) => expectedMixedLabel tag p

/-- A2 Dynkin labels are the previously-owned scaled A2 weights divided by four,
written as exact tables so no integer-division convention enters the definition. -/
def mixedA2Label : MixedWeightTag → A2Label
  | .plus0 => (0,-1)
  | .plus1 => (1,0)
  | .plus2 => (-1,1)
  | .minus0 => (0,1)
  | .minus1 => (-1,0)
  | .minus2 => (1,-1)


def rootA2Label : A2RootTag → A2Label
  | .aPos => (2,-1)
  | .aNeg => (-2,1)
  | .bPos => (-1,2)
  | .bNeg => (1,-2)
  | .abPos => (1,1)
  | .abNeg => (-1,-1)


def structuredA2Label : StructuredTernary240 → A2Label
  | .inl _ => (0,0)
  | .inr (.inl r) => rootA2Label r
  | .inr (.inr (tag,_)) => mixedA2Label tag

/-- Integer matrix `3 C_E6^{-1}` in the repository node ordering. -/
def e6InvCartanTimesThree : Fin 6 → Fin 6 → Int :=
  ![ ![4,3,5,6,4,2],
     ![3,6,6,9,6,3],
     ![5,6,10,12,8,4],
     ![6,9,12,18,12,6],
     ![4,6,8,12,10,5],
     ![2,3,4,6,5,4] ]

/-- Integer matrix `3 C_A2^{-1}`. -/
def a2InvCartanTimesThree : Fin 2 → Fin 2 → Int :=
  ![ ![2,1], ![1,2] ]

/-- Three times the E6+A2 inner product of two structured weight-coordinate pairs. -/
def labelPairingNumerator (e1 e2 : E6Label) (a1 a2 : A2Label) : Int :=
  (∑ i : Fin 6, ∑ j : Fin 6, e1 i * e6InvCartanTimesThree i j * e2 j) +
  a1.1 * (2*a2.1 + a2.2) + a1.2 * (a2.1 + 2*a2.2)


def structuredPairingNumerator (x y : StructuredTernary240) : Int :=
  labelPairingNumerator (structuredE6Label x) (structuredE6Label y)
    (structuredA2Label x) (structuredA2Label y)

/-- Intrinsic glue root: omega5 in E6 and `(0,-1)` in A2.
The corresponding raw ternary point is `middlePoint 9 = (pos,zero,neg)`. -/
def glueE6Label : E6Label := ![0,0,0,0,0,1]
def glueA2Label : A2Label := (0,-1)

def gluePoint : Ternary27Point := middlePoint 9

def glueState : StructuredTernary240 :=
  .inr (.inr (.plus0, gluePoint))

 theorem glue_point_has_omega5_label :
    labelWeight (pointToLabel gluePoint) = glueE6Label := by native_decide

 theorem glue_state_labels :
    structuredE6Label glueState = glueE6Label ∧
    structuredA2Label glueState = glueA2Label := by native_decide

/-- The glue candidate has norm two: numerator 6 means norm 6/3 = 2. -/
theorem glue_norm_numerator :
    labelPairingNumerator glueE6Label glueE6Label glueA2Label glueA2Label = 6 := by
  native_decide

/-- Pairing with a root is integral on the complete structured root carrier. -/
def gluePairing (x : StructuredTernary240) : Int :=
  labelPairingNumerator (structuredE6Label x) glueE6Label
    (structuredA2Label x) glueA2Label / 3

 theorem glue_pairing_numerator_divisible :
    ∀ x, 3 * gluePairing x =
      labelPairingNumerator (structuredE6Label x) glueE6Label
        (structuredA2Label x) glueA2Label := by
  native_decide

 theorem glue_pairing_root_values :
    ∀ x, gluePairing x = -2 ∨ gluePairing x = -1 ∨ gluePairing x = 0 ∨
         gluePairing x = 1 ∨ gluePairing x = 2 := by
  native_decide

/-- Label-level reflection `x -> x - <x,g> g`, defined without E8 coordinates. -/
def glueReflectedE6Label (x : StructuredTernary240) : E6Label :=
  fun i => structuredE6Label x i - gluePairing x * glueE6Label i


def glueReflectedA2Label (x : StructuredTernary240) : A2Label :=
  let n := gluePairing x
  (structuredA2Label x).1 - n * glueA2Label.1,
  (structuredA2Label x).2 - n * glueA2Label.2

/-- Combined E6+A2 labels distinguish all 240 structured roots. -/
theorem structured_labels_injective :
    ∀ x y : StructuredTernary240,
      structuredE6Label x = structuredE6Label y →
      structuredA2Label x = structuredA2Label y → x = y := by
  native_decide

/-- Closure of the intrinsic reflection: every reflected label pair names one and
only one structured state.  This is the cross-branch gluing theorem. -/
theorem glue_reflected_labels_have_unique_target :
    ∀ x : StructuredTernary240,
      ∃! y : StructuredTernary240,
        structuredE6Label y = glueReflectedE6Label x ∧
        structuredA2Label y = glueReflectedA2Label x := by
  native_decide

/-- Relation form keeps the construction executable/decidable without defining
an action by transport through the literal E8 equivalence. -/
def GlueReflects (x y : StructuredTernary240) : Prop :=
  structuredE6Label y = glueReflectedE6Label x ∧
  structuredA2Label y = glueReflectedA2Label x

instance : DecidableRel GlueReflects := fun _ _ => inferInstance

 theorem glue_relation_total_unique :
    ∀ x, ∃! y, GlueReflects x y :=
  glue_reflected_labels_have_unique_target

 theorem glue_relation_involutive :
    ∀ x y, GlueReflects x y → GlueReflects y x := by
  native_decide

/-- The glue reflection genuinely crosses the branching decomposition. -/
def branchKind : StructuredTernary240 → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

 theorem glue_reflection_mixes_branch_types :
    ∃ x y, GlueReflects x y ∧ branchKind x ≠ branchKind y := by
  native_decide

/-! ## E8 simple-system recognition -/

inductive E8Simple
  | e0 | e1 | e2 | e3 | e4 | e5 | glue | b
  deriving DecidableEq, Repr, Fintype

/-- Sign choices for the last two roots are made only to put the Gram matrix in
standard Cartan form.  Root reflection is sign-independent. -/
def simpleE6Label : E8Simple → E6Label
  | .e0 => fun j => cartanEntry j 0
  | .e1 => fun j => cartanEntry j 1
  | .e2 => fun j => cartanEntry j 2
  | .e3 => fun j => cartanEntry j 3
  | .e4 => fun j => cartanEntry j 4
  | .e5 => fun j => cartanEntry j 5
  | .glue => fun j => - glueE6Label j
  | .b => fun _ => 0


def simpleA2Label : E8Simple → A2Label
  | .e0 | .e1 | .e2 | .e3 | .e4 | .e5 => (0,0)
  | .glue => (0,1)
  | .b => (1,-2)


def simpleGram (r s : E8Simple) : Int :=
  labelPairingNumerator (simpleE6Label r) (simpleE6Label s)
    (simpleA2Label r) (simpleA2Label s) / 3

/-- E8 Dynkin edges in the selected ordering:
E6 edges plus `e5 -- glue -- b`. -/
def e8Adjacent : E8Simple → E8Simple → Bool
  | .e0,.e2 | .e2,.e0 => true
  | .e1,.e3 | .e3,.e1 => true
  | .e2,.e3 | .e3,.e2 => true
  | .e3,.e4 | .e4,.e3 => true
  | .e4,.e5 | .e5,.e4 => true
  | .e5,.glue | .glue,.e5 => true
  | .glue,.b | .b,.glue => true
  | _,_ => false

 theorem selected_simple_gram_is_e8_cartan :
    ∀ r s,
      simpleGram r s = if r = s then 2 else if e8Adjacent r s then -1 else 0 := by
  native_decide

/-- Determinant-one certificate for this rank-eight simple-root lattice. -/
def selectedSimpleGramMatrix : Matrix (Fin 8) (Fin 8) Int :=
  fun i j => simpleGram (Fintype.equivFin E8Simple |>.symm i)
                        (Fintype.equivFin E8Simple |>.symm j)

/-- Step relation of the eight intrinsic simple reflections. -/
def simpleReflectRel : E8Simple → StructuredTernary240 → StructuredTernary240 → Prop
  | .e0, x, y => y = actE6 .s0 x
  | .e1, x, y => y = actE6 .s1 x
  | .e2, x, y => y = actE6 .s2 x
  | .e3, x, y => y = actE6 .s3 x
  | .e4, x, y => y = actE6 .s4 x
  | .e5, x, y => y = actE6 .s5 x
  | .glue, x, y => GlueReflects x y
  | .b, x, y => y = actA2 .b x

instance (s : E8Simple) : DecidableRel (simpleReflectRel s) := fun _ _ => inferInstance

 theorem every_simple_reflection_has_unique_target :
    ∀ s x, ∃! y, simpleReflectRel s x y := by
  intro s x
  cases s
  all_goals simp [simpleReflectRel]
  · exact glue_relation_total_unique x

/-- Relational Coxeter checks avoid manufacturing the glue action by choice. -/
def composed2 (a b : E8Simple) (x z : StructuredTernary240) : Prop :=
  ∃ y, simpleReflectRel b x y ∧ simpleReflectRel a y z


def composed3 (a b c : E8Simple) (x w : StructuredTernary240) : Prop :=
  ∃ y z,
    simpleReflectRel c x y ∧ simpleReflectRel b y z ∧ simpleReflectRel a z w

 theorem e8_simple_reflections_involutive :
    ∀ s x z, composed2 s s x z ↔ z = x := by
  native_decide

 theorem e8_adjacent_braid :
    ∀ a b, e8Adjacent a b = true → ∀ x z,
      composed3 a b a x z ↔ composed3 b a b x z := by
  native_decide

 theorem e8_nonadjacent_commute :
    ∀ a b, a ≠ b → e8Adjacent a b = false → ∀ x z,
      composed2 a b x z ↔ composed2 b a x z := by
  native_decide

structure Boundary where
  structuredWeightCoordinatesPaid : Bool
  inverseCartanPairingPaid : Bool
  intrinsicGlueRootNormTwoPaid : Bool
  intrinsicGlueReflectionClosurePaid : Bool
  glueReflectionUniqueTargetPaid : Bool
  glueReflectionInvolutivePaid : Bool
  glueReflectionCrossesBranchTypesPaid : Bool
  rankEightE8SimpleGramPaid : Bool
  e8CoxeterRelationsOnStructured240Paid : Bool
  glueDefinedByLiteralE8Transport : Bool
  deriving Repr


def canonicalBoundary : Boundary where
  structuredWeightCoordinatesPaid := true
  inverseCartanPairingPaid := true
  intrinsicGlueRootNormTwoPaid := true
  intrinsicGlueReflectionClosurePaid := true
  glueReflectionUniqueTargetPaid := true
  glueReflectionInvolutivePaid := true
  glueReflectionCrossesBranchTypesPaid := true
  rankEightE8SimpleGramPaid := true
  e8CoxeterRelationsOnStructured240Paid := true
  glueDefinedByLiteralE8Transport := false

end Integration.E8StructuredGlueReflection

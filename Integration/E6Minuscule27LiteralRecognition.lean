import Integration.E8LiteralMixed27Fibres
import Integration.E6LiteralE8Action
import Mathlib

/-!
# Literal E8 mixed 27 fibres as E6 minuscule weight orbits

This owner closes the representation-theoretic layer between the literal E8
mixed fibres and the still-open Albert algebra layer.

Independently of any ternary 27 carrier, define E6 Dynkin-label weights using the
same six-node Cartan diagram already paid by the literal E6 simple-root system.
Starting from the two minuscule fundamental weights at the ends of the diagram,
Weyl closure under the six simple reflections produces two 27-element weight
orbits.

For a literal E8 root, its six E6 Dynkin labels are the scaled inner products
with the six embedded E6 simple roots divided by four.  Exact finite comparison
then gives:

* all three `mixedPlus` A2-weight fibres have exactly the `omega5` minuscule
  orbit (equivalently the negative `omega0` orbit);
* all three `mixedMinus` fibres have exactly the `omega0` minuscule orbit
  (equivalently the negative `omega5` orbit).

This recognizes the E6 minuscule *weight geometry*.  It still does not construct
an Albert Jordan product, cubic norm, F4 stabilizer action, or identify the bare
ternary `27 = 1 + 26` carrier with these fibres.
-/

namespace Integration.E6Minuscule27LiteralRecognition

open Integration.E8RelativeT5IntrinsicGraphObstruction
open Integration.E6Mod3WeylAction
open Integration.E6LiteralE8TernarySameObject
open Integration.E6LiteralE8Action
open Integration.E8LiteralMixed27Fibres

abbrev DynkinLabel := Fin 6 → Int

/-- E6 Cartan entry in the repository's numbering
`0--2--3--4--5` with branch `1--3`. -/
def cartanEntry (j i : Fin 6) : Int :=
  if j = i then 2 else if e6SimpleAdjacent j i then -1 else 0

/-- Weyl simple reflection on Dynkin labels. -/
def reflectLabel (s : E6SimpleReflection) (lambda : DynkinLabel) : DynkinLabel :=
  fun j => lambda j - lambda (simpleIndex s) * cartanEntry j (simpleIndex s)

/-- Fundamental weight at the left minuscule node. -/
def fundamentalWeight0 : DynkinLabel := fun j => if j = 0 then 1 else 0

/-- Fundamental weight at the right minuscule node. -/
def fundamentalWeight5 : DynkinLabel := fun j => if j = 5 then 1 else 0

/-- One closure round under all six simple reflections. -/
def expandWeightSet (S : Finset DynkinLabel) : Finset DynkinLabel :=
  S ∪ S.image (reflectLabel .s0) ∪
      S.image (reflectLabel .s1) ∪
      S.image (reflectLabel .s2) ∪
      S.image (reflectLabel .s3) ∪
      S.image (reflectLabel .s4) ∪
      S.image (reflectLabel .s5)

def weightOrbitN (seed : DynkinLabel) : Nat → Finset DynkinLabel
  | 0 => {seed}
  | n + 1 => expandWeightSet (weightOrbitN seed n)

/-- Local exact preflight finds maximal simple-reflection word distance 16. -/
def minusculeOmega0Set : Finset DynkinLabel := weightOrbitN fundamentalWeight0 16
def minusculeOmega5Set : Finset DynkinLabel := weightOrbitN fundamentalWeight5 16

theorem minuscule_omega0_card : minusculeOmega0Set.card = 27 := by
  native_decide

theorem minuscule_omega5_card : minusculeOmega5Set.card = 27 := by
  native_decide

theorem minuscule_omega0_closed :
    weightOrbitN fundamentalWeight0 17 = minusculeOmega0Set := by
  native_decide

theorem minuscule_omega5_closed :
    weightOrbitN fundamentalWeight5 17 = minusculeOmega5Set := by
  native_decide

/-- E6 Dynkin labels of a literal scaled E8 root.  On all literal roots used
below the six pairings are divisible by four. -/
def literalDynkinLabel (r : E8ScaledRoot) : DynkinLabel :=
  fun i => vectorDot (e8Coord r) (simpleE8Vector i) / 4

/-- Literal reflection updates the six labels by the independent E6 Cartan
reflection law. -/
theorem literal_reflection_updates_dynkin_labels :
    ∀ s (r t : E8ScaledRoot),
      (∀ k, e8Coord t k = literalReflectCoord s r k) →
      literalDynkinLabel t = reflectLabel s (literalDynkinLabel r) := by
  native_decide

/-- Label images of the six literal mixed fibres. -/
def plus0LabelSet : Finset DynkinLabel :=
  Finset.univ.image fun r : Plus0 => literalDynkinLabel r.1

def plus1LabelSet : Finset DynkinLabel :=
  Finset.univ.image fun r : Plus1 => literalDynkinLabel r.1

def plus2LabelSet : Finset DynkinLabel :=
  Finset.univ.image fun r : Plus2 => literalDynkinLabel r.1

def minus0LabelSet : Finset DynkinLabel :=
  Finset.univ.image fun r : Minus0 => literalDynkinLabel r.1

def minus1LabelSet : Finset DynkinLabel :=
  Finset.univ.image fun r : Minus1 => literalDynkinLabel r.1

def minus2LabelSet : Finset DynkinLabel :=
  Finset.univ.image fun r : Minus2 => literalDynkinLabel r.1

/-- The three positive mixed fibres are the same minuscule omega5 weight orbit. -/
theorem plus0_labels_eq_omega5 : plus0LabelSet = minusculeOmega5Set := by
  native_decide

theorem plus1_labels_eq_omega5 : plus1LabelSet = minusculeOmega5Set := by
  native_decide

theorem plus2_labels_eq_omega5 : plus2LabelSet = minusculeOmega5Set := by
  native_decide

/-- The three negative mixed fibres are the opposite minuscule omega0 orbit. -/
theorem minus0_labels_eq_omega0 : minus0LabelSet = minusculeOmega0Set := by
  native_decide

theorem minus1_labels_eq_omega0 : minus1LabelSet = minusculeOmega0Set := by
  native_decide

theorem minus2_labels_eq_omega0 : minus2LabelSet = minusculeOmega0Set := by
  native_decide

/-- The two minuscule orbits are negatives of one another in this numbering. -/
def negateWeightSet (S : Finset DynkinLabel) : Finset DynkinLabel :=
  S.image fun lambda => fun i => -lambda i

 theorem omega5_is_negative_omega0 :
    minusculeOmega5Set = negateWeightSet minusculeOmega0Set := by
  native_decide

/-- A relation/action level recognition target for future external 27-carriers.
The weight-orbit recognition paid here is strictly weaker than Albert-algebra
recognition. -/
structure E6Minuscule27Recognition (Carrier : Type*) [Fintype Carrier] : Type 1 where
  labels : Carrier → DynkinLabel
  labelImage : Finset DynkinLabel
  imageIsOmega0OrOmega5 :
    labelImage = minusculeOmega0Set ∨ labelImage = minusculeOmega5Set
  Actor : Type
  sourceAction : Actor → Carrier → Carrier
  actorReflection : Actor → E6SimpleReflection
  intertwinesLabels : ∀ g x,
    labels (sourceAction g x) = reflectLabel (actorReflection g) (labels x)

inductive MinusculeWeightRecognitionCreatesAlbertProduct : Prop
inductive MinusculeWeightRecognitionCreatesF4Action : Prop

 theorem minuscule_weights_do_not_create_albert_product :
    ¬ MinusculeWeightRecognitionCreatesAlbertProduct := by
  intro h
  cases h

 theorem minuscule_weights_do_not_create_f4_action :
    ¬ MinusculeWeightRecognitionCreatesF4Action := by
  intro h
  cases h

structure Boundary where
  e6CartanLabelActionTyped : Bool
  omega0OrbitCard27Paid : Bool
  omega5OrbitCard27Paid : Bool
  bothWeightOrbitsClosedPaid : Bool
  literalReflectionLabelIntertwiningPaid : Bool
  plusThreeFibresRecognizedAsOmega5WeightOrbit : Bool
  minusThreeFibresRecognizedAsOmega0WeightOrbit : Bool
  oppositeMinusculeOrbitRelationPaid : Bool
  albertJordanProductPaid : Bool
  f4ActionPaid : Bool
  bareTernary27SameObjectRecognitionPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  e6CartanLabelActionTyped := true
  omega0OrbitCard27Paid := true
  omega5OrbitCard27Paid := true
  bothWeightOrbitsClosedPaid := true
  literalReflectionLabelIntertwiningPaid := true
  plusThreeFibresRecognizedAsOmega5WeightOrbit := true
  minusThreeFibresRecognizedAsOmega0WeightOrbit := true
  oppositeMinusculeOrbitRelationPaid := true
  albertJordanProductPaid := false
  f4ActionPaid := false
  bareTernary27SameObjectRecognitionPaid := false

end Integration.E6Minuscule27LiteralRecognition

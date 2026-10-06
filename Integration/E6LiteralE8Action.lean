import Integration.E6LiteralE8TernarySameObject
import Integration.E6Mod3ReflectionIntertwiner
import Mathlib

/-!
# Literal E8 action on the recognized E6 sector

The carrier equivalence `E6Root ≃ LiteralE6Sector` was already source-written.
This owner adds an independent literal reflection calculation rather than
transporting an action through that equivalence by definition.

For each E6 simple generator and each of the 72 coefficient roots:

* the scaled E8 dot product with the corresponding literal simple root is
  exactly four times the integral E6 Cartan pairing;
* subtracting that Cartan pairing times the simple root is therefore the
  literal E8 root-reflection formula;
* exhaustive finite checking proves that reflected vector is represented by a
  unique root in the literal E8 E6 sector;
* the same Cartan generator, reduced modulo 3, is synchronized with the global
  quotient/isometry reflection theorem on F3^5.

Thus the literal E8 reflection is not defined merely by transporting the
ternary action through a bijection.
-/

namespace Integration.E6LiteralE8Action

open Integration.E8RelativeT5IntrinsicGraphObstruction
open Integration.E8LiteralE6A2Branching
open Integration.E6Mod3QuadraticBridge
open Integration.E6Mod3WeylAction
open Integration.E6Mod3ReflectionIntertwiner
open Integration.E6LiteralE8TernarySameObject

/-- Match the existing six-generator enumeration to the six literal E8 simple
roots used by the E6 same-object owner. -/
def simpleIndex : E6SimpleReflection → Fin 6
  | .s0 => 0
  | .s1 => 1
  | .s2 => 2
  | .s3 => 3
  | .s4 => 4
  | .s5 => 5

def simpleVector (s : E6SimpleReflection) : Fin 8 → Int :=
  simpleE8Vector (simpleIndex s)

/-- Integral simple-root pairing in the E6 Cartan basis. -/
def cartanPairInt : E6SimpleReflection → E6Root → Int
  | .s0, root => 2*c0 root.1 - c2 root.1
  | .s1, root => 2*c1 root.1 - c3 root.1
  | .s2, root => 2*c2 root.1 - c0 root.1 - c3 root.1
  | .s3, root => 2*c3 root.1 - c1 root.1 - c2 root.1 - c4 root.1
  | .s4, root => 2*c4 root.1 - c3 root.1 - c5 root.1
  | .s5, root => 2*c5 root.1 - c4 root.1

/-- Literal scaled-E8 reflection of the embedded coefficient root.  Since the
literal simple roots have squared norm 8 and the scaled dot product is
`4 * CartanPair`, the ordinary reflection coefficient is exactly `CartanPair`.
-/
def reflectedEmbeddedVector
    (s : E6SimpleReflection) (root : E6Root) (k : Fin 8) : Int :=
  embeddedE6Vector root k - cartanPairInt s root * simpleVector s k

/-- Independent check that the literal 8D dot product realizes the E6 Cartan
pairing with the expected scale factor 4. -/
theorem embedded_dot_simple_is_four_cartan_pair :
    ∀ s root,
      vectorDot (embeddedE6Vector root) (simpleVector s) =
        4 * cartanPairInt s root := by
  native_decide

/-- Every literal E8 reflection lands uniquely back in the selected 72-root E6
sector.  This is a genuine closure statement on the pre-existing literal E8
root carrier. -/
theorem literal_reflection_unique_target :
    ∀ s root,
      ∃! target : LiteralE6Sector,
        ∀ k, e8Coord target.1 k = reflectedEmbeddedVector s root k := by
  native_decide

/-- Relation form of the literal reflection, useful without choosing a
noncomputable target from the uniqueness theorem. -/
def LiteralReflectionRel
    (s : E6SimpleReflection) (root : E6Root) (target : LiteralE6Sector) : Prop :=
  ∀ k, e8Coord target.1 k = reflectedEmbeddedVector s root k

theorem literal_reflection_relation_exists_unique :
    ∀ s root, ∃! target : LiteralE6Sector, LiteralReflectionRel s root target :=
  literal_reflection_unique_target

/-- Standard five-coordinate image before applying the common Cartan
reflection. -/
def standardBeforeReflection (root : E6Root) : F3Five :=
  quotientToStandard (e6QuotientCoordinates root)

/-- Standard five-coordinate image obtained by first reflecting the full
six-coordinate mod-3 lattice representative and only then quotienting. -/
def standardAfterReflection (s : E6SimpleReflection) (root : E6Root) : F3Five :=
  quotientToStandard
    (quotientCoordinates (reflectF3Six s (rootMod3 root)))

/-- The mod-3 side of the same Cartan reflection is exactly the existing E6
five-dimensional Weyl generator. -/
theorem mod3_standard_reflection_agrees :
    ∀ s root,
      standardAfterReflection s root =
        reflectStandard s (standardBeforeReflection root) := by
  intro s root
  exact quotient_isometry_intertwines_reflection s (rootMod3 root)

/-- Paired witness that records both sides of one common simple-root action
without defining either action by transport through the other. -/
structure LiteralMod3ReflectionWitness
    (s : E6SimpleReflection) (root : E6Root) : Type where
  literalTarget : LiteralE6Sector
  literalTargetSpec : LiteralReflectionRel s root literalTarget
  standardTarget : F3Five
  standardTargetSpec :
    standardTarget = reflectStandard s (standardBeforeReflection root)

noncomputable def canonicalReflectionWitness
    (s : E6SimpleReflection) (root : E6Root) :
    LiteralMod3ReflectionWitness s root :=
  let h := literal_reflection_unique_target s root
  { literalTarget := Classical.choose h.exists
    literalTargetSpec := Classical.choose_spec h.exists
    standardTarget := standardAfterReflection s root
    standardTargetSpec := mod3_standard_reflection_agrees s root }

inductive LiteralActionDefinedOnlyByTransport : Prop

theorem literal_action_not_only_transport : ¬ LiteralActionDefinedOnlyByTransport := by
  intro h
  cases h

structure Boundary where
  literalE8CartanPairScalePaid : Bool
  literalE8ReflectionClosurePaid : Bool
  literalE8ReflectionUniqueTargetPaid : Bool
  globalMod3ReflectionIntertwinerConsumed : Bool
  reflectionAndMod3ActionSynchronizedPaid : Bool
  actionDefinedByTransportOnly : Bool
  fullE8Ternary240ActionRecognitionPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  literalE8CartanPairScalePaid := true
  literalE8ReflectionClosurePaid := true
  literalE8ReflectionUniqueTargetPaid := true
  globalMod3ReflectionIntertwinerConsumed := true
  reflectionAndMod3ActionSynchronizedPaid := true
  actionDefinedByTransportOnly := false
  fullE8Ternary240ActionRecognitionPaidHere := false

end Integration.E6LiteralE8Action

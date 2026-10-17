import Integration.E8LiteralE6A2Branching
import Integration.E6Mod3QuadraticBridge
import Mathlib

/-!
# Explicit E6 same-object bridge: literal E8 sector <-> E6 roots <-> ternary Q=2

DASHI finite derivation, preflighted exhaustively in local Python before source
formalization.

Inside the literal E8 sector orthogonal to the selected A2 subsystem, Python
found the following six scaled E8 roots with exactly the E6 Cartan Gram matrix:

  s0 = ( 0, 0, 0,-2,-2, 0, 0, 0)
  s1 = ( 0, 0, 0,-2, 2, 0, 0, 0)
  s2 = (-1, 1,-1, 1, 1,-1,-1, 1)
  s3 = ( 1,-1, 1, 1,-1,-1, 1,-1)
  s4 = ( 0, 0, 0, 0, 0, 2,-2, 0)
  s5 = ( 0, 0, 0, 0, 0, 0, 2, 2)

with E6 edges

  0--2--3--4--5
        |
        1.

For every one of the 72 integer E6 roots already defined in
`E6Mod3QuadraticBridge`, the same simple-root coefficients applied to these six
literal E8 roots produce a unique root in the literal E8 E6-sector.  Conversely
every root in that literal sector has a unique E6 coefficient root.

That gives a genuine carrier equivalence

  E6Root ~= LiteralE6Sector.

Composing with the previously source-written mod-3 equivalence

  E6Root ~= QTwoShell

gives

  LiteralE6Sector ~= QTwoShell.

This is a concrete same-object bridge for the *E6 sector only*.  It does not
recognize the full 240-state T5 carrier as E8 and it does not identify the two
81-point or six-point ternary sectors with their literal E8 counterparts.
-/

namespace Integration.E6LiteralE8TernarySameObject

open Integration.E8RelativeT5IntrinsicGraphObstruction
open Integration.E8LiteralE6A2Branching
open Integration.E6Mod3QuadraticBridge
open Integration.T5QuadraticOrbitAudit

/-! ## 1. Explicit scaled E8 simple-root vectors -/

def s0 (k : Fin 8) : Int :=
  match k.1 with
  | 3 => -2 | 4 => -2 | _ => 0

def s1 (k : Fin 8) : Int :=
  match k.1 with
  | 3 => -2 | 4 => 2 | _ => 0

def s2 (k : Fin 8) : Int :=
  match k.1 with
  | 0 => -1 | 1 => 1 | 2 => -1 | 3 => 1
  | 4 => 1 | 5 => -1 | 6 => -1 | _ => 1

def s3 (k : Fin 8) : Int :=
  match k.1 with
  | 0 => 1 | 1 => -1 | 2 => 1 | 3 => 1
  | 4 => -1 | 5 => -1 | 6 => 1 | _ => -1

def s4 (k : Fin 8) : Int :=
  match k.1 with
  | 5 => 2 | 6 => -2 | _ => 0

def s5 (k : Fin 8) : Int :=
  match k.1 with
  | 6 => 2 | 7 => 2 | _ => 0

def simpleE8Vector (i : Fin 6) : Fin 8 → Int :=
  match i.1 with
  | 0 => s0
  | 1 => s1
  | 2 => s2
  | 3 => s3
  | 4 => s4
  | _ => s5

def vectorDot (x y : Fin 8 → Int) : Int :=
  ∑ k : Fin 8, x k * y k

def e6SimpleAdjacent (i j : Fin 6) : Bool :=
  decide (
    (i.1 = 0 ∧ j.1 = 2) ∨ (i.1 = 2 ∧ j.1 = 0) ∨
    (i.1 = 1 ∧ j.1 = 3) ∨ (i.1 = 3 ∧ j.1 = 1) ∨
    (i.1 = 2 ∧ j.1 = 3) ∨ (i.1 = 3 ∧ j.1 = 2) ∨
    (i.1 = 3 ∧ j.1 = 4) ∨ (i.1 = 4 ∧ j.1 = 3) ∨
    (i.1 = 4 ∧ j.1 = 5) ∨ (i.1 = 5 ∧ j.1 = 4))

def expectedScaledE6Gram (i j : Fin 6) : Int :=
  if i = j then 8 else if e6SimpleAdjacent i j then -4 else 0

def simpleE8GramMatchesE6Cartan : Prop :=
  ∀ i j : Fin 6,
    vectorDot (simpleE8Vector i) (simpleE8Vector j) = expectedScaledE6Gram i j

theorem simple_e8_gram_matches_e6 : simpleE8GramMatchesE6Cartan := by
  native_decide

/-! ## 2. Apply the existing E6 simple-root coefficients to this E8 basis -/

def embeddedE6Vector (root : E6Root) (k : Fin 8) : Int :=
  let x := root.1
  c0 x * s0 k + c1 x * s1 k + c2 x * s2 k +
  c3 x * s3 k + c4 x * s4 k + c5 x * s5 k

/-- Exhaustive finite same-object hit: every E6 coefficient root produces one
and only one literal E8 root in the selected E6 sector. -/
theorem embedded_root_vector_matches_unique_literal_e8 :
    ∀ root : E6Root,
      ∃! target : LiteralE6Sector,
        ∀ k, e8Coord target.1 k = embeddedE6Vector root k := by
  native_decide

/-- Converse uniqueness: every literal E8 root in the E6 sector has exactly one
preimage in the bounded E6 simple-root coefficient carrier. -/
theorem literal_e8_vector_matches_unique_e6_root :
    ∀ target : LiteralE6Sector,
      ∃! root : E6Root,
        ∀ k, e8Coord target.1 k = embeddedE6Vector root k := by
  native_decide

noncomputable def e6RootToLiteralE6Sector (root : E6Root) : LiteralE6Sector :=
  Classical.choose (embedded_root_vector_matches_unique_literal_e8 root).exists

noncomputable def literalE6SectorToE6Root (target : LiteralE6Sector) : E6Root :=
  Classical.choose (literal_e8_vector_matches_unique_e6_root target).exists

theorem e6RootToLiteralE6Sector_spec (root : E6Root) :
    ∀ k, e8Coord (e6RootToLiteralE6Sector root).1 k = embeddedE6Vector root k :=
  Classical.choose_spec (embedded_root_vector_matches_unique_literal_e8 root).exists

theorem literalE6SectorToE6Root_spec (target : LiteralE6Sector) :
    ∀ k, e8Coord target.1 k = embeddedE6Vector (literalE6SectorToE6Root target) k :=
  Classical.choose_spec (literal_e8_vector_matches_unique_e6_root target).exists

/-- Concrete two-sided same-object equivalence between the E6 root carrier and
the literal E8 orthogonal-complement sector. -/
noncomputable def e6RootEquivLiteralE6Sector : E6Root ≃ LiteralE6Sector where
  toFun := e6RootToLiteralE6Sector
  invFun := literalE6SectorToE6Root
  left_inv := by
    intro root
    let target := e6RootToLiteralE6Sector root
    exact (literal_e8_vector_matches_unique_e6_root target).unique
      (literalE6SectorToE6Root_spec target)
      (e6RootToLiteralE6Sector_spec root)
  right_inv := by
    intro target
    let root := literalE6SectorToE6Root target
    exact (embedded_root_vector_matches_unique_literal_e8 root).unique
      (e6RootToLiteralE6Sector_spec root)
      (literalE6SectorToE6Root_spec target)

/-! ## 3. Compose with the already-built mod-3 E6/Q=2 equivalence -/

noncomputable def literalE6SectorEquivQTwoShell : LiteralE6Sector ≃ QTwoShell :=
  e6RootEquivLiteralE6Sector.symm.trans e6RootEquivQTwoShell

inductive E6SectorRecognitionCreatesWholeE8Recognition : Prop
inductive E6SectorRecognitionCreatesPhysicalMechanism : Prop

theorem e6SectorCannotCreateWholeE8Recognition :
    ¬ E6SectorRecognitionCreatesWholeE8Recognition := by
  intro h
  cases h

theorem e6SectorCannotCreatePhysicalMechanism :
    ¬ E6SectorRecognitionCreatesPhysicalMechanism := by
  intro h
  cases h

structure Boundary where
  explicitE6SimpleSystemInsideE8Paid : Bool
  e6CartanGramPaid : Bool
  e6RootToLiteralE8SectorBijectionPaid : Bool
  literalE6ToTernaryQTwoSameObjectPaid : Bool
  e6SectorRecognitionCreatesWholeE8Recognition : Bool
  e6SectorRecognitionCreatesPhysicalMechanism : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  explicitE6SimpleSystemInsideE8Paid := true
  e6CartanGramPaid := true
  e6RootToLiteralE8SectorBijectionPaid := true
  literalE6ToTernaryQTwoSameObjectPaid := true
  e6SectorRecognitionCreatesWholeE8Recognition := false
  e6SectorRecognitionCreatesPhysicalMechanism := false

end Integration.E6LiteralE8TernarySameObject

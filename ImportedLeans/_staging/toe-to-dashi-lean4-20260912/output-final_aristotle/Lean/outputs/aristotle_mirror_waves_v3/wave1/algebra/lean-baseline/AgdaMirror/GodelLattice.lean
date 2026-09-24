import Mathlib
import AgdaMirror.MonsterOntos

/-!
# Lean mirror of `Ontology/GodelLattice.agda` (the `Vec15` 15-slot carrier)

Faithful transcription of the factor-exponent vector over the 15 supersingular
primes (`Vec15`), the prime-indexed update operators (`updateField`,
`updateVec15`) with their commutation laws, and the `CoordinateLaw` contract.

In addition to a faithful mirror we equip the carrier with genuine
`map` / `zipWith` / `foldr` / `sum` structure and prove the expected functor and
aggregation laws, since `Vec15` is pervasively imported as the base coordinate of
the whole arithmetic chain.

Honesty discipline: the Agda `postulate`s (`Text`, `encode`, `factorMap`) are
rendered as explicit parameters of the `CoordinateLaw` contract, never as Lean
`axiom`s.
-/

namespace AgdaMirror.GodelLattice

open AgdaMirror.MonsterOntos
open SSP

/-- A factor-exponent vector over the 15 supersingular primes: a canonical
coordinate.  Mirrors the Agda record `Vec15`. -/
structure Vec15 (A : Type*) where
  e2  : A
  e3  : A
  e5  : A
  e7  : A
  e11 : A
  e13 : A
  e17 : A
  e19 : A
  e23 : A
  e29 : A
  e31 : A
  e41 : A
  e47 : A
  e59 : A
  e71 : A
deriving DecidableEq

/-- An exponent is a natural number. -/
abbrev Exponent : Type := Nat

/-- The factor vector: exponents over the 15 primes. -/
abbrev FactorVec : Type := Vec15 Exponent

/-- A constant vector (all slots equal). -/
def replicate {A : Type*} (x : A) : Vec15 A :=
  ⟨x, x, x, x, x, x, x, x, x, x, x, x, x, x, x⟩

/-- Functorial map over all 15 slots. -/
def map {A B : Type*} (f : A → B) (v : Vec15 A) : Vec15 B :=
  ⟨f v.e2, f v.e3, f v.e5, f v.e7, f v.e11, f v.e13, f v.e17, f v.e19,
   f v.e23, f v.e29, f v.e31, f v.e41, f v.e47, f v.e59, f v.e71⟩

/-- Pointwise binary zip over all 15 slots. -/
def zipWith {A B C : Type*} (f : A → B → C) (u : Vec15 A) (v : Vec15 B) : Vec15 C :=
  ⟨f u.e2 v.e2, f u.e3 v.e3, f u.e5 v.e5, f u.e7 v.e7, f u.e11 v.e11,
   f u.e13 v.e13, f u.e17 v.e17, f u.e19 v.e19, f u.e23 v.e23, f u.e29 v.e29,
   f u.e31 v.e31, f u.e41 v.e41, f u.e47 v.e47, f u.e59 v.e59, f u.e71 v.e71⟩

/-- Right fold over the 15 slots, in prime order. -/
def foldr {A B : Type*} (f : A → B → B) (z : B) (v : Vec15 A) : B :=
  f v.e2 (f v.e3 (f v.e5 (f v.e7 (f v.e11 (f v.e13 (f v.e17 (f v.e19
    (f v.e23 (f v.e29 (f v.e31 (f v.e41 (f v.e47 (f v.e59 (f v.e71 z))))))))))))))

/-- Sum of the 15 slots. -/
def sum (v : Vec15 Nat) : Nat :=
  v.e2 + v.e3 + v.e5 + v.e7 + v.e11 + v.e13 + v.e17 + v.e19 + v.e23 + v.e29 +
  v.e31 + v.e41 + v.e47 + v.e59 + v.e71

/-! ### Functor / aggregation laws -/

@[simp] theorem map_id {A : Type*} (v : Vec15 A) : map id v = v := by
  cases v; rfl

theorem map_comp {A B C : Type*} (f : A → B) (g : B → C) (v : Vec15 A) :
    map g (map f v) = map (g ∘ f) v := by
  cases v; rfl

@[simp] theorem map_replicate {A B : Type*} (f : A → B) (x : A) :
    map f (replicate x) = replicate (f x) := rfl

/-- `map (· + ·)` distributes the sum over `zipWith (+)`. -/
theorem sum_zipWith_add (u v : Vec15 Nat) :
    sum (zipWith (· + ·) u v) = sum u + sum v := by
  cases u; cases v; simp only [sum, zipWith]; ring

@[simp] theorem sum_replicate (x : Nat) : sum (replicate x) = 15 * x := by
  simp only [sum, replicate]; ring

theorem sum_map_succ (v : Vec15 Nat) :
    sum (map Nat.succ v) = sum v + 15 := by
  cases v; simp only [sum, map]; omega

/-! ### Prime-indexed updates -/

/-- Update a slot identified by `lane` with `f` exactly when `p = lane`. -/
def updateField {A : Type*} (p lane : SSP) (f : A → A) (x : A) : A :=
  if p = lane then f x else x

/-- Update the slot of `v` selected by prime `p` with `f`. -/
def updateVec15 {A : Type*} (p : SSP) (f : A → A) (v : Vec15 A) : Vec15 A :=
  ⟨updateField p p2 f v.e2, updateField p p3 f v.e3, updateField p p5 f v.e5,
   updateField p p7 f v.e7, updateField p p11 f v.e11, updateField p p13 f v.e13,
   updateField p p17 f v.e17, updateField p p19 f v.e19, updateField p p23 f v.e23,
   updateField p p29 f v.e29, updateField p p31 f v.e31, updateField p p41 f v.e41,
   updateField p p47 f v.e47, updateField p p59 f v.e59, updateField p p71 f v.e71⟩

/-- Updates of the same lane by commuting maps commute. -/
theorem updateField_commutes {A : Type*} (p q lane : SSP) (f g : A → A)
    (fg : ∀ x, f (g x) = g (f x)) (x : A) :
    updateField p lane f (updateField q lane g x)
      = updateField q lane g (updateField p lane f x) := by
  unfold updateField
  by_cases hp : p = lane <;> by_cases hq : q = lane <;> simp [hp, hq, fg]

/-- Prime-indexed updates with commuting maps commute on the whole vector. -/
theorem updateVec15_commutes {A : Type*} (p q : SSP) (f g : A → A)
    (fg : ∀ x, f (g x) = g (f x)) (v : Vec15 A) :
    updateVec15 p f (updateVec15 q g v)
      = updateVec15 q g (updateVec15 p f v) := by
  cases v
  simp only [updateVec15, Vec15.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact updateField_commutes p q _ f g fg _

/-! ### Gödel encoding contract

The Agda module `postulate`s an abstract `Text` type with `encode` and
`factorMap`, and bundles a `CoordinateLaw` stating factor-vector equality is a
stable identifier.  We render those postulates as parameters of the contract,
never as axioms. -/

/-- The Gödel coordinate contract: equal factor vectors give equal encodings. -/
structure CoordinateLaw (Text : Type*) (encode : Text → Nat)
    (factorMap : Text → FactorVec) : Prop where
  stable_id : ∀ t₁ t₂ : Text, factorMap t₁ = factorMap t₂ → encode t₁ = encode t₂

/-- A genuine witness: any encoding that factors through `factorMap` satisfies
the coordinate law. -/
theorem coordinateLaw_of_factorsThrough {Text : Type*} (factorMap : Text → FactorVec)
    (h : FactorVec → Nat) :
    CoordinateLaw Text (fun t => h (factorMap t)) factorMap :=
  ⟨fun _ _ heq => by rw [heq]⟩

end AgdaMirror.GodelLattice

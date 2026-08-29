import Mathlib

/-!
# Lean mirror of the join-semilattice interface in
`DASHI/Core/UniversalOperatorBasis.agda` (genuine interface + witness)

Faithful transcription of the order-theoretic surfaces used by the universal
operator basis:

* `JoinSurface A` — a join-semilattice (preorder `⊑J` plus an idempotent,
  associative, commutative join `⊔J`),
* `JoinPreserving J f` — a join-preserving, monotone endomorphism,
* `DualOrderSymmetry A` — an involutive order dual.

We give genuine *witnesses*: `Bool` with `or`/implication forms a `JoinSurface`,
the identity map preserves its joins, and boolean negation is an involutive
order dual.  No `sorry`, axiom-clean.
-/

namespace AgdaMirror.JoinLattice

universe u

/-- A join-semilattice surface (Agda `record JoinSurface`). -/
structure JoinSurface (A : Type u) where
  le : A → A → Prop
  join : A → A → A
  refl_le : ∀ a, le a a
  trans_le : ∀ a b c, le a b → le b c → le a c
  join_idem : ∀ a, join a a = a
  join_assoc : ∀ a b c, join (join a b) c = join a (join b c)
  join_comm : ∀ a b, join a b = join b a

/-- A join-preserving, monotone endomorphism (Agda `record JoinPreserving`). -/
structure JoinPreserving {A : Type u} (J : JoinSurface A) (f : A → A) where
  preserves_join : ∀ a b, f (J.join a b) = J.join (f a) (f b)
  monotone : ∀ {a b}, J.le a b → J.le (f a) (f b)

/-- An involutive order dual (Agda `record DualOrderSymmetry`). -/
structure DualOrderSymmetry (A : Type u) where
  dual : A → A
  involutive : ∀ a, dual (dual a) = a

/-- Genuine witness: `Bool` with `or` join and implication order. -/
def boolJoinSurface : JoinSurface Bool where
  le := fun a b => a = true → b = true
  join := or
  refl_le := fun _ h => h
  trans_le := fun _ _ _ hab hbc h => hbc (hab h)
  join_idem := by decide
  join_assoc := by decide
  join_comm := by decide

/-- Genuine witness: the identity map preserves the boolean joins. -/
def idJoinPreserving : JoinPreserving boolJoinSurface (id) where
  preserves_join := fun _ _ => rfl
  monotone := fun h => h

/-- Genuine witness: boolean negation is an involutive order dual. -/
def boolDualOrderSymmetry : DualOrderSymmetry Bool where
  dual := not
  involutive := by decide

end AgdaMirror.JoinLattice

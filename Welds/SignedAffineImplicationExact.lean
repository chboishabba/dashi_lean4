import Mathlib

/- Source-scoped proof rules of the signed affine implication collector.
   The original normal addition/evaluation law and numerical envelope proof
   are explicit inputs. This file is not a completeness or complexity proof. -/
namespace SignedAffineImplication

def flipBit : Bool → Bool
  | false => true
  | true => false

def xorBit : Bool → Bool → Bool
  | false, b => b
  | true, b => flipBit b

theorem oppositeBit (x b : Bool) (h : x ≠ b) : x = flipBit b := by
  cases x <;> cases b <;> simp_all [flipBit]

structure Literal (N : Type) where
  normal : N
  bit : Bool

variable {State N : Type}

def Holds (eval : N → State → Bool) (l : Literal N) (z : State) : Prop :=
  eval l.normal z = l.bit

def opposite (l : Literal N) : Literal N :=
  ⟨l.normal, flipBit l.bit⟩

def Entails (eval : N → State → Bool) (S : State → Prop) (l : Literal N) : Prop :=
  ∀ z, S z → Holds eval l z

def Excludes (eval : N → State → Bool) (S : State → Prop)
    (a b : Literal N) : Prop :=
  ∀ z, S z → Holds eval a z → Holds eval b z → False

variable {eval : N → State → Bool} {S : State → Prop} {a b : Literal N}

theorem unit (no : Excludes eval S a b) (yes : Entails eval S a) :
    Entails eval S (opposite b) := by
  intro z hz
  exact oppositeBit _ _ (fun hb => no z hz (yes z hz) hb)

theorem reverseUnit (no : Excludes eval S a b) (yes : Entails eval S b) :
    Entails eval S (opposite a) := by
  intro z hz
  exact oppositeBit _ _ (fun ha => no z hz ha (yes z hz))

def sumLiteral (add : N → N → N) (a b : Literal N) : Literal N :=
  ⟨add a.normal b.normal, xorBit a.bit b.bit⟩

theorem xorSound (add : N → N → N)
    (evalAdd : ∀ a b z, eval (add a b) z = xorBit (eval a z) (eval b z))
    (ha : Entails eval S a) (hb : Entails eval S b) :
    Entails eval S (sumLiteral add a b) := by
  intro z hz
  change eval (add a.normal b.normal) z = xorBit a.bit b.bit
  rw [evalAdd, show eval a.normal z = a.bit from ha z hz,
    show eval b.normal z = b.bit from hb z hz]

theorem refute (no : ∀ z, S z → Holds eval a z → False) :
    Entails eval S (opposite a) := by
  intro z hz
  exact oppositeBit _ _ (no z hz)

theorem conditionedFloor (weight : State → Nat) (cap lo : Nat)
    (upper : ∀ z, S z → weight z ≤ cap)
    (lower : ∀ z, S z → Holds eval a z → lo ≤ weight z)
    (strict : cap < lo) : Entails eval S (opposite a) :=
  refute (fun z hz ha => (Nat.not_lt_of_ge (Nat.le_trans (lower z hz ha) (upper z hz))) strict)

end SignedAffineImplication

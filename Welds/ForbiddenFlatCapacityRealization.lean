import Mathlib

namespace ForbiddenFlatCapacityRealization

def xorB : Bool → Bool → Bool
  | false, b => b
  | true, b => !b

def bit : Bool → Nat
  | false => 0
  | true => 1

def weight (p q : Bool) : Nat :=
  bit (!p) + bit (!q) + bit (!(xorB p q))

theorem weightExact (p q : Bool) :
    weight p q = if p = false ∧ q = false then 3 else 1 := by
  cases p <;> cases q <;> decide

theorem allowedExact (p q : Bool) :
    weight p q ≤ 1 ↔ p = true ∨ q = true := by
  cases p <;> cases q <;> decide

def nae (a b c : Bool) : Bool :=
  (xorB a b) || (xorB b c)

def splitChoice (a b : Bool) : Bool :=
  if a = b then !a else false

theorem splitForward (a b c : Bool) (h : a || b || c = true) :
    nae a b (splitChoice a b) = true ∧
      nae (!(splitChoice a b)) c false = true := by
  cases a <;> cases b <;> cases c <;> simp_all [nae, xorB, splitChoice]

theorem splitReverse (a b c t : Bool)
    (h₁ : nae a b t = true) (h₂ : nae (!t) c false = true) :
    a || b || c = true := by
  cases a <;> cases b <;> cases c <;> cases t <;>
    simp_all [nae, xorB]

end ForbiddenFlatCapacityRealization

import Welds.PNPF3SyndromeBoundaryExact

namespace PNPAffinePinReopening
open PNPF3SyndromeBoundary

-- Reuse the original Boolean lift fibre, not an ambient ternary count.
-- A forced part of the source is exactly fixed; remaining witnesses
-- are equivalent to the original witnesses, not merely equicardinal.
def Original {r : Nat} {A B : Type*}
    (l : A → Syndrome r) (q : B → Syndrome r) (t : Syndrome r)
    (valid : A → B → Prop) :=
  {p : A × B // valid p.1 p.2 ∧ l p.1+q p.2=t}

def Residual {r : Nat} {A B : Type*}
    (l : A → Syndrome r) (q : B → Syndrome r) (t : Syndrome r)
    (valid : A → B → Prop) (pin : A) :=
  {y : B // valid pin y ∧ q y=t-l pin}

def pinEquiv {r : Nat} {A B : Type*}
    (l : A → Syndrome r) (q : B → Syndrome r) (t : Syndrome r)
    (valid : A → B → Prop) (pin : A)
    (forced : ∀ x y, valid x y → l x+q y=t → x=pin) :
    Original l q t valid ≃ Residual l q t valid pin where
  toFun p := by
    obtain ⟨⟨x,y⟩,hv,he⟩ := p
    have hp := forced x y hv he
    subst x
    exact ⟨y,hv,by rw [← he]; abel⟩
  invFun y := ⟨(pin,y.val),y.property.1,by rw [y.property.2]; abel⟩
  left_inv p := by
    obtain ⟨⟨x,y⟩,hv,he⟩ := p
    have hp := forced x y hv he
    subst x
    rfl
  right_inv y := by
    cases y
    rfl

theorem pinCard {r : Nat} {A B : Type*}
    (l : A → Syndrome r) (q : B → Syndrome r) (t : Syndrome r)
    (valid : A → B → Prop) (pin : A)
    (forced : ∀ x y, valid x y → l x+q y=t → x=pin)
    [Fintype (Original l q t valid)] [Fintype (Residual l q t valid pin)] :
    Fintype.card (Original l q t valid) =
      Fintype.card (Residual l q t valid pin) :=
  Fintype.card_congr (pinEquiv l q t valid pin forced)

def embed (b : Bool) : ZMod 3 := if b then 1 else 0

theorem singleton_zero (b : Bool) (h : embed b=0) : b=false := by
  cases b <;> simp [embed] at h ⊢

theorem singleton_one (b : Bool) (h : embed b=1) : b=true := by
  cases b <;> simp [embed] at h ⊢

theorem singleton_two (b : Bool) (h : embed b=2) : False := by
  cases b <;> simp [embed] at h <;> decide

-- An actual linear combination of the original rows is a sound
-- derived equation. Row reduction still needs its complete concrete
-- trace attachment to use these premises without assumptions.
theorem derived_row {n m : Nat}
    (a : Fin m → Fin n → ZMod 3) (t : Fin m → ZMod 3)
    (c : Fin m → ZMod 3) (x : Fin n → Bool)
    (h : ∀ i, (∑ j, a i j * embed (x j))=t i) :
    (∑ j, (∑ i, c i*a i j)*embed (x j)) = ∑ i,c i*t i := by
  classical
  simp only [Finset.sum_mul,mul_assoc,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.mul_sum,h]

end PNPAffinePinReopening

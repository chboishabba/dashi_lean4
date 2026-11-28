import Mathlib
import Welds.PNPConstructiveDescentExact

namespace PNPBinarySupport

-- Actual binary observable has no label 2. The full count is encoded in
-- the otherwise unused third contrast, so seed isolation is not necessary.
def contrast (a b : ℤ) : Fin 3 → ℤ :=
  ![2*a-b,2*b-a,-(a+b)]

theorem mass_readout (a b : ℤ) :
    -(contrast a b 2)=a+b := by simp [contrast]

theorem child0_readout (a b : ℤ) :
    contrast a b 0-contrast a b 2=3*a := by
  simp [contrast]; ring

theorem child1_readout (a b : ℤ) :
    contrast a b 1-contrast a b 2=3*b := by
  simp [contrast]; ring

-- Partial interval certificates suffice. No exact counting assumption.
theorem child_bounds (a b l u l0 u0 l1 u1 : ℤ)
    (ha : 0≤a) (hb : 0≤b) (hm : l≤a+b ∧ a+b≤u)
    (h0 : l0≤2*a-b ∧ 2*a-b≤u0)
    (h1 : l1≤2*b-a ∧ 2*b-a≤u1) :
    l0+l≤3*a ∧ 3*a≤u0+u ∧ l1+l≤3*b ∧ 3*b≤u1+u := by
  omega

theorem inherited_lower (a b l u : ℤ)
    (h : l≤a+b) (hb : b≤u) : l-u≤a := by omega

theorem inherited_upper (a b l u : ℤ)
    (h : a+b≤u) (hb : l≤b) : a≤u-l := by omega

theorem empty_of_upper (a b : ℕ) (h : a+b≤0) : a=0 ∧ b=0 := by omega

theorem positive_direction_exists (a b : ℤ)
    (ha : 0≤a) (hb : 0≤b) (h : 0<a+b) :
    0<2*a-b ∨ 0<2*b-a := by omega

theorem certified_child (a b L : ℤ) (h : 0<L) (hb : L≤a) :
    0<a := by omega

-- A verified anchor plus the complement of its exact point gives a
-- clipped-support receiver. This statement uses the original carrier.
theorem anchor_complete {A : Type*} (P : A → Prop) (x : A)
    (hx : P x) (empty : ¬∃ y, P y ∧ y≠x) :
    ∀ y, P y ↔ y=x := by
  intro y
  constructor
  · intro hy
    by_contra h
    exact empty ⟨y,hy,h⟩
  · rintro rfl
    exact hx

def guarded {A : Type*} (P : A → Prop) (zero : A) (z : Bool × A) : Prop :=
  (z.1=false ∧ z.2=zero) ∨ (z.1=true ∧ P z.2)

theorem guarded_puncture {A : Type*} (P : A → Prop) (zero : A) :
    (∃ z, guarded P zero z ∧ z≠(false,zero)) ↔ ∃ x, P x := by
  constructor
  · rintro ⟨⟨s,x⟩,h,hne⟩
    rcases h with ⟨hs,hx⟩ | ⟨hs,hx⟩
    · exact False.elim (hne (Prod.ext hs hx))
    · exact ⟨x,hx⟩
  · rintro ⟨x,hx⟩
    exact ⟨(true,x),Or.inr ⟨rfl,hx⟩,by decide⟩

-- On the original Boolean carrier a unit identity hash isolates its
-- already recovered witness; not a discovery theorem.
theorem identity_isolation {n : Nat} (P : (Fin n → Bool) → Prop)
    (x : Fin n → Bool) (hx : P x) :
    ∀ y, (P y ∧ (∀ i, y i=x i)) ↔ y=x := by
  intro y
  constructor
  · intro h
    exact funext h.2
  · rintro rfl
    exact ⟨hx,fun _ => rfl⟩

-- Sufficient uniform progress is the only universal premise here.
-- It is not asserted merely from the algebraic readout above.
theorem descent {A : Type*} (I : Nat → A → Prop)
    (step : Nat → A → A) (n : Nat) (x : A)
    (root : I 0 x)
    (progress : ∀ j<n, ∀ a, I j a → I (j+1) (step j a)) :
    ∃ y, I n y := by
  induction n with
  | zero => exact ⟨x,root⟩
  | succ n ih =>
    obtain ⟨y,hy⟩ := ih (fun j hj => progress j (by omega))
    exact ⟨step n y,progress n (by omega) y hy⟩

end PNPBinarySupport

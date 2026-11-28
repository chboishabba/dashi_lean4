import Mathlib

namespace PNPLocalAutarky

abbrev Assignment (n : Nat) := Fin n → Bool
abbrev Clause (n : Nat) := List (Fin n × Bool)

def holds {n : Nat} (x : Assignment n) (c : Clause n) : Prop :=
  ∃ l ∈ c, x l.1=l.2

def touches {n : Nat} (D : Finset (Fin n)) (c : Clause n) : Prop :=
  ∃ l ∈ c, l.1 ∈ D

def models {n : Nat} (F : List (Clause n)) (x : Assignment n) : Prop :=
  ∀ c ∈ F, holds x c

def residual {n : Nat} (F : List (Clause n)) (D : Finset (Fin n))
    (x : Assignment n) : Prop := ∀ c ∈ F, ¬touches D c → holds x c

def good {n : Nat} (F : List (Clause n)) (D : Finset (Fin n))
    (p : Assignment n) : Prop :=
  ∀ c ∈ F, touches D c → ∃ l ∈ c, l.1 ∈ D ∧ p l.1=l.2

def overwrite {n : Nat} (D : Finset (Fin n)) (p x : Assignment n) :
    Assignment n := fun i => if i∈D then p i else x i

-- Every touched original clause is satisfied by the local patch;
-- all untouched clauses keep their original truth value.
theorem reopen {n : Nat} (F : List (Clause n)) (D : Finset (Fin n))
    (p x : Assignment n) (hp : good F D p) (hx : residual F D x) :
    models F (overwrite D p x) := by
  classical
  intro c hc
  by_cases h : touches D c
  · obtain ⟨l,hl,hd,he⟩ := hp c hc h
    exact ⟨l,hl,by simpa [overwrite,hd] using he⟩
  · obtain ⟨l,hl,he⟩ := hx c hc h
    have hn : l.1 ∉ D := fun hd => h ⟨l,hl,hd⟩
    exact ⟨l,hl,by simpa [overwrite,hn] using he⟩

theorem sat_bidi {n : Nat} (F : List (Clause n)) (D : Finset (Fin n))
    (p : Assignment n) (hp : good F D p) :
    (∃ x, models F x) ↔ ∃ x, residual F D x := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x,fun c hc _ => hx c hc⟩
  · rintro ⟨x,hx⟩
    exact ⟨overwrite D p x,reopen F D p x hp hx⟩

-- The only forgotten coordinates are exactly D. Keeping these bits
-- in the fibre gives an inverse of the overwrite image.
theorem overwrite_fibre_injective {n : Nat} (D : Finset (Fin n))
    (p : Assignment n) :
    Function.Injective (fun x : Assignment n =>
      (overwrite D p x,fun i : ↥D => x i)) := by
  intro x y h
  funext i
  by_cases hi : i∈D
  · exact congrFun (congrArg Prod.snd h) ⟨i,hi⟩
  · simpa [overwrite,hi] using congrFun (congrArg Prod.fst h) i

theorem mass_image_bound {n : Nat} (S : Finset (Assignment n))
    (D : Finset (Fin n)) (p : Assignment n) :
    S.card ≤ (S.image (overwrite D p)).card*2^D.card := by
  classical
  let f : ↥S → ↥(S.image (overwrite D p)) × (↥D → Bool) :=
    fun x => (⟨overwrite D p x,Finset.mem_image.mpr ⟨x,x.property,rfl⟩⟩,
      fun i => x i)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply overwrite_fibre_injective D p
    exact Prod.ext (congrArg (fun z => z.1.val) h) (congrArg Prod.snd h)
  simpa using Fintype.card_le_of_injective f hf

-- These are local sufficient certificates, not an assertion that every
-- inhabited CNF has a bounded-width autarky. No affine side constraints
-- are discarded: the executable caller admits this only on plain CNF.
end PNPLocalAutarky

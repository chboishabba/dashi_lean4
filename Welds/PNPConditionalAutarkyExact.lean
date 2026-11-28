import Mathlib
import Welds.PNPLocalAutarkyExact

namespace PNPConditionalAutarky
open PNPLocalAutarky
open scoped BigOperators

-- The external boundary is retained.  Every literal in a touched clause
-- lies in D or S.  A local solver can enumerate D × S, and for affine
-- sources its table also records the contribution of D.
def boundary {n : Nat} (F : List (Clause n)) (D S : Finset (Fin n)) : Prop :=
  ∀ c ∈ F, touches D c → ∀ l ∈ c, l.1 ∈ D ∨ l.1 ∈ S

def localOK {n : Nat} (F : List (Clause n)) (D : Finset (Fin n))
    (x : Assignment n) : Prop :=
  ∀ c ∈ F, touches D c → holds x c

def agrees {n : Nat} (S : Finset (Fin n)) (x y : Assignment n) : Prop :=
  ∀ i ∈ S, x i = y i

theorem holds_transport {n : Nat} (c : Clause n) (x y : Assignment n)
    (h : ∀ l ∈ c, x l.1=y l.1) : holds x c ↔ holds y c := by
  constructor
  · rintro ⟨l,hl,hx⟩
    exact ⟨l,hl,(h l hl).symm.trans hx⟩
  · rintro ⟨l,hl,hy⟩
    exact ⟨l,hl,(h l hl).trans hy⟩

theorem local_transport {n : Nat} (F : List (Clause n)) (D S : Finset (Fin n))
    (hb : boundary F D S) (p x y : Assignment n)
    (hxy : agrees S x y) :
    localOK F D (overwrite D p x) ↔ localOK F D (overwrite D p y) := by
  classical
  have eq (c : Clause n) (hc : c∈F) (ht : touches D c) :
      holds (overwrite D p x) c ↔ holds (overwrite D p y) c := by
    apply holds_transport
    intro l hl
    rcases hb c hc ht l hl with hD | hS
    · simp [overwrite,hD]
    · by_cases hD : l.1∈D
      · simp [overwrite,hD]
      · simpa [overwrite,hD] using hxy l.1 hS
  exact ⟨fun h c hc ht => (eq c hc ht).mp (h c hc ht),
    fun h c hc ht => (eq c hc ht).mpr (h c hc ht)⟩

theorem split_reopen {n : Nat} (F : List (Clause n)) (D : Finset (Fin n))
    (p x : Assignment n) :
    models F (overwrite D p x) ↔ residual F D x ∧ localOK F D (overwrite D p x) := by
  classical
  have untouched (c : Clause n) (ht : ¬touches D c) :
      holds (overwrite D p x) c ↔ holds x c := by
    apply holds_transport
    intro l hl
    have h : l.1∉D := fun hd => ht ⟨l,hl,hd⟩
    simp [overwrite,h]
  constructor
  · intro h
    exact ⟨fun c hc ht => (untouched c ht).mp (h c hc),
      fun c hc _ => h c hc⟩
  · rintro ⟨hR,hL⟩ c hc
    by_cases ht : touches D c
    · exact hL c hc ht
    · exact (untouched c ht).mpr (hR c hc ht)

-- Includes the affine case: the additive observation of a partial
-- assignment is preserved exactly by selecting the matching local key.
def part {n r : Nat} (A : Fin r → Fin n → ZMod 3)
    (D : Finset (Fin n)) (x : Assignment n) : Fin r → ZMod 3 :=
  fun j => ∑ i ∈ D, if x i then A j i else 0

theorem part_overwrite {n r : Nat} (A : Fin r → Fin n → ZMod 3)
    (D : Finset (Fin n)) (p x : Assignment n) :
    part A D (overwrite D p x) = part A D p := by
  classical
  funext j
  apply Finset.sum_congr rfl
  intro i hi
  simp [overwrite,hi]

theorem outside_overwrite {n r : Nat} (A : Fin r → Fin n → ZMod 3)
    (D : Finset (Fin n)) (p x : Assignment n) :
    part A (Finset.univ \ D) (overwrite D p x) =
      part A (Finset.univ \ D) x := by
  classical
  funext j
  apply Finset.sum_congr rfl
  intro i hi
  have h : i∉D := (Finset.mem_sdiff.mp hi).2
  simp [overwrite,h]

def projected {n r : Nat} (F : List (Clause n))
    (A : Fin r → Fin n → ZMod 3) (D : Finset (Fin n))
    (target : Fin r → ZMod 3) (x : Assignment n) : Prop :=
  residual F D x ∧ ∃ p, localOK F D (overwrite D p x) ∧
    part A D p + part A (Finset.univ \ D) x = target

theorem projected_exact {n r : Nat} (F : List (Clause n))
    (A : Fin r → Fin n → ZMod 3) (D : Finset (Fin n))
    (target : Fin r → ZMod 3) (x : Assignment n) :
    projected F A D target x ↔
      ∃ p, models F (overwrite D p x) ∧
        part A D (overwrite D p x) + part A (Finset.univ \ D) (overwrite D p x) = target := by
  constructor
  · rintro ⟨hr,p,hl,ha⟩
    refine ⟨p,(split_reopen F D p x).mpr ⟨hr,hl⟩,?_⟩
    simpa only [part_overwrite,outside_overwrite] using ha
  · rintro ⟨p,hm,ha⟩
    obtain ⟨hr,hl⟩ := (split_reopen F D p x).mp hm
    exact ⟨hr,p,hl,by simpa only [part_overwrite,outside_overwrite] using ha⟩

-- Branch-dependent patch: even when the patch is chosen as a function
-- of x, the only discarded information is the original D coordinate.
theorem conditional_fibre_injective {n : Nat} (D : Finset (Fin n))
    (choose : Assignment n → Assignment n) :
    Function.Injective (fun x : Assignment n =>
      (overwrite D (choose x) x,fun i : ↥D => x i)) := by
  intro x y h
  funext i
  by_cases hi : i∈D
  · exact congrFun (congrArg Prod.snd h) ⟨i,hi⟩
  · simpa [overwrite,hi] using congrFun (congrArg Prod.fst h) i

theorem conditional_mass {n : Nat} (X : Finset (Assignment n))
    (D : Finset (Fin n)) (choose : Assignment n → Assignment n) :
    X.card ≤ (X.image (fun x => overwrite D (choose x) x)).card * 2^D.card := by
  classical
  let f : ↥X → ↥(X.image (fun x => overwrite D (choose x) x)) × (↥D → Bool) :=
    fun x => (⟨overwrite D (choose x) x,Finset.mem_image.mpr ⟨x,x.property,rfl⟩⟩,
      fun i => x i)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply conditional_fibre_injective D choose
    exact Prod.ext (congrArg (fun z => z.1.val) h) (congrArg Prod.snd h)
  simpa using Fintype.card_le_of_injective f hf

end PNPConditionalAutarky

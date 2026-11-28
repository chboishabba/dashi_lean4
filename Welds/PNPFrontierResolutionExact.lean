import Welds.PNPPuncturedSupportGainBisectionExact

namespace PNPFrontierResolution
abbrev Literal (n : Nat) := Fin n × Bool
abbrev Clause (n : Nat) := Finset (Literal n)
abbrev Assignment (n : Nat) := Fin n → Bool

def flip {n : Nat} (p : Literal n) : Literal n := (p.1,!p.2)

def SatClause {n : Nat} (x : Assignment n) (c : Clause n) : Prop :=
  ∃ p ∈ c, x p.1 = p.2

def SatAll {n : Nat} (x : Assignment n) (F : List (Clause n)) : Prop :=
  ∀ c ∈ F, SatClause x c

def resolve {n : Nat} (a b : Clause n) (p : Literal n) : Clause n :=
  (a.erase p) ∪ (b.erase (flip p))

theorem resolution_sound {n : Nat} (x : Assignment n) (a b : Clause n)
    (p : Literal n) (ha : SatClause x a) (hb : SatClause x b) :
    SatClause x (resolve a b p) := by
  by_cases hp : x p.1 = p.2
  · obtain ⟨l,hl,hs⟩ := hb
    have hn : l ≠ flip p := by
      intro he
      subst l
      cases h : p.2 <;> simp [flip,h,hp] at hs
    exact ⟨l,Finset.mem_union.mpr (Or.inr (Finset.mem_erase.mpr ⟨hn,hl⟩)),hs⟩
  · obtain ⟨l,hl,hs⟩ := ha
    have hn : l ≠ p := by
      intro he
      subst l
      exact hp hs
    exact ⟨l,Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨hn,hl⟩)),hs⟩

def lookup {A : Type*} : List A → Nat → Option A
  | [],_ => none
  | a::_,0 => some a
  | _::as,k+1 => lookup as k

theorem lookup_mem {A : Type*} {xs : List A} {k : Nat} {a : A}
    (h : lookup xs k = some a) : a ∈ xs := by
  induction xs generalizing k with
  | nil => simp [lookup] at h
  | cons b bs ih =>
    cases k with
    | zero => simp [lookup] at h; simp [h]
    | succ k => exact List.mem_cons_of_mem _ (ih (by simpa [lookup] using h))

structure Receipt (n : Nat) where
  left : Nat
  right : Nat
  pivot : Literal n
  claimed : Clause n

def check {n : Nat} (D : List (Clause n)) (s : Receipt n) : Option (List (Clause n)) :=
  match lookup D s.left,lookup D s.right with
  | some a,some b =>
    if s.pivot∈a ∧ flip s.pivot∈b ∧ s.claimed=resolve a b s.pivot
    then some (D++[s.claimed]) else none
  | _,_ => none

theorem check_sound {n : Nat} {D E : List (Clause n)} (s : Receipt n)
    (h : check D s=some E) (x : Assignment n) (hd : SatAll x D) :
    SatAll x E := by
  unfold check at h
  cases ha : lookup D s.left with
  | none => simp [ha] at h
  | some a =>
    cases hb : lookup D s.right with
    | none => simp [ha,hb] at h
    | some b =>
      simp only [ha,hb] at h
      split at h
      · rename_i hv
        have he : D++[s.claimed]=E := Option.some.inj h
        subst E
        intro c hc
        rcases List.mem_append.mp hc with hc|hc
        · exact hd c hc
        · have hc' : c=s.claimed := by simpa using hc
          subst c
          rw [hv.2.2]
          exact resolution_sound x a b s.pivot (hd a (lookup_mem ha)) (hd b (lookup_mem hb))
      · simp at h

def replay {n : Nat} (D : List (Clause n)) : List (Receipt n) → Option (List (Clause n))
  | [] => some D
  | s::ss => (check D s).bind (fun E => replay E ss)

theorem replay_sound {n : Nat} {D E : List (Clause n)} (ss : List (Receipt n))
    (h : replay D ss=some E) (x : Assignment n) (hd : SatAll x D) :
    SatAll x E := by
  induction ss generalizing D with
  | nil =>
    have e : D=E := Option.some.inj h
    subst E
    exact hd
  | cons s ss ih =>
    cases hc : check D s with
    | none => simp [replay,hc] at h
    | some M =>
      exact ih (by simpa [replay,hc] using h) (check_sound s hc x hd)

theorem replay_empty_refutes {n : Nat} {D E : List (Clause n)} (ss : List (Receipt n))
    (h : replay D ss=some E) (he : ∅∈E) :
    ¬ ∃ x : Assignment n, SatAll x D := by
  rintro ⟨x,hx⟩
  obtain ⟨p,hp,_⟩ := replay_sound ss h x hx ∅ he
  simpa using hp

def block {n : Nat} (x : Assignment n) : Clause n :=
  Finset.univ.image (fun i : Fin n => (i,!x i))

theorem block_exact {n : Nat} (a x : Assignment n) :
    SatClause x (block a) ↔ x≠a := by
  rw [← PNPPuncturedSupport.block_exact]
  constructor
  · rintro ⟨p,hp,hs⟩
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hp
    subst p
    refine ⟨i,?_⟩
    intro e
    rw [e] at hs
    cases h : a i <;> simp [h] at hs
  · rintro ⟨i,hi⟩
    refine ⟨(i,!a i),Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,?_⟩
    cases ha : a i <;> cases hx : x i <;> simp_all

theorem puncture_receipt_unique {n : Nat} (F : List (Clause n))
    (a : Assignment n) (ha : SatAll a F) (ss : List (Receipt n))
    {E : List (Clause n)} (h : replay (F++[block a]) ss=some E) (he : ∅∈E) :
    ∀ x, SatAll x F → x=a := by
  intro x hx
  by_contra hn
  apply replay_empty_refutes ss h he
  refine ⟨x,?_⟩
  intro c hc
  rcases List.mem_append.mp hc with hc|hc
  · exact hx c hc
  · have hcb : c=block a := by simpa using hc
    subst c
    exact (block_exact a x).2 hn

-- Proof DAG replay is executable on finite clauses. This is soundness,
-- not a uniform bound on the size of a resolution refutation.
end PNPFrontierResolution

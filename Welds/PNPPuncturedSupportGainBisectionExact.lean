import Welds.PNPEndpointClippedOccupancyExact

namespace PNPPuncturedSupport
open PNPEndpointClippedOccupancy

-- The actual original blocking clause: one literal for each original
-- coordinate, with polarity opposite the known witness.
def block {n : Nat} (anchor x : Fin n → Bool) : Prop :=
  ∃ i, x i ≠ anchor i

theorem block_exact {n : Nat} (anchor x : Fin n → Bool) :
    block anchor x ↔ x ≠ anchor := by
  classical
  constructor
  · rintro ⟨i,hi⟩ he
    exact hi (congrFun he i)
  · intro h
    by_contra hn
    apply h
    funext i
    by_contra hi
    exact hn ⟨i,hi⟩

def Puncture {X : Type*} (sat : X → Prop) (a : X) :=
  {x : X // sat x ∧ x ≠ a}

noncomputable def splitAnchor {X : Type*} (sat : X → Prop) (a : X)
    (ha : sat a) : Option (Puncture sat a) ≃ {x : X // sat x} := by
  classical
  exact
    { toFun := fun
        | none => ⟨a,ha⟩
        | some x => ⟨x.val,x.property.1⟩
      invFun := fun x =>
        if h : x.val = a then none
        else some ⟨x.val,x.property,h⟩
      left_inv := by
        intro p
        cases p with
        | none => simp
        | some x => simp [x.property.2]
      right_inv := by
        intro x
        split
        · rename_i h
          exact Subtype.ext h.symm
        · rfl }

theorem puncture_card {X : Type*} (sat : X → Prop) (a : X) (ha : sat a)
    [Fintype (Puncture sat a)] [Fintype {x : X // sat x}] :
    Fintype.card {x : X // sat x} = 1 + Fintype.card (Puncture sat a) := by
  rw [← Fintype.card_congr (splitAnchor sat a ha),Fintype.card_option]
  omega

theorem puncture_clipped_singleton {X : Type*} (sat : X → Prop)
    (a : X) (ha : sat a)
    [Fintype (Puncture sat a)] [Fintype {x : X // sat x}] :
    clip (Fintype.card {x : X // sat x}) = 1 ↔
      Fintype.card (Puncture sat a) = 0 := by
  rw [puncture_card sat a ha,clip_singleton]
  omega

-- Only two exact existential tests are necessary for clipped occupancy.
-- The second test is a real original source, not an uncharged count oracle.
theorem puncture_witness_or_unique {X : Type*} (sat : X → Prop)
    (a : X) (ha : sat a) :
    (¬ ∃ x, sat x ∧ x ≠ a) ↔ ∀ x, sat x → x = a := by
  classical
  constructor
  · intro h x hx
    by_contra hn
    exact h ⟨x,hx,hn⟩
  · intro h ⟨x,hx,hn⟩
    exact hn (h x hx)

end PNPPuncturedSupport

namespace PNPGainBisection
-- The score is the verified success bit of one fixed clocked producer
-- on the original pin path. It need not be monotone.
def search (score : Nat → Bool) : Nat → Nat → Nat → Option Nat
  | 0, lo, hi => if hi=lo+1 then some lo else none
  | k+1, lo, hi =>
    if hi=lo+1 then some lo
    else
      let m := (lo+hi)/2
      if score m then search score k lo m else search score k m hi

theorem search_exact (score : Nat → Bool) (k lo hi : Nat)
    (hgap : lo<hi) (hbound : hi-lo ≤ 2^k)
    (hlo : score lo=false) (hhi : score hi=true) :
    ∃ i, search score k lo hi=some i ∧
      lo≤i ∧ i+1≤hi ∧ score i=false ∧ score (i+1)=true := by
  induction k generalizing lo hi with
  | zero =>
    have he : hi=lo+1 := by simp at hbound; omega
    subst hi
    exact ⟨lo,by simp [search],by omega,by omega,hlo,hhi⟩
  | succ k ih =>
    by_cases he : hi=lo+1
    · subst hi
      exact ⟨lo,by simp [search],by omega,by omega,hlo,hhi⟩
    · let m := (lo+hi)/2
      have hmid : lo<m ∧ m<hi := by dsimp [m]; omega
      rw [pow_succ] at hbound
      have hl : m-lo≤2^k := by dsimp [m]; omega
      have hr : hi-m≤2^k := by dsimp [m]; omega
      cases hm : score m with
      | false =>
        obtain ⟨i,hs,h1,h2,h3,h4⟩ := ih m hi hmid.2 hr hm hhi
        refine ⟨i,?_,by omega,h2,h3,h4⟩
        simpa [search,he,m,hm] using hs
      | true =>
        obtain ⟨i,hs,h1,h2,h3,h4⟩ := ih lo m hmid.1 hl hlo hm
        refine ⟨i,?_,h1,by omega,h3,h4⟩
        simpa [search,he,m,hm] using hs

-- The recursion uses at most k midpoint evaluations; taking k with
-- hi-lo ≤ 2^k is logarithmic. The original missed witness is still
-- required to supply the opposite endpoint scores. This is not an
-- unconditional first-gain deadline for all full program codes.
end PNPGainBisection

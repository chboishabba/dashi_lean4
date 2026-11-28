import Welds.PNPEndpointClippedOccupancyExact

namespace PNPLiveMassPartition
open PNPEndpointClippedOccupancy

-- Each original prefix is retained in its actual key fibre. The next
-- bit is independent of the representative chosen for that fibre.
def Fibre {X K : Type*} (key : X → K) (k : K) :=
  {x : X // key x = k}

def Successor {X K J : Type*} (key : X → K)
    (step : K → Bool → Option J) (j : J) :=
  {p : X × Bool // step (key p.1) p.2 = some j}

def Incoming {K J : Type*} (step : K → Bool → Option J) (j : J) :=
  {p : K × Bool // step p.1 p.2 = some j}

def successorPartition {X K J : Type*} (key : X → K)
    (step : K → Bool → Option J) (j : J) :
    Successor key step j ≃
      (Σ p : Incoming step j, Fibre key p.val.1) where
  toFun p := ⟨⟨(key p.val.1,p.val.2),p.property⟩,⟨p.val.1,rfl⟩⟩
  invFun p := ⟨(p.2.val,p.1.val.2),by rw [p.2.property]; exact p.1.property⟩
  left_inv p := by cases p; rfl
  right_inv p := by
    rcases p with ⟨⟨⟨k,b⟩,h⟩,⟨x,e⟩⟩
    subst k
    rfl

-- This is the exact multiplicity recurrence on ORIGINAL prefixes,
-- including two different bit extensions that merge into one key.
theorem successorCard {X K J : Type*} (key : X → K)
    (step : K → Bool → Option J) (j : J)
    [Fintype (Successor key step j)] [Fintype (Incoming step j)]
    [∀ p : Incoming step j, Fintype (Fibre key p.val.1)] :
    Fintype.card (Successor key step j) =
      ∑ p : Incoming step j, Fintype.card (Fibre key p.val.1) := by
  classical
  rw [Fintype.card_congr (successorPartition key step j),Fintype.card_sigma]

theorem clip_sum {I : Type*} (s : Finset I) (a : I → Nat) :
    clip (∑ i ∈ s, a i) = clip (∑ i ∈ s, clip (a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    calc
      clip (a i + ∑ j ∈ s, a j) =
          clip (clip (a i) + clip (∑ j ∈ s, a j)) := clip_add _ _
      _ = clip (clip (a i) + clip (∑ j ∈ s, clip (a j))) := by rw [ih]
      _ = clip (clip (a i) + ∑ j ∈ s, clip (a j)) := by
        rw [clip_add (clip (a i)) (∑ j ∈ s, clip (a j))]
        simp [clip, min_assoc]

theorem clippedSuccessorCard {X K J : Type*} (key : X → K)
    (step : K → Bool → Option J) (j : J)
    [Fintype (Successor key step j)] [Fintype (Incoming step j)]
    [∀ p : Incoming step j, Fintype (Fibre key p.val.1)] :
    clip (Fintype.card (Successor key step j)) =
      clip (∑ p : Incoming step j, clip (Fintype.card (Fibre key p.val.1))) := by
  rw [successorCard]
  exact clip_sum Finset.univ _

-- A concrete key transition must be shown to agree with the original
-- prefix constraints, especially last-use retirement. No assumption
-- of uniform width or complete polynomial execution is made here.
end PNPLiveMassPartition

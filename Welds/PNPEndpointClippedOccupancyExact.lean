import Welds.PNPClauseSyndromeRowOperationsExact

namespace PNPEndpointClippedOccupancy

def clip (n : Nat) : Nat := min 2 n

theorem clip_add (a b : Nat) : clip (a+b)=clip (clip a+clip b) := by
  unfold clip
  omega

theorem clip_mul (a b : Nat) : clip (a*b)=clip (clip a*clip b) := by
  rcases a with _|a
  · simp [clip]
  rcases b with _|b
  · simp [clip]
  rcases a with _|a
  · simp [clip]
  rcases b with _|b
  · simp [clip]
  have h : 2≤(a+2)*(b+2) := by positivity
  simp [clip,Nat.min_eq_left (show 2≤a+2 by omega),
    Nat.min_eq_left (show 2≤b+2 by omega),Nat.min_eq_left h]

theorem clip_zero (n : Nat) : clip n=0 ↔ n=0 := by
  unfold clip
  omega

theorem clip_singleton (n : Nat) : clip n=1 ↔ n=1 := by
  unfold clip
  omega

-- The existing guarded anchor construction at the original assignment
-- carrier. No auxiliary multiplicity is introduced.
def Guarded {X : Type*} (anchor : X) (sat : X → Prop) :=
  {p : Bool × X // (p.1=false ∧ p.2=anchor) ∨ (p.1=true ∧ sat p.2)}

def guardEquiv {X : Type*} (anchor : X) (sat : X → Prop) :
    Option {x : X // sat x} ≃ Guarded anchor sat where
  toFun
    | none => ⟨(false,anchor),Or.inl ⟨rfl,rfl⟩⟩
    | some x => ⟨(true,x.val),Or.inr ⟨rfl,x.property⟩⟩
  invFun p := by
    rcases p with ⟨⟨s,x⟩,h⟩
    cases s
    · exact none
    · exact some ⟨x,by rcases h with h|h; cases h.1; exact h.2⟩
  left_inv p := by cases p <;> rfl
  right_inv p := by
    rcases p with ⟨⟨s,x⟩,h⟩
    cases s
    · rcases h with h|h
      · have e := h.2
        subst x
        rfl
      · cases h.1
    · rfl

theorem guardCard {X : Type*} (anchor : X) (sat : X → Prop)
    [Fintype {x : X // sat x}] [Fintype (Guarded anchor sat)] :
    Fintype.card (Guarded anchor sat)=1+Fintype.card {x : X // sat x} := by
  rw [← Fintype.card_congr (guardEquiv anchor sat),Fintype.card_option]
  omega

theorem guardClippedSingleton {X : Type*} (anchor : X) (sat : X → Prop)
    [Fintype {x : X // sat x}] [Fintype (Guarded anchor sat)] :
    clip (Fintype.card (Guarded anchor sat))=1 ↔
      Fintype.card {x : X // sat x}=0 := by
  rw [guardCard,clip_singleton]
  omega

-- Local last-use rule for a natural one-cover row. All contributions
-- are nonnegative; a completed row may disappear, an overfull row
-- cannot be repaired by adding more selected columns.
theorem exactOne_retire (past future : Nat) (h : future=0) :
    past+future=1 ↔ past=1 := by omega

theorem exactOne_overfull (past future : Nat) (h : 1<past) :
    past+future≠1 := by omega

-- The live-table program must still prove all original constraint
-- contributions and disjoint multiplicity partition at each stage;
-- these endpoint and clipping identities do not supply universal
-- completion under a polynomial allowance.
end PNPEndpointClippedOccupancy

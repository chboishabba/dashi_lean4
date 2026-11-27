import Mathlib

/- Semantic seam of the scoped normal-boundary fold.
   Costs remain signed integers; hard exclusions are predicates, not finite
   penalties. The executable table generator is not kernel-certified here. -/
namespace SignedMaskedBoundary

structure Entry (State : Type) where
  witness : State
  cost : Int

def Exact (S : State → Prop) (w : State → Int) (r : Option (Entry State)) : Prop :=
  match r with
  | none => ∀ z, S z → False
  | some e => S e.witness ∧ w e.witness = e.cost ∧ ∀ z, S z → e.cost ≤ w z

variable {State : Type} {S F : State → Prop} {w : State → Int}

theorem maskedEmpty (mask : ∀ z, S z → F z)
    (h : Exact F w none) : ∀ z, S z → False :=
  fun z hz => h z (mask z hz)

theorem maskedFloor (mask : ∀ z, S z → F z) {e : Entry State}
    (h : Exact F w (some e)) (cap : Int)
    (upper : ∀ z, S z → w z ≤ cap) (strict : cap < e.cost) :
    ∀ z, S z → False := by
  intro z hz
  have lo := h.2.2 z (mask z hz)
  have hi := upper z hz
  omega

/-- Exact selection of the cheaper of two disjoint or overlapping sections. -/
def choose (a b : Option (Entry State)) : Option (Entry State) :=
  match a, b with
  | none, r => r
  | r, none => r
  | some x, some y => if x.cost ≤ y.cost then some x else some y

theorem chooseExact {P Q : State → Prop} {a b : Option (Entry State)}
    (ha : Exact P w a) (hb : Exact Q w b) :
    Exact (fun z => P z ∨ Q z) w (choose a b) := by
  cases a with
  | none =>
    cases b with
    | none =>
      intro z hz
      exact hz.elim (ha z) (hb z)
    | some y =>
      exact ⟨Or.inr hb.1, hb.2.1, fun z hz =>
        hz.elim (fun hp => False.elim (ha z hp)) (hb.2.2 z)⟩
  | some x =>
    cases b with
    | none =>
      exact ⟨Or.inl ha.1, ha.2.1, fun z hz =>
        hz.elim (ha.2.2 z) (fun hq => False.elim (hb z hq))⟩
    | some y =>
      by_cases h : x.cost ≤ y.cost
      · simpa only [choose, if_pos h, Exact] using
          (show P x.witness ∨ Q x.witness from Or.inl ha.1,
           ha.2.1, fun z (hz : P z ∨ Q z) =>
            hz.elim (ha.2.2 z) (fun hq => le_trans h (hb.2.2 z hq)))
      · have h' : y.cost ≤ x.cost := by omega
        simpa only [choose, if_neg h, Exact] using
          (show P y.witness ∨ Q y.witness from Or.inr hb.1,
           hb.2.1, fun z (hz : P z ∨ Q z) =>
            hz.elim (fun hp => le_trans h' (ha.2.2 z hp)) (hb.2.2 z))

/-- For one fixed shared label, compatible optimal child witnesses give an
    optimal parent. The caller must prove the affine gluing law, not assume
    that independently chosen witnesses agree on the whole carrier. -/
theorem joinExact {L R P : State → Prop} {wl wr : State → Int}
    {a b : Entry State} (ha : Exact L wl (some a)) (hb : Exact R wr (some b))
    (cover : ∀ z, P z → L z ∧ R z)
    (z : State) (hz : P z)
    (leftCost : wl z = a.cost) (rightCost : wr z = b.cost) :
    Exact P (fun x => wl x + wr x) (some ⟨z,a.cost+b.cost⟩) := by
  refine ⟨hz, by rw [leftCost, rightCost], ?_⟩
  intro x hx
  exact add_le_add (ha.2.2 x (cover x hx).1) (hb.2.2 x (cover x hx).2)

end SignedMaskedBoundary

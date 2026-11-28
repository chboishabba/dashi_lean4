import Welds.PNPBooleanSeparatorExact

namespace PNPSeparatorMarginals
open scoped BigOperators

-- Exact support test for the actual rational affine value, not merely
-- the support of an ambient linear relaxation.
theorem value_agreement {n d : Nat} (a : Fin n → ℚ) (B : Fin n → Fin d → ℚ)
    (u v : PNPBooleanFibre.Bits d) (j : Fin n)
    (agree : ∀ k, B j k≠0 → u k=v k) :
    PNPBooleanFibre.value a B u j=PNPBooleanFibre.value a B v j := by
  unfold PNPBooleanFibre.value
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : B j k=0
  · simp [h]
  · rw [agree k h]

-- A pulled-back factor may read several original affine coordinates.
-- Agreement on the union of their nonzero supports suffices.
theorem original_factor_agreement {n d : Nat} (a : Fin n → ℚ)
    (B : Fin n → Fin d → ℚ) (u v : PNPBooleanFibre.Bits d)
    (S : Finset (Fin n)) (P : (Fin n → ℚ) → Prop)
    (local : ∀ x y, (∀ j∈S,x j=y j) → (P x ↔ P y))
    (agree : ∀ j∈S, ∀ k, B j k≠0 → u k=v k) :
    P (PNPBooleanFibre.value a B u) ↔ P (PNPBooleanFibre.value a B v) :=
  local _ _ (fun j hj => value_agreement a B u v j (agree j hj))

-- Reverse outside-context transport. A child's context is the
-- sum of all compatible parent contexts multiplied by the other
-- private masses. Zero entries require no division.
theorem context_transport {S T : Type*} [Fintype S] [Fintype T]
    (context : S → Nat) (other : S → T → Nat) (child : T → Nat) :
    (∑ s : S, context s * (∑ t : T, other s t * child t)) =
      ∑ t : T, (∑ s : S, context s * other s t) * child t := by
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_mul]

-- Positive exact masses admit division by the child factor, as used
-- in the implementation. This is not valid for clipped counts.
theorem positive_context_divide (context other child : Nat) (h : 0<child) :
    (context*other*child)/child=context*other := by
  exact Nat.mul_div_cancel _ h

-- Partition original assignments by the original Boolean readout.
def AtBit {X : Type*} (read : X → Bool) (b : Bool) :=
  {x : X // read x=b}

def bitPartition {X : Type*} (read : X → Bool) :
    X ≃ (Σ b : Bool, AtBit read b) where
  toFun x := ⟨read x,⟨x,rfl⟩⟩
  invFun p := p.2.val
  left_inv x := rfl
  right_inv p := by
    rcases p with ⟨b,⟨x,h⟩⟩
    subst b
    rfl

theorem bitCard {X : Type*} (read : X → Bool) [Fintype X]
    [∀ b : Bool, Fintype (AtBit read b)] :
    Fintype.card X = Fintype.card (AtBit read false)+Fintype.card (AtBit read true) := by
  rw [Fintype.card_congr (bitPartition read),Fintype.card_sigma]
  simp [add_comm]

-- The same equivalence used for original witness reopening transports
-- every marginal. It is not enough to know only the total cardinality.
def marginalEquiv {X Y : Type*} (e : X ≃ Y) (readX : X → Bool)
    (readY : Y → Bool) (h : ∀ x,readY (e x)=readX x) (b : Bool) :
    AtBit readX b ≃ AtBit readY b where
  toFun x := ⟨e x.val,(h x.val).trans x.property⟩
  invFun y := ⟨e.symm y.val,by
    rw [← h (e.symm y.val),e.apply_symm_apply]
    exact y.property⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.val

theorem marginalCard {X Y : Type*} (e : X ≃ Y) (readX : X → Bool)
    (readY : Y → Bool) (h : ∀ x,readY (e x)=readX x) (b : Bool)
    [Fintype (AtBit readX b)] [Fintype (AtBit readY b)] :
    Fintype.card (AtBit readX b)=Fintype.card (AtBit readY b) :=
  Fintype.card_congr (marginalEquiv e readX readY h b)

-- Exact child masses suffice to choose a nonempty child on the
-- bounded-width class, independently of any signed estimate.
theorem larger_child_positive (a b : Nat) (inhabited : 0<a+b) :
    0 < (if a≥b then a else b) := by split <;> omega

end PNPSeparatorMarginals

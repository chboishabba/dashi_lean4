import Welds.PNPIncidenceLineExact
import Welds.PNPLiveMassPartitionExact
import Welds.PNPResidualGeometryBridgeExact

namespace PNPBooleanFibre
open PNPOriginalModularIncidence
open scoped BigOperators

abbrev Bits (n : Nat) := Fin n → Bool

def value {n d : Nat} (a : Fin n → ℚ) (B : Fin n → Fin d → ℚ)
    (u : Bits d) (j : Fin n) : ℚ :=
  a j + ∑ k, B j k * emb ℚ (u k)

def decode {n d : Nat} (a : Fin n → ℚ) (B : Fin n → Fin d → ℚ)
    (u : Bits d) : Bits n := fun j => decide (value a B u j=1)

def Valid {n d : Nat} (F : Bits n → Prop)
    (a : Fin n → ℚ) (B : Fin n → Fin d → ℚ) (u : Bits d) : Prop :=
  (∀ j, value a B u j=0 ∨ value a B u j=1) ∧ F (decode a B u)

theorem decode_emb {n d : Nat} (a : Fin n → ℚ) (B : Fin n → Fin d → ℚ)
    (u : Bits d) (j : Fin n) (h : value a B u j=0 ∨ value a B u j=1) :
    emb ℚ (decode a B u j)=value a B u j := by
  rcases h with h|h <;> simp [decode,emb,h]

theorem emb_injective : Function.Injective (emb ℚ) := by
  intro x y h
  cases x <;> cases y <;> simp [emb] at h ⊢

-- Derived rational rows determine all original coordinates.
-- Free-coordinate rows are actual coordinate identities, not an
-- arbitrary projected basis of the ambient lattice.
def originalEquiv {n d : Nat} (F : Bits n → Prop)
    (free : Fin d → Fin n) (a : Fin n → ℚ) (B : Fin n → Fin d → ℚ)
    (derived : ∀ x, F x → ∀ j,
      emb ℚ (x j)=value a B (fun k => x (free k)) j)
    (freeExact : ∀ u k, value a B u (free k)=emb ℚ (u k)) :
    {x : Bits n // F x} ≃ {u : Bits d // Valid F a B u} where
  toFun x := by
    let u : Bits d := fun k => x.val (free k)
    have h : ∀ j, value a B u j=emb ℚ (x.val j) :=
      fun j => (derived x.val x.property j).symm
    have e : decode a B u=x.val := by
      funext j
      cases hj : x.val j <;> simp [decode,h j,emb,hj]
    refine ⟨u,⟨fun j => ?_,by rw [e]; exact x.property⟩⟩
    rw [h j]
    cases hj : x.val j <;> simp [emb,hj]
  invFun u := ⟨decode a B u.val,u.property.2⟩
  left_inv x := by
    apply Subtype.ext
    funext j
    have h := derived x.val x.property j
    cases hj : x.val j <;> simp [decode,← h,emb,hj]
  right_inv u := by
    apply Subtype.ext
    funext k
    apply emb_injective
    exact (decode_emb a B u.val (free k) (u.property.1 (free k))).trans
      (freeExact u.val k)

-- Once a checked chart is supplied, every original Boolean solution
-- is represented in a carrier with exactly 2^d assignments.
theorem candidate_count (d : Nat) : Fintype.card (Bits d)=2^d := by
  simp [Bits,Fintype.card_fun]

-- The global assignment is a product of disjoint local assignments.
-- This equivalence requires the actual pulled-back constraints to
-- factor; overlapping face feasibility alone is insufficient.
def componentEquiv {I : Type*} {X : I → Type*}
    (P : ∀ i, X i → Prop) :
    {u : ∀ i, X i // ∀ i, P i (u i)} ≃ (∀ i, {x : X i // P i x}) where
  toFun u i := ⟨u.val i,u.property i⟩
  invFun u := ⟨fun i => (u i).val,fun i => (u i).property⟩
  left_inv u := by cases u; rfl
  right_inv u := by funext i; apply Subtype.ext; rfl

theorem componentCard {I : Type*} [Fintype I] {X : I → Type*}
    (P : ∀ i, X i → Prop)
    [Fintype {u : ∀ i, X i // ∀ i, P i (u i)}]
    [∀ i, Fintype {x : X i // P i x}] :
    Fintype.card {u : ∀ i, X i // ∀ i, P i (u i)} =
      ∏ i, Fintype.card {x : X i // P i x} := by
  rw [Fintype.card_congr (componentEquiv P),Fintype.card_pi]

-- For each explicit component d_i, at most 2^d_i points are
-- enumerated. The joint count is a product, not a sum, but local
-- enumeration work is a sum. A bound d_i <= w gives this inequality.
theorem local_point_bound {I : Type*} [Fintype I] (d : I → Nat) (w : Nat)
    (hw : ∀ i, d i≤w) : (∑ i,2^(d i))≤Fintype.card I*2^w := by
  calc
    (∑ i,2^(d i)) ≤ ∑ _i : I,2^w := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.pow_le_pow_right (by omega) (hw i)
    _ = _ := by simp

-- Barrier: any distinct points in a fixed lossy original observation
-- already give a coordinate-projection consumer that does not descend.
-- Projection is a zero-gate consumer; this obstruction is not useful
-- against arbitrary polynomial circuits.
theorem lossy_coordinate_non_descent {n : Nat} {K : Type*}
    (key : Bits n → K) (x y : Bits n) (same : key x=key y) (different : x≠y) :
    ∃ i : Fin n, ¬ ∃ f : Set.range key → Bool,
      ∀ z, f ⟨key z,⟨z,rfl⟩⟩=z i := by
  classical
  have h : ∃ i, x i≠y i := by
    by_contra hn
    push_neg at hn
    exact different (funext hn)
  obtain ⟨i,hi⟩ := h
  refine ⟨i,fun hf => hi ?_⟩
  exact (PNPResidualGeometryBridge.consumer_factor_iff key (fun z => z i)).2 hf x y same

end PNPBooleanFibre

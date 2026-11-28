import Mathlib

/- Aggregate arithmetic for the existing shared Tseitin threshold producer.
   The recurrence here is its Boolean specification, not a clocked evaluator:
   sharing/memoization is supplied by the concrete DAG builder. -/
namespace PNPAggregateExcess

def bitCount : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + bitCount bs

def threshold : List Bool → Nat → Bool
  | _, 0 => true
  | [], _ + 1 => false
  | b :: bs, k + 1 => threshold bs (k + 1) || (b && threshold bs k)

theorem threshold_true (bs : List Bool) (k : Nat) :
    threshold bs k = true ↔ k ≤ bitCount bs := by
  induction bs generalizing k with
  | nil => cases k <;> simp [threshold, bitCount]
  | cons b bs ih =>
    cases k with
    | zero => simp [threshold]
    | succ k =>
      cases b <;> simp [threshold, bitCount, ih] <;> omega

theorem bitCount_le_length (bs : List Bool) : bitCount bs ≤ bs.length := by
  induction bs with
  | nil => simp [bitCount]
  | cons b bs ih =>
    cases b <;> simp [bitCount] <;> omega

theorem bitCount_append (a b : List Bool) :
    bitCount (a ++ b) = bitCount a + bitCount b := by
  induction a with
  | nil => simp [bitCount]
  | cons x xs ih => simp [bitCount, ih, Nat.add_assoc]

-- cap+1, cap+2, ..., cap+fuel, retaining every indexed threshold.
def slice (bs : List Bool) (cap : Nat) : Nat → List Bool
  | 0 => []
  | f+1 => threshold bs (cap+1) :: slice bs (cap+1) f

theorem slice_count (bs : List Bool) (cap fuel : Nat) :
    bitCount (slice bs cap fuel) = min fuel (bitCount bs - cap) := by
  induction fuel generalizing cap with
  | zero => simp [slice, bitCount]
  | succ f ih =>
    rw [slice, bitCount, ih]
    by_cases h : threshold bs (cap+1) = true
    · have h' := (threshold_true bs (cap+1)).mp h
      simp only [h, if_true]
      omega
    · have h' : ¬ cap+1 ≤ bitCount bs := fun hc => h ((threshold_true bs (cap+1)).mpr hc)
      simp only [h, if_false, Nat.zero_add]
      omega

def rowBits (r : List Bool × Nat) : List Bool :=
  slice r.1 r.2 (r.1.length-r.2)

theorem row_count (r : List Bool × Nat) :
    bitCount (rowBits r) = bitCount r.1 - r.2 := by
  unfold rowBits
  rw [slice_count, min_eq_right]
  exact Nat.sub_le_sub_right (bitCount_le_length r.1) r.2

def aggregateBits : List (List Bool × Nat) → List Bool
  | [] => []
  | r :: rs => rowBits r ++ aggregateBits rs

def excess : List (List Bool × Nat) → Nat
  | [] => 0
  | r :: rs => (bitCount r.1 - r.2) + excess rs

theorem aggregate_count (rs : List (List Bool × Nat)) :
    bitCount (aggregateBits rs) = excess rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [aggregateBits, excess, bitCount_append, row_count, ih]

def accept (rs : List (List Bool × Nat)) (ceiling : Nat) : Bool :=
  !(threshold (aggregateBits rs) (ceiling+1))

theorem accept_exact (rs : List (List Bool × Nat)) (ceiling : Nat) :
    accept rs ceiling = true ↔ excess rs ≤ ceiling := by
  have h := threshold_true (aggregateBits rs) (ceiling+1)
  rw [aggregate_count] at h
  unfold accept
  cases ht : threshold (aggregateBits rs) (ceiling+1) <;>
    simp_all <;> omega

-- Zero and strict improvement use the same original potential, not a
-- successor-relative residual or an auxiliary gate count.
theorem strict_demand (rs : List (List Bool × Nat)) (incumbent : Nat)
    (positive : 0 < incumbent) :
    accept rs (incumbent-1) = true ↔ excess rs < incumbent := by
  rw [accept_exact]
  omega

-- Reverse reduction: a known hard-feasible incumbent does not make the
-- improvement query easier in the unrestricted source family.
-- The three-bit odd row [true,selector,selector] uses distinct physical
-- columns for the last two entries, equated by the affine demand.
def switchRow (s : Bool) : List (List Bool × Nat) := [([true,s,s],1)]

theorem switch_excess (s : Bool) :
    excess (switchRow s) = if s then 2 else 0 := by
  cases s <;> decide

def hard (F : X → Prop) (s : Bool) (x : X) : Prop := s = true ∨ F x

theorem known_incumbent (F : X → Prop) (x : X) :
    hard F true x ∧ excess (switchRow true) = 2 := by
  exact ⟨Or.inl rfl, rfl⟩

theorem improvement_iff_original (F : X → Prop) :
    (∃ s x, hard F s x ∧ excess (switchRow s) < 2) ↔ ∃ x, F x := by
  constructor
  · rintro ⟨s,x,h,hlt⟩
    cases s with
    | false => exact ⟨x, by simpa [hard] using h⟩
    | true => rw [switch_excess] at hlt; simp at hlt
  · rintro ⟨x,h⟩
    exact ⟨false,x,Or.inr h,by decide⟩

-- An UNKNOWN exit is not an exclusion. A supplied exact productive step
-- yields a bounded finite descent, without claiming affordable discovery.
theorem finite_zero_of_progress {X : Type} (P : X → Prop) (cost : X → Nat)
    (advance : ∀ x, P x → 0 < cost x → ∃ y, P y ∧ cost y < cost x)
    (x : X) (hx : P x) : ∃ y, P y ∧ cost y = 0 := by
  have aux : ∀ k x, cost x ≤ k → P x → ∃ y, P y ∧ cost y = 0 := by
    intro k
    induction k with
    | zero =>
      intro x h hx
      exact ⟨x,hx,by omega⟩
    | succ k ih =>
      intro x h hx
      by_cases z : cost x = 0
      · exact ⟨x,hx,z⟩
      · obtain ⟨y,hy,lt⟩ := advance x hx (by omega)
        exact ih y (by omega) hy
  exact aux (cost x) x le_rfl hx

end PNPAggregateExcess

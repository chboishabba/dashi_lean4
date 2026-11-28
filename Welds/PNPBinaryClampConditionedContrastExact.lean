import Mathlib

/- Native arithmetic behind the actual aggregate ceiling and signed
   contrast producers. No oracle for source capacities or model counts. -/
namespace PNPBinaryClampConditionedContrast

def digit (b : Bool) : Nat := if b then 1 else 0

def decodeFrom (s : Nat) : List Bool → Nat
  | [] => s
  | b :: bs => decodeFrom (2*s+digit b) bs

def saturatedFrom (M s : Nat) : List Bool → Nat
  | [] => s
  | b :: bs => saturatedFrom M (min M (2*s+digit b)) bs

theorem saturated_step (M x : Nat) (b : Bool) :
    min M (2*min M x+digit b) = min M (2*x+digit b) := by
  by_cases h : x ≤ M
  · rw [min_eq_right h]
  · have hm : M ≤ x := by omega
    rw [min_eq_left hm]
    have h1 : M ≤ 2*M+digit b := by omega
    have h2 : M ≤ 2*x+digit b := by omega
    rw [min_eq_left h1, min_eq_left h2]

theorem saturatedFrom_exact (M s : Nat) (bs : List Bool) :
    saturatedFrom M (min M s) bs = min M (decodeFrom s bs) := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    simp only [saturatedFrom, decodeFrom]
    rw [saturated_step]
    exact ih (2*s+digit b)

def decodeBits (bs : List Bool) : Nat := decodeFrom 0 bs

def saturatedBits (M : Nat) (bs : List Bool) : Nat :=
  saturatedFrom M 0 bs

theorem saturatedBits_exact (M : Nat) (bs : List Bool) :
    saturatedBits M bs = min M (decodeBits bs) := by
  simpa [saturatedBits, decodeBits] using saturatedFrom_exact M 0 bs

theorem saturatedBits_bound (M : Nat) (bs : List Bool) :
    saturatedBits M bs ≤ M := by
  rw [saturatedBits_exact]
  exact min_le_left _ _

theorem ceiling_equiv (M v : Nat) (bs : List Bool) (h : v ≤ M) :
    v ≤ saturatedBits M bs ↔ v ≤ decodeBits bs := by
  rw [saturatedBits_exact, le_min_iff]
  exact ⟨fun a => a.2, fun a => ⟨h,a⟩⟩

/- p and q are the actual counts of a selected trit and its complement.
   C is a certified common capacity; Cp and Cq are source-conditioned
   capacities (Cq may be the sum of the other two trit capacities).
   Both masses and their signs are retained until the final contrast. -/
theorem conditioned_contrast (p q C Cp Cq : Nat)
    (total : p+q ≤ C) (hp : p ≤ Cp) (hq : q ≤ Cq) (w : ℚ) :
    let P : ℚ := (min C Cp : Nat)
    let Q : ℚ := (min C Cq : Nat)
    min (-w*Q) (w*(2*P)) ≤ w*(2*(p:ℚ)-(q:ℚ)) ∧
    w*(2*(p:ℚ)-(q:ℚ)) ≤ max (-w*Q) (w*(2*P)) := by
  dsimp
  have hp' : p ≤ min C Cp := le_min (by omega) hp
  have hq' : q ≤ min C Cq := le_min (by omega) hq
  have hpR : (p:ℚ) ≤ ((min C Cp : Nat):ℚ) := by exact_mod_cast hp'
  have hqR : (q:ℚ) ≤ ((min C Cq : Nat):ℚ) := by exact_mod_cast hq'
  have hp0 : 0 ≤ (p:ℚ) := by positivity
  have hq0 : 0 ≤ (q:ℚ) := by positivity
  have lo : -((min C Cq : Nat):ℚ) ≤ 2*(p:ℚ)-(q:ℚ) := by linarith
  have hi : 2*(p:ℚ)-(q:ℚ) ≤ 2*((min C Cp : Nat):ℚ) := by linarith
  by_cases hw : 0 ≤ w
  · constructor
    · calc
        _ ≤ -w * ((min C Cq : Nat):ℚ) := min_le_left _ _
        _ = w * (-((min C Cq : Nat):ℚ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left lo hw
    · exact le_trans (mul_le_mul_of_nonneg_left hi hw) (le_max_right _ _)
  · have hw' : w ≤ 0 := le_of_not_ge hw
    constructor
    · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hi hw')
    · calc
        _ ≤ w * (-((min C Cq : Nat):ℚ)) := mul_le_mul_of_nonpos_left lo hw'
        _ = -w * ((min C Cq : Nat):ℚ) := by ring
        _ ≤ _ := le_max_left _ _

end PNPBinaryClampConditionedContrast

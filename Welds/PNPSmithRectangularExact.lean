import Welds.PNPSmithCertificateExact

namespace PNPSmithRectangular
open scoped BigOperators

-- Rectangular diagonal row map. Zero rows have no pivot; any present
-- pivot belongs to only one row. Zero diagonal coefficients are allowed.
def diagonal {I J : Type*} (pivot : I → Option J) (d : I → ℤ)
    (z : J → ℤ) (i : I) : ℤ :=
  match pivot i with
  | none => 0
  | some j => d i*z j

def Condition {I J : Type*} (pivot : I → Option J)
    (d c : I → ℤ) (i : I) : Prop :=
  match pivot i with
  | none => c i=0
  | some _ => d i ∣ c i

theorem diagonal_iff {I J : Type*} (pivot : I → Option J) (d c : I → ℤ)
    (injective : ∀ i i' j, pivot i=some j → pivot i'=some j → i=i') :
    (∃ z : J → ℤ, ∀ i, diagonal pivot d z i=c i) ↔
      ∀ i, Condition pivot d c i := by
  classical
  constructor
  · rintro ⟨z,h⟩ i
    cases hp : pivot i with
    | none => simpa [Condition,diagonal,hp] using (h i).symm
    | some j => exact by
        simp only [Condition,hp]
        exact ⟨z j,by simpa [diagonal,hp] using (h i).symm⟩
  · intro h
    have hval : ∀ i, ∃ v : ℤ, match pivot i with
        | none => c i=0
        | some _ => d i*v=c i := by
      intro i
      have hi := h i
      cases hp : pivot i with
      | none => exact ⟨0,by simpa [Condition,hp] using hi⟩
      | some j =>
        simp only [Condition,hp] at hi
        obtain ⟨v,hv⟩ := hi
        exact ⟨v,hv.symm⟩
    choose g hg using hval
    let z : J → ℤ := fun j =>
      if p : ∃ i, pivot i=some j then g (Classical.choose p) else 0
    refine ⟨z,fun i => ?_⟩
    have hi := hg i
    cases hp : pivot i with
    | none =>
      have hc : c i=0 := by simpa [hp] using hi
      simpa [diagonal,hp] using hc.symm
    | some j =>
      have he : ∃ i, pivot i=some j := ⟨i,hp⟩
      have eq : Classical.choose he=i :=
        injective _ i j (Classical.choose_spec he) hp
      simpa [diagonal,hp,z,he,eq] using hi

theorem membership {I J : Type*}
    (A : (J → ℤ) → (I → ℤ))
    (U : (I → ℤ) ≃ (I → ℤ)) (V : (J → ℤ) ≃ (J → ℤ))
    (pivot : I → Option J) (d b : I → ℤ)
    (injective : ∀ i i' j, pivot i=some j → pivot i'=some j → i=i')
    (smith : ∀ z i, U (A (V z)) i=diagonal pivot d z i) :
    (∃ x, A x=b) ↔ ∀ i, Condition pivot d (U b) i := by
  rw [← diagonal_iff pivot d (U b) injective]
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨V.symm x,fun i => ?_⟩
    rw [← smith,V.apply_symm_apply,hx]
  · rintro ⟨z,hz⟩
    refine ⟨V z,U.injective ?_⟩
    funext i
    rw [smith,hz]

-- A row-character certificate with integer denominator d (including
-- d=0 for an exact zero row). The column divisibility check is local.
theorem divisor_refutes {m n : Nat}
    (A : Fin m → Fin n → ℤ) (b y : Fin m → ℤ) (d : ℤ)
    (cols : ∀ j, d ∣ ∑ i,y i*A i j)
    (bad : ¬ d ∣ ∑ i,y i*b i) :
    ¬ ∃ x : Fin n → ℤ, ∀ i, (∑ j,A i j*x j)=b i := by
  rintro ⟨x,hx⟩
  choose k hk using cols
  apply bad
  refine ⟨∑ j,k j*x j,?_⟩
  calc
    (∑ i,y i*b i) = ∑ i,y i*(∑ j,A i j*x j) := by simp_rw [hx]
    _ = ∑ i,∑ j,y i*A i j*x j := by simp [Finset.mul_sum,mul_assoc]
    _ = ∑ j,∑ i,y i*A i j*x j := Finset.sum_comm
    _ = ∑ j,(∑ i,y i*A i j)*x j := by simp [Finset.sum_mul]
    _ = d*(∑ j,k j*x j) := by simp [hk,Finset.mul_sum,mul_assoc]

-- The actual Smith row action proves each column divisible, by
-- applying it to the original standard basis. No ambient rank bound.
theorem row_action_divides {m n : Nat}
    (A : Fin m → Fin n → ℤ) (y : Fin m → ℤ) (d : ℤ)
    (coord : (Fin n → ℤ) → ℤ)
    (rowAction : ∀ x, (∑ i,y i*(∑ j,A i j*x j))=d*coord x) :
    ∀ j, d ∣ ∑ i,y i*A i j := by
  classical
  intro j
  let e : Fin n → ℤ := fun k => if k=j then 1 else 0
  refine ⟨coord e,?_⟩
  simpa [e,Finset.mul_ite] using rowAction e

-- With a checked U row and V inverse coordinate action, this is the
-- original integer infeasibility receiver, including an unmatched
-- zero row. For nonzero d the rational character is y/d; for d=0
-- use y/(|y·b|+1). Actual rational certificates are replayed in Python.
theorem bad_smith_row {m n : Nat}
    (A : Fin m → Fin n → ℤ) (b y : Fin m → ℤ) (d : ℤ)
    (coord : (Fin n → ℤ) → ℤ)
    (rowAction : ∀ x, (∑ i,y i*(∑ j,A i j*x j))=d*coord x)
    (bad : ¬ d ∣ ∑ i,y i*b i) :
    ¬ ∃ x : Fin n → ℤ, ∀ i, (∑ j,A i j*x j)=b i :=
  divisor_refutes A b y d (row_action_divides A y d coord rowAction) bad

end PNPSmithRectangular

import Welds.PNPOriginalModularIncidenceExact

namespace PNPSmithCertificate
open scoped BigOperators

-- Supplied Smith multipliers (integer equivalences), on a square
-- padded carrier. Rectangular executable certificates use m×n directly.
-- Existence and polynomial construction of Smith form are classical;
-- this receiver does not assume the SymPy algorithm has a paid clock.
theorem diagonal_iff {I : Type*} (d c : I → ℤ) :
    (∃ z : I → ℤ, ∀ i, d i * z i = c i) ↔ ∀ i, d i ∣ c i := by
  constructor
  · rintro ⟨z,h⟩ i
    exact ⟨z i,(h i).symm⟩
  · intro h
    choose z hz using h
    exact ⟨z,fun i => (hz i).symm⟩

theorem smith_membership {I : Type*}
    (A : (I → ℤ) → (I → ℤ))
    (U V : (I → ℤ) ≃ (I → ℤ)) (d b : I → ℤ)
    (smith : ∀ z i, U (A (V z)) i = d i * z i) :
    (∃ x, A x=b) ↔ ∀ i, d i ∣ U b i := by
  rw [← diagonal_iff]
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨V.symm x,fun i => ?_⟩
    rw [← smith, V.apply_symm_apply, hx]
  · rintro ⟨z,hz⟩
    refine ⟨V z,U.injective ?_⟩
    funext i
    rw [smith,hz]

theorem bad_coordinate_refutes {I : Type*}
    (A : (I → ℤ) → (I → ℤ))
    (U V : (I → ℤ) ≃ (I → ℤ)) (d b : I → ℤ)
    (smith : ∀ z i, U (A (V z)) i = d i * z i)
    (i : I) (bad : ¬ d i ∣ U b i) : ¬ ∃ x, A x=b := by
  intro h
  exact bad ((smith_membership A U V d b smith).1 h i)

-- Exact parameterization in Smith coordinates: all nonzero
-- diagonal coordinates are fixed, all zero coordinates are free.
theorem diagonal_fibre {I : Type*} (d c z0 z : I → ℤ)
    (h0 : ∀ i, d i*z0 i=c i) :
    (∀ i, d i*z i=c i) ↔ ∀ i, d i≠0 → z i=z0 i := by
  constructor
  · intro h i hi
    have he : d i*(z i-z0 i)=0 := by rw [mul_sub,h,h0,sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hi)
  · intro h i
    by_cases hi : d i=0
    · simpa [hi] using h0 i
    · rw [h i hi,h0]

-- Rational integer-Farkas certificate soundness, with an explicit
-- integer column character. This is independent of the Smith producer.
theorem integer_character_refutes {m n : Nat}
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (y : Fin m → ℚ) (k : Fin n → ℤ)
    (cols : ∀ j, (∑ i,y i*(A i j : ℚ))=(k j : ℚ))
    (nonint : ∀ z : ℤ, (∑ i,y i*(b i : ℚ))≠(z : ℚ)) :
    ¬ ∃ x : Fin n → ℤ, ∀ i, (∑ j,A i j*x j)=b i := by
  rintro ⟨x,hx⟩
  apply nonint (∑ j,k j*x j)
  have hq : ∀ i, (∑ j,(A i j : ℚ)*(x j : ℚ))=(b i : ℚ) := by
    intro i
    exact_mod_cast hx i
  calc
    (∑ i,y i*(b i : ℚ)) = ∑ i,y i*(∑ j,(A i j : ℚ)*(x j : ℚ)) := by simp_rw [hq]
    _ = ∑ i,∑ j,y i*(A i j : ℚ)*(x j : ℚ) := by simp [Finset.mul_sum,mul_assoc]
    _ = ∑ j,∑ i,y i*(A i j : ℚ)*(x j : ℚ) := Finset.sum_comm
    _ = ∑ j,(∑ i,y i*(A i j : ℚ))*(x j : ℚ) := by simp [Finset.sum_mul]
    _ = ((∑ j,k j*x j : ℤ) : ℚ) := by simp [cols]

-- The receiver for a verified rectangular multiplier matrix and the
-- complete rational covector extraction from its bad row are still
-- native receipt attachments, not claimed checked by this file.
end PNPSmithCertificate

import Synthesis.MillenniumHodgeDicksonGenericSignedFibreExact

/-!
Actual signed Q0 root fibre, finite orientation pairing. On a punctured
address d, the 64 deck sign choices split into two product fibres.
The full product character separates them; all proper monomials in
distinct derivative coordinates have zero signed pairing. This is
a fibre trace, NOT a primitive Chow cycle-class pairing.
-/
namespace DASHI.Hodge.DicksonCoupled
open scoped BigOperators
noncomputable section

abbrev Mask := Address → Bool

def signZ (b : Bool) : ℤ := if b then -1 else 1
def signChar (b : Mask) : ℤ := ∏ i,signZ (b i)
def signMonomial (s : Finset Address) (b : Mask) : ℤ :=
  ∏ i ∈ s,signZ (b i)

/-- Closed finite sign calculation on all 64 support masks and all
64 deck choices, without identifying full orientation with a count. -/
set_option maxHeartbeats 3000000 in
theorem sign_character_orthogonality :
    ∀ s : Finset Address,
      (∑ b : Mask,signChar b*signMonomial s b)=
        if s=Finset.univ then 64 else 0 := by
  decide

variable {F : Type*} [Field F] [CharZero F]

def changedDerivative (d : Address → F) (b : Mask) : Address → F :=
  fun i => (signZ (b i):F)*d i

theorem changedDerivative_sq (d : Address → F) (b : Mask) (i : Address) :
    (changedDerivative d b i)^2=(d i)^2 := by
  unfold changedDerivative
  cases hb : b i <;> simp [signZ,hb] <;> ring

theorem changedDerivative_product (d : Address → F) (b : Mask) :
    (∏ i,changedDerivative d b i)=(signChar b:F)*(∏ i,d i) := by
  unfold changedDerivative signChar
  rw [Finset.prod_mul_distrib]
  push_cast
  rfl

/-- Pull the actual root coordinate back by the existing inverse
chart. Each sign choice still solves the original Q0 equation. -/
def changedRoot (a : Address → F) (d : Address → F) (b : Mask) : Address → F :=
  fun i => inverseField (a i) (changedDerivative d b i)

theorem changedRoot_equation (a y d : Address → F)
    (h : ∀ i,d i^2=deltaField (a i) (y i)) (b : Mask) (i : Address) :
    Q0Field (a i) (changedRoot a d b i)=y i+(a i)^7/y i := by
  apply (field_root_iff _ _ _).mpr
  rw [changedRoot,dField_inverse,changedDerivative_sq,h]

theorem changedRoot_orientation (a d : Address → F) (b : Mask) :
    (∏ i,dField (a i) (changedRoot a d b i))=
      (signChar b:F)*(∏ i,d i) := by
  simp only [changedRoot,dField_inverse]
  exact changedDerivative_product d b

/-- The signed pairing of the ACTUAL derivative-coordinate monomial
on the original Q0 lift. This is the full deck trace, not an arbitrary
SO6-invariant coefficient or a cohomology class. -/
def actualOrientationTrace (a d : Address → F) (s : Finset Address) : F :=
  ∑ b : Mask,(signChar b:F)*
    (∏ i ∈ s,dField (a i) (changedRoot a d b i))

theorem actualOrientationTrace_eq (a d : Address → F) (s : Finset Address) :
    actualOrientationTrace a d s =
      (if s=Finset.univ then (64:F) else 0)*(∏ i ∈ s,d i) := by
  classical
  unfold actualOrientationTrace
  simp only [changedRoot,dField_inverse,changedDerivative,Finset.prod_mul_distrib]
  have he (b : Mask) :
      (∏ i ∈ s,(signZ (b i):F))=(signMonomial s b:F) := by
    unfold signMonomial
    push_cast
    rfl
  simp_rw [he,← mul_assoc,← Int.cast_mul]
  rw [← Finset.sum_mul,← Int.cast_sum,sign_character_orthogonality]
  split_ifs <;> norm_num

theorem actualOrientationTrace_proper_zero (a d : Address → F)
    (s : Finset Address) (h : s≠Finset.univ) :
    actualOrientationTrace a d s=0 := by
  rw [actualOrientationTrace_eq,if_neg h,zero_mul]

theorem actualOrientationTrace_full_nonzero (a d : Address → F)
    (δ : F) (hd : (∏ i,d i)=δ) (hδ : δ≠0) :
    actualOrientationTrace a d Finset.univ≠0 := by
  rw [actualOrientationTrace_eq,if_pos rfl,hd]
  exact mul_ne_zero (by norm_num) hδ

/-- Inhabited actual algebraic fibre with nonzero full orientation
trace under the already established punctured product condition. -/
theorem exists_nonzero_actual_orientation [IsAlgClosed F]
    (a y : Address → F) (δ : F) (hδ : δ≠0)
    (hprod : δ^2=∏ i,deltaField (a i) (y i)) :
    ∃ d : SignedFibre (fun i=>deltaField (a i) (y i)) δ,
      actualOrientationTrace a d.1 Finset.univ≠0 := by
  obtain ⟨d⟩ := signedFibre_inhabited _ δ hδ hprod
  exact ⟨d,actualOrientationTrace_full_nonzero a d.1 δ d.2.2 hδ⟩

end
end DASHI.Hodge.DicksonCoupled

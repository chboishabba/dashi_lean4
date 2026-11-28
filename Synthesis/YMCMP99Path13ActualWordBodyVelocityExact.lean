import Synthesis.YMCMP99Path13ActualSignedWordDerivativeExact

namespace CMP99Pivot.Path13
open scoped Quaternion
noncomputable section

theorem q_unit_inverse_pair (q : Q) (hq : ‖q‖=1) :
    star q*q=1 ∧ q*star q=1 := by
  have h := Quaternion.normSq_eq_norm_mul_self q
  rw [hq,mul_one] at h
  constructor
  · rw [Quaternion.star_mul_eq_coe,h]
    simp
  · rw [Quaternion.mul_star_eq_coe,h]
    simp

/-- Body (left-trivialized) velocity of the literal ordered word. -/
def actualWordBodyVelocity (bs : List ActualSignedBond) : Q :=
  star (actualWordValue bs)*actualWordVelocity bs

theorem actualBond_body_velocity (b : ActualSignedBond) (hu : ‖b.q‖=1) :
    star b.value*b.velocity =
      if b.negative then -(b.q*b.h*star b.q) else b.h := by
  cases h : b.negative
  · simp [ActualSignedBond.value,ActualSignedBond.velocity,h,
      ← mul_assoc,(q_unit_inverse_pair b.q hu).1]
  · simp [ActualSignedBond.value,ActualSignedBond.velocity,h,mul_assoc]

/-- For W=bV, W^{-1}W' = Ad_{V^{-1}}(b^{-1}b')+V^{-1}V'.
The exact suffix conjugation matters for noncommuting selected words. -/
theorem actualWordBody_cons (b : ActualSignedBond) (bs : List ActualSignedBond)
    (hu : ‖b.q‖=1) :
    actualWordBodyVelocity (b::bs)=
      star (actualWordValue bs)*(star b.value*b.velocity)*actualWordValue bs+
        actualWordBodyVelocity bs := by
  have hv : ‖b.value‖=1 := by
    cases h : b.negative <;> simp [ActualSignedBond.value,h,norm_star,hu]
  have hi := (q_unit_inverse_pair b.value hv).1
  simp only [actualWordBodyVelocity,actualWordValue,actualWordVelocity,star_mul]
  calc
    _ = star (actualWordValue bs)*(star b.value*b.velocity)*actualWordValue bs+
        star (actualWordValue bs)*(star b.value*b.value)*actualWordVelocity bs := by noncomm_ring
    _ = _ := by rw [hi,mul_one]

theorem actualWordBody_norm (bs : List ActualSignedBond)
    (hu : ∀ b∈bs,‖b.q‖=1) :
    ‖actualWordBodyVelocity bs‖=‖actualWordVelocity bs‖ := by
  unfold actualWordBodyVelocity
  rw [norm_mul,norm_star,actualWordValue_unit bs hu,one_mul]

theorem actualWordBody_bound (bs : List ActualSignedBond)
    (hu : ∀ b∈bs,‖b.q‖=1) :
    ‖actualWordBodyVelocity bs‖≤(bs.map (fun b=>‖b.h‖)).sum := by
  rw [actualWordBody_norm bs hu]
  exact actualWordVelocity_bound bs hu

/-- Left trivialization is reversible on the original unit word. -/
theorem actualWordBody_reopen (bs : List ActualSignedBond)
    (hu : ∀ b∈bs,‖b.q‖=1) :
    actualWordValue bs*actualWordBodyVelocity bs=actualWordVelocity bs := by
  unfold actualWordBodyVelocity
  rw [← mul_assoc,(q_unit_inverse_pair _ (actualWordValue_unit bs hu)).2,one_mul]

end
end CMP99Pivot.Path13

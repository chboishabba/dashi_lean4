import Synthesis.YMCMP99Path13QuaternionBondBallExact

namespace CMP99Pivot.Path13
open scoped Quaternion
noncomputable section

def qLeftLinear (q : Q) : Q →ₗ[ℝ] Q where
  toFun H := q*H
  map_add' H K := by noncomm_ring
  map_smul' r H := by simp [mul_smul_comm]

def qRightLinear (q : Q) : Q →ₗ[ℝ] Q where
  toFun H := H*q
  map_add' H K := by noncomm_ring
  map_smul' r H := by simp [smul_mul_assoc]

def qLeft (q : Q) : Q →L[ℝ] Q :=
  (qLeftLinear q).mkContinuous ‖q‖ (fun H=>by
    change ‖q*H‖≤_
    rw [norm_mul])

def qRight (q : Q) : Q →L[ℝ] Q :=
  (qRightLinear q).mkContinuous ‖q‖ (fun H=>by
    change ‖H*q‖≤_
    rw [norm_mul,mul_comm])

theorem qLeft_isometry_norm (q H : Q) (hq : ‖q‖=1) :
    ‖qLeft q H‖=‖H‖ := by
  change ‖q*H‖=_
  rw [norm_mul,hq,one_mul]

theorem qRight_isometry_norm (q H : Q) (hq : ‖q‖=1) :
    ‖qRight q H‖=‖H‖ := by
  change ‖H*q‖=_
  rw [norm_mul,hq,mul_one]

theorem qLeft_norm_le (q : Q) (hq : ‖q‖=1) : ‖qLeft q‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro H
  rw [qLeft_isometry_norm q H hq,one_mul]

theorem qRight_norm_le (q : Q) (hq : ‖q‖=1) : ‖qRight q‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro H
  rw [qRight_isometry_norm q H hq,one_mul]

/-- Actual tangent of left-translated pure velocity is orthogonal to
the unit quaternion in the ambient real coordinate metric. -/
theorem qLeft_tangent_real (q H : Q) (hH : H.re=0) :
    (star q*(qLeft q H)).re=0 := by
  change (star q*(q*H)).re=0
  simp [Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,
    Quaternion.imK_mul,hH] <;> ring

/-- Two moving unit bonds, rather than a comparison only with identity. -/
theorem qConj_two_point (q p : Q) (hq : ‖q‖=1) (hp : ‖p‖=1) :
    ‖qConj q-qConj p‖≤2*‖q-p‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro H
  change ‖q*H*star q-p*H*star p‖≤_
  have he : q*H*star q-p*H*star p=(q-p)*H*star q+p*H*(star q-star p) := by noncomm_ring
  rw [he]
  have hs : ‖star q-star p‖=‖q-p‖ := by rw [← star_sub,norm_star]
  calc
    _ ≤ ‖(q-p)*H*star q‖+‖p*H*(star q-star p)‖ := norm_add_le _ _
    _ = _ := by simp only [norm_mul,norm_star,hq,hp,hs]; ring

/-- Populate the original BondBound using the actual left translated
tangent operator. This is not yet identification with the selected
Path13 tangent map or the derivative of its logarithm. -/
theorem quaternionBond_left_chord (q : Q) (hq : ‖q‖=1) (e : ℝ)
    (he : ‖q-1‖≤e) (negative : Bool) :
    BondBound e (quaternionBond q negative (qLeft q)) :=
  quaternionBond_chord q hq e he negative _ (qLeft_norm_le q hq)

end
end CMP99Pivot.Path13

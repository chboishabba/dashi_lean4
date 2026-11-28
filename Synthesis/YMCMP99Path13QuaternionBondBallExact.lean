import Synthesis.YMCMP99Path13QuaternionAngleAdExact
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The literal unit-quaternion adjoint is the signed word's BondBound
producer. Chord radius and principal-angle radius are distinguished.
The chord-to-angle conversion costs pi/2 globally; no silent reuse of
the old 148e constant on a chord-defined ball. -/
namespace CMP99Pivot.Path13
open scoped Quaternion
noncomputable section

theorem qChord_sq (q : Q) (hq : ‖q‖=1) :
    ‖q-1‖^2=2-2*q.re := by
  have h := Quaternion.normSq_eq_norm_mul_self (q-1)
  rw [Quaternion.normSq_def'] at h
  have hq' := unit_quaternion_coordinates q hq
  simp only [Quaternion.re_sub,Quaternion.imI_sub,Quaternion.imJ_sub,Quaternion.imK_sub,
    Quaternion.re_one,Quaternion.imI_one,Quaternion.imJ_one,Quaternion.imK_one,sub_zero] at h
  nlinarith

theorem qChord_angle (q : Q) (hq : ‖q‖=1) :
    ‖q-1‖=2*Real.sin (qAngle q/2) := by
  have hc := qChord_sq q hq
  have hh := Real.cos_two_mul (qAngle q/2)
  rw [show 2*(qAngle q/2)=qAngle q by ring,qAngle_cos q hq] at hh
  have hs := Real.sin_sq_add_cos_sq (qAngle q/2)
  have he : ‖q-1‖^2=(2*Real.sin (qAngle q/2))^2 := by nlinarith
  have hnon := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [qAngle_nonneg q] : 0≤qAngle q/2)
    (by linarith [qAngle_le_pi q,Real.pi_pos] : qAngle q/2≤Real.pi)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h|h
  · exact h
  · linarith [norm_nonneg (q-1)]

theorem qChord_le_angle (q : Q) (hq : ‖q‖=1) : ‖q-1‖≤qAngle q := by
  rw [qChord_angle q hq]
  linarith [Real.sin_le (show 0≤qAngle q/2 by linarith [qAngle_nonneg q])]

theorem qAngle_le_chord (q : Q) (hq : ‖q‖=1) :
    qAngle q≤(Real.pi/2)*‖q-1‖ := by
  rw [qChord_angle q hq]
  have h := Real.mul_le_sin (show 0≤qAngle q/2 by linarith [qAngle_nonneg q])
    (show qAngle q/2≤Real.pi/2 by linarith [qAngle_le_pi q])
  have hh := mul_le_mul_of_nonneg_left h Real.pi_pos.le
  have hπ : Real.pi*(2/Real.pi*(qAngle q/2))=qAngle q := by
    field_simp [Real.pi_ne_zero] <;> ring
  rw [hπ] at hh
  linarith

def qConjLinear (q : Q) : Q →ₗ[ℝ] Q where
  toFun H := q*H*star q
  map_add' H K := by noncomm_ring
  map_smul' r H := by simp [mul_smul_comm,smul_mul_assoc]

theorem qConjLinear_bound (q H : Q) :
    ‖qConjLinear q H‖≤‖q‖^2*‖H‖ := by
  change ‖q*H*star q‖≤_
  rw [norm_mul,norm_mul,norm_star]
  ring_nf
  exact le_refl _

def qConj (q : Q) : Q →L[ℝ] Q :=
  (qConjLinear q).mkContinuous (‖q‖^2) (qConjLinear_bound q)

theorem qConj_norm (q : Q) (hq : ‖q‖=1) : ‖qConj q‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro H
  simpa [hq,qConj] using qConjLinear_bound q H

theorem qConj_defect (q : Q) (hq : ‖q‖=1) :
    ‖qConj q-1‖≤2*‖q-1‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro H
  change ‖q*H*star q-H‖≤_
  have h : q*H*star q-H=(q-1)*H*star q+H*(star q-1) := by noncomm_ring
  rw [h]
  have hs : ‖star q-1‖=‖q-1‖ := by rw [← star_one,← star_sub,norm_star]
  calc
    _ ≤ ‖(q-1)*H*star q‖+‖H*(star q-1)‖ := norm_add_le _ _
    _ = _ := by rw [norm_mul,norm_mul,norm_mul,norm_star,hq,hs]; ring

/-- Actual quaternion adjoint and a supplied unit tangent injection
populate the existing signed-word BondBound, on either ball.
The tangent injection itself retains its original source obligation. -/
def quaternionBond (q : Q) (negative : Bool) (T : Q →L[ℝ] Q) :
    BondVariation (Q →L[ℝ] Q) := ⟨qConj q,negative,T⟩

theorem quaternionBond_chord (q : Q) (hq : ‖q‖=1) (e : ℝ)
    (he : ‖q-1‖≤e) (negative : Bool) (T : Q →L[ℝ] Q) (hT : ‖T‖≤1) :
    BondBound e (quaternionBond q negative T) := by
  exact ⟨qConj_norm q hq,(qConj_defect q hq).trans (by linarith),hT⟩

theorem quaternionBond_angle (q : Q) (hq : ‖q‖=1) (e : ℝ)
    (he : qAngle q≤e) (negative : Bool) (T : Q →L[ℝ] Q) (hT : ‖T‖≤1) :
    BondBound e (quaternionBond q negative T) :=
  quaternionBond_chord q hq e ((qChord_le_angle q hq).trans he) negative T hT

/-- If the actual CMP102 ball is measured in chord radius, the
relative word series still has an explicit enclosure, but at the
enlarged angle radius pi*e/2. -/
theorem qPath74_chord_series_inverse (p : List Q) (e : ℝ) (he : 0≤e)
    (hp : ∀ q∈p,‖q‖=1 ∧ ‖q-1‖≤e) (hL : p.length≤74)
    (hsmall : 148*(Real.pi/2*e)≤1/2) :
    let D := dexpSeries (qAd (qPrincipalVector p.prod))
    ∃ J : Q →L[ℝ] Q,D*J=1 ∧ J*D=1 ∧
      ‖D-1‖≤148*(Real.pi/2*e) ∧ ‖J‖≤2 ∧ ‖J-1‖≤296*(Real.pi/2*e) := by
  apply qPath74_series_inverse p (Real.pi/2*e) (by positivity) _ hL _ hsmall
  · intro q hq
    exact ⟨(hp q hq).1,(qAngle_le_chord q (hp q hq).1).trans
      (mul_le_mul_of_nonneg_left (hp q hq).2 (by positivity))⟩
  · have hπ := Real.pi_gt_three
    linarith

end
end CMP99Pivot.Path13

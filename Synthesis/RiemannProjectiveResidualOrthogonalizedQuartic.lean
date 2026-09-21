import Synthesis.RiemannProjectiveResidualOrthogonalization

/-!
# Quartic local detector after exact residual orthogonalization

A continuous compact physical profile P with

  integral P = 0,
  integral P u^2 = 0,
  integral P u^4 < 0

has both local observables required by the quartic route:

  integral P(u) cos(q u) du < 0
  integral P(u) cosh(a u) du < 0

for sufficiently small nonzero q and a.

Apply this to the profile obtained by projecting the finite N-mu residual out of
two quartic profiles.  If the residual/fourth-moment determinant is nonzero, we
can orient the projected profile so its fourth moment is negative.  The residual
remains exactly zero under this sign flip.

Thus the finite-window arithmetic obligation is reduced to one scalar
transversality condition:

  E(Q) M4(P) - E(P) M4(Q) != 0.

No sign assumption on E(P) or E(Q) is needed.
-/

noncomputable section

open MeasureTheory Set Topology
open scoped Real

namespace Synthesis

theorem profileLinearCombination_continuous
    {P Q : ℝ -> ℝ}
    (hP : Continuous P) (hQ : Continuous Q)
    (a b : ℝ) :
    Continuous (profileLinearCombination a b P Q) := by
  unfold profileLinearCombination
  fun_prop

theorem profileLinearCombination_compact
    {P Q : ℝ -> ℝ}
    (hPc : HasCompactSupport P) (hQc : HasCompactSupport Q)
    (a b : ℝ) :
    HasCompactSupport (profileLinearCombination a b P Q) := by
  unfold profileLinearCombination
  exact hPc.mul_left.add hQc.mul_left

theorem compactCosine_zero_of_profileZerothMoment_zero
    {P : ℝ -> ℝ}
    (hP0 : profileZerothMoment P = 0) :
    compactCosineTransform P 0 = 0 := by
  unfold compactCosineTransform profileZerothMoment
  simp only [zero_mul,Real.cos_zero,mul_one]
  exact hP0

theorem compactCosineD2_zero_of_profileSecondMoment_zero
    {P : ℝ -> ℝ}
    (hP2 : profileSecondMoment P = 0) :
    compactCosineD2 P 0 = 0 := by
  unfold compactCosineD2 profileSecondMoment
  simp only [zero_mul,Real.cos_zero,mul_one]
  rw [← integral_neg,hP2]
  simp

theorem compactCosineD4_zero_eq_profileFourthMoment
    (P : ℝ -> ℝ) :
    compactCosineD4 P 0 = profileFourthMoment P := by
  unfold compactCosineD4 profileFourthMoment
  simp

theorem compactCosh_zero_of_profileZerothMoment_zero
    {P : ℝ -> ℝ}
    (hP0 : profileZerothMoment P = 0) :
    compactCoshTransform P 0 = 0 := by
  unfold compactCoshTransform profileZerothMoment
  simp only [zero_mul,Real.cosh_zero,mul_one]
  exact hP0

theorem compactCoshD2_zero_of_profileSecondMoment_zero
    {P : ℝ -> ℝ}
    (hP2 : profileSecondMoment P = 0) :
    compactCoshD2 P 0 = 0 := by
  unfold compactCoshD2 profileSecondMoment
  simp only [zero_mul,Real.cosh_zero,mul_one]
  exact hP2

theorem compactCoshD4_zero_eq_profileFourthMoment
    (P : ℝ -> ℝ) :
    compactCoshD4 P 0 = profileFourthMoment P := by
  unfold compactCoshD4 profileFourthMoment
  simp

theorem exists_profile_cosine_neg_right_of_quartic_moments
    {P : ℝ -> ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (hP0 : profileZerothMoment P = 0)
    (hP2 : profileSecondMoment P = 0)
    (hP4 : profileFourthMoment P < 0) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ q : ℝ, 0 < q -> q < eps ->
        compactCosineTransform P q < 0 := by
  exact
    exists_neg_right_of_fourth_deriv_neg
      (f:=compactCosineTransform P)
      (f1:=compactCosineD1 P)
      (f2:=compactCosineD2 P)
      (f3:=compactCosineD3 P)
      (f4:=compactCosineD4 P)
      (fun q => compactCosineTransform_hasDerivAt hP hPc q)
      (fun q => compactCosineD1_deriv hP hPc q)
      (fun q => compactCosineD2_deriv hP hPc q)
      (fun q => compactCosineD3_deriv hP hPc q)
      (compactCosineD4_continuous hP hPc)
      (compactCosine_zero_of_profileZerothMoment_zero hP0)
      (compactCosineD1_zero P)
      (compactCosineD2_zero_of_profileSecondMoment_zero hP2)
      (compactCosineD3_zero P)
      (by simpa [compactCosineD4_zero_eq_profileFourthMoment] using hP4)

theorem exists_profile_cosh_neg_right_of_quartic_moments
    {P : ℝ -> ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (hP0 : profileZerothMoment P = 0)
    (hP2 : profileSecondMoment P = 0)
    (hP4 : profileFourthMoment P < 0) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ a : ℝ, 0 < a -> a < eps ->
        compactCoshTransform P a < 0 := by
  exact
    exists_neg_right_of_fourth_deriv_neg
      (f:=compactCoshTransform P)
      (f1:=compactCoshD1 P)
      (f2:=compactCoshD2 P)
      (f3:=compactCoshD3 P)
      (f4:=compactCoshD4 P)
      (fun a => compactCoshTransform_hasDerivAt hP hPc a)
      (fun a => compactCoshD1_deriv hP hPc a)
      (fun a => compactCoshD2_deriv hP hPc a)
      (fun a => compactCoshD3_deriv hP hPc a)
      (compactCoshD4_continuous hP hPc)
      (compactCosh_zero_of_profileZerothMoment_zero hP0)
      (by
        unfold compactCoshD1
        simp)
      (compactCoshD2_zero_of_profileSecondMoment_zero hP2)
      (by
        unfold compactCoshD3
        simp)
      (by simpa [compactCoshD4_zero_eq_profileFourthMoment] using hP4)

def orientedResidualOrthogonalizedProfile
    (P Q : ℝ -> ℝ) (t A B : ℝ) : ℝ -> ℝ :=
  let R := residualOrthogonalizedProfile P Q t A B
  if residualMomentTransversality P Q t A B < 0
  then R
  else fun u => -R u

theorem orientedResidualOrthogonalizedProfile_residual_zero
    {P Q : ℝ -> ℝ}
    (hP : Continuous P) (hPc : HasCompactSupport P)
    (hQ : Continuous Q) (hQc : HasCompactSupport Q)
    (t A B : ℝ) :
    profileZetaMuWindowResidual
      (orientedResidualOrthogonalizedProfile P Q t A B)
      t A B = 0 := by
  unfold orientedResidualOrthogonalizedProfile
  split_ifs with hsign
  · exact residualOrthogonalizedProfile_residual_zero
      hP hPc hQ hQc t A B
  · have hR :=
      residualOrthogonalizedProfile_residual_zero
        hP hPc hQ hQc t A B
    have hcont :
        Continuous (residualOrthogonalizedProfile P Q t A B) := by
      unfold residualOrthogonalizedProfile
      exact profileLinearCombination_continuous hP hQ _ _
    have hcomp :
        HasCompactSupport
          (residualOrthogonalizedProfile P Q t A B) := by
      unfold residualOrthogonalizedProfile
      exact profileLinearCombination_compact hPc hQc _ _
    have hlin :=
      profileZetaMuWindowResidual_linearCombination
        hcont hcomp continuous_zero hasCompactSupport_zero
        (-1) 0 t A B
    simpa [profileLinearCombination,hR] using hlin

theorem orientedResidualOrthogonalizedProfile_fourthMoment_neg
    {P Q : ℝ -> ℝ}
    (hP : Continuous P) (hPc : HasCompactSupport P)
    (hQ : Continuous Q) (hQc : HasCompactSupport Q)
    {t A B : ℝ}
    (htrans : residualMomentTransversality P Q t A B ≠ 0) :
    profileFourthMoment
      (orientedResidualOrthogonalizedProfile P Q t A B) < 0 := by
  unfold orientedResidualOrthogonalizedProfile
  by_cases hneg : residualMomentTransversality P Q t A B < 0
  · simp [hneg]
    rw [residualOrthogonalizedProfile_fourthMoment
      hP hPc hQ hQc]
    exact hneg
  · simp [hneg]
    have hpos :
        0 < residualMomentTransversality P Q t A B := by
      exact lt_of_le_of_ne
        (le_of_not_gt hneg)
        (Ne.symm htrans)
    have hR :=
      residualOrthogonalizedProfile_fourthMoment
        hP hPc hQ hQc t A B
    unfold profileFourthMoment
    rw [show
      (fun u : ℝ =>
        - residualOrthogonalizedProfile P Q t A B u * u^4)
        =
      fun u => -(residualOrthogonalizedProfile P Q t A B u*u^4) by
        funext u
        ring,
      integral_neg,hR]
    linarith

end Synthesis

import Synthesis.RiemannProjectiveQuarticNMuSameObject
import Synthesis.RiemannZetaMuExactAbel
import Synthesis.RiemannCompactCosineFourthDerivative

/-!
# Exact finite-window Abel consumer for the quartic projective test

The quartic physical ordinate test is

  phi_t(gamma)
    = r^-2 Phi_Q((gamma-t)/r),  r=t/16.

Its exact derivative is

  phi_t'(gamma)
    = r^-3 Phi_Q'((gamma-t)/r).

This file installs that derivative and specializes the literal N-mu Abel
identity to the actual quartic test.  No absolute value is taken.

Thus on every finite physical window [A,B],

  Z_phi(A,B) - integral_A^B phi_t mu
    =
  phi_t(B) E_A(B)
    - integral_A^B phi_t'(x) E_A(x) dx.

This is the exact signed scalar whose global/infinite one-sided control is the
remaining number-theoretic theorem in the quartic route.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval Real

namespace Synthesis

def quarticNegativeOrdinateTestDeriv
    (W : QuarticHighWitness)
    (t gamma : ℝ) : ℝ :=
  let r := quarticNegativeWindowRadius t
  (1 / r^3) *
    compactCosineD1
      (genericProjectivePhysicalProfile
        (quarticThreeWindowProfile W.R W.lam) 1)
      ((gamma-t)/r)

theorem quarticNegativeOrdinateTest_hasDerivAt
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t)
    (gamma : ℝ) :
    HasDerivAt
      (quarticNegativeOrdinateTest W t)
      (quarticNegativeOrdinateTestDeriv W t gamma)
      gamma := by
  let r : ℝ := quarticNegativeWindowRadius t
  let P : ℝ → ℝ :=
    genericProjectivePhysicalProfile
      (quarticThreeWindowProfile W.R W.lam) 1
  have hr : 0 < r := by
    dsimp [r, quarticNegativeWindowRadius]
    positivity
  have hG :
      Continuous (quarticThreeWindowProfile W.R W.lam) :=
    quarticThreeWindowProfile_continuous W.Rpos
  have hGc :
      HasCompactSupport (quarticThreeWindowProfile W.R W.lam) :=
    quarticThreeWindowProfile_compact W.Rpos
  have hP : Continuous P := by
    dsimp [P]
    exact genericProjectivePhysicalProfile_continuous hG 1
  have hPc : HasCompactSupport P := by
    dsimp [P]
    exact genericProjectivePhysicalProfile_compact hGc 1
  have hinner :
      HasDerivAt (fun x : ℝ => (x-t)/r) (1/r) gamma := by
    convert ((hasDerivAt_id gamma).sub_const t).div_const r using 1
    ring
  have hcos :=
    (compactCosineTransform_hasDerivAt hP hPc ((gamma-t)/r)).comp
      gamma hinner
  have hscaled :=
    hcos.const_mul (1/r^2)
  unfold quarticNegativeOrdinateTest
    quarticNegativeOrdinateTestDeriv
  dsimp [r, P] at hscaled ⊢
  convert hscaled using 1 <;> field_simp [hr.ne'] <;> ring

theorem quarticNegativeOrdinateTestDeriv_continuous
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t) :
    Continuous (quarticNegativeOrdinateTestDeriv W t) := by
  let r : ℝ := quarticNegativeWindowRadius t
  let P : ℝ → ℝ :=
    genericProjectivePhysicalProfile
      (quarticThreeWindowProfile W.R W.lam) 1
  have hr : 0 < r := by
    dsimp [r, quarticNegativeWindowRadius]
    positivity
  have hG :
      Continuous (quarticThreeWindowProfile W.R W.lam) :=
    quarticThreeWindowProfile_continuous W.Rpos
  have hGc :
      HasCompactSupport (quarticThreeWindowProfile W.R W.lam) :=
    quarticThreeWindowProfile_compact W.Rpos
  have hP : Continuous P := by
    dsimp [P]
    exact genericProjectivePhysicalProfile_continuous hG 1
  have hPc : HasCompactSupport P := by
    dsimp [P]
    exact genericProjectivePhysicalProfile_compact hGc 1
  have hD1 : Continuous (compactCosineD1 P) :=
    continuous_of_forall_continuousAt fun q =>
      (compactCosineD1_deriv hP hPc q).continuousAt
  unfold quarticNegativeOrdinateTestDeriv
  dsimp [r, P]
  fun_prop

theorem quarticNegativeOrdinateTestDeriv_intervalIntegrable
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t)
    (A B : ℝ) :
    IntervalIntegrable
      (quarticNegativeOrdinateTestDeriv W t)
      volume A B :=
  (quarticNegativeOrdinateTestDeriv_continuous W ht).intervalIntegrable A B

def quarticZetaMuWindowResidual
    (W : QuarticHighWitness)
    (t A B : ℝ) : ℝ :=
  zetaWindowMinusMuPair A B (quarticNegativeOrdinateTest W t)

/--
Exact signed Abel identity on the literal physical quartic test.
-/
theorem quarticZetaMuWindowResidual_eq_discrepancyAbel
    (W : QuarticHighWitness)
    {t A B : ℝ}
    (ht : 0 < t)
    (hAB : A <= B) :
    quarticZetaMuWindowResidual W t A B
      =
    quarticNegativeOrdinateTest W t B
      * zetaMuCumulativeDiscrepancy A B
      -
    ∫ x in A..B,
      quarticNegativeOrdinateTestDeriv W t x
        * zetaMuCumulativeDiscrepancy A x := by
  unfold quarticZetaMuWindowResidual
  exact
    zetaWindowMinusMuPair_eq_discrepancyAbel
      (A:=A) (B:=B)
      (phi:=quarticNegativeOrdinateTest W t)
      (phi':=quarticNegativeOrdinateTestDeriv W t)
      hAB
      (by
        intro x hx
        exact quarticNegativeOrdinateTest_hasDerivAt W ht x)
      (quarticNegativeOrdinateTestDeriv_intervalIntegrable
        W ht A B)

end Synthesis

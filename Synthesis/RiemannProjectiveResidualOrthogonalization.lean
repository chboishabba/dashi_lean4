import Synthesis.RiemannZetaMuPairingLinearity
import Synthesis.RiemannCompactCosineFourthDerivative
import Synthesis.RiemannCompactCoshFourthDerivative
import Synthesis.RiemannFourthOrderLocalSignCompiler

/-!
# Orthogonalizing the signed N-mu residual at physical-profile level

The explicit formula is linear in the actual test profile.  Consequently the
remaining signed N-mu functional should be projected out at the profile level,
rather than forcing one nonlinear taper family to have a prescribed sign.

For a continuous compact physical profile P define

  Phi_P(q) = integral P(u) cos(q u) du,

and on a finite ordinate window

  E_{A,B,t}(P)
    = sum_{A<gamma<=B} m_gamma Phi_P(gamma-t)
      - integral_A^B Phi_P(x-t) mu(x) dx.

This is linear in P.

Given two profiles P1,P2 with residuals E1,E2, define

  P_perp = E2 P1 - E1 P2.

Then E(P_perp)=0 identically.

If both profiles have zero zeroth and second moments, so does P_perp.  Its
fourth moment is

  E2 M4(P1) - E1 M4(P2).

Thus a single transversality condition saying this determinant is nonzero lets
us orient P_perp so that its fourth moment is negative.  Standard fourth-order
calculus then gives simultaneously:

* a punctured negative cosine lobe;
* a punctured negative hyperbolic transform, hence positive target detector
  after the usual -1/4 normalization.

This is a strictly weaker arithmetic target than demanding a predetermined
sign for E(P) on one fixed detector.
-/

noncomputable section

open MeasureTheory Set Topology
open scoped Interval Real

namespace Synthesis

def profileCosineOrdinateTest
    (P : ℝ -> ℝ) (t : ℝ) : ℝ -> ℝ :=
  fun x => compactCosineTransform P (x-t)

def profileZetaMuWindowResidual
    (P : ℝ -> ℝ) (t A B : ℝ) : ℝ :=
  zetaWindowMinusMuPair A B (profileCosineOrdinateTest P t)

def profileLinearCombination
    (a b : ℝ) (P Q : ℝ -> ℝ) : ℝ -> ℝ :=
  fun u => a*P u + b*Q u

theorem compactCosineTransform_linearCombination
    {P Q : ℝ -> ℝ}
    (hP : Continuous P) (hPc : HasCompactSupport P)
    (hQ : Continuous Q) (hQc : HasCompactSupport Q)
    (a b q : ℝ) :
    compactCosineTransform (profileLinearCombination a b P Q) q
      =
    a*compactCosineTransform P q
      + b*compactCosineTransform Q q := by
  unfold compactCosineTransform profileLinearCombination
  have hPi :
      Integrable (fun u => P u*Real.cos (q*u)) :=
    (hP.mul (by fun_prop)).integrable_of_hasCompactSupport hPc.mul_right
  have hQi :
      Integrable (fun u => Q u*Real.cos (q*u)) :=
    (hQ.mul (by fun_prop)).integrable_of_hasCompactSupport hQc.mul_right
  have hpoint :
      (fun u : ℝ => (a*P u+b*Q u)*Real.cos (q*u))
        =
      fun u => a*(P u*Real.cos (q*u))
        + b*(Q u*Real.cos (q*u)) := by
    funext u
    ring
  rw [hpoint,
      integral_add (hPi.const_mul a) (hQi.const_mul b),
      integral_const_mul, integral_const_mul]

theorem profileCosineOrdinateTest_linearCombination
    {P Q : ℝ -> ℝ}
    (hP : Continuous P) (hPc : HasCompactSupport P)
    (hQ : Continuous Q) (hQc : HasCompactSupport Q)
    (a b t x : ℝ) :
    profileCosineOrdinateTest
        (profileLinearCombination a b P Q) t x
      =
    a*profileCosineOrdinateTest P t x
      + b*profileCosineOrdinateTest Q t x := by
  unfold profileCosineOrdinateTest
  exact compactCosineTransform_linearCombination
    hP hPc hQ hQc a b (x-t)

theorem profileZetaMuWindowResidual_linearCombination
    {P Q : ℝ -> ℝ}
    (hP : Continuous P) (hPc : HasCompactSupport P)
    (hQ : Continuous Q) (hQc : HasCompactSupport Q)
    (a b t A B : ℝ) :
    profileZetaMuWindowResidual
        (profileLinearCombination a b P Q) t A B
      =
    a*profileZetaMuWindowResidual P t A B
      + b*profileZetaMuWindowResidual Q t A B := by
  have hPt :
      Continuous (profileCosineOrdinateTest P t) := by
    unfold profileCosineOrdinateTest
    have hc : Continuous (compactCosineTransform P) := by
      apply continuous_of_forall_continuousAt
      intro q
      exact (compactCosineTransform_hasDerivAt hP hPc q).continuousAt
    exact hc.comp (continuous_id.sub continuous_const)
  have hQt :
      Continuous (profileCosineOrdinateTest Q t) := by
    unfold profileCosineOrdinateTest
    have hc : Continuous (compactCosineTransform Q) := by
      apply continuous_of_forall_continuousAt
      intro q
      exact (compactCosineTransform_hasDerivAt hQ hQc q).continuousAt
    exact hc.comp (continuous_id.sub continuous_const)
  have hPmu :
      IntervalIntegrable
        (fun x => profileCosineOrdinateTest P t x * Zeta23.mu x)
        volume A B :=
    (hPt.mul Zeta23.gammaFacts.smooth.continuous).intervalIntegrable A B
  have hQmu :
      IntervalIntegrable
        (fun x => profileCosineOrdinateTest Q t x * Zeta23.mu x)
        volume A B :=
    (hQt.mul Zeta23.gammaFacts.smooth.continuous).intervalIntegrable A B

  unfold profileZetaMuWindowResidual
  have hfun :
      profileCosineOrdinateTest
        (profileLinearCombination a b P Q) t
        =
      fun x =>
        a*profileCosineOrdinateTest P t x
          + b*profileCosineOrdinateTest Q t x := by
    funext x
    exact profileCosineOrdinateTest_linearCombination
      hP hPc hQ hQc a b t x
  rw [hfun]
  have ha :
      IntervalIntegrable
        (fun x =>
          (a*profileCosineOrdinateTest P t x)*Zeta23.mu x)
        volume A B := by
    have heq :
        (fun x : ℝ =>
          (a*profileCosineOrdinateTest P t x)*Zeta23.mu x)
          =
        fun x => a*(profileCosineOrdinateTest P t x*Zeta23.mu x) := by
      funext x
      ring
    rw [heq]
    exact hPmu.const_mul a
  have hb :
      IntervalIntegrable
        (fun x =>
          (b*profileCosineOrdinateTest Q t x)*Zeta23.mu x)
        volume A B := by
    have heq :
        (fun x : ℝ =>
          (b*profileCosineOrdinateTest Q t x)*Zeta23.mu x)
          =
        fun x => b*(profileCosineOrdinateTest Q t x*Zeta23.mu x) := by
      funext x
      ring
    rw [heq]
    exact hQmu.const_mul b
  rw [zetaWindowMinusMuPair_add ha hb,
      zetaWindowMinusMuPair_smul hPmu,
      zetaWindowMinusMuPair_smul hQmu]

def profileFourthMoment (P : ℝ -> ℝ) : ℝ :=
  ∫ u : ℝ, P u*u^4

def profileSecondMoment (P : ℝ -> ℝ) : ℝ :=
  ∫ u : ℝ, P u*u^2

def profileZerothMoment (P : ℝ -> ℝ) : ℝ :=
  ∫ u : ℝ, P u

theorem profileMoment_linearCombination
    {P Q : ℝ -> ℝ}
    (hP : Continuous P) (hPc : HasCompactSupport P)
    (hQ : Continuous Q) (hQc : HasCompactSupport Q)
    (a b : ℝ) (k : ℕ) :
    (∫ u : ℝ,
      profileLinearCombination a b P Q u * u^k)
      =
    a*(∫ u : ℝ,P u*u^k)
      + b*(∫ u : ℝ,Q u*u^k) := by
  have hPi :
      Integrable (fun u => P u*u^k) :=
    (hP.mul (by fun_prop)).integrable_of_hasCompactSupport hPc.mul_right
  have hQi :
      Integrable (fun u => Q u*u^k) :=
    (hQ.mul (by fun_prop)).integrable_of_hasCompactSupport hQc.mul_right
  have hpoint :
      (fun u : ℝ =>
        profileLinearCombination a b P Q u*u^k)
        =
      fun u => a*(P u*u^k)+b*(Q u*u^k) := by
    funext u
    unfold profileLinearCombination
    ring
  rw [hpoint,
      integral_add (hPi.const_mul a) (hQi.const_mul b),
      integral_const_mul, integral_const_mul]

def residualOrthogonalizedProfile
    (P Q : ℝ -> ℝ) (t A B : ℝ) : ℝ -> ℝ :=
  profileLinearCombination
    (profileZetaMuWindowResidual Q t A B)
    (-profileZetaMuWindowResidual P t A B)
    P Q

theorem residualOrthogonalizedProfile_residual_zero
    {P Q : ℝ -> ℝ}
    (hP : Continuous P) (hPc : HasCompactSupport P)
    (hQ : Continuous Q) (hQc : HasCompactSupport Q)
    (t A B : ℝ) :
    profileZetaMuWindowResidual
        (residualOrthogonalizedProfile P Q t A B)
        t A B
      = 0 := by
  unfold residualOrthogonalizedProfile
  rw [profileZetaMuWindowResidual_linearCombination
      hP hPc hQ hQc]
  ring

def residualMomentTransversality
    (P Q : ℝ -> ℝ) (t A B : ℝ) : ℝ :=
  profileZetaMuWindowResidual Q t A B * profileFourthMoment P
    - profileZetaMuWindowResidual P t A B * profileFourthMoment Q

theorem residualOrthogonalizedProfile_fourthMoment
    {P Q : ℝ -> ℝ}
    (hP : Continuous P) (hPc : HasCompactSupport P)
    (hQ : Continuous Q) (hQc : HasCompactSupport Q)
    (t A B : ℝ) :
    profileFourthMoment
      (residualOrthogonalizedProfile P Q t A B)
      =
    residualMomentTransversality P Q t A B := by
  unfold profileFourthMoment residualOrthogonalizedProfile
    residualMomentTransversality
  rw [profileMoment_linearCombination hP hPc hQ hQc
      (profileZetaMuWindowResidual Q t A B)
      (-profileZetaMuWindowResidual P t A B) 4]
  ring

theorem residualOrthogonalizedProfile_secondMoment_zero
    {P Q : ℝ -> ℝ}
    (hP : Continuous P) (hPc : HasCompactSupport P)
    (hQ : Continuous Q) (hQc : HasCompactSupport Q)
    (hP2 : profileSecondMoment P = 0)
    (hQ2 : profileSecondMoment Q = 0)
    (t A B : ℝ) :
    profileSecondMoment
      (residualOrthogonalizedProfile P Q t A B) = 0 := by
  unfold profileSecondMoment residualOrthogonalizedProfile
  rw [profileMoment_linearCombination hP hPc hQ hQc
      (profileZetaMuWindowResidual Q t A B)
      (-profileZetaMuWindowResidual P t A B) 2]
  rw [show (∫ u : ℝ,P u*u^2)=0 by exact hP2,
      show (∫ u : ℝ,Q u*u^2)=0 by exact hQ2]
  ring

theorem residualOrthogonalizedProfile_zerothMoment_zero
    {P Q : ℝ -> ℝ}
    (hP : Continuous P) (hPc : HasCompactSupport P)
    (hQ : Continuous Q) (hQc : HasCompactSupport Q)
    (hP0 : profileZerothMoment P = 0)
    (hQ0 : profileZerothMoment Q = 0)
    (t A B : ℝ) :
    profileZerothMoment
      (residualOrthogonalizedProfile P Q t A B) = 0 := by
  unfold profileZerothMoment residualOrthogonalizedProfile
  have hlin :=
    profileMoment_linearCombination hP hPc hQ hQc
      (profileZetaMuWindowResidual Q t A B)
      (-profileZetaMuWindowResidual P t A B) 0
  simpa [pow_zero,hP0,hQ0] using hlin

end Synthesis

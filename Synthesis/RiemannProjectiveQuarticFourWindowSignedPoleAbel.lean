import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleNMu
import Synthesis.RiemannZetaMuExactAbel
import Synthesis.RiemannCompactCosineFourthDerivative

/-!
# Exact Abel and centered jet for the signed four-window quartic test

For r=t/16, each endpoint ordinate test is

  phi(x) = r^-2 C_P((x-t)/r),

where P is the normalized projective physical profile.  The signed-pole test

  Psi_t = P_two * phi_half - P_half * phi_two

is therefore exactly the same rescaling of the signed combined projective
profile already used by the quantitative target theorem.

This file transports the existing compact-cosine derivative calculus to that
literal G3 consumer.  It proves:

* endpoint and signed first-derivative formulas;
* the complete centered 0/1/2/3/4 jet;
* Psi''''(t) = -4 S(W)/(t/16)^6 < 0;
* the exact finite-window N-mu Abel identity on the signed combined test.

No discrepancy estimate is introduced.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Interval Real

namespace Synthesis

def quarticFourOrdinateTestDeriv
    (R lam mu t x : ℝ) : ℝ :=
  let r := t/16
  (1/r^3) *
    compactCosineD1
      (quarticFourNormalizedProjectiveProfile R lam mu)
      ((x-t)/r)

theorem quarticFourOrdinateTest_hasDerivAt
    {R lam mu t : ℝ}
    (hR : 0 < R)
    (ht : 0 < t)
    (x : ℝ) :
    HasDerivAt
      (quarticFourOrdinateTest R lam mu t)
      (quarticFourOrdinateTestDeriv R lam mu t x)
      x := by
  let r : ℝ := t/16
  let P : ℝ -> ℝ :=
    quarticFourNormalizedProjectiveProfile R lam mu
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hP : Continuous P := by
    dsimp [P]
    exact quarticFourNormalizedProjectiveProfile_continuous hR
  have hPc : HasCompactSupport P := by
    dsimp [P]
    exact quarticFourNormalizedProjectiveProfile_compact hR
  have hinner :
      HasDerivAt (fun y : ℝ => (y-t)/r) (1/r) x := by
    convert ((hasDerivAt_id x).sub_const t).div_const r using 1
    ring
  have hc :=
    (compactCosineTransform_hasDerivAt hP hPc ((x-t)/r)).comp
      x hinner
  have hs := hc.const_mul (1/r^2)
  unfold quarticFourOrdinateTest quarticFourOrdinateTestDeriv
    genericProjectiveBaseKernel
  dsimp [r, P] at hs ⊢
  convert hs using 1 <;> field_simp [hr.ne'] <;> ring

theorem quarticFourOrdinateTestDeriv_continuous
    {R lam mu t : ℝ}
    (hR : 0 < R)
    (ht : 0 < t) :
    Continuous (quarticFourOrdinateTestDeriv R lam mu t) := by
  let P : ℝ -> ℝ :=
    quarticFourNormalizedProjectiveProfile R lam mu
  have hP : Continuous P := by
    dsimp [P]
    exact quarticFourNormalizedProjectiveProfile_continuous hR
  have hPc : HasCompactSupport P := by
    dsimp [P]
    exact quarticFourNormalizedProjectiveProfile_compact hR
  have hD1 : Continuous (compactCosineD1 P) :=
    continuous_of_forall_continuousAt fun q =>
      (compactCosineD1_deriv hP hPc q).continuousAt
  unfold quarticFourOrdinateTestDeriv
  dsimp [P]
  fun_prop

theorem quarticFourOrdinateTestDeriv_intervalIntegrable
    {R lam mu t : ℝ}
    (hR : 0 < R)
    (ht : 0 < t)
    (A B : ℝ) :
    IntervalIntegrable
      (quarticFourOrdinateTestDeriv R lam mu t)
      volume A B :=
  (quarticFourOrdinateTestDeriv_continuous hR ht).intervalIntegrable A B

def QuarticFourSignedPolePair.signedOrdinateTestDeriv
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ -> ℝ :=
  fun x =>
    W.poleTwo *
      quarticFourOrdinateTestDeriv W.R (1/2) W.muHalf t x
      +
    (-W.poleHalf) *
      quarticFourOrdinateTestDeriv W.R (2/3) W.muTwo t x

theorem QuarticFourSignedPolePair.signedOrdinateTest_hasDerivAt
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (x : ℝ) :
    HasDerivAt
      W.signedOrdinateTest
      (W.signedOrdinateTestDeriv x)
      x := by
  unfold QuarticFourSignedPolePair.signedOrdinateTest
    QuarticFourSignedPolePair.signedOrdinateTestDeriv
    QuarticFourSignedPolePair.ordinateTestHalf
    QuarticFourSignedPolePair.ordinateTestTwo
  exact
    ((quarticFourOrdinateTest_hasDerivAt
        (R:=W.R) (lam:=(1/2 : ℝ)) (mu:=W.muHalf) W.Rpos ht x).const_mul
      W.poleTwo).add
      ((quarticFourOrdinateTest_hasDerivAt
        (R:=W.R) (lam:=(2/3 : ℝ)) (mu:=W.muTwo) W.Rpos ht x).const_mul
      (-W.poleHalf))

theorem QuarticFourSignedPolePair.signedOrdinateTestDeriv_continuous
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    Continuous W.signedOrdinateTestDeriv := by
  unfold QuarticFourSignedPolePair.signedOrdinateTestDeriv
  have h1 :=
    quarticFourOrdinateTestDeriv_continuous
      (R:=W.R) (lam:=(1/2 : ℝ)) (mu:=W.muHalf) W.Rpos ht
  have h2 :=
    quarticFourOrdinateTestDeriv_continuous
      (R:=W.R) (lam:=(2/3 : ℝ)) (mu:=W.muTwo) W.Rpos ht
  fun_prop

theorem QuarticFourSignedPolePair.signedOrdinateTestDeriv_intervalIntegrable
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (A B : ℝ) :
    IntervalIntegrable W.signedOrdinateTestDeriv volume A B :=
  (W.signedOrdinateTestDeriv_continuous ht).intervalIntegrable A B

/--
Same-object compression: the signed endpoint test is exactly the rescaled
compact cosine transform of the signed combined projective profile.
-/
theorem QuarticFourSignedPolePair.signedOrdinateTest_eq_combinedCosine
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (x : ℝ) :
    W.signedOrdinateTest x
      =
    let r := t/16
    (1/r^2) *
      compactCosineTransform
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t)
        ((x-t)/r) := by
  let P1 :=
    quarticFourNormalizedProjectiveProfile W.R (1/2) W.muHalf
  let P2 :=
    quarticFourNormalizedProjectiveProfile W.R (2/3) W.muTwo
  have hlin :=
    compactCosineTransform_linearCombination
      (quarticFourNormalizedProjectiveProfile_continuous W.Rpos)
      (quarticFourNormalizedProjectiveProfile_compact W.Rpos)
      (quarticFourNormalizedProjectiveProfile_continuous W.Rpos)
      (quarticFourNormalizedProjectiveProfile_compact W.Rpos)
      W.poleTwo (-W.poleHalf) ((x-t)/(t/16))
  unfold QuarticFourSignedPolePair.signedOrdinateTest
    QuarticFourSignedPolePair.ordinateTestHalf
    QuarticFourSignedPolePair.ordinateTestTwo
    quarticFourOrdinateTest
    genericProjectiveBaseKernel
    quarticFourSignedPoleCombinedProfile
  dsimp [P1, P2] at hlin ⊢
  rw [hlin]
  ring

def QuarticFourSignedPolePair.signedOrdinateTestDeriv2
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ -> ℝ :=
  fun x =>
    let r := t/16
    (1/r^4) *
      compactCosineD2
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t)
        ((x-t)/r)

def QuarticFourSignedPolePair.signedOrdinateTestDeriv3
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ -> ℝ :=
  fun x =>
    let r := t/16
    (1/r^5) *
      compactCosineD3
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t)
        ((x-t)/r)

def QuarticFourSignedPolePair.signedOrdinateTestDeriv4
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ -> ℝ :=
  fun x =>
    let r := t/16
    (1/r^6) *
      compactCosineD4
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t)
        ((x-t)/r)

theorem QuarticFourSignedPolePair.signedOrdinateTestDeriv_eq_combinedD1
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (x : ℝ) :
    W.signedOrdinateTestDeriv x
      =
    let r := t/16
    (1/r^3) *
      compactCosineD1
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t)
        ((x-t)/r) := by
  let r := t/16
  let P1 :=
    quarticFourNormalizedProjectiveProfile W.R (1/2) W.muHalf
  let P2 :=
    quarticFourNormalizedProjectiveProfile W.R (2/3) W.muTwo
  have h1 :
      compactCosineD1
        (profileLinearCombination W.poleTwo (-W.poleHalf) P1 P2)
        ((x-t)/r)
      =
      W.poleTwo * compactCosineD1 P1 ((x-t)/r)
        + (-W.poleHalf) * compactCosineD1 P2 ((x-t)/r) := by
    unfold compactCosineD1 profileLinearCombination
    have hP1i :
        Integrable (fun u : ℝ => -P1 u * Real.sin (((x-t)/r)*u) * u) :=
      Continuous.integrable_of_hasCompactSupport
        (by dsimp [P1]; fun_prop)
        (((quarticFourNormalizedProjectiveProfile_compact W.Rpos).neg.mul_right).mul_right)
    have hP2i :
        Integrable (fun u : ℝ => -P2 u * Real.sin (((x-t)/r)*u) * u) :=
      Continuous.integrable_of_hasCompactSupport
        (by dsimp [P2]; fun_prop)
        (((quarticFourNormalizedProjectiveProfile_compact W.Rpos).neg.mul_right).mul_right)
    have hp :
        (fun u : ℝ =>
          -(W.poleTwo * P1 u + (-W.poleHalf) * P2 u)
            * Real.sin (((x-t)/r)*u) * u)
        =
        fun u =>
          W.poleTwo * (-P1 u * Real.sin (((x-t)/r)*u) * u)
            + (-W.poleHalf) *
              (-P2 u * Real.sin (((x-t)/r)*u) * u) := by
      funext u
      ring
    rw [hp, integral_add (hP1i.const_mul _) (hP2i.const_mul _),
      integral_const_mul, integral_const_mul]
  unfold QuarticFourSignedPolePair.signedOrdinateTestDeriv
    quarticFourOrdinateTestDeriv
    quarticFourSignedPoleCombinedProfile
  dsimp [r, P1, P2] at h1 ⊢
  rw [h1]
  ring

theorem QuarticFourSignedPolePair.signedOrdinateTestDeriv_hasDerivAt
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (x : ℝ) :
    HasDerivAt
      W.signedOrdinateTestDeriv
      (W.signedOrdinateTestDeriv2 x)
      x := by
  let r : ℝ := t/16
  let P :=
    quarticFourSignedPoleCombinedProfile W.R W.muHalf W.muTwo t
  have hr : 0 < r := by dsimp [r]; positivity
  have hP : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hinner :
      HasDerivAt (fun y : ℝ => (y-t)/r) (1/r) x := by
    convert ((hasDerivAt_id x).sub_const t).div_const r using 1
    ring
  have hc :=
    (compactCosineD1_deriv hP hPc ((x-t)/r)).comp x hinner
  have hs := hc.const_mul (1/r^3)
  rw [W.signedOrdinateTestDeriv_eq_combinedD1 ht]
  unfold QuarticFourSignedPolePair.signedOrdinateTestDeriv2
  dsimp [r, P] at hs ⊢
  convert hs using 1 <;> field_simp [hr.ne'] <;> ring

theorem QuarticFourSignedPolePair.signedOrdinateTestDeriv2_hasDerivAt
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (x : ℝ) :
    HasDerivAt
      W.signedOrdinateTestDeriv2
      (W.signedOrdinateTestDeriv3 x)
      x := by
  let r : ℝ := t/16
  let P :=
    quarticFourSignedPoleCombinedProfile W.R W.muHalf W.muTwo t
  have hr : 0 < r := by dsimp [r]; positivity
  have hP : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hinner :
      HasDerivAt (fun y : ℝ => (y-t)/r) (1/r) x := by
    convert ((hasDerivAt_id x).sub_const t).div_const r using 1
    ring
  have hc :=
    (compactCosineD2_deriv hP hPc ((x-t)/r)).comp x hinner
  have hs := hc.const_mul (1/r^4)
  unfold QuarticFourSignedPolePair.signedOrdinateTestDeriv2
    QuarticFourSignedPolePair.signedOrdinateTestDeriv3
  dsimp [r, P] at hs ⊢
  convert hs using 1 <;> field_simp [hr.ne'] <;> ring

theorem QuarticFourSignedPolePair.signedOrdinateTestDeriv3_hasDerivAt
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (x : ℝ) :
    HasDerivAt
      W.signedOrdinateTestDeriv3
      (W.signedOrdinateTestDeriv4 x)
      x := by
  let r : ℝ := t/16
  let P :=
    quarticFourSignedPoleCombinedProfile W.R W.muHalf W.muTwo t
  have hr : 0 < r := by dsimp [r]; positivity
  have hP : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hinner :
      HasDerivAt (fun y : ℝ => (y-t)/r) (1/r) x := by
    convert ((hasDerivAt_id x).sub_const t).div_const r using 1
    ring
  have hc :=
    (compactCosineD3_deriv hP hPc ((x-t)/r)).comp x hinner
  have hs := hc.const_mul (1/r^5)
  unfold QuarticFourSignedPolePair.signedOrdinateTestDeriv3
    QuarticFourSignedPolePair.signedOrdinateTestDeriv4
  dsimp [r, P] at hs ⊢
  convert hs using 1 <;> field_simp [hr.ne'] <;> ring

theorem QuarticFourSignedPolePair.signedOrdinateTest_center_zero
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.signedOrdinateTest t = 0 := by
  rw [W.signedOrdinateTest_eq_combinedCosine]
  dsimp
  rw [sub_self, zero_div,
    compactCosine_zero_of_profileZerothMoment_zero
      (quarticFourSignedPoleCombinedProfile_zeroth_zero W.Rpos)]
  ring

theorem QuarticFourSignedPolePair.signedOrdinateTestDeriv_center_zero
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.signedOrdinateTestDeriv t = 0 := by
  rw [W.signedOrdinateTestDeriv_eq_combinedD1 ht]
  dsimp
  unfold compactCosineD1
  simp

theorem QuarticFourSignedPolePair.signedOrdinateTestDeriv2_center_zero
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.signedOrdinateTestDeriv2 t = 0 := by
  unfold QuarticFourSignedPolePair.signedOrdinateTestDeriv2
  dsimp
  rw [sub_self, zero_div]
  unfold compactCosineD2 profileSecondMoment
  simp only [zero_mul, Real.cos_zero, mul_one]
  rw [show
      (∫ u : ℝ,
        -quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t u * u^2)
        =
      - profileSecondMoment
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t) by
        rw [integral_neg]
        rfl,
      quarticFourSignedPoleCombinedProfile_second_zero
        W.Rpos W.J2Half W.J2Two]
  ring

theorem QuarticFourSignedPolePair.signedOrdinateTestDeriv3_center_zero
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.signedOrdinateTestDeriv3 t = 0 := by
  unfold QuarticFourSignedPolePair.signedOrdinateTestDeriv3
  dsimp
  rw [sub_self, zero_div]
  unfold compactCosineD3
  simp

theorem QuarticFourSignedPolePair.signedOrdinateTestDeriv4_center
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.signedOrdinateTestDeriv4 t
      =
    -4 * W.targetStrength / (t/16)^6 := by
  unfold QuarticFourSignedPolePair.signedOrdinateTestDeriv4
  dsimp
  rw [sub_self, zero_div]
  unfold compactCosineD4
  simp only [zero_mul, Real.cos_zero, mul_one]
  rw [show
      (∫ u : ℝ,
        quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t u * u^4)
        =
      profileFourthMoment
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t) by rfl,
      quarticFourSignedPoleCombinedProfile_fourth W.Rpos]
  field_simp [show t/16 ≠ 0 by positivity]
  ring

theorem QuarticFourSignedPolePair.signedOrdinateTestDeriv4_center_neg
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.signedOrdinateTestDeriv4 t < 0 := by
  rw [W.signedOrdinateTestDeriv4_center ht]
  have hr6 : 0 < (t/16)^6 := by positivity
  have hs := W.targetStrength_pos
  exact div_neg_of_neg_of_pos (by nlinarith) hr6

def QuarticFourSignedPolePair.signedZetaMuWindowResidual
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (A B : ℝ) : ℝ :=
  zetaWindowMinusMuPair A B W.signedOrdinateTest

/--
Exact finite-window Abel representation on the actual signed G3 test.
-/
theorem quarticFourSignedPoleZetaMuWindowResidual_eq_discrepancyAbel
    {t A B : ℝ}
    (ht : 0 < t)
    (hAB : A <= B)
    (W : QuarticFourSignedPolePair t) :
    W.signedZetaMuWindowResidual A B
      =
    W.signedOrdinateTest B
      * zetaMuCumulativeDiscrepancy A B
      -
    ∫ x in A..B,
      W.signedOrdinateTestDeriv x
        * zetaMuCumulativeDiscrepancy A x := by
  unfold QuarticFourSignedPolePair.signedZetaMuWindowResidual
  exact
    zetaWindowMinusMuPair_eq_discrepancyAbel
      (A:=A) (B:=B)
      (phi:=W.signedOrdinateTest)
      (phi':=W.signedOrdinateTestDeriv)
      hAB
      (by
        intro x hx
        exact W.signedOrdinateTest_hasDerivAt ht x)
      (W.signedOrdinateTestDeriv_intervalIntegrable ht A B)

end Synthesis

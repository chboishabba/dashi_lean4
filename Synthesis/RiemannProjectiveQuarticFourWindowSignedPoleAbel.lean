import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleNMu
import Synthesis.RiemannZetaMuExactAbel
import Synthesis.RiemannCompactCosineFourthDerivative
import Synthesis.RiemannProjectiveQuarticDerivativeSign
import Synthesis.RiemannZetaMuNegativeHeightReflection

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


/--
The cosine fifth-moment Lipschitz constant is dominated by the cosh envelope
already used to define the quantitative target radius.
-/
theorem compactProfileAbsMoment_five_le_compactCoshFourthLipschitzConstant
    {P : ℝ -> ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P) :
    compactProfileAbsMoment P 5
      <= compactCoshFourthLipschitzConstant P := by
  unfold compactProfileAbsMoment compactCoshFourthLipschitzConstant
  have hleft :
      Integrable (fun u : ℝ => |P u| * |u|^5) :=
    compactProfile_absMoment_integrable hP hPc 5
  have hright :=
    compactCoshFourthLipschitzMajorant_integrable hP hPc
  apply integral_mono hleft hright
  intro u
  have hc : 1 <= Real.cosh |u| := Real.one_le_cosh _
  have hP0 : 0 <= |P u| := abs_nonneg _
  have hu0 : 0 <= |u|^5 := pow_nonneg (abs_nonneg u) _
  nlinarith

/--
Quantitative radial derivative sign for a compact cosine transform with
vanishing quadratic moment and negative quartic margin.

The radius is the same fourth-order radius built from the cosh envelope K.
-/
theorem compactCosineD1_radial_neg_of_quantitative_quartic_margin
    {P : ℝ -> ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    {m : ℝ}
    (hm : 0 < m)
    (hM2 : profileSecondMoment P = 0)
    (hM4 : profileFourthMoment P <= -m) :
    ∀ q : ℝ,
      0 < |q| ->
      |q| <
        quantitativeFourthOrderRadius
          m (compactCoshFourthLipschitzConstant P) ->
      q * compactCosineD1 P q < 0 := by
  let K := compactCoshFourthLipschitzConstant P
  let eps := quantitativeFourthOrderRadius m K
  have hK : 0 <= K :=
    compactCoshFourthLipschitzConstant_nonneg P
  have heps : 0 < eps :=
    quantitativeFourthOrderRadius_pos hm hK
  have hKeps : K * eps < m/2 :=
    quantitativeFourthOrderRadius_mul_K_le_half hm hK
  have hM5 :
      compactProfileAbsMoment P 5 <= K :=
    compactProfileAbsMoment_five_le_compactCoshFourthLipschitzConstant hP hPc
  have hD20 : compactCosineD2 P 0 = 0 := by
    unfold compactCosineD2 profileSecondMoment at *
    simpa using hM2
  have hD30 : compactCosineD3 P 0 = 0 :=
    compactCosineD3_zero P
  have hD40 : compactCosineD4 P 0 <= -m := by
    unfold compactCosineD4 profileFourthMoment at *
    simpa using hM4

  have hD4neg :
      ∀ x : ℝ, 0 < x -> x < eps ->
        compactCosineD4 P x < 0 := by
    intro x hx0 hxe
    have hxone : |x| <= 1 := by
      rw [abs_of_pos hx0]
      exact hxe.le.trans (quantitativeFourthOrderRadius_le_one m K)
    have hvar0 :=
      compactCosineD4_lipschitz hP hPc 0 x
    have hvar :
        |compactCosineD4 P x - compactCosineD4 P 0|
          <= K * |x| := by
      have hm5non : 0 <= compactProfileAbsMoment P 5 := by
        unfold compactProfileAbsMoment
        positivity
      calc
        |compactCosineD4 P x - compactCosineD4 P 0|
          <= compactProfileAbsMoment P 5 * |x| := by
            simpa using hvar0
        _ <= K * |x| :=
          mul_le_mul_of_nonneg_right hM5 (abs_nonneg x)
    have hupp :
        compactCosineD4 P x - compactCosineD4 P 0
          <= K*x := by
      have := (abs_le.mp hvar).2
      simpa [abs_of_pos hx0] using this
    have hKx : K*x <= K*eps :=
      mul_le_mul_of_nonneg_left hxe.le hK
    linarith

  have hD3cont : Continuous (compactCosineD3 P) :=
    continuous_of_forall_continuousAt fun x =>
      (compactCosineD3_deriv hP hPc x).continuousAt
  have hD2cont : Continuous (compactCosineD2 P) :=
    continuous_of_forall_continuousAt fun x =>
      (compactCosineD2_deriv hP hPc x).continuousAt
  have hD1cont : Continuous (compactCosineD1 P) :=
    continuous_of_forall_continuousAt fun x =>
      (compactCosineD1_deriv hP hPc x).continuousAt

  have hanti3 :
      StrictAntiOn (compactCosineD3 P) (Set.Icc 0 eps) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 eps)
      hD3cont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(compactCosineD3_deriv hP hPc x).deriv]
    exact hD4neg x hx.1 hx.2

  have hD3neg :
      ∀ x : ℝ, 0 < x -> x < eps ->
        compactCosineD3 P x < 0 := by
    intro x hx0 hxe
    have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) eps := ⟨le_rfl,heps.le⟩
    have hx : x ∈ Set.Icc (0:ℝ) eps := ⟨hx0.le,hxe.le⟩
    have h := hanti3 h0 hx hx0
    rw [hD30] at h
    exact h

  have hanti2 :
      StrictAntiOn (compactCosineD2 P) (Set.Icc 0 eps) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 eps)
      hD2cont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(compactCosineD2_deriv hP hPc x).deriv]
    exact hD3neg x hx.1 hx.2

  have hD2neg :
      ∀ x : ℝ, 0 < x -> x < eps ->
        compactCosineD2 P x < 0 := by
    intro x hx0 hxe
    have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) eps := ⟨le_rfl,heps.le⟩
    have hx : x ∈ Set.Icc (0:ℝ) eps := ⟨hx0.le,hxe.le⟩
    have h := hanti2 h0 hx hx0
    rw [hD20] at h
    exact h

  have hanti1 :
      StrictAntiOn (compactCosineD1 P) (Set.Icc 0 eps) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 eps)
      hD1cont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(compactCosineD1_deriv hP hPc x).deriv]
    exact hD2neg x hx.1 hx.2

  have hright :
      ∀ x : ℝ, 0 < x -> x < eps ->
        compactCosineD1 P x < 0 := by
    intro x hx0 hxe
    have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) eps := ⟨le_rfl,heps.le⟩
    have hx : x ∈ Set.Icc (0:ℝ) eps := ⟨hx0.le,hxe.le⟩
    have h := hanti1 h0 hx hx0
    rw [compactCosineD1_zero P] at h
    exact h

  intro q hq0 hqe
  by_cases hq : 0 <= q
  · have hqpos : 0 < q := by
      rw [abs_of_nonneg hq] at hq0
      exact hq0
    have hd := hright q hqpos (by simpa [abs_of_pos hqpos] using hqe)
    exact mul_neg_of_pos_of_neg hqpos hd
  · have hqneg : q < 0 := lt_of_not_ge hq
    have hqpos : 0 < -q := by linarith
    have hdneg :=
      hright (-q) hqpos
        (by simpa [abs_of_neg hqneg] using hqe)
    have hodd := compactCosineD1_odd P q
    have hdpos : 0 < compactCosineD1 P q := by
      rw [show q = -(-q) by ring, compactCosineD1_odd]
      linarith
    exact mul_neg_of_neg_of_pos hqneg hdpos

/--
The exact signed G3 test has the favorable quartic radial derivative sign on
the same quantitative radius used by G1.
-/
theorem QuarticFourSignedPolePair.signedOrdinateTestDeriv_radial_neg
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    {x : ℝ}
    (hx0 : 0 < |x-t|)
    (hx :
      |x-t| < (t/16) * W.quantitativeTargetRadius) :
    (x-t) * W.signedOrdinateTestDeriv x < 0 := by
  let r : ℝ := t/16
  let P :=
    quarticFourSignedPoleCombinedProfile W.R W.muHalf W.muTwo t
  let q : ℝ := (x-t)/r
  have hr : 0 < r := by dsimp [r]; positivity
  have hP : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hq0 : 0 < |q| := by
    dsimp [q]
    rw [abs_div, abs_of_pos hr]
    positivity
  have hq :
      |q| < W.quantitativeTargetRadius := by
    dsimp [q]
    rw [abs_div, abs_of_pos hr]
    rw [div_lt_iff₀ hr]
    simpa [r] using hx
  have hrad :=
    compactCosineD1_radial_neg_of_quantitative_quartic_margin
      hP hPc
      (m:=4*W.targetStrength)
      (by nlinarith [W.targetStrength_pos])
      (quarticFourSignedPoleCombinedProfile_second_zero
        W.Rpos W.J2Half W.J2Two)
      (by
        rw [quarticFourSignedPoleCombinedProfile_fourth W.Rpos])
      q hq0
      (by
        simpa [QuarticFourSignedPolePair.quantitativeTargetRadius, P]
          using hq)
  rw [W.signedOrdinateTestDeriv_eq_combinedD1 ht]
  dsimp [q, r, P] at hrad ⊢
  have hr3 : 0 < r^3 := by positivity
  have hscale :
      x-t = r * ((x-t)/r) := by
    field_simp [hr.ne']
  rw [hscale]
  have hfac : 0 < r * (1/r^3) := by positivity
  nlinarith


/-!
## Centred discrepancy and finite two-sided Abel identity

For x<t we deliberately reverse the finite zero window rather than relying on
any convention for `Ncount t x`.
-/

def centeredZetaMuDiscrepancy (t x : ℝ) : ℝ :=
  if h : t <= x then
    zetaMuCumulativeDiscrepancy t x
  else
    - zetaMuCumulativeDiscrepancy x t

theorem centeredZetaMuDiscrepancy_of_le
    {t x : ℝ} (h : t <= x) :
    centeredZetaMuDiscrepancy t x
      = zetaMuCumulativeDiscrepancy t x := by
  simp [centeredZetaMuDiscrepancy, h]

theorem centeredZetaMuDiscrepancy_of_lt
    {t x : ℝ} (h : x < t) :
    centeredZetaMuDiscrepancy t x
      = - zetaMuCumulativeDiscrepancy x t := by
  simp [centeredZetaMuDiscrepancy, not_le.mpr h]

theorem centeredZetaMuDiscrepancy_self (t : ℝ) :
    centeredZetaMuDiscrepancy t t = 0 := by
  simp [centeredZetaMuDiscrepancy,
    zetaMuCumulativeDiscrepancy,
    zetaMuPrimitive_self]

/--
Finite two-sided signed residual around the target ordinate.
-/
def QuarticFourSignedPolePair.signedCenteredWindowResidual
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (A B : ℝ) : ℝ :=
  W.signedZetaMuWindowResidual A t
    + W.signedZetaMuWindowResidual t B

/--
Exact right-hand centred Abel identity.  The lower endpoint vanishes because
Psi_t(t)=0.
-/
theorem QuarticFourSignedPolePair.signedZetaMuWindowResidual_right_eq_centeredAbel
    {t B : ℝ}
    (ht : 0 < t)
    (hB : t <= B)
    (W : QuarticFourSignedPolePair t) :
    W.signedZetaMuWindowResidual t B
      =
    W.signedOrdinateTest B
      * centeredZetaMuDiscrepancy t B
      -
    ∫ x in t..B,
      W.signedOrdinateTestDeriv x
        * centeredZetaMuDiscrepancy t x := by
  rw [quarticFourSignedPoleZetaMuWindowResidual_eq_discrepancyAbel
      ht hB W]
  rw [centeredZetaMuDiscrepancy_of_le hB]
  apply congrArg (fun y : ℝ =>
    W.signedOrdinateTest B * zetaMuCumulativeDiscrepancy t B - y)
  apply intervalIntegral.integral_congr
  intro x hx
  have htx : t <= x := by
    simpa [Set.uIcc_of_le hB] using hx.1
  rw [centeredZetaMuDiscrepancy_of_le htx]

/--
Cumulative discrepancy is additive on ordered finite windows.
-/
theorem zetaMuCumulativeDiscrepancy_add
    {A B C : ℝ}
    (hAB : A <= B)
    (hBC : B <= C) :
    zetaMuCumulativeDiscrepancy A C
      =
    zetaMuCumulativeDiscrepancy A B
      + zetaMuCumulativeDiscrepancy B C := by
  rw [zetaMuCumulativeDiscrepancy_endpoint,
      zetaMuCumulativeDiscrepancy_endpoint,
      zetaMuCumulativeDiscrepancy_endpoint]
  unfold zetaMuWindowDiscrepancy
  have hN := Zeta23.Ncount_add
    (a:=A) (b:=B) (c:=C) hAB hBC
  have hmu1 :
      IntervalIntegrable Zeta23.mu volume A B :=
    Zeta23.gammaFacts.smooth.continuous.intervalIntegrable A B
  have hmu2 :
      IntervalIntegrable Zeta23.mu volume B C :=
    Zeta23.gammaFacts.smooth.continuous.intervalIntegrable B C
  have hmu :=
    intervalIntegral.integral_add_adjacent_intervals hmu1 hmu2
  rw [show
      (zetaZeroConfig.N A C : ℝ)
        =
      (zetaZeroConfig.N A B : ℝ)
        + (zetaZeroConfig.N B C : ℝ) by
        exact_mod_cast hN,
      hmu]
  ring

theorem zetaMuCumulativeDiscrepancy_left_eq_centered
    {A t x : ℝ}
    (hAx : A <= x)
    (hxt : x <= t) :
    zetaMuCumulativeDiscrepancy A x
      =
    zetaMuCumulativeDiscrepancy A t
      + centeredZetaMuDiscrepancy t x := by
  have hadd :=
    zetaMuCumulativeDiscrepancy_add hAx hxt
  by_cases hEq : x = t
  · subst x
    simp [centeredZetaMuDiscrepancy_self] at *
  · have hlt : x < t := lt_of_le_of_ne hxt hEq
    rw [centeredZetaMuDiscrepancy_of_lt hlt]
    linarith

/--
Exact left-hand centred Abel identity.

The finite left boundary survives explicitly and is the term which must vanish
under global exhaustion.
-/
theorem QuarticFourSignedPolePair.signedZetaMuWindowResidual_left_eq_centeredAbel
    {A t : ℝ}
    (ht : 0 < t)
    (hA : A <= t)
    (W : QuarticFourSignedPolePair t) :
    W.signedZetaMuWindowResidual A t
      =
    W.signedOrdinateTest A
      * zetaMuCumulativeDiscrepancy A t
      -
    ∫ x in A..t,
      W.signedOrdinateTestDeriv x
        * centeredZetaMuDiscrepancy t x := by
  rw [quarticFourSignedPoleZetaMuWindowResidual_eq_discrepancyAbel
      ht hA W]
  rw [W.signedOrdinateTest_center_zero ht]
  simp only [zero_mul, zero_sub]

  have hderInt :=
    W.signedOrdinateTestDeriv_intervalIntegrable ht A t
  have hN :
      IntervalIntegrable
        (fun x =>
          W.signedOrdinateTestDeriv x * (Ncount A x : ℝ))
        volume A t :=
    phi_mul_Ncount_intervalIntegrable hA hderInt
  have hM :
      IntervalIntegrable
        (fun x =>
          W.signedOrdinateTestDeriv x * zetaMuPrimitive A x)
        volume A t :=
    phi_mul_zetaMuPrimitive_intervalIntegrable hderInt
  have hD :
      IntervalIntegrable
        (fun x =>
          W.signedOrdinateTestDeriv x
            * zetaMuCumulativeDiscrepancy A x)
        volume A t := by
    unfold zetaMuCumulativeDiscrepancy
    simpa [mul_sub] using hN.sub hM
  have hconst :
      IntervalIntegrable
        (fun x =>
          W.signedOrdinateTestDeriv x
            * zetaMuCumulativeDiscrepancy A t)
        volume A t := by
    simpa [mul_comm] using
      hderInt.const_mul (zetaMuCumulativeDiscrepancy A t)
  have hcenter :
      IntervalIntegrable
        (fun x =>
          W.signedOrdinateTestDeriv x
            * centeredZetaMuDiscrepancy t x)
        volume A t := by
    have hsub := hD.sub hconst
    refine hsub.congr_ae ?_
    rw [Filter.EventuallyEq,
      MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with x hx
    have hxI : x ∈ Set.Icc A t := by
      rw [Set.uIoc_of_le hA] at hx
      exact ⟨hx.1.le, hx.2⟩
    rw [zetaMuCumulativeDiscrepancy_left_eq_centered
      hxI.1 hxI.2]
    ring

  have hrewrite :
      (∫ x in A..t,
        W.signedOrdinateTestDeriv x
          * zetaMuCumulativeDiscrepancy A x)
        =
      (∫ x in A..t,
        W.signedOrdinateTestDeriv x
          * zetaMuCumulativeDiscrepancy A t)
        +
      (∫ x in A..t,
        W.signedOrdinateTestDeriv x
          * centeredZetaMuDiscrepancy t x) := by
    rw [← intervalIntegral.integral_add hconst hcenter]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxI : x ∈ Set.Icc A t := by
      simpa [Set.uIcc_of_le hA] using hx
    rw [zetaMuCumulativeDiscrepancy_left_eq_centered
      hxI.1 hxI.2]
    ring
  rw [hrewrite]

  have hFTC :=
    intervalIntegral.integral_deriv_eq_sub'
      (fun x hx => W.signedOrdinateTest_hasDerivAt ht x)
      hderInt
  rw [W.signedOrdinateTest_center_zero ht] at hFTC
  have hconstValue :
      (∫ x in A..t,
        W.signedOrdinateTestDeriv x
          * zetaMuCumulativeDiscrepancy A t)
        =
      - W.signedOrdinateTest A
        * zetaMuCumulativeDiscrepancy A t := by
    rw [← intervalIntegral.integral_const_mul]
    rw [hFTC]
    ring
  rw [hconstValue]
  ring

/--
Exact finite two-sided centred Abel identity around t.
-/
theorem QuarticFourSignedPolePair.signedCenteredWindowResidual_eq_centeredAbel
    {A t B : ℝ}
    (ht : 0 < t)
    (hA : A <= t)
    (hB : t <= B)
    (W : QuarticFourSignedPolePair t) :
    W.signedCenteredWindowResidual A B
      =
    W.signedOrdinateTest A
      * zetaMuCumulativeDiscrepancy A t
      +
    W.signedOrdinateTest B
      * centeredZetaMuDiscrepancy t B
      -
    (∫ x in A..t,
      W.signedOrdinateTestDeriv x
        * centeredZetaMuDiscrepancy t x)
      -
    (∫ x in t..B,
      W.signedOrdinateTestDeriv x
        * centeredZetaMuDiscrepancy t x) := by
  unfold QuarticFourSignedPolePair.signedCenteredWindowResidual
  rw [W.signedZetaMuWindowResidual_left_eq_centeredAbel ht hA,
      W.signedZetaMuWindowResidual_right_eq_centeredAbel ht hB]
  ring


/-!
## Global centred-Abel exhaustion compiler

This record is intentionally analytic but not number-theoretic.  It says
exactly what remains to pass the finite centred identity to the global
`signedNMuPair` scalar.
-/

def QuarticFourSignedPolePair.centeredAbelIntegrand
    {t : ℝ} (W : QuarticFourSignedPolePair t) (x : ℝ) : ℝ :=
  W.signedOrdinateTestDeriv x * centeredZetaMuDiscrepancy t x

def QuarticFourSignedPolePair.leftCenteredAbelPartial
    {t : ℝ} (W : QuarticFourSignedPolePair t) (n : ℕ) : ℝ :=
  ∫ x in (t - n)..t, W.centeredAbelIntegrand x

def QuarticFourSignedPolePair.rightCenteredAbelPartial
    {t : ℝ} (W : QuarticFourSignedPolePair t) (n : ℕ) : ℝ :=
  ∫ x in t..(t + n), W.centeredAbelIntegrand x

def QuarticFourSignedPolePair.leftCenteredBoundary
    {t : ℝ} (W : QuarticFourSignedPolePair t) (n : ℕ) : ℝ :=
  W.signedOrdinateTest (t - n)
    * zetaMuCumulativeDiscrepancy (t - n) t

def QuarticFourSignedPolePair.rightCenteredBoundary
    {t : ℝ} (W : QuarticFourSignedPolePair t) (n : ℕ) : ℝ :=
  W.signedOrdinateTest (t + n)
    * centeredZetaMuDiscrepancy t (t + n)

def QuarticFourSignedPolePair.centeredWindowResidualAt
    {t : ℝ} (W : QuarticFourSignedPolePair t) (n : ℕ) : ℝ :=
  W.signedCenteredWindowResidual (t - n) (t + n)

record QuarticFourSignedPolePair.CenteredAbelExhaustion
    {t : ℝ} (W : QuarticFourSignedPolePair t) : Type where
  field
    leftLimit : ℝ
    rightLimit : ℝ

    residual_tendsto :
      Tendsto W.centeredWindowResidualAt atTop
        (𝓝 W.signedNMuPair)

    leftBoundary_tendsto_zero :
      Tendsto W.leftCenteredBoundary atTop (𝓝 0)

    rightBoundary_tendsto_zero :
      Tendsto W.rightCenteredBoundary atTop (𝓝 0)

    leftIntegral_tendsto :
      Tendsto W.leftCenteredAbelPartial atTop (𝓝 leftLimit)

    rightIntegral_tendsto :
      Tendsto W.rightCenteredAbelPartial atTop (𝓝 rightLimit)

open QuarticFourSignedPolePair.CenteredAbelExhaustion

/--
Finite centred Abel identity on the canonical symmetric exhaustion.
-/
theorem QuarticFourSignedPolePair.centeredWindowResidualAt_eq
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.centeredWindowResidualAt n
      =
    W.leftCenteredBoundary n
      + W.rightCenteredBoundary n
      - W.leftCenteredAbelPartial n
      - W.rightCenteredAbelPartial n := by
  unfold QuarticFourSignedPolePair.centeredWindowResidualAt
    QuarticFourSignedPolePair.leftCenteredBoundary
    QuarticFourSignedPolePair.rightCenteredBoundary
    QuarticFourSignedPolePair.leftCenteredAbelPartial
    QuarticFourSignedPolePair.rightCenteredAbelPartial
    QuarticFourSignedPolePair.centeredAbelIntegrand
  have hA : t - n <= t := by
    norm_num
  have hB : t <= t + n := by
    norm_num
  simpa using
    W.signedCenteredWindowResidual_eq_centeredAbel
      ht hA hB

/--
Global centred Abel compiler.

Once the standard exhaustion limits are paid, the literal global signed N-mu
scalar is exactly minus the two centred derivative-correlation limits.
-/
theorem QuarticFourSignedPolePair.signedNMuPair_eq_centeredAbel_limits
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (E : W.CenteredAbelExhaustion) :
    W.signedNMuPair = - E.leftLimit - E.rightLimit := by
  have hfinite :
      (fun n : ℕ => W.centeredWindowResidualAt n)
        =
      fun n =>
        W.leftCenteredBoundary n
          + W.rightCenteredBoundary n
          - W.leftCenteredAbelPartial n
          - W.rightCenteredAbelPartial n := by
    funext n
    exact W.centeredWindowResidualAt_eq ht n
  have hrhs :
      Tendsto
        (fun n =>
          W.leftCenteredBoundary n
            + W.rightCenteredBoundary n
            - W.leftCenteredAbelPartial n
            - W.rightCenteredAbelPartial n)
        atTop
        (𝓝 (0 + 0 - E.leftLimit - E.rightLimit)) :=
    ((E.leftBoundary_tendsto_zero.add
      E.rightBoundary_tendsto_zero).sub
      E.leftIntegral_tendsto).sub
      E.rightIntegral_tendsto
  have hres :
      Tendsto W.centeredWindowResidualAt atTop
        (𝓝 (0 + 0 - E.leftLimit - E.rightLimit)) := by
    rw [hfinite]
    exact hrhs
  have huniq :=
    tendsto_nhds_unique E.residual_tendsto hres
  simpa using huniq

/--
The joint G3 analytic functional after centred-Abel exhaustion.
-/
def QuarticFourSignedPolePair.centeredCompletedResidual
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (leftAbel rightAbel : ℝ) : ℝ :=
  -(1/2 : ℝ) * leftAbel
    - (1/2 : ℝ) * rightAbel
    + W.signedHorizontalRemainder

theorem QuarticFourSignedPolePair.completedSignedResidual_eq_centered
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (E : W.CenteredAbelExhaustion) :
    W.completedSignedResidual
      =
    W.centeredCompletedResidual E.leftLimit E.rightLimit := by
  unfold QuarticFourSignedPolePair.completedSignedResidual
    QuarticFourSignedPolePair.centeredCompletedResidual
  rw [W.signedNMuPair_eq_centeredAbel_limits ht E]
  ring

/--
Diagnostic no-go: on the quantitative quartic band, an outward-pointing
centred discrepancy has the wrong sign for making the Abel contribution
negative.
-/
theorem QuarticFourSignedPolePair.outwardCenteredDiscrepancy_mul_deriv_nonpos
    {t x : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hx0 : 0 < |x-t|)
    (hx :
      |x-t| < (t/16) * W.quantitativeTargetRadius)
    (hout :
      0 <= (x-t) * centeredZetaMuDiscrepancy t x) :
    W.signedOrdinateTestDeriv x
        * centeredZetaMuDiscrepancy t x
      <= 0 := by
  have hrad :=
    W.signedOrdinateTestDeriv_radial_neg ht hx0 hx
  by_cases hxt : 0 < x-t
  · have hE : 0 <= centeredZetaMuDiscrepancy t x := by
      nlinarith
    have hD : W.signedOrdinateTestDeriv x < 0 := by
      nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg hD.le hE
  · have hxt' : x-t < 0 := by
      have hne : x-t ≠ 0 := by
        intro hz
        rw [hz, abs_zero] at hx0
        linarith
      exact lt_of_not_ge (fun h => hxt (lt_of_le_of_ne h (Ne.symm hne)))
    have hE : centeredZetaMuDiscrepancy t x <= 0 := by
      nlinarith
    have hD : 0 < W.signedOrdinateTestDeriv x := by
      nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos hD.le hE


/-!
## Right-tail decay on the exact signed Psi test
-/

def QuarticFourSignedPolePair.signedOrdinateCurvature
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  |W.poleTwo| *
      genericProjectiveBaseCurvature
        (quarticFourWindowProfile W.R (1/2) W.muHalf)
    +
  |W.poleHalf| *
      genericProjectiveBaseCurvature
        (quarticFourWindowProfile W.R (2/3) W.muTwo)

theorem QuarticFourSignedPolePair.signedOrdinateCurvature_nonneg
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    0 <= W.signedOrdinateCurvature := by
  unfold QuarticFourSignedPolePair.signedOrdinateCurvature
  positivity

theorem quarticFourOrdinateTest_abs_le_gap_sq
    {R lam mu t x : ℝ}
    (hR : 0 < R)
    (ht : 0 < t)
    (hxt : x ≠ t) :
    |quarticFourOrdinateTest R lam mu t x|
      <=
    genericProjectiveBaseCurvature
        (quarticFourWindowProfile R lam mu)
      / (x-t)^2 := by
  let r : ℝ := t/16
  let G := quarticFourWindowProfile R lam mu
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hq : (x-t)/r ≠ 0 := by
    exact div_ne_zero (sub_ne_zero.mpr hxt) hr.ne'
  have hdec :=
    genericProjectiveBaseKernel_abs_le_invSq
      (G:=G)
      (quarticFourWindowProfile_contDiff
        (lam:=lam) (mu:=mu) hR)
      (quarticFourWindowProfile_compact
        (lam:=lam) (mu:=mu) hR)
      hq
  unfold quarticFourOrdinateTest
  dsimp [r, G]
  rw [abs_mul, abs_of_pos (by positivity : 0 < 1/(t/16)^2)]
  have hscale :=
    mul_le_mul_of_nonneg_left hdec (by positivity : 0 <= 1/(t/16)^2)
  calc
    (1/(t/16)^2)
        * |genericProjectiveBaseKernel
            (quarticFourWindowProfile R lam mu) 1
            ((x-t)/(t/16))|
      <=
    (1/(t/16)^2)
      * (genericProjectiveBaseCurvature
          (quarticFourWindowProfile R lam mu)
        / (((x-t)/(t/16))^2)) := hscale
    _ =
    genericProjectiveBaseCurvature
        (quarticFourWindowProfile R lam mu)
      / (x-t)^2 := by
        field_simp [sub_ne_zero.mpr hxt, ne_of_gt ht]
        ring

theorem QuarticFourSignedPolePair.signedOrdinateTest_abs_le_gap_sq
    {t x : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hxt : x ≠ t) :
    |W.signedOrdinateTest x|
      <= W.signedOrdinateCurvature / (x-t)^2 := by
  have h1 :=
    quarticFourOrdinateTest_abs_le_gap_sq
      (R:=W.R) (lam:=(1/2 : ℝ)) (mu:=W.muHalf)
      W.Rpos ht hxt
  have h2 :=
    quarticFourOrdinateTest_abs_le_gap_sq
      (R:=W.R) (lam:=(2/3 : ℝ)) (mu:=W.muTwo)
      W.Rpos ht hxt
  unfold QuarticFourSignedPolePair.signedOrdinateTest
    QuarticFourSignedPolePair.ordinateTestHalf
    QuarticFourSignedPolePair.ordinateTestTwo
    QuarticFourSignedPolePair.signedOrdinateCurvature
  calc
    |W.poleTwo *
        quarticFourOrdinateTest W.R (1/2) W.muHalf t x
      + (-W.poleHalf) *
        quarticFourOrdinateTest W.R (2/3) W.muTwo t x|
      <=
    |W.poleTwo *
        quarticFourOrdinateTest W.R (1/2) W.muHalf t x|
      +
    |(-W.poleHalf) *
        quarticFourOrdinateTest W.R (2/3) W.muTwo t x| :=
      abs_add _ _
    _ =
    |W.poleTwo| *
        |quarticFourOrdinateTest W.R (1/2) W.muHalf t x|
      +
    |W.poleHalf| *
        |quarticFourOrdinateTest W.R (2/3) W.muTwo t x| := by
      rw [abs_mul, abs_mul, abs_neg]
    _ <=
    |W.poleTwo| *
      (genericProjectiveBaseCurvature
        (quarticFourWindowProfile W.R (1/2) W.muHalf)
        / (x-t)^2)
      +
    |W.poleHalf| *
      (genericProjectiveBaseCurvature
        (quarticFourWindowProfile W.R (2/3) W.muTwo)
        / (x-t)^2) := by
      gcongr
    _ =
    (|W.poleTwo| *
        genericProjectiveBaseCurvature
          (quarticFourWindowProfile W.R (1/2) W.muHalf)
      +
      |W.poleHalf| *
        genericProjectiveBaseCurvature
          (quarticFourWindowProfile W.R (2/3) W.muTwo))
      / (x-t)^2 := by ring

/--
The exact right Abel boundary has the expected logarithmic-over-quadratic
envelope from the theorem-bearing arbitrary-endpoint discrepancy bound.
-/
theorem exists_quarticFourSignedPole_rightBoundary_gap_sq_bound :
    ∃ C T0 : ℝ, 0 <= C ∧
      ∀ {t : ℝ},
        (W : QuarticFourSignedPolePair t) ->
        max T0 4 <= t ->
        ∀ B : ℝ,
          t < B ->
          |W.signedOrdinateTest B
            * centeredZetaMuDiscrepancy t B|
          <=
          (W.signedOrdinateCurvature / (B-t)^2)
            *
          (C * (Real.log (t+3) + Real.log (B+4))) := by
  obtain ⟨C,T0,hC,hD⟩ :=
    exists_zetaMuWindowDiscrepancy_arbitrary_bound
  refine ⟨C,T0,hC,?_⟩
  intro t W ht B htB
  have htpos : 0 < t := by
    have ht4 : 4 <= t := (le_max_right T0 4).trans ht
    linarith
  have hphi :=
    W.signedOrdinateTest_abs_le_gap_sq htpos (ne_of_gt htB)
  have hdisc :
      |centeredZetaMuDiscrepancy t B|
        <= C * (Real.log (t+3) + Real.log (B+4)) := by
    rw [centeredZetaMuDiscrepancy_of_le htB.le,
        zetaMuCumulativeDiscrepancy_endpoint]
    exact hD t B ht htB
  have hfactor :
      0 <= W.signedOrdinateCurvature / (B-t)^2 := by
    have hcurv := W.signedOrdinateCurvature_nonneg
    positivity
  rw [abs_mul]
  exact mul_le_mul hphi hdisc (abs_nonneg _) hfactor


/-!
## Far-left centred boundary envelope
-/

/--
The t-anchored cumulative discrepancy on a far-negative left endpoint is the
reflected growing segment plus the fixed central segment [-t,t].
-/
theorem zetaMuCumulativeDiscrepancy_farLeft_split
    {A t : ℝ}
    (ht : 0 <= t)
    (hA : A <= -t) :
    zetaMuCumulativeDiscrepancy A t
      =
    zetaMuWindowDiscrepancy A (-t)
      + zetaMuWindowDiscrepancy (-t) t := by
  have hadd :=
    zetaMuCumulativeDiscrepancy_add hA (by linarith : -t <= t)
  rw [zetaMuCumulativeDiscrepancy_endpoint,
      zetaMuCumulativeDiscrepancy_endpoint,
      zetaMuCumulativeDiscrepancy_endpoint] at hadd
  exact hadd

/--
Explicit logarithmic-over-quadratic envelope for the actual left centred Abel
boundary.

The central discrepancy D(-t,t) is fixed once t is fixed; all A-growth has
been reflected to the positive RvM window.
-/
theorem exists_quarticFourSignedPole_leftBoundary_gap_sq_log_bound :
    ∃ C T0 A0 : ℝ, 0 <= C ∧ 1 <= A0 ∧
      ∀ {t : ℝ},
        (W : QuarticFourSignedPolePair t) ->
        max T0 4 <= t ->
        ∀ A : ℝ,
          A < -t ->
          |W.signedOrdinateTest A
            * zetaMuCumulativeDiscrepancy A t|
          <=
          (W.signedOrdinateCurvature / (A-t)^2)
            *
          (C * (Real.log (t+3) + Real.log (-A+4))
            + A0 * Real.log (|t-1|+3)
            + A0 * Real.log (|A-1|+3)
            + |zetaMuWindowDiscrepancy (-t) t|) := by
  obtain ⟨C,T0,A0,hC,hA01,hneg⟩ :=
    exists_zetaMuWindowDiscrepancy_negativeSegment_bound
  refine ⟨C,T0,A0,hC,hA01,?_⟩
  intro t W ht A hAt
  have ht4 : 4 <= t := (le_max_right T0 4).trans ht
  have htpos : 0 < t := by linarith
  have hAle : A <= -t := hAt.le
  have hAt' : A ≠ t := by linarith
  have hphi :=
    W.signedOrdinateTest_abs_le_gap_sq htpos hAt'
  have hseg := hneg t A ht hAt
  have hsplit :=
    zetaMuCumulativeDiscrepancy_farLeft_split htpos.le hAle
  have hdisc :
      |zetaMuCumulativeDiscrepancy A t|
        <=
      C * (Real.log (t+3) + Real.log (-A+4))
        + A0 * Real.log (|t-1|+3)
        + A0 * Real.log (|A-1|+3)
        + |zetaMuWindowDiscrepancy (-t) t| := by
    rw [hsplit]
    exact (abs_add _ _).trans (add_le_add hseg le_rfl)
  have hfactor :
      0 <= W.signedOrdinateCurvature / (A-t)^2 := by
    have hc := W.signedOrdinateCurvature_nonneg
    positivity
  rw [abs_mul]
  exact mul_le_mul hphi hdisc (abs_nonneg _) hfactor


/--
For every sufficiently high fixed target t, the exact left centred boundary is
eventually O(1/n) on the canonical exhaustion A=t-n.

This is deliberately coarse: all logarithms are bounded linearly before the
quadratic kernel gap is used.
-/
theorem exists_quarticFourSignedPole_leftBoundary_eventually_inv_bound :
    ∃ T0 : ℝ,
      ∀ {t : ℝ},
        (W : QuarticFourSignedPolePair t) ->
        T0 <= t ->
        ∃ K : ℝ, 0 <= K ∧
          ∀ᶠ n : ℕ in atTop,
            |W.leftCenteredBoundary n|
              <= K / (n : ℝ) := by
  obtain ⟨C,T1,A0,hC,hA01,hbound⟩ :=
    exists_quarticFourSignedPole_leftBoundary_gap_sq_log_bound
  refine ⟨max T1 4, ?_⟩
  intro t W ht
  have ht1 : max T1 4 <= t := ht
  have ht4 : 4 <= t := (le_max_right T1 4).trans ht
  let D0 : ℝ := |zetaMuWindowDiscrepancy (-t) t|
  let K : ℝ :=
    W.signedOrdinateCurvature * (2*C + 3*A0 + 1)
  have hK : 0 <= K := by
    dsimp [K]
    have hcurv := W.signedOrdinateCurvature_nonneg
    nlinarith
  refine ⟨K,hK,?_⟩

  have hcast :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards
    [hcast.eventually (eventually_gt_atTop (2*t)),
     hcast.eventually (eventually_ge_atTop (Real.log (t+3))),
     hcast.eventually (eventually_ge_atTop (Real.log (|t-1|+3))),
     hcast.eventually (eventually_ge_atTop D0),
     hcast.eventually (eventually_ge_atTop (|t-1|+2)),
     hcast.eventually (eventually_ge_atTop 1)]
    with n hn2t hnlogt hnlogtm1 hnD hnshift hn1

  let N : ℝ := (n : ℝ)
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hn1
  have hAt : t - N < -t := by
    dsimp [N] at hn2t ⊢
    linarith
  have hraw :=
    hbound W ht1 (t-N) hAt

  have hlogMove1 :
      Real.log (-(t-N)+4) <= N := by
    have hy : 0 < -(t-N)+4 := by
      dsimp [N] at *
      linarith
    have h := Real.log_le_sub_one_of_pos hy
    linarith

  have habsShift :
      |t-N-1| <= |t-1| + N := by
    calc
      |t-N-1| = |(t-1) + (-N)| := by ring_nf
      _ <= |t-1| + |-N| := abs_add _ _
      _ = |t-1| + N := by
        rw [abs_neg, abs_of_pos hNpos]

  have hlogMove2 :
      Real.log (|t-N-1|+3) <= 2*N := by
    have hy : 0 < |t-N-1|+3 := by positivity
    have hlog := Real.log_le_sub_one_of_pos hy
    have hlin : |t-N-1| + 2 <= 2*N := by
      calc
        |t-N-1| + 2
          <= |t-1| + N + 2 := by linarith [habsShift]
        _ <= 2*N := by
          dsimp [N] at hnshift ⊢
          linarith
    linarith

  have hparent :
      C * (Real.log (t+3) + Real.log (-(t-N)+4))
        + A0 * Real.log (|t-1|+3)
        + A0 * Real.log (|t-N-1|+3)
        + D0
      <=
      (2*C + 3*A0 + 1) * N := by
    have hA00 : 0 <= A0 := le_trans (by norm_num) hA01
    have hD0 : D0 <= N := by simpa [D0, N] using hnD
    have hlt : Real.log (t+3) <= N := by simpa [N] using hnlogt
    have hltm1 : Real.log (|t-1|+3) <= N := by
      simpa [N] using hnlogtm1
    nlinarith

  unfold QuarticFourSignedPolePair.leftCenteredBoundary
  have hgap : ((t-N)-t)^2 = N^2 := by ring
  rw [show t - (n : ℝ) = t-N by rfl] at hraw
  rw [hgap] at hraw
  have hfac :
      0 <= W.signedOrdinateCurvature / N^2 := by
    have hc := W.signedOrdinateCurvature_nonneg
    positivity
  have hdom :=
    mul_le_mul_of_nonneg_left hparent hfac
  have hmain :
      |W.signedOrdinateTest (t-N)
        * zetaMuCumulativeDiscrepancy (t-N) t|
        <=
      K / N := by
    calc
      |W.signedOrdinateTest (t-N)
        * zetaMuCumulativeDiscrepancy (t-N) t|
        <=
      (W.signedOrdinateCurvature / N^2)
        *
      (C * (Real.log (t+3) + Real.log (-(t-N)+4))
        + A0 * Real.log (|t-1|+3)
        + A0 * Real.log (|t-N-1|+3)
        + D0) := by
          simpa [N, D0] using hraw
      _ <=
      (W.signedOrdinateCurvature / N^2)
        * ((2*C + 3*A0 + 1)*N) := hdom
      _ = K / N := by
        dsimp [K]
        field_simp [ne_of_gt hNpos]
        ring
  simpa [N] using hmain

end Synthesis

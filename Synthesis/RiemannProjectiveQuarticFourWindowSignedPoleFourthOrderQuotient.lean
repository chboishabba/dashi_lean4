import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleAbel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Low-mode quotient diagnostics for the exact signed four-window G3 consumer

The centered jet

  Psi(t)=Psi'(t)=Psi''(t)=Psi'''(t)=0

is local information.  It must not be silently promoted to the global claim
that the Abel functional is invariant under adding an arbitrary centered
cubic polynomial to the discrepancy.

For the preferred symmetric finite consumer, parity gives an exact and useful
quotient:

  E ~ E + a0 + a2 (x-t)^2.

The constant and centered-quadratic modes are invisible because Psi' is odd
about t.  The centered-linear and centered-cubic modes survive as explicit
global obstruction coordinates.

This file therefore records the strongest quotient justified by the current
same-object geometry, and makes the additional obligations for a full cubic
quotient explicit.
-/

noncomputable section

open MeasureTheory Set Topology
open scoped Interval Real

namespace Synthesis

def centeredMonomial (t : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (x - t)^k

def QuarticFourSignedPolePair.centeredModeDefectAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (n k : ℕ) : ℝ :=
  ∫ x in (t - (n : ℝ))..(t + (n : ℝ)),
    W.signedOrdinateTestDeriv x * centeredMonomial t k x

def QuarticFourSignedPolePair.centeredAbelCorrelationAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (n : ℕ) (E : ℝ -> ℝ) : ℝ :=
  ∫ x in (t - (n : ℝ))..(t + (n : ℝ)),
    W.signedOrdinateTestDeriv x * E x

def QuarticFourSignedPolePair.centeredCompletedFunctionalAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (n : ℕ) (E : ℝ -> ℝ) : ℝ :=
  -(1/2 : ℝ) * W.centeredAbelCorrelationAt n E
    + W.signedHorizontalRemainder

/--
The compact cosine transform is even in its frequency variable.
-/
theorem compactCosineTransform_even
    (P : ℝ -> ℝ) (q : ℝ) :
    compactCosineTransform P (-q)
      = compactCosineTransform P q := by
  unfold compactCosineTransform
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    rw [show (-q) * u = -(q*u) by ring, Real.cos_neg]

/--
Psi' is odd about the target ordinate t.
-/
theorem QuarticFourSignedPolePair.signedOrdinateTestDeriv_center_reflection
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (y : ℝ) :
    W.signedOrdinateTestDeriv (t - y)
      =
    - W.signedOrdinateTestDeriv (t + y) := by
  rw [W.signedOrdinateTestDeriv_eq_combinedD1 ht,
      W.signedOrdinateTestDeriv_eq_combinedD1 ht]
  dsimp
  have hodd :=
    compactCosineD1_odd
      (quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t)
      (y / (t/16))
  have hleft :
      (t - y - t) / (t/16) = -(y / (t/16)) := by ring
  have hright :
      (t + y - t) / (t/16) = y / (t/16) := by ring
  rw [hleft, hright, hodd]
  ring

/--
An odd function integrates to zero on a symmetric interval.
-/
theorem intervalIntegral_eq_zero_of_odd
    {f : ℝ -> ℝ}
    (hodd : ∀ x : ℝ, f (-x) = - f x)
    (a : ℝ) :
    (∫ x in (-a)..a, f x) = 0 := by
  have hreflect :
      (∫ x in (-a)..a, f (-x))
        =
      ∫ x in (-a)..a, f x := by
    simpa using
      (intervalIntegral.integral_comp_neg
        (f:=f) (a:=(-a)) (b:=a))
  have hneg :
      (∫ x in (-a)..a, f (-x))
        =
      - ∫ x in (-a)..a, f x := by
    calc
      (∫ x in (-a)..a, f (-x))
        =
      ∫ x in (-a)..a, - f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact hodd x
      _ = - ∫ x in (-a)..a, f x := by
        rw [intervalIntegral.integral_neg]
  linarith

/--
The centered constant discrepancy mode is exactly invisible to every symmetric
finite Abel consumer.
-/
theorem QuarticFourSignedPolePair.centeredModeDefectAt_zero
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.centeredModeDefectAt n 0 = 0 := by
  unfold QuarticFourSignedPolePair.centeredModeDefectAt centeredMonomial
  simp only [pow_zero, mul_one]
  have hFTC :=
    intervalIntegral.integral_deriv_eq_sub'
      (fun x hx => W.signedOrdinateTest_hasDerivAt ht x)
      (W.signedOrdinateTestDeriv_intervalIntegrable
        ht (t - (n : ℝ)) (t + (n : ℝ)))
  have hreflect :
      W.signedOrdinateTest (t - (n : ℝ))
        =
      W.signedOrdinateTest (t + (n : ℝ)) := by
    rw [W.signedOrdinateTest_eq_combinedCosine,
        W.signedOrdinateTest_eq_combinedCosine]
    dsimp
    have harg :
        (t - (n : ℝ) - t) / (t/16)
          =
        - ((t + (n : ℝ) - t) / (t/16)) := by
      ring
    rw [harg, compactCosineTransform_even]
  rw [hFTC, hreflect]
  ring

/--
The centered quadratic discrepancy mode is also exactly invisible.  After
translation to y=x-t, the integrand is the product of the odd function Psi'(t+y)
with the even factor y^2.
-/
theorem QuarticFourSignedPolePair.centeredModeDefectAt_two
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.centeredModeDefectAt n 2 = 0 := by
  unfold QuarticFourSignedPolePair.centeredModeDefectAt centeredMonomial
  let f : ℝ -> ℝ :=
    fun y => W.signedOrdinateTestDeriv (t + y) * y^2
  have hfodd : ∀ y : ℝ, f (-y) = - f y := by
    intro y
    dsimp [f]
    have hreflect :=
      W.signedOrdinateTestDeriv_center_reflection ht y
    rw [show t + -y = t - y by ring, hreflect]
    ring
  have hzero :
      (∫ y in (-(n : ℝ))..(n : ℝ), f y) = 0 :=
    intervalIntegral_eq_zero_of_odd hfodd (n : ℝ)
  have hshift :=
    intervalIntegral.integral_comp_add_left
      (fun x : ℝ =>
        W.signedOrdinateTestDeriv x * (x-t)^2)
      t
      (a:=(-(n : ℝ))) (b:=(n : ℝ))
  dsimp [f] at hzero
  have hpoint :
      (fun y : ℝ =>
        W.signedOrdinateTestDeriv (t + y)
          * (t + y - t)^2)
      =
      fun y =>
        W.signedOrdinateTestDeriv (t + y) * y^2 := by
    funext y
    ring
  rw [hpoint] at hshift
  have hb1 : t + (-(n : ℝ)) = t - (n : ℝ) := by ring
  have hb2 : t + (n : ℝ) = t + (n : ℝ) := rfl
  rw [hb1, hb2] at hshift
  rw [← hshift]
  exact hzero

/--
The exact even low-mode shift seen by the symmetric Abel consumer.
-/
def centeredEvenLowMode
    (t a0 a2 x : ℝ) : ℝ :=
  a0 + a2 * (x-t)^2

theorem QuarticFourSignedPolePair.centeredEvenLowMode_integral_zero
    {t a0 a2 : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    (∫ x in (t - (n : ℝ))..(t + (n : ℝ)),
      W.signedOrdinateTestDeriv x
        * centeredEvenLowMode t a0 a2 x)
      = 0 := by
  have hD :=
    W.signedOrdinateTestDeriv_continuous ht
  have h0 :
      IntervalIntegrable
        (fun x : ℝ =>
          W.signedOrdinateTestDeriv x * a0)
        volume (t - (n : ℝ)) (t + (n : ℝ)) := by
    fun_prop
  have h2 :
      IntervalIntegrable
        (fun x : ℝ =>
          W.signedOrdinateTestDeriv x * (a2 * (x-t)^2))
        volume (t - (n : ℝ)) (t + (n : ℝ)) := by
    fun_prop
  unfold centeredEvenLowMode
  have hsplit :
      (fun x : ℝ =>
        W.signedOrdinateTestDeriv x * (a0 + a2 * (x-t)^2))
      =
      fun x =>
        (W.signedOrdinateTestDeriv x * a0)
          +
        a2 * (W.signedOrdinateTestDeriv x * (x-t)^2) := by
    funext x
    ring
  rw [hsplit, intervalIntegral.integral_add h0
      (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using h2)]
  rw [show
      (∫ x in (t - (n : ℝ))..(t + (n : ℝ)),
        W.signedOrdinateTestDeriv x * a0)
        =
      a0 * W.centeredModeDefectAt n 0 by
        unfold QuarticFourSignedPolePair.centeredModeDefectAt centeredMonomial
        rw [intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x hx
        ring,
      show
      (∫ x in (t - (n : ℝ))..(t + (n : ℝ)),
        a2 * (W.signedOrdinateTestDeriv x * (x-t)^2))
        =
      a2 * W.centeredModeDefectAt n 2 by
        rw [intervalIntegral.integral_const_mul]
        rfl,
      W.centeredModeDefectAt_zero ht,
      W.centeredModeDefectAt_two ht]
  ring

/--
Finite symmetric Abel correlation is invariant under the exact even low-mode
quotient E ~ E + a0 + a2(x-t)^2.
-/
theorem QuarticFourSignedPolePair.centeredAbelCorrelationAt_add_evenLowMode
    {t a0 a2 : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (E : ℝ -> ℝ)
    (hE :
      IntervalIntegrable
        (fun x : ℝ => W.signedOrdinateTestDeriv x * E x)
        volume (t - (n : ℝ)) (t + (n : ℝ))) :
    W.centeredAbelCorrelationAt n
        (fun x => E x + centeredEvenLowMode t a0 a2 x)
      =
    W.centeredAbelCorrelationAt n E := by
  unfold QuarticFourSignedPolePair.centeredAbelCorrelationAt
  have hshift :
      IntervalIntegrable
        (fun x : ℝ =>
          W.signedOrdinateTestDeriv x
            * centeredEvenLowMode t a0 a2 x)
        volume (t - (n : ℝ)) (t + (n : ℝ)) := by
    have hD := W.signedOrdinateTestDeriv_continuous ht
    unfold centeredEvenLowMode
    fun_prop
  have hpoint :
      (fun x : ℝ =>
        W.signedOrdinateTestDeriv x
          * (E x + centeredEvenLowMode t a0 a2 x))
      =
      fun x =>
        W.signedOrdinateTestDeriv x * E x
          +
        W.signedOrdinateTestDeriv x
          * centeredEvenLowMode t a0 a2 x := by
    funext x
    ring
  rw [hpoint, intervalIntegral.integral_add hE hshift,
      W.centeredEvenLowMode_integral_zero ht]
  ring

theorem QuarticFourSignedPolePair.centeredCompletedFunctionalAt_add_evenLowMode
    {t a0 a2 : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (E : ℝ -> ℝ)
    (hE :
      IntervalIntegrable
        (fun x : ℝ => W.signedOrdinateTestDeriv x * E x)
        volume (t - (n : ℝ)) (t + (n : ℝ))) :
    W.centeredCompletedFunctionalAt n
        (fun x => E x + centeredEvenLowMode t a0 a2 x)
      =
    W.centeredCompletedFunctionalAt n E := by
  unfold QuarticFourSignedPolePair.centeredCompletedFunctionalAt
  rw [W.centeredAbelCorrelationAt_add_evenLowMode ht n E hE]

/--
A full quotient modulo all centered polynomials of degree <= 3 requires every
mode defect 0,1,2,3 to vanish.  Modes 0 and 2 are paid below by symmetry;
modes 1 and 3 are retained as explicit global obstructions.
-/
def QuarticFourSignedPolePair.fullCubicQuotientAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (n : ℕ) : Prop :=
  W.centeredModeDefectAt n 0 = 0
    ∧ W.centeredModeDefectAt n 1 = 0
    ∧ W.centeredModeDefectAt n 2 = 0
    ∧ W.centeredModeDefectAt n 3 = 0

/--
Because the even modes are already paid by symmetry, a full cubic quotient is
equivalent to the two remaining odd-mode obligations.
-/
theorem QuarticFourSignedPolePair.fullCubicQuotientAt_iff_oddModes
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.fullCubicQuotientAt n
      ↔
    W.centeredModeDefectAt n 1 = 0
      ∧ W.centeredModeDefectAt n 3 = 0 := by
  constructor
  · intro h
    exact ⟨h.2.1,h.2.2.2⟩
  · rintro ⟨h1,h3⟩
    exact ⟨
      W.centeredModeDefectAt_zero ht n,
      h1,
      W.centeredModeDefectAt_two ht n,
      h3
    ⟩

/--
The actual centered discrepancy consumer is represented by the generic
functional introduced above.
-/
theorem QuarticFourSignedPolePair.combinedCenteredAbelPartial_eq_generic
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.combinedCenteredAbelPartial n
      =
    W.centeredAbelCorrelationAt n
      (centeredZetaMuDiscrepancy t) := by
  unfold QuarticFourSignedPolePair.combinedCenteredAbelPartial
    QuarticFourSignedPolePair.leftCenteredAbelPartial
    QuarticFourSignedPolePair.rightCenteredAbelPartial
    QuarticFourSignedPolePair.centeredAbelIntegrand
    QuarticFourSignedPolePair.centeredAbelCorrelationAt
  have hleft :=
    W.centeredAbelIntegrand_intervalIntegrable
      ht (A:=t-(n:ℝ)) (B:=t)
  have hright :=
    W.centeredAbelIntegrand_intervalIntegrable
      ht (A:=t) (B:=t+(n:ℝ))
  symm
  exact intervalIntegral.integral_add_adjacent_intervals hleft hright

theorem QuarticFourSignedPolePair.centeredCompletedResidualAt_eq_generic
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.centeredCompletedResidualAt n
      =
    W.centeredCompletedFunctionalAt n
      (centeredZetaMuDiscrepancy t) := by
  unfold QuarticFourSignedPolePair.centeredCompletedResidualAt
    QuarticFourSignedPolePair.centeredCompletedFunctionalAt
  rw [W.combinedCenteredAbelPartial_eq_generic ht]


/--
Centered odd and cubic low-mode carriers.
-/
def centeredOddLowMode
    (t a1 a3 x : ℝ) : ℝ :=
  a1 * (x-t) + a3 * (x-t)^3

def centeredCubicLowMode
    (t a0 a1 a2 a3 x : ℝ) : ℝ :=
  centeredEvenLowMode t a0 a2 x
    + centeredOddLowMode t a1 a3 x

/--
The odd low-mode integral is exactly the linear combination of the centered
mode-1 and mode-3 defects.
-/
theorem QuarticFourSignedPolePair.centeredOddLowMode_integral_eq
    {t a1 a3 : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    (∫ x in (t - (n : ℝ))..(t + (n : ℝ)),
      W.signedOrdinateTestDeriv x
        * centeredOddLowMode t a1 a3 x)
      =
    a1 * W.centeredModeDefectAt n 1
      + a3 * W.centeredModeDefectAt n 3 := by
  have hD := W.signedOrdinateTestDeriv_continuous ht
  have h1 :
      IntervalIntegrable
        (fun x : ℝ =>
          a1 * (W.signedOrdinateTestDeriv x * (x-t)))
        volume (t - (n : ℝ)) (t + (n : ℝ)) := by
    fun_prop
  have h3 :
      IntervalIntegrable
        (fun x : ℝ =>
          a3 * (W.signedOrdinateTestDeriv x * (x-t)^3))
        volume (t - (n : ℝ)) (t + (n : ℝ)) := by
    fun_prop
  unfold centeredOddLowMode
  have hpoint :
      (fun x : ℝ =>
        W.signedOrdinateTestDeriv x
          * (a1 * (x-t) + a3 * (x-t)^3))
      =
      fun x =>
        a1 * (W.signedOrdinateTestDeriv x * (x-t))
          +
        a3 * (W.signedOrdinateTestDeriv x * (x-t)^3) := by
    funext x
    ring
  rw [hpoint, intervalIntegral.integral_add h1 h3,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  unfold QuarticFourSignedPolePair.centeredModeDefectAt centeredMonomial
  rfl

/--
The full centered cubic shift has no constant or quadratic contribution.  Its
entire finite Abel effect is carried by the two odd obstruction coordinates.
-/
theorem QuarticFourSignedPolePair.centeredCubicLowMode_integral_eq_oddDefects
    {t a0 a1 a2 a3 : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    (∫ x in (t - (n : ℝ))..(t + (n : ℝ)),
      W.signedOrdinateTestDeriv x
        * centeredCubicLowMode t a0 a1 a2 a3 x)
      =
    a1 * W.centeredModeDefectAt n 1
      + a3 * W.centeredModeDefectAt n 3 := by
  have heven :
      IntervalIntegrable
        (fun x : ℝ =>
          W.signedOrdinateTestDeriv x
            * centeredEvenLowMode t a0 a2 x)
        volume (t - (n : ℝ)) (t + (n : ℝ)) := by
    have hD := W.signedOrdinateTestDeriv_continuous ht
    unfold centeredEvenLowMode
    fun_prop
  have hodd :
      IntervalIntegrable
        (fun x : ℝ =>
          W.signedOrdinateTestDeriv x
            * centeredOddLowMode t a1 a3 x)
        volume (t - (n : ℝ)) (t + (n : ℝ)) := by
    have hD := W.signedOrdinateTestDeriv_continuous ht
    unfold centeredOddLowMode
    fun_prop
  unfold centeredCubicLowMode
  have hpoint :
      (fun x : ℝ =>
        W.signedOrdinateTestDeriv x
          * (centeredEvenLowMode t a0 a2 x
            + centeredOddLowMode t a1 a3 x))
      =
      fun x =>
        W.signedOrdinateTestDeriv x
            * centeredEvenLowMode t a0 a2 x
          +
        W.signedOrdinateTestDeriv x
            * centeredOddLowMode t a1 a3 x := by
    funext x
    ring
  rw [hpoint, intervalIntegral.integral_add heven hodd,
      W.centeredEvenLowMode_integral_zero ht,
      W.centeredOddLowMode_integral_eq ht]
  ring

/--
Exact obstruction normal form for the complete finite G3 functional under a
centered cubic discrepancy shift.

The horizontal remainder is deliberately left coupled to the functional and
is not split or bounded here.  Since this synthetic shift changes only the
discrepancy carrier, H_comb is unchanged; therefore the only quotient defects
are the two odd Abel modes.
-/
theorem QuarticFourSignedPolePair.centeredCompletedFunctionalAt_add_cubicLowMode
    {t a0 a1 a2 a3 : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (E : ℝ -> ℝ)
    (hE :
      IntervalIntegrable
        (fun x : ℝ =>
          W.signedOrdinateTestDeriv x * E x)
        volume (t - (n : ℝ)) (t + (n : ℝ))) :
    W.centeredCompletedFunctionalAt n
        (fun x => E x + centeredCubicLowMode t a0 a1 a2 a3 x)
      =
    W.centeredCompletedFunctionalAt n E
      -
    (1/2 : ℝ) *
      (a1 * W.centeredModeDefectAt n 1
        + a3 * W.centeredModeDefectAt n 3) := by
  unfold QuarticFourSignedPolePair.centeredCompletedFunctionalAt
    QuarticFourSignedPolePair.centeredAbelCorrelationAt
  have hcubic :
      IntervalIntegrable
        (fun x : ℝ =>
          W.signedOrdinateTestDeriv x
            * centeredCubicLowMode t a0 a1 a2 a3 x)
        volume (t - (n : ℝ)) (t + (n : ℝ)) := by
    have hD := W.signedOrdinateTestDeriv_continuous ht
    unfold centeredCubicLowMode centeredEvenLowMode centeredOddLowMode
    fun_prop
  have hpoint :
      (fun x : ℝ =>
        W.signedOrdinateTestDeriv x
          * (E x + centeredCubicLowMode t a0 a1 a2 a3 x))
      =
      fun x =>
        W.signedOrdinateTestDeriv x * E x
          +
        W.signedOrdinateTestDeriv x
          * centeredCubicLowMode t a0 a1 a2 a3 x := by
    funext x
    ring
  rw [hpoint, intervalIntegral.integral_add hE hcubic,
      W.centeredCubicLowMode_integral_eq_oddDefects ht]
  ring

/--
A full cubic quotient for the completed finite functional is available exactly
when both odd mode defects vanish.
-/
theorem QuarticFourSignedPolePair.completedFunctional_cubic_invariant_of_oddModes
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (h1 : W.centeredModeDefectAt n 1 = 0)
    (h3 : W.centeredModeDefectAt n 3 = 0)
    (E : ℝ -> ℝ)
    (hE :
      IntervalIntegrable
        (fun x : ℝ =>
          W.signedOrdinateTestDeriv x * E x)
        volume (t - (n : ℝ)) (t + (n : ℝ)))
    (a0 a1 a2 a3 : ℝ) :
    W.centeredCompletedFunctionalAt n
        (fun x => E x + centeredCubicLowMode t a0 a1 a2 a3 x)
      =
    W.centeredCompletedFunctionalAt n E := by
  rw [W.centeredCompletedFunctionalAt_add_cubicLowMode
      ht n E hE, h1, h3]
  ring


/--
Finite symmetric zeroth and second moments of the actual signed test Psi_t.
These are global-in-x moments of Psi_t itself, not the profile moments which
control the centered jet.
-/
def QuarticFourSignedPolePair.centeredPsiMassAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (n : ℕ) : ℝ :=
  ∫ x in (t - (n : ℝ))..(t + (n : ℝ)),
    W.signedOrdinateTest x

def QuarticFourSignedPolePair.centeredPsiSecondMassAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (n : ℕ) : ℝ :=
  ∫ x in (t - (n : ℝ))..(t + (n : ℝ)),
    W.signedOrdinateTest x * (x-t)^2

/--
Exact finite formula for the surviving centered-linear discrepancy defect:

  D1(n) = 2 n Psi(t+n) - integral Psi.

The local centered jet does not force the second term to vanish.
-/
theorem QuarticFourSignedPolePair.centeredModeDefectAt_one_eq
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.centeredModeDefectAt n 1
      =
    2 * (n : ℝ) * W.signedOrdinateTest (t + (n : ℝ))
      - W.centeredPsiMassAt n := by
  let a : ℝ := t - (n : ℝ)
  let b : ℝ := t + (n : ℝ)
  let F : ℝ -> ℝ :=
    fun x => W.signedOrdinateTest x * (x-t)
  let F' : ℝ -> ℝ :=
    fun x =>
      W.signedOrdinateTestDeriv x * (x-t)
        + W.signedOrdinateTest x
  have hderiv :
      ∀ x ∈ Set.Icc a b, HasDerivAt F (F' x) x := by
    intro x hx
    dsimp [F,F']
    convert
      (W.signedOrdinateTest_hasDerivAt ht x).mul
        ((hasDerivAt_id x).sub_const t) using 1 <;> ring
  have hF'int : IntervalIntegrable F' volume a b := by
    dsimp [F']
    have hD := W.signedOrdinateTestDeriv_continuous ht
    have hP : Continuous W.signedOrdinateTest := by
      exact continuous_of_forall_continuousAt fun x =>
        (W.signedOrdinateTest_hasDerivAt ht x).continuousAt
    fun_prop
  have hFTC :=
    intervalIntegral.integral_deriv_eq_sub' hderiv hF'int
  have hDint :
      IntervalIntegrable
        (fun x : ℝ =>
          W.signedOrdinateTestDeriv x * (x-t))
        volume a b := by
    have hD := W.signedOrdinateTestDeriv_continuous ht
    fun_prop
  have hPint :
      IntervalIntegrable W.signedOrdinateTest volume a b := by
    exact
      (continuous_of_forall_continuousAt fun x =>
        (W.signedOrdinateTest_hasDerivAt ht x).continuousAt)
        .intervalIntegrable a b
  have hsplit :
      (∫ x in a..b, F' x)
        =
      (∫ x in a..b,
        W.signedOrdinateTestDeriv x * (x-t))
        +
      (∫ x in a..b, W.signedOrdinateTest x) := by
    dsimp [F']
    rw [intervalIntegral.integral_add hDint hPint]
  rw [hsplit] at hFTC
  have hreflect :
      W.signedOrdinateTest a = W.signedOrdinateTest b := by
    dsimp [a,b]
    rw [W.signedOrdinateTest_eq_combinedCosine,
        W.signedOrdinateTest_eq_combinedCosine]
    dsimp
    have harg :
        (t - (n : ℝ) - t) / (t/16)
          =
        - ((t + (n : ℝ) - t) / (t/16)) := by ring
    rw [harg, compactCosineTransform_even]
  unfold QuarticFourSignedPolePair.centeredModeDefectAt
    centeredMonomial
    QuarticFourSignedPolePair.centeredPsiMassAt
  simp only [pow_one]
  dsimp [a,b,F] at hFTC hreflect ⊢
  rw [hreflect] at hFTC
  linarith

/--
Exact finite formula for the surviving centered-cubic discrepancy defect:

  D3(n) = 2 n^3 Psi(t+n)
          - 3 integral Psi(x)(x-t)^2 dx.

Again, the obstruction is a global moment of Psi_t, not a centered-jet datum.
-/
theorem QuarticFourSignedPolePair.centeredModeDefectAt_three_eq
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.centeredModeDefectAt n 3
      =
    2 * (n : ℝ)^3 * W.signedOrdinateTest (t + (n : ℝ))
      - 3 * W.centeredPsiSecondMassAt n := by
  let a : ℝ := t - (n : ℝ)
  let b : ℝ := t + (n : ℝ)
  let F : ℝ -> ℝ :=
    fun x => W.signedOrdinateTest x * (x-t)^3
  let F' : ℝ -> ℝ :=
    fun x =>
      W.signedOrdinateTestDeriv x * (x-t)^3
        + 3 * W.signedOrdinateTest x * (x-t)^2
  have hderiv :
      ∀ x ∈ Set.Icc a b, HasDerivAt F (F' x) x := by
    intro x hx
    dsimp [F,F']
    have hp := ((hasDerivAt_id x).sub_const t).pow 3
    convert
      (W.signedOrdinateTest_hasDerivAt ht x).mul hp
      using 1 <;> ring
  have hDint :
      IntervalIntegrable
        (fun x : ℝ =>
          W.signedOrdinateTestDeriv x * (x-t)^3)
        volume a b := by
    have hD := W.signedOrdinateTestDeriv_continuous ht
    fun_prop
  have hP2int :
      IntervalIntegrable
        (fun x : ℝ =>
          3 * W.signedOrdinateTest x * (x-t)^2)
        volume a b := by
    have hP : Continuous W.signedOrdinateTest :=
      continuous_of_forall_continuousAt fun x =>
        (W.signedOrdinateTest_hasDerivAt ht x).continuousAt
    fun_prop
  have hF'int : IntervalIntegrable F' volume a b := by
    dsimp [F']
    exact hDint.add hP2int
  have hFTC :=
    intervalIntegral.integral_deriv_eq_sub' hderiv hF'int
  have hsplit :
      (∫ x in a..b, F' x)
        =
      (∫ x in a..b,
        W.signedOrdinateTestDeriv x * (x-t)^3)
        +
      3 *
      (∫ x in a..b,
        W.signedOrdinateTest x * (x-t)^2) := by
    dsimp [F']
    rw [intervalIntegral.integral_add hDint hP2int]
    have hbase :
        IntervalIntegrable
          (fun x : ℝ =>
            W.signedOrdinateTest x * (x-t)^2)
          volume a b := by
      have hP : Continuous W.signedOrdinateTest :=
        continuous_of_forall_continuousAt fun x =>
          (W.signedOrdinateTest_hasDerivAt ht x).continuousAt
      fun_prop
    rw [show
        (∫ x in a..b,
          3 * W.signedOrdinateTest x * (x-t)^2)
          =
        3 * ∫ x in a..b,
          W.signedOrdinateTest x * (x-t)^2 by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro x hx
          ring]
  have hreflect :
      W.signedOrdinateTest a = W.signedOrdinateTest b := by
    dsimp [a,b]
    rw [W.signedOrdinateTest_eq_combinedCosine,
        W.signedOrdinateTest_eq_combinedCosine]
    dsimp
    have harg :
        (t - (n : ℝ) - t) / (t/16)
          =
        - ((t + (n : ℝ) - t) / (t/16)) := by ring
    rw [harg, compactCosineTransform_even]
  unfold QuarticFourSignedPolePair.centeredModeDefectAt
    centeredMonomial
    QuarticFourSignedPolePair.centeredPsiSecondMassAt
  dsimp [a,b,F] at hFTC hreflect ⊢
  rw [hreflect] at hFTC
  linarith


/-!
## C4 regularity lift and quartic Fourier decay

The historical quantitative bump API exposed only C2 because that was enough
for the original explicit-formula construction.  The underlying Mathlib
ContDiffBump is smooth.  We expose only the C4 slice needed to make the
centered-cubic obstruction a legitimate global object.
-/

open Zeta23Bridge.LiteralWeilOddChannelTaper
open Zeta23Bridge.OscillatoryKernelDecay

theorem unitBump_contDiff_four :
    ContDiff ℝ 4 unitBump :=
  unitContDiffBump.contDiff (n := 4)

theorem scaledUnitBump_contDiff_four
    {R : ℝ} (hR : R ≠ 0) (c : ℝ) :
    ContDiff ℝ 4 (scaledUnitBump c R) := by
  unfold scaledUnitBump
  exact unitBump_contDiff_four.comp
    ((contDiff_id.sub contDiff_const).div_const hR)

theorem quantitativeSymBump_contDiff_four
    {c R : ℝ} (hR : R ≠ 0) :
    ContDiff ℝ 4 (quantitativeSymBump c R) := by
  unfold quantitativeSymBump
  exact symmetrize_contDiff
    (scaledUnitBump_contDiff_four hR c)

theorem quarticFourWindowRaw_contDiff_four
    {R lam mu : ℝ} (hR : 0 < R) :
    ContDiff ℝ 4 (quarticFourWindowRaw R lam mu) := by
  unfold quarticFourWindowRaw
  exact
    (((quantitativeSymBump_contDiff_four
        (c:=0) hR.ne').sub
      (quantitativeSymBump_contDiff_four
        (c:=Real.pi/3) hR.ne')).add
      (contDiff_const.mul
        (quantitativeSymBump_contDiff_four
          (c:=Real.pi/2) hR.ne'))).add
      (contDiff_const.mul
        (quantitativeSymBump_contDiff_four
          (c:=Real.pi) hR.ne'))

theorem quarticFourWindowProfile_contDiff_four
    {R lam mu : ℝ} (hR : 0 < R) :
    ContDiff ℝ 4 (quarticFourWindowProfile R lam mu) := by
  unfold quarticFourWindowProfile
  exact contDiff_const.mul
    (quarticFourWindowRaw_contDiff_four
      (lam:=lam) (mu:=mu) hR)

theorem genericProjectivePhysicalProfile_contDiff_four
    {g : ℝ -> ℝ}
    (hg : ContDiff ℝ 4 g)
    (r : ℝ) :
    ContDiff ℝ 4 (genericProjectivePhysicalProfile g r) := by
  unfold genericProjectivePhysicalProfile
    Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.twoRadiusBracket
    Zeta23Bridge.LiteralWeilParityBalance.evenResp
  fun_prop

theorem quarticFourNormalizedProjectiveProfile_contDiff_four
    {R lam mu : ℝ}
    (hR : 0 < R) :
    ContDiff ℝ 4
      (quarticFourNormalizedProjectiveProfile R lam mu) := by
  unfold quarticFourNormalizedProjectiveProfile
  exact genericProjectivePhysicalProfile_contDiff_four
    (quarticFourWindowProfile_contDiff_four
      (lam:=lam) (mu:=mu) hR) 1

theorem quarticFourSignedPoleCombinedProfile_contDiff_four
    {R muHalf muTwo t : ℝ}
    (hR : 0 < R) :
    ContDiff ℝ 4
      (quarticFourSignedPoleCombinedProfile
        R muHalf muTwo t) := by
  unfold quarticFourSignedPoleCombinedProfile profileLinearCombination
  exact
    (contDiff_const.mul
      (quarticFourNormalizedProjectiveProfile_contDiff_four
        (lam:=(1/2 : ℝ)) (mu:=muHalf) hR)).add
    (contDiff_const.mul
      (quarticFourNormalizedProjectiveProfile_contDiff_four
        (lam:=(2/3 : ℝ)) (mu:=muTwo) hR))

def compactCosineFourthDecayCurvature
    (P : ℝ -> ℝ) : ℝ :=
  ∫ u : ℝ,
    |deriv (deriv (deriv (deriv P))) u|

theorem compactCosineFourthDecayCurvature_nonneg
    (P : ℝ -> ℝ) :
    0 <= compactCosineFourthDecayCurvature P := by
  unfold compactCosineFourthDecayCurvature
  positivity

/--
Four integrations by parts on a compact C4 profile.
-/
theorem compactCosineTransform_abs_le_invPowFour
    {P : ℝ -> ℝ}
    (hP : ContDiff ℝ 4 P)
    (hPc : HasCompactSupport P)
    {q : ℝ}
    (hq : q ≠ 0) :
    |compactCosineTransform P q|
      <= compactCosineFourthDecayCurvature P / q^4 := by
  have hP1 : ContDiff ℝ 1 P := hP.of_le (by norm_num)
  have hD1_3 : ContDiff ℝ 3 (deriv P) := ContDiff.deriv' hP
  have hD1_1 : ContDiff ℝ 1 (deriv P) :=
    hD1_3.of_le (by norm_num)
  have hD2_2 : ContDiff ℝ 2 (deriv (deriv P)) :=
    ContDiff.deriv' hD1_3
  have hD2_1 : ContDiff ℝ 1 (deriv (deriv P)) :=
    hD2_2.of_le (by norm_num)
  have hD3_1 : ContDiff ℝ 1 (deriv (deriv (deriv P))) :=
    ContDiff.deriv' hD2_2
  have h1 := integral_mul_cos_eq hP1 hPc hq
  have h2 := integral_mul_sin_eq hD1_1 hPc.deriv hq
  have h3 := integral_mul_cos_eq hD2_1 hPc.deriv.deriv hq
  have h4 := integral_mul_sin_eq hD3_1 hPc.deriv.deriv.deriv hq
  have hfourth :
      (∫ u : ℝ, P u * Real.cos (q*u))
        =
      (1 / q^4) *
        ∫ u : ℝ,
          deriv (deriv (deriv (deriv P))) u
            * Real.cos (q*u) := by
    rw [h1,h2,h3,h4]
    field_simp [hq]
    ring
  have hD4c :
      Continuous (deriv (deriv (deriv (deriv P)))) :=
    hD3_1.continuous_deriv le_rfl
  have hD4s :
      HasCompactSupport
        (deriv (deriv (deriv (deriv P)))) :=
    hPc.deriv.deriv.deriv.deriv
  have hi :
      Integrable
        (fun u : ℝ =>
          deriv (deriv (deriv (deriv P))) u
            * Real.cos (q*u)) :=
    Continuous.integrable_of_hasCompactSupport
      (hD4c.mul (by fun_prop)) hD4s.mul_right
  have hiabs :
      Integrable
        (fun u : ℝ =>
          |deriv (deriv (deriv (deriv P))) u|) :=
    hD4c.abs.integrable_of_hasCompactSupport hD4s.abs
  have hbound :
      |∫ u : ℝ,
        deriv (deriv (deriv (deriv P))) u
          * Real.cos (q*u)|
        <=
      ∫ u : ℝ,
        |deriv (deriv (deriv (deriv P))) u| := by
    calc
      |∫ u : ℝ,
        deriv (deriv (deriv (deriv P))) u
          * Real.cos (q*u)|
        <=
      ∫ u : ℝ,
        |deriv (deriv (deriv (deriv P))) u
          * Real.cos (q*u)| :=
        abs_integral_le_integral_abs
      _ <=
      ∫ u : ℝ,
        |deriv (deriv (deriv (deriv P))) u| := by
        apply integral_mono hi.abs hiabs
        intro u
        rw [abs_mul]
        exact mul_le_of_le_one_right
          (abs_nonneg _) (Real.abs_cos_le_one _)
  unfold compactCosineTransform
  rw [hfourth, abs_mul,
      abs_of_nonneg (by positivity : 0 <= 1/q^4)]
  unfold compactCosineFourthDecayCurvature
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

/--
The actual physical signed test has inverse-fourth-power tail decay.
-/
theorem QuarticFourSignedPolePair.signedOrdinateTest_abs_le_gap_four
    {t x : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hxt : x ≠ t) :
    |W.signedOrdinateTest x|
      <=
    (t/16)^2
      * compactCosineFourthDecayCurvature
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t)
      / (x-t)^4 := by
  let r : ℝ := t/16
  let P :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hq : (x-t)/r ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr hxt) hr.ne'
  have hdec :=
    compactCosineTransform_abs_le_invPowFour
      (quarticFourSignedPoleCombinedProfile_contDiff_four W.Rpos)
      (quarticFourSignedPoleCombinedProfile_compact W.Rpos)
      hq
  rw [W.signedOrdinateTest_eq_combinedCosine]
  dsimp [r,P]
  rw [abs_mul, abs_of_pos (by positivity : 0 < 1/(t/16)^2)]
  have hmul :=
    mul_le_mul_of_nonneg_left hdec
      (by positivity : 0 <= 1/(t/16)^2)
  calc
    (1/(t/16)^2)
      * |compactCosineTransform
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t)
          ((x-t)/(t/16))|
      <=
    (1/(t/16)^2)
      * (compactCosineFourthDecayCurvature
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t)
        / (((x-t)/(t/16))^4)) := hmul
    _ =
    (t/16)^2
      * compactCosineFourthDecayCurvature
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t)
      / (x-t)^4 := by
        field_simp [ne_of_gt ht, sub_ne_zero.mpr hxt]
        ring


/--
The cubic boundary contribution vanishes on the canonical symmetric
exhaustion.  C4 regularity is exactly what upgrades the old 1/n^2 kernel tail
to the 1/n^4 decay needed here.
-/
theorem QuarticFourSignedPolePair.cubicBoundary_tendsto_zero
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ)^3 *
          W.signedOrdinateTest (t + (n : ℝ)))
      atTop (𝓝 0) := by
  let K : ℝ :=
    (t/16)^2
      * compactCosineFourthDecayCurvature
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t)
  have hK : 0 <= K := by
    dsimp [K]
    have hC :=
      compactCosineFourthDecayCurvature_nonneg
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t)
    positivity
  apply tendsto_zero_of_eventually_abs_le_const_div_nat hK
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hneq : t + (n : ℝ) ≠ t := by
    linarith
  have hdec :=
    W.signedOrdinateTest_abs_le_gap_four ht hneq
  have hgap :
      (t + (n : ℝ) - t)^4 = (n : ℝ)^4 := by
    ring
  rw [hgap] at hdec
  rw [abs_mul, abs_of_nonneg (pow_nonneg (by positivity) 3)]
  have hmul :=
    mul_le_mul_of_nonneg_left hdec
      (pow_nonneg (by positivity) 3)
  calc
    (n : ℝ)^3 *
        |W.signedOrdinateTest (t + (n : ℝ))|
      <=
    (n : ℝ)^3 * (K / (n : ℝ)^4) := by
      simpa [K] using hmul
    _ = K / (n : ℝ) := by
      field_simp [ne_of_gt hnpos]
      ring

/--
The linear boundary contribution vanishes a fortiori.
-/
theorem QuarticFourSignedPolePair.linearBoundary_tendsto_zero
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          W.signedOrdinateTest (t + (n : ℝ)))
      atTop (𝓝 0) := by
  let K : ℝ :=
    (t/16)^2
      * compactCosineFourthDecayCurvature
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t)
  have hK : 0 <= K := by
    dsimp [K]
    have hC :=
      compactCosineFourthDecayCurvature_nonneg
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t)
    positivity
  have hstrong :
      ∀ᶠ n : ℕ in atTop,
        |(n : ℝ) *
          W.signedOrdinateTest (t + (n : ℝ))|
          <= K / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hneq : t + (n : ℝ) ≠ t := by linarith
    have hdec :=
      W.signedOrdinateTest_abs_le_gap_four ht hneq
    have hgap :
        (t + (n : ℝ) - t)^4 = (n : ℝ)^4 := by ring
    rw [hgap] at hdec
    rw [abs_mul, abs_of_pos hnpos]
    have hmul :=
      mul_le_mul_of_nonneg_left hdec hnpos.le
    calc
      (n : ℝ) *
          |W.signedOrdinateTest (t + (n : ℝ))|
        <= (n : ℝ) * (K / (n : ℝ)^4) := by
          simpa [K] using hmul
      _ <= K / (n : ℝ) := by
        have hn1 : (1 : ℝ) <= n := by exact_mod_cast hn
        have hKnon := hK
        field_simp [ne_of_gt hnpos]
        nlinarith [sq_nonneg ((n : ℝ)^2 - 1)]
  exact tendsto_zero_of_eventually_abs_le_const_div_nat hK hstrong


/--
Uniform L1 bound for a compact cosine transform.
-/
theorem compactCosineTransform_abs_le_taperMass
    {P : ℝ -> ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (q : ℝ) :
    |compactCosineTransform P q|
      <= Zeta23Bridge.LiteralWeilProjectiveStripConstant.taperMass P := by
  unfold compactCosineTransform
    Zeta23Bridge.LiteralWeilProjectiveStripConstant.taperMass
  have hi :
      Integrable
        (fun u : ℝ => P u * Real.cos (q*u)) :=
    (hP.mul (by fun_prop)).integrable_of_hasCompactSupport hPc.mul_right
  have hiabs :
      Integrable (fun u : ℝ => |P u|) :=
    hP.abs.integrable_of_hasCompactSupport hPc.abs
  calc
    |∫ u : ℝ, P u * Real.cos (q*u)|
      <= ∫ u : ℝ, |P u * Real.cos (q*u)| :=
        abs_integral_le_integral_abs
    _ <= ∫ u : ℝ, |P u| := by
      apply integral_mono hi.abs hiabs
      intro u
      rw [abs_mul]
      exact mul_le_of_le_one_right
        (abs_nonneg _) (Real.abs_cos_le_one _)

/--
A global, non-decaying bound for the actual physical signed test.
-/
theorem QuarticFourSignedPolePair.signedOrdinateTest_abs_le_global
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (x : ℝ) :
    |W.signedOrdinateTest x|
      <=
    (1/(t/16)^2)
      *
    Zeta23Bridge.LiteralWeilProjectiveStripConstant.taperMass
      (quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t) := by
  have hP :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hC :=
    compactCosineTransform_abs_le_taperMass
      hP hPc ((x-t)/(t/16))
  rw [W.signedOrdinateTest_eq_combinedCosine]
  dsimp
  rw [abs_mul, abs_of_pos (by positivity : 0 < 1/(t/16)^2)]
  exact mul_le_mul_of_nonneg_left hC (by positivity)

/--
The weighted global Psi moment needed by the cubic quotient obstruction is
absolutely integrable.

The bounded middle is controlled by the transform L1 bound; the far tail uses
the C4 inverse-fourth decay.  Both pieces are dominated by one translated
Cauchy kernel C/(1+(x-t)^2).
-/
theorem QuarticFourSignedPolePair.signedOrdinateTest_mul_centeredSq_integrable
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    Integrable
      (fun x : ℝ =>
        W.signedOrdinateTest x * (x-t)^2) := by
  let P :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  let A : ℝ :=
    (t/16)^2 * compactCosineFourthDecayCurvature P
  let B : ℝ :=
    (1/(t/16)^2)
      * Zeta23Bridge.LiteralWeilProjectiveStripConstant.taperMass P
  let C : ℝ := 2 * (A + B)
  have hA : 0 <= A := by
    dsimp [A,P]
    have hcurv :=
      compactCosineFourthDecayCurvature_nonneg
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t)
    positivity
  have hB : 0 <= B := by
    dsimp [B,P]
    have hm :=
      Zeta23Bridge.LiteralWeilProjectiveStripConstant.taperMass_nonneg
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t)
    positivity
  have hC : 0 <= C := by
    dsimp [C]
    positivity
  have hbase :
      Integrable (fun y : ℝ => (1 + y^2)⁻¹) :=
    integrable_inv_one_add_sq
  have hshift :
      Integrable (fun x : ℝ => (1 + (x-t)^2)⁻¹) := by
    simpa using Integrable.comp_sub_right hbase t
  have hmajor :
      Integrable
        (fun x : ℝ => C * (1 + (x-t)^2)⁻¹) :=
    hshift.const_mul C
  have htargetC :
      Continuous
        (fun x : ℝ =>
          W.signedOrdinateTest x * (x-t)^2) := by
    have hPsi : Continuous W.signedOrdinateTest :=
      continuous_of_forall_continuousAt fun x =>
        (W.signedOrdinateTest_hasDerivAt ht x).continuousAt
    fun_prop
  refine Integrable.mono' hmajor
    htargetC.aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  let y : ℝ := x-t
  have hden : 0 < 1 + y^2 := by positivity
  have hmajorAbs :
      |C * (1 + y^2)⁻¹|
        = C / (1 + y^2) := by
    rw [abs_mul, abs_of_nonneg hC, abs_inv,
        abs_of_pos hden]
    rfl
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_mul, abs_pow, abs_of_nonneg (sq_nonneg y),
      show x-t = y by rfl, hmajorAbs]
  by_cases hy : y^2 <= 1
  · have hPsi :
        |W.signedOrdinateTest x| <= B := by
      dsimp [B,P]
      exact W.signedOrdinateTest_abs_le_global ht x
    have hz : 0 <= y^2 := sq_nonneg y
    have hshape : y^2 * (1 + y^2) <= 2 := by
      have hzprod :
          0 <= (1-y^2) * y^2 :=
        mul_nonneg (sub_nonneg.mpr hy) hz
      nlinarith
    have hlocal :
        |W.signedOrdinateTest x| * y^2 * (1+y^2)
          <= C := by
      have h1 :=
        mul_le_mul_of_nonneg_right hPsi hz
      have h2 :
          |W.signedOrdinateTest x| * y^2 * (1+y^2)
            <= B * (y^2 * (1+y^2)) := by
        nlinarith [h1, abs_nonneg (W.signedOrdinateTest x)]
      have h3 :
          B * (y^2 * (1+y^2)) <= 2*B :=
        mul_le_mul_of_nonneg_left hshape hB
      dsimp [C]
      nlinarith
    exact (le_div_iff₀ hden).2 (by simpa [mul_assoc] using hlocal)
  · have hy' : 1 < y^2 := lt_of_not_ge hy
    have hyne : y ≠ 0 := by
      intro hz
      subst y
      norm_num at hy'
    have hPsi :
        |W.signedOrdinateTest x| <= A / y^4 := by
      dsimp [A,P]
      simpa [y] using
        W.signedOrdinateTest_abs_le_gap_four ht
          (sub_ne_zero.mp hyne)
    have hweighted :
        |W.signedOrdinateTest x| * y^2
          <= A / y^2 := by
      have hm :=
        mul_le_mul_of_nonneg_right hPsi (sq_nonneg y)
      calc
        |W.signedOrdinateTest x| * y^2
          <= (A / y^4) * y^2 := hm
        _ = A / y^2 := by
          field_simp [hyne]
          ring
    have hshape :
        A * (1+y^2) <= C * y^2 := by
      have htwo : 1 + y^2 <= 2*y^2 := by linarith
      have h1 :=
        mul_le_mul_of_nonneg_left htwo hA
      dsimp [C]
      nlinarith [mul_nonneg hB (sq_nonneg y)]
    have hfar :
        (A / y^2) <= C / (1+y^2) := by
      rw [div_le_div_iff₀ (sq_pos_of_ne_zero hyne) hden]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hshape
    exact hweighted.trans hfar


/--
The unweighted signed test is also globally integrable.
-/
theorem QuarticFourSignedPolePair.signedOrdinateTest_integrable
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    Integrable W.signedOrdinateTest := by
  let P :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  let A : ℝ :=
    (t/16)^2 * compactCosineFourthDecayCurvature P
  let B : ℝ :=
    (1/(t/16)^2)
      * Zeta23Bridge.LiteralWeilProjectiveStripConstant.taperMass P
  let C : ℝ := 2 * (A + B)
  have hA : 0 <= A := by
    dsimp [A,P]
    have hcurv :=
      compactCosineFourthDecayCurvature_nonneg
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t)
    positivity
  have hB : 0 <= B := by
    dsimp [B,P]
    have hm :=
      Zeta23Bridge.LiteralWeilProjectiveStripConstant.taperMass_nonneg
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t)
    positivity
  have hC : 0 <= C := by
    dsimp [C]
    positivity
  have hbase :
      Integrable (fun y : ℝ => (1 + y^2)⁻¹) :=
    integrable_inv_one_add_sq
  have hshift :
      Integrable (fun x : ℝ => (1 + (x-t)^2)⁻¹) := by
    simpa using Integrable.comp_sub_right hbase t
  have hmajor :
      Integrable
        (fun x : ℝ => C * (1 + (x-t)^2)⁻¹) :=
    hshift.const_mul C
  have hPsiC : Continuous W.signedOrdinateTest :=
    continuous_of_forall_continuousAt fun x =>
      (W.signedOrdinateTest_hasDerivAt ht x).continuousAt
  refine Integrable.mono' hmajor
    hPsiC.aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  let y : ℝ := x-t
  have hden : 0 < 1 + y^2 := by positivity
  have hmajorAbs :
      |C * (1 + y^2)⁻¹|
        = C / (1 + y^2) := by
    rw [abs_mul, abs_of_nonneg hC, abs_inv,
        abs_of_pos hden]
    rfl
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
      show x-t = y by rfl, hmajorAbs]
  by_cases hy : y^2 <= 1
  · have hPsi :
        |W.signedOrdinateTest x| <= B := by
      dsimp [B,P]
      exact W.signedOrdinateTest_abs_le_global ht x
    have hshape : B * (1+y^2) <= C := by
      dsimp [C]
      nlinarith [hB,hA]
    apply (le_div_iff₀ hden).2
    exact (mul_le_mul_of_nonneg_right hPsi hden.le).trans hshape
  · have hy' : 1 < y^2 := lt_of_not_ge hy
    have hyne : y ≠ 0 := by
      intro hz
      subst y
      norm_num at hy'
    have hPsi :
        |W.signedOrdinateTest x| <= A / y^4 := by
      dsimp [A,P]
      simpa [y] using
        W.signedOrdinateTest_abs_le_gap_four ht
          (sub_ne_zero.mp hyne)
    have hshape :
        A * (1+y^2) <= C * y^4 := by
      have hy2non : 0 <= y^2 := sq_nonneg y
      have htwo : 1+y^2 <= 2*y^2 := by linarith
      have hy4 : y^2 <= y^4 := by
        have := mul_le_mul_of_nonneg_right hy'.le hy2non
        nlinarith
      have h1 :=
        mul_le_mul_of_nonneg_left htwo hA
      dsimp [C]
      nlinarith [mul_nonneg hB (pow_nonneg y 4)]
    have hfar :
        A / y^4 <= C / (1+y^2) := by
      rw [div_le_div_iff₀ (pow_pos (by
        exact lt_of_le_of_ne (sq_nonneg y) (Ne.symm (pow_ne_zero 2 hyne))) 2)
        hden]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hshape
    exact hPsi.trans hfar

/--
Symmetric interval exhaustion of any globally integrable real-line function.
-/
theorem symmetricIntervalIntegral_tendsto_full
    {t : ℝ} {f : ℝ -> ℝ}
    (hInt : Integrable f) :
    Tendsto
      (fun n : ℕ => ∫ x in (t-(n:ℝ))..(t+(n:ℝ)), f x)
      atTop
      (𝓝 (∫ x : ℝ, f x)) := by
  let s : ℕ -> Set ℝ :=
    fun n => Set.Ioc (t - n) (t + n)
  have hsMeas : ∀ n, MeasurableSet (s n) :=
    fun _ => measurableSet_Ioc
  have hsMono : Monotone s := by
    intro m n hmn
    intro x hx
    dsimp [s] at hx ⊢
    have hmnR : (m : ℝ) <= n := by exact_mod_cast hmn
    constructor <;> linarith [hx.1, hx.2]
  have hsUnion : (⋃ n : ℕ, s n) = (Set.univ : Set ℝ) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt (|x-t| + 1)
    refine ⟨n,?_⟩
    dsimp [s]
    have habs :=
      abs_lt.mp (lt_trans (lt_add_one _) (by exact_mod_cast hn))
    constructor <;> linarith
  have hlim :=
    tendsto_setIntegral_of_monotone
      hsMeas hsMono
      (by simpa [hsUnion] using hInt.integrableOn)
  rw [hsUnion] at hlim
  simpa [s, intervalIntegral.integral_of_le] using hlim

def QuarticFourSignedPolePair.globalLinearModeDefect
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  - ∫ x : ℝ, W.signedOrdinateTest x

def QuarticFourSignedPolePair.globalCubicModeDefect
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  -3 * ∫ x : ℝ,
    W.signedOrdinateTest x * (x-t)^2

theorem QuarticFourSignedPolePair.centeredPsiMassAt_tendsto_full
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    Tendsto W.centeredPsiMassAt atTop
      (𝓝 (∫ x : ℝ, W.signedOrdinateTest x)) := by
  unfold QuarticFourSignedPolePair.centeredPsiMassAt
  exact symmetricIntervalIntegral_tendsto_full
    (W.signedOrdinateTest_integrable ht)

theorem QuarticFourSignedPolePair.centeredPsiSecondMassAt_tendsto_full
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    Tendsto W.centeredPsiSecondMassAt atTop
      (𝓝 (∫ x : ℝ,
        W.signedOrdinateTest x * (x-t)^2)) := by
  unfold QuarticFourSignedPolePair.centeredPsiSecondMassAt
  exact symmetricIntervalIntegral_tendsto_full
    (W.signedOrdinateTest_mul_centeredSq_integrable ht)

/--
The finite centered-linear quotient defect converges to one concrete global
Psi moment.
-/
theorem QuarticFourSignedPolePair.centeredModeDefectAt_one_tendsto_global
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    Tendsto
      (fun n : ℕ => W.centeredModeDefectAt n 1)
      atTop
      (𝓝 W.globalLinearModeDefect) := by
  have hb :=
    (W.linearBoundary_tendsto_zero ht).const_mul 2
  have hm :=
    W.centeredPsiMassAt_tendsto_full ht
  have h :=
    hb.sub hm
  apply h.congr'
  filter_upwards with n
  rw [W.centeredModeDefectAt_one_eq ht]
  unfold QuarticFourSignedPolePair.globalLinearModeDefect
  rfl

/--
The finite centered-cubic quotient defect converges to the weighted global Psi
moment made legitimate by the C4 lift.
-/
theorem QuarticFourSignedPolePair.centeredModeDefectAt_three_tendsto_global
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    Tendsto
      (fun n : ℕ => W.centeredModeDefectAt n 3)
      atTop
      (𝓝 W.globalCubicModeDefect) := by
  have hb :=
    (W.cubicBoundary_tendsto_zero ht).const_mul 2
  have hm :=
    (W.centeredPsiSecondMassAt_tendsto_full ht).const_mul (-3)
  have h :=
    hb.add hm
  apply h.congr'
  filter_upwards with n
  rw [W.centeredModeDefectAt_three_eq ht]
  unfold QuarticFourSignedPolePair.globalCubicModeDefect
  ring


def QuarticFourSignedPolePair.centeredCompletedResidualCubicShiftAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (a0 a1 a2 a3 : ℝ)
    (n : ℕ) : ℝ :=
  W.centeredCompletedFunctionalAt n
    (fun x =>
      centeredZetaMuDiscrepancy t x
        + centeredCubicLowMode t a0 a1 a2 a3 x)

/--
Exact finite shift formula on the actual G3 discrepancy carrier.
-/
theorem QuarticFourSignedPolePair.centeredCompletedResidualCubicShiftAt_eq
    {t a0 a1 a2 a3 : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.centeredCompletedResidualCubicShiftAt a0 a1 a2 a3 n
      =
    W.centeredCompletedResidualAt n
      -
    (1/2 : ℝ) *
      (a1 * W.centeredModeDefectAt n 1
        + a3 * W.centeredModeDefectAt n 3) := by
  unfold QuarticFourSignedPolePair.centeredCompletedResidualCubicShiftAt
  have hE :
      IntervalIntegrable
        (fun x : ℝ =>
          W.signedOrdinateTestDeriv x
            * centeredZetaMuDiscrepancy t x)
        volume (t - (n : ℝ)) (t + (n : ℝ)) := by
    exact W.centeredAbelIntegrand_intervalIntegrable ht
  rw [W.centeredCompletedFunctionalAt_add_cubicLowMode
      ht n (centeredZetaMuDiscrepancy t) hE]
  rw [← W.centeredCompletedResidualAt_eq_generic ht n]

def QuarticFourSignedPolePair.globalCubicShiftDefect
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (a1 a3 : ℝ) : ℝ :=
  -(1/2 : ℝ) *
    (a1 * W.globalLinearModeDefect
      + a3 * W.globalCubicModeDefect)

/--
The finite cubic-shift defect converges to the exact linear combination of the
two global odd-mode obstructions.
-/
theorem QuarticFourSignedPolePair.centeredCompletedResidualCubicShift_diff_tendsto
    {t a0 a1 a2 a3 : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    Tendsto
      (fun n : ℕ =>
        W.centeredCompletedResidualCubicShiftAt a0 a1 a2 a3 n
          - W.centeredCompletedResidualAt n)
      atTop
      (𝓝 (W.globalCubicShiftDefect a1 a3)) := by
  have h1 :=
    W.centeredModeDefectAt_one_tendsto_global ht
  have h3 :=
    W.centeredModeDefectAt_three_tendsto_global ht
  have hlin :
      Tendsto
        (fun n : ℕ =>
          a1 * W.centeredModeDefectAt n 1
            + a3 * W.centeredModeDefectAt n 3)
        atTop
        (𝓝 (a1 * W.globalLinearModeDefect
          + a3 * W.globalCubicModeDefect)) :=
    (tendsto_const_nhds.mul h1).add
      (tendsto_const_nhds.mul h3)
  have hscaled :
      Tendsto
        (fun n : ℕ =>
          -(1/2 : ℝ) *
            (a1 * W.centeredModeDefectAt n 1
              + a3 * W.centeredModeDefectAt n 3))
        atTop
        (𝓝 (W.globalCubicShiftDefect a1 a3)) := by
    unfold QuarticFourSignedPolePair.globalCubicShiftDefect
    exact tendsto_const_nhds.mul hlin
  apply hscaled.congr'
  filter_upwards with n
  rw [W.centeredCompletedResidualCubicShiftAt_eq ht]
  ring

def QuarticFourSignedPolePair.globalFullCubicQuotient
    {t : ℝ} (W : QuarticFourSignedPolePair t) : Prop :=
  W.globalLinearModeDefect = 0
    ∧ W.globalCubicModeDefect = 0

/--
If the two global odd defects vanish, every centered cubic discrepancy shift is
asymptotically invisible to the complete finite G3 functional.
-/
theorem QuarticFourSignedPolePair.globalFullCubicQuotient_implies_shiftInvisible
    {t a0 a1 a2 a3 : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hQ : W.globalFullCubicQuotient) :
    Tendsto
      (fun n : ℕ =>
        W.centeredCompletedResidualCubicShiftAt a0 a1 a2 a3 n
          - W.centeredCompletedResidualAt n)
      atTop (𝓝 0) := by
  have h :=
    W.centeredCompletedResidualCubicShift_diff_tendsto
      (a0:=a0) (a1:=a1) (a2:=a2) (a3:=a3) ht
  unfold QuarticFourSignedPolePair.globalFullCubicQuotient at hQ
  unfold QuarticFourSignedPolePair.globalCubicShiftDefect at h
  rw [hQ.1,hQ.2] at h
  simpa using h

/--
Conversely, asymptotic invisibility of the centered-linear and centered-cubic
unit shifts forces the two global odd defects to vanish.
-/
theorem QuarticFourSignedPolePair.globalFullCubicQuotient_of_unitShiftInvisible
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (h1 :
      Tendsto
        (fun n : ℕ =>
          W.centeredCompletedResidualCubicShiftAt 0 1 0 0 n
            - W.centeredCompletedResidualAt n)
        atTop (𝓝 0))
    (h3 :
      Tendsto
        (fun n : ℕ =>
          W.centeredCompletedResidualCubicShiftAt 0 0 0 1 n
            - W.centeredCompletedResidualAt n)
        atTop (𝓝 0)) :
    W.globalFullCubicQuotient := by
  have h1' :=
    W.centeredCompletedResidualCubicShift_diff_tendsto
      (a0:=0) (a1:=1) (a2:=0) (a3:=0) ht
  have h3' :=
    W.centeredCompletedResidualCubicShift_diff_tendsto
      (a0:=0) (a1:=0) (a2:=0) (a3:=1) ht
  have hu1 := tendsto_nhds_unique h1 h1'
  have hu3 := tendsto_nhds_unique h3 h3'
  unfold QuarticFourSignedPolePair.globalCubicShiftDefect at hu1 hu3
  unfold QuarticFourSignedPolePair.globalFullCubicQuotient
  constructor <;> nlinarith


/-!
## Frequency-space local obstruction coordinates

These are the same-object profile coordinates which Fourier inversion would
relate to the two global odd defects.  No Fourier normalization claim is made
here.
-/

theorem genericProjectivePhysicalProfile_zero
    (g : ℝ -> ℝ) (r : ℝ) :
    genericProjectivePhysicalProfile g r 0
      =
    4 * g 0 *
      (Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 r
        -
       Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 (2*r)) := by
  unfold genericProjectivePhysicalProfile
    Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.twoRadiusBracket
  simp

theorem quarticFourNormalizedProjectiveProfile_zero
    {R lam mu : ℝ}
    (hR : 0 < R) :
    quarticFourNormalizedProjectiveProfile R lam mu 0
      =
    4 * quarticFourWindowProfile R lam mu 0 *
      (quarticFourWindowPairing R lam mu
          (quarticFourNormalizedOnLineWeight 1)
        -
       quarticFourWindowPairing R lam mu
          (quarticFourNormalizedOnLineWeight 2)) := by
  unfold quarticFourNormalizedProjectiveProfile
  rw [genericProjectivePhysicalProfile_zero]
  unfold Zeta23Bridge.LiteralWeilParityBalance.evenResp
  rw [quarticFourWindowProfile_pairing_eq
      (R:=R) (lam:=lam) (mu:=mu) hR
      (quarticFourNormalizedOnLineWeight_continuous 1),
      quarticFourWindowProfile_pairing_eq
      (R:=R) (lam:=lam) (mu:=mu) hR
      (quarticFourNormalizedOnLineWeight_continuous 2)]
  unfold quarticFourNormalizedOnLineWeight
  simp

/--
Exact local profile value carried by the signed-pole combination.

Nothing in the already-paid pole cancellation rewrites this expression to
zero: it is a distinct same-object coordinate.
-/
theorem QuarticFourSignedPolePair.combinedProfile_zero_eq
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t 0
      =
    W.poleTwo *
      (4 * quarticFourWindowProfile W.R (1/2) W.muHalf 0 *
        (quarticFourWindowPairing W.R (1/2) W.muHalf
            (quarticFourNormalizedOnLineWeight 1)
          -
         quarticFourWindowPairing W.R (1/2) W.muHalf
            (quarticFourNormalizedOnLineWeight 2)))
      +
    (-W.poleHalf) *
      (4 * quarticFourWindowProfile W.R (2/3) W.muTwo 0 *
        (quarticFourWindowPairing W.R (2/3) W.muTwo
            (quarticFourNormalizedOnLineWeight 1)
          -
         quarticFourWindowPairing W.R (2/3) W.muTwo
            (quarticFourNormalizedOnLineWeight 2))) := by
  unfold quarticFourSignedPoleCombinedProfile profileLinearCombination
  rw [quarticFourNormalizedProjectiveProfile_zero
        (lam:=(1/2 : ℝ)) (mu:=W.muHalf) W.Rpos,
      quarticFourNormalizedProjectiveProfile_zero
        (lam:=(2/3 : ℝ)) (mu:=W.muTwo) W.Rpos]


/--
A compact C4 profile has an integrable cosine transform.
-/
theorem compactCosineTransform_integrable_of_contDiff_four
    {P : ℝ -> ℝ}
    (hP : ContDiff ℝ 4 P)
    (hPc : HasCompactSupport P) :
    Integrable (compactCosineTransform P) := by
  let A : ℝ := compactCosineFourthDecayCurvature P
  let B : ℝ :=
    Zeta23Bridge.LiteralWeilProjectiveStripConstant.taperMass P
  let C : ℝ := 2 * (A + B)
  have hA : 0 <= A := by
    dsimp [A]
    exact compactCosineFourthDecayCurvature_nonneg P
  have hB : 0 <= B := by
    dsimp [B]
    exact
      Zeta23Bridge.LiteralWeilProjectiveStripConstant.taperMass_nonneg P
  have hC : 0 <= C := by
    dsimp [C]
    positivity
  have hbase :
      Integrable (fun q : ℝ => (1 + q^2)⁻¹) :=
    integrable_inv_one_add_sq
  have hmajor :
      Integrable (fun q : ℝ => C * (1 + q^2)⁻¹) :=
    hbase.const_mul C
  have hCT :
      Continuous (compactCosineTransform P) := by
    exact continuous_of_forall_continuousAt fun q =>
      (compactCosineTransform_hasDerivAt
        hP.continuous hPc q).continuousAt
  refine Integrable.mono' hmajor hCT.aestronglyMeasurable
    (ae_of_all _ fun q => ?_)
  have hden : 0 < 1 + q^2 := by positivity
  have hmajorAbs :
      |C * (1 + q^2)⁻¹|
        = C / (1 + q^2) := by
    rw [abs_mul, abs_of_nonneg hC, abs_inv,
        abs_of_pos hden]
    rfl
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hmajorAbs]
  by_cases hq : q^2 <= 1
  · have hcos :
        |compactCosineTransform P q| <= B := by
      dsimp [B]
      exact compactCosineTransform_abs_le_taperMass
        hP.continuous hPc q
    have hshape : B * (1+q^2) <= C := by
      dsimp [C]
      nlinarith [hA,hB]
    apply (le_div_iff₀ hden).2
    exact
      (mul_le_mul_of_nonneg_right hcos hden.le).trans hshape
  · have hq' : 1 < q^2 := lt_of_not_ge hq
    have hqne : q ≠ 0 := by
      intro hz
      subst q
      norm_num at hq'
    have hcos :
        |compactCosineTransform P q| <= A / q^4 := by
      dsimp [A]
      exact compactCosineTransform_abs_le_invPowFour hP hPc hqne
    have hshape :
        A * (1+q^2) <= C * q^4 := by
      have hq2non : 0 <= q^2 := sq_nonneg q
      have htwo : 1+q^2 <= 2*q^2 := by linarith
      have hq4 : q^2 <= q^4 := by
        have := mul_le_mul_of_nonneg_right hq'.le hq2non
        nlinarith
      have h1 :=
        mul_le_mul_of_nonneg_left htwo hA
      dsimp [C]
      nlinarith [mul_nonneg hB (pow_nonneg q 4)]
    have hfar :
        A / q^4 <= C / (1+q^2) := by
      have hq4pos : 0 < q^4 := by
        positivity
      rw [div_le_div_iff₀ hq4pos hden]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hshape
    exact hcos.trans hfar


/-!
## Fourier-normalization bridge for the global linear defect
-/

theorem genericProjectivePhysicalProfile_even_of_even
    {g : ℝ -> ℝ}
    (hg : ∀ u : ℝ, g (-u) = g u)
    (r u : ℝ) :
    genericProjectivePhysicalProfile g r (-u)
      =
    genericProjectivePhysicalProfile g r u := by
  unfold genericProjectivePhysicalProfile
    Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.twoRadiusBracket
  rw [hg]
  simp only [mul_neg, Real.cos_neg]
  ring

theorem quarticFourNormalizedProjectiveProfile_even
    {R lam mu : ℝ}
    (hR : 0 < R)
    (u : ℝ) :
    quarticFourNormalizedProjectiveProfile R lam mu (-u)
      =
    quarticFourNormalizedProjectiveProfile R lam mu u := by
  unfold quarticFourNormalizedProjectiveProfile
  exact genericProjectivePhysicalProfile_even_of_even
    (quarticFourWindowProfile_even
      (R:=R) (lam:=lam) (mu:=mu) hR) 1 u

theorem QuarticFourSignedPolePair.combinedProfile_even
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (u : ℝ) :
    quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t (-u)
      =
    quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t u := by
  unfold quarticFourSignedPoleCombinedProfile profileLinearCombination
  rw [quarticFourNormalizedProjectiveProfile_even
        (lam:=(1/2 : ℝ)) (mu:=W.muHalf) W.Rpos,
      quarticFourNormalizedProjectiveProfile_even
        (lam:=(2/3 : ℝ)) (mu:=W.muTwo) W.Rpos]

theorem integral_mul_sin_eq_zero_of_even_compact
    {P : ℝ -> ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (heven : ∀ u : ℝ, P (-u) = P u)
    (q : ℝ) :
    (∫ u : ℝ, P u * Real.sin (q*u)) = 0 := by
  let f : ℝ -> ℝ := fun u => P u * Real.sin (q*u)
  have hf : Integrable f := by
    dsimp [f]
    exact
      (hP.mul (by fun_prop)).integrable_of_hasCompactSupport
        hPc.mul_right
  have hreflect :
      (∫ u : ℝ, f (-u)) = ∫ u : ℝ, f u := by
    exact integral_neg_eq_self
  have hodd : ∀ u : ℝ, f (-u) = - f u := by
    intro u
    dsimp [f]
    rw [heven]
    simp
    ring
  have hneg :
      (∫ u : ℝ, f (-u)) = - ∫ u : ℝ, f u := by
    calc
      (∫ u : ℝ, f (-u))
        = ∫ u : ℝ, - f u := by
          apply integral_congr_ae
          exact ae_of_all _ hodd
      _ = - ∫ u : ℝ, f u := by
          rw [integral_neg]
  have hz : (∫ u : ℝ, f u) = 0 := by
    linarith
  simpa [f] using hz

def complexifyRealProfile
    (P : ℝ -> ℝ) : ℝ -> ℂ :=
  fun u => (P u : ℂ)

theorem complexifyRealProfile_integrable
    {P : ℝ -> ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P) :
    Integrable (complexifyRealProfile P) := by
  unfold complexifyRealProfile
  exact
    (Complex.continuous_ofReal.comp hP)
      .integrable_of_hasCompactSupport hPc

/--
For an even real compact profile, Mathlib's 2pi-normalized complex Fourier
transform is exactly the real cosine transform at frequency 2*pi*xi.
-/
theorem fourier_complexify_even_eq_compactCosine
    {P : ℝ -> ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (heven : ∀ u : ℝ, P (-u) = P u)
    (xi : ℝ) :
    𝓕 (complexifyRealProfile P) xi
      =
    (compactCosineTransform P (2 * Real.pi * xi) : ℂ) := by
  have hsin :
      (∫ u : ℝ,
        P u * Real.sin ((2 * Real.pi * xi) * u)) = 0 :=
    integral_mul_sin_eq_zero_of_even_compact
      hP hPc heven (2 * Real.pi * xi)
  have hcosInt :
      Integrable
        (fun u : ℝ =>
          P u * Real.cos ((2 * Real.pi * xi) * u)) :=
    (hP.mul (by fun_prop)).integrable_of_hasCompactSupport hPc.mul_right
  have hsinInt :
      Integrable
        (fun u : ℝ =>
          P u * Real.sin ((2 * Real.pi * xi) * u)) :=
    (hP.mul (by fun_prop)).integrable_of_hasCompactSupport hPc.mul_right
  rw [Real.fourier_eq']
  apply Complex.ext
  · rw [← integral_re]
    · unfold compactCosineTransform
      simp only [Complex.smul_re, Complex.ofReal_re]
      congr with u
      simp [Complex.exp_mul_I, real_inner_comm]
      ring
    · exact
        ((Complex.continuous_exp.comp
          (by fun_prop)).smul
          (Complex.continuous_ofReal.comp hP))
          .integrable_of_hasCompactSupport hPc.smul_left
  · rw [← integral_im]
    · simp only [Complex.smul_im, Complex.ofReal_re]
      have him :
          (fun u : ℝ =>
            (Complex.exp
              ((↑(-2 * Real.pi * ⟪u, xi⟫_ℝ) * Complex.I))
              • (P u : ℂ)).im)
          =
          fun u =>
            - (P u * Real.sin ((2 * Real.pi * xi) * u)) := by
        funext u
        simp [Complex.exp_mul_I, real_inner_comm]
        ring
      rw [him, integral_neg, hsin]
      simp
    · exact
        ((Complex.continuous_exp.comp
          (by fun_prop)).smul
          (Complex.continuous_ofReal.comp hP))
          .integrable_of_hasCompactSupport hPc.smul_left


theorem fourier_complexify_even_integrable
    {P : ℝ -> ℝ}
    (hP4 : ContDiff ℝ 4 P)
    (hPc : HasCompactSupport P)
    (heven : ∀ u : ℝ, P (-u) = P u) :
    Integrable (𝓕 (complexifyRealProfile P)) := by
  have hC :
      Integrable (compactCosineTransform P) :=
    compactCosineTransform_integrable_of_contDiff_four hP4 hPc
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hscaled :
      Integrable
        (fun xi : ℝ =>
          compactCosineTransform P (xi * (2 * Real.pi))) :=
    hC.comp_mul_right' h2pi
  have hscaledC :
      Integrable
        (fun xi : ℝ =>
          (compactCosineTransform P
            (2 * Real.pi * xi) : ℂ)) := by
    have h := hscaled.ofReal (𝕜 := ℂ)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  refine hscaledC.congr ?_
  exact ae_of_all _ fun xi => by
    rw [fourier_complexify_even_eq_compactCosine
      hP4.continuous hPc heven xi]

/--
Fourier inversion with Mathlib's 2*pi convention gives the exact whole-line
cosine-transform mass.
-/
theorem integral_compactCosineTransform_eq_two_pi_mul_value
    {P : ℝ -> ℝ}
    (hP4 : ContDiff ℝ 4 P)
    (hPc : HasCompactSupport P)
    (heven : ∀ u : ℝ, P (-u) = P u) :
    (∫ q : ℝ, compactCosineTransform P q)
      =
    2 * Real.pi * P 0 := by
  let Pc : ℝ -> ℂ := complexifyRealProfile P
  have hPcInt : Integrable Pc := by
    dsimp [Pc]
    exact complexifyRealProfile_integrable hP4.continuous hPc
  have hFInt : Integrable (𝓕 Pc) := by
    dsimp [Pc]
    exact fourier_complexify_even_integrable hP4 hPc heven
  have hPcCont : Continuous Pc := by
    dsimp [Pc, complexifyRealProfile]
    exact Complex.continuous_ofReal.comp hP4.continuous
  have hinv :=
    hPcInt.fourierInv_fourier_eq
      hFInt (v := (0 : ℝ)) hPcCont.continuousAt
  rw [Real.fourierInv_eq'] at hinv
  simp only [inner_zero_right, mul_zero, neg_zero,
    Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul] at hinv
  have hfun :
      (fun xi : ℝ => 𝓕 Pc xi)
        =
      fun xi =>
        (compactCosineTransform P
          (2 * Real.pi * xi) : ℂ) := by
    funext xi
    dsimp [Pc]
    exact fourier_complexify_even_eq_compactCosine
      hP4.continuous hPc heven xi
  rw [hfun, integral_ofReal] at hinv
  have hscaled :
      (∫ xi : ℝ,
        compactCosineTransform P
          (2 * Real.pi * xi))
        = P 0 := by
    exact Complex.ofReal_injective hinv
  have hscale :=
    Measure.integral_comp_mul_right
      (compactCosineTransform P) (2 * Real.pi)
  have h2pi : 0 < (2 * Real.pi : ℝ) := by positivity
  have hscale' :
      P 0
        =
      (2 * Real.pi)⁻¹
        * (∫ q : ℝ, compactCosineTransform P q) := by
    rw [← hscaled]
    calc
      (∫ xi : ℝ,
        compactCosineTransform P
          (2 * Real.pi * xi))
        =
      (∫ xi : ℝ,
        compactCosineTransform P
          (xi * (2 * Real.pi))) := by
          apply integral_congr_ae
          exact ae_of_all _ fun xi => by
            congr 1
            ring
      _ =
      |(2 * Real.pi)⁻¹| •
        (∫ q : ℝ, compactCosineTransform P q) := hscale
      _ =
      (2 * Real.pi)⁻¹ *
        (∫ q : ℝ, compactCosineTransform P q) := by
          rw [abs_of_pos (inv_pos.mpr h2pi)]
          rfl
  have h2pine : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt h2pi
  field_simp [h2pine] at hscale' ⊢
  nlinarith

/--
Physical rescaling of the exact signed test:
  integral Psi_t = (2*pi/r) P_comb(0), r=t/16.
-/
theorem QuarticFourSignedPolePair.integral_signedOrdinateTest_eq_profile_zero
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    (∫ x : ℝ, W.signedOrdinateTest x)
      =
    (2 * Real.pi / (t/16))
      *
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t 0 := by
  let r : ℝ := t/16
  let P :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hCInt :
      Integrable (compactCosineTransform P) :=
    compactCosineTransform_integrable_of_contDiff_four
      (quarticFourSignedPoleCombinedProfile_contDiff_four W.Rpos)
      (quarticFourSignedPoleCombinedProfile_compact W.Rpos)
  have hCmass :
      (∫ q : ℝ, compactCosineTransform P q)
        = 2 * Real.pi * P 0 := by
    exact integral_compactCosineTransform_eq_two_pi_mul_value
      (quarticFourSignedPoleCombinedProfile_contDiff_four W.Rpos)
      (quarticFourSignedPoleCombinedProfile_compact W.Rpos)
      W.combinedProfile_even
  have hshift :
      (∫ x : ℝ,
        compactCosineTransform P ((x-t)/r))
        =
      ∫ y : ℝ, compactCosineTransform P (y/r) := by
    simpa [sub_eq_add_neg] using
      (integral_sub_right_eq_self
        (fun y : ℝ => compactCosineTransform P (y/r)) t).symm
  have hscale :=
    Measure.integral_comp_div
      (compactCosineTransform P) r
  have hscaled :
      (∫ x : ℝ,
        compactCosineTransform P ((x-t)/r))
        =
      r * (∫ q : ℝ, compactCosineTransform P q) := by
    rw [hshift, hscale, abs_of_pos hr]
    rfl
  rw [W.signedOrdinateTest_eq_combinedCosine]
  dsimp [r,P]
  rw [integral_const_mul, hscaled, hCmass]
  field_simp [ne_of_gt hr]
  ring

/--
The global centered-linear quotient defect is exactly the zero-frequency
local profile obstruction.
-/
theorem QuarticFourSignedPolePair.globalLinearModeDefect_eq_profile_zero
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.globalLinearModeDefect
      =
    -(2 * Real.pi / (t/16))
      *
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t 0 := by
  unfold QuarticFourSignedPolePair.globalLinearModeDefect
  rw [W.integral_signedOrdinateTest_eq_profile_zero ht]
  ring

theorem QuarticFourSignedPolePair.globalLinearModeDefect_eq_zero_iff
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.globalLinearModeDefect = 0
      ↔
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t 0 = 0 := by
  rw [W.globalLinearModeDefect_eq_profile_zero ht]
  have hcoef :
      -(2 * Real.pi / (t/16)) ≠ 0 := by
    have hr : t/16 ≠ 0 := by positivity
    positivity
  exact mul_eq_zero_iff_right_nonzero hcoef


theorem compactCosineTransform_sqWeight_integrable_of_contDiff_four
    {P : ℝ -> ℝ}
    (hP : ContDiff ℝ 4 P)
    (hPc : HasCompactSupport P) :
    Integrable
      (fun q : ℝ => q^2 * compactCosineTransform P q) := by
  let A : ℝ := compactCosineFourthDecayCurvature P
  let B : ℝ :=
    Zeta23Bridge.LiteralWeilProjectiveStripConstant.taperMass P
  let C : ℝ := 2 * (A + B)
  have hA : 0 <= A := by
    dsimp [A]
    exact compactCosineFourthDecayCurvature_nonneg P
  have hB : 0 <= B := by
    dsimp [B]
    exact
      Zeta23Bridge.LiteralWeilProjectiveStripConstant.taperMass_nonneg P
  have hC : 0 <= C := by
    dsimp [C]
    positivity
  have hbase :
      Integrable (fun q : ℝ => (1 + q^2)⁻¹) :=
    integrable_inv_one_add_sq
  have hmajor :
      Integrable (fun q : ℝ => C * (1 + q^2)⁻¹) :=
    hbase.const_mul C
  have hCT :
      Continuous (compactCosineTransform P) :=
    continuous_of_forall_continuousAt fun q =>
      (compactCosineTransform_hasDerivAt
        hP.continuous hPc q).continuousAt
  have htargetC :
      Continuous
        (fun q : ℝ => q^2 * compactCosineTransform P q) := by
    fun_prop
  refine Integrable.mono' hmajor htargetC.aestronglyMeasurable
    (ae_of_all _ fun q => ?_)
  have hden : 0 < 1 + q^2 := by positivity
  have hmajorAbs :
      |C * (1 + q^2)⁻¹|
        = C / (1 + q^2) := by
    rw [abs_mul, abs_of_nonneg hC, abs_inv,
        abs_of_pos hden]
    rfl
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_mul, abs_pow, hmajorAbs]
  by_cases hq : q^2 <= 1
  · have hcos :
        |compactCosineTransform P q| <= B := by
      dsimp [B]
      exact compactCosineTransform_abs_le_taperMass
        hP.continuous hPc q
    have hlocal :
        q^2 * |compactCosineTransform P q| * (1+q^2)
          <= C := by
      have hqnon : 0 <= q^2 := sq_nonneg q
      have h1 :=
        mul_le_mul_of_nonneg_left hcos hqnon
      have hshape : q^2 * (1+q^2) <= 2 := by
        nlinarith [sq_nonneg (1-q^2)]
      have h2 :
          q^2 * |compactCosineTransform P q| * (1+q^2)
            <= B * (q^2 * (1+q^2)) := by
        nlinarith [abs_nonneg (compactCosineTransform P q)]
      have h3 :
          B * (q^2 * (1+q^2)) <= 2*B :=
        mul_le_mul_of_nonneg_left hshape hB
      dsimp [C]
      nlinarith
    exact (le_div_iff₀ hden).2
      (by simpa [mul_assoc] using hlocal)
  · have hq' : 1 < q^2 := lt_of_not_ge hq
    have hqne : q ≠ 0 := by
      intro hz
      subst q
      norm_num at hq'
    have hcos :
        |compactCosineTransform P q| <= A / q^4 := by
      dsimp [A]
      exact compactCosineTransform_abs_le_invPowFour hP hPc hqne
    have hweighted :
        q^2 * |compactCosineTransform P q|
          <= A / q^2 := by
      have hm :=
        mul_le_mul_of_nonneg_left hcos (sq_nonneg q)
      calc
        q^2 * |compactCosineTransform P q|
          <= q^2 * (A / q^4) := hm
        _ = A / q^2 := by
          field_simp [hqne]
          ring
    have hshape :
        A * (1+q^2) <= C * q^2 := by
      have htwo : 1+q^2 <= 2*q^2 := by linarith
      have h1 := mul_le_mul_of_nonneg_left htwo hA
      dsimp [C]
      nlinarith [mul_nonneg hB (sq_nonneg q)]
    have hfar :
        A / q^2 <= C / (1+q^2) := by
      have hq2pos : 0 < q^2 := sq_pos_of_ne_zero hqne
      rw [div_le_div_iff₀ hq2pos hden]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hshape
    exact hweighted.trans hfar

theorem deriv_complexifyRealProfile_eq
    {P : ℝ -> ℝ}
    (hP : Differentiable ℝ P) :
    deriv (complexifyRealProfile P)
      =
    fun x => (deriv P x : ℂ) := by
  funext x
  have hx := (hP x).hasDerivAt
  have hc :=
    Complex.ofRealCLM.hasDerivAt.scomp x hx
  simpa [complexifyRealProfile] using hc.deriv

theorem secondDeriv_complexifyRealProfile_eq
    {P : ℝ -> ℝ}
    (hP2 : ContDiff ℝ 2 P) :
    deriv (deriv (complexifyRealProfile P))
      =
    fun x => (deriv (deriv P) x : ℂ) := by
  have hPdiff : Differentiable ℝ P :=
    hP2.differentiable (by norm_num)
  have hPd1 : ContDiff ℝ 1 (deriv P) :=
    (ContDiff.deriv' hP2)
  rw [deriv_complexifyRealProfile_eq hPdiff]
  exact deriv_complexifyRealProfile_eq
    (hPd1.differentiable (by norm_num))


/--
The weighted cosine-transform moment is the local second derivative of the
profile, with the exact sign and 2*pi normalization fixed by Mathlib's Fourier
convention.
-/
theorem integral_sq_mul_compactCosineTransform_eq_neg_two_pi_mul_secondDeriv
    {P : ℝ -> ℝ}
    (hP4 : ContDiff ℝ 4 P)
    (hPc : HasCompactSupport P)
    (heven : ∀ u : ℝ, P (-u) = P u) :
    (∫ q : ℝ, q^2 * compactCosineTransform P q)
      =
    - (2 * Real.pi) * deriv (deriv P) 0 := by
  let Pc : ℝ -> ℂ := complexifyRealProfile P
  have hPc4 : ContDiff ℝ 4 Pc := by
    dsimp [Pc, complexifyRealProfile]
    exact Complex.ofRealCLM.contDiff.comp hP4
  have hPcInt : Integrable Pc := by
    dsimp [Pc]
    exact complexifyRealProfile_integrable hP4.continuous hPc
  have hD1eq :
      deriv Pc = fun x => (deriv P x : ℂ) := by
    dsimp [Pc]
    exact deriv_complexifyRealProfile_eq
      (hP4.differentiable (by norm_num))
  have hP1 : ContDiff ℝ 3 (deriv P) :=
    ContDiff.deriv' hP4
  have hD1Int : Integrable (deriv Pc) := by
    rw [hD1eq]
    exact
      ((hP1.continuous.integrable_of_hasCompactSupport hPc.deriv)
        .ofReal (𝕜 := ℂ))
  have hD2eq :
      deriv (deriv Pc)
        =
      fun x => (deriv (deriv P) x : ℂ) := by
    dsimp [Pc]
    exact secondDeriv_complexifyRealProfile_eq
      (hP4.of_le (by norm_num))
  have hP2 : ContDiff ℝ 2 (deriv (deriv P)) :=
    ContDiff.deriv' hP1
  have hD2Int : Integrable (deriv (deriv Pc)) := by
    rw [hD2eq]
    exact
      ((hP2.continuous.integrable_of_hasCompactSupport
        hPc.deriv.deriv).ofReal (𝕜 := ℂ))
  have hPcDiff : Differentiable ℝ Pc :=
    hPc4.differentiable (by norm_num)
  have hD1Diff : Differentiable ℝ (deriv Pc) :=
    (ContDiff.deriv' hPc4).differentiable (by norm_num)
  have hF1 :=
    Real.fourier_deriv hPcInt hPcDiff hD1Int
  have hF2 :=
    Real.fourier_deriv hD1Int hD1Diff hD2Int
  have hF2point :
      ∀ xi : ℝ,
      𝓕 (deriv (deriv Pc)) xi
        =
      (- ((2 * Real.pi * xi)^2)
        * compactCosineTransform P
            (2 * Real.pi * xi) : ℂ) := by
    intro xi
    rw [congrFun hF2 xi, congrFun hF1 xi]
    dsimp [Pc]
    rw [fourier_complexify_even_eq_compactCosine
      hP4.continuous hPc heven xi]
    simp only [smul_eq_mul]
    rw [Complex.I_mul_I]
    push_cast
    ring
  have hSq :
      Integrable
        (fun q : ℝ =>
          q^2 * compactCosineTransform P q) :=
    compactCosineTransform_sqWeight_integrable_of_contDiff_four hP4 hPc
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hSqScaled :
      Integrable
        (fun xi : ℝ =>
          (xi * (2 * Real.pi))^2
            * compactCosineTransform P
                (xi * (2 * Real.pi))) :=
    hSq.comp_mul_right' h2pi
  have hSqScaledC :
      Integrable
        (fun xi : ℝ =>
          (- ((2 * Real.pi * xi)^2)
            * compactCosineTransform P
                (2 * Real.pi * xi) : ℂ)) := by
    have h :=
      (hSqScaled.neg).ofReal (𝕜 := ℂ)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hFD2Int :
      Integrable (𝓕 (deriv (deriv Pc))) := by
    refine hSqScaledC.congr ?_
    exact ae_of_all _ fun xi => (hF2point xi).symm
  have hD2cont :
      Continuous (deriv (deriv Pc)) :=
    (ContDiff.deriv' (ContDiff.deriv' hPc4)).continuous
  have hinv :=
    hD2Int.fourierInv_fourier_eq
      hFD2Int (v := (0 : ℝ)) hD2cont.continuousAt
  rw [Real.fourierInv_eq'] at hinv
  simp only [inner_zero_right, mul_zero, neg_zero,
    Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul] at hinv
  have hfun :
      (fun xi : ℝ => 𝓕 (deriv (deriv Pc)) xi)
        =
      fun xi =>
        (- ((2 * Real.pi * xi)^2)
          * compactCosineTransform P
              (2 * Real.pi * xi) : ℂ) := by
    funext xi
    exact hF2point xi
  rw [hfun] at hinv
  have hleftReal :
      (∫ xi : ℝ,
        - ((2 * Real.pi * xi)^2)
          * compactCosineTransform P
              (2 * Real.pi * xi))
        =
      deriv (deriv P) 0 := by
    rw [← integral_ofReal]
    rw [hD2eq] at hinv
    simpa using hinv
  have hscale :=
    Measure.integral_comp_mul_right
      (fun q : ℝ =>
        q^2 * compactCosineTransform P q)
      (2 * Real.pi)
  have h2pipos : 0 < (2 * Real.pi : ℝ) := by positivity
  have hscaledReal :
      (∫ xi : ℝ,
        (2 * Real.pi * xi)^2
          * compactCosineTransform P
              (2 * Real.pi * xi))
        =
      (2 * Real.pi)⁻¹
        *
      (∫ q : ℝ,
        q^2 * compactCosineTransform P q) := by
    calc
      (∫ xi : ℝ,
        (2 * Real.pi * xi)^2
          * compactCosineTransform P
              (2 * Real.pi * xi))
        =
      (∫ xi : ℝ,
        (xi * (2 * Real.pi))^2
          * compactCosineTransform P
              (xi * (2 * Real.pi))) := by
          apply integral_congr_ae
          exact ae_of_all _ fun xi => by
            congr 2 <;> ring
      _ =
      |(2 * Real.pi)⁻¹| •
      (∫ q : ℝ,
        q^2 * compactCosineTransform P q) := hscale
      _ =
      (2 * Real.pi)⁻¹
        *
      (∫ q : ℝ,
        q^2 * compactCosineTransform P q) := by
          rw [abs_of_pos (inv_pos.mpr h2pipos)]
          rfl
  have hnegscaled :
      -
      (∫ xi : ℝ,
        (2 * Real.pi * xi)^2
          * compactCosineTransform P
              (2 * Real.pi * xi))
        =
      deriv (deriv P) 0 := by
    rw [← hleftReal]
    rw [integral_neg]
  rw [hscaledReal] at hnegscaled
  have h2pine : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt h2pipos
  field_simp [h2pine] at hnegscaled ⊢
  nlinarith

/--
Physical weighted second moment:
  integral Psi_t(x) (x-t)^2 dx = -2*pi*r*P_comb''(0).
-/
theorem QuarticFourSignedPolePair.integral_signedOrdinateTest_centeredSq_eq_profile_secondDeriv
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    (∫ x : ℝ,
      W.signedOrdinateTest x * (x-t)^2)
      =
    - (2 * Real.pi) * (t/16)
      * deriv (deriv
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t)) 0 := by
  let r : ℝ := t/16
  let P :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  let G : ℝ -> ℝ :=
    fun q => q^2 * compactCosineTransform P q
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hGInt : Integrable G := by
    dsimp [G,P]
    exact
      compactCosineTransform_sqWeight_integrable_of_contDiff_four
        (quarticFourSignedPoleCombinedProfile_contDiff_four W.Rpos)
        (quarticFourSignedPoleCombinedProfile_compact W.Rpos)
  have hGmass :
      (∫ q : ℝ, G q)
        =
      - (2 * Real.pi)
        * deriv (deriv P) 0 := by
    dsimp [G,P]
    exact
      integral_sq_mul_compactCosineTransform_eq_neg_two_pi_mul_secondDeriv
        (quarticFourSignedPoleCombinedProfile_contDiff_four W.Rpos)
        (quarticFourSignedPoleCombinedProfile_compact W.Rpos)
        W.combinedProfile_even
  have hpoint :
      (fun x : ℝ =>
        W.signedOrdinateTest x * (x-t)^2)
      =
      fun x =>
        G ((x-t)/r) := by
    funext x
    rw [W.signedOrdinateTest_eq_combinedCosine]
    dsimp [G,r,P]
    field_simp [ne_of_gt hr]
    ring
  rw [hpoint]
  have hshift :
      (∫ x : ℝ, G ((x-t)/r))
        =
      ∫ y : ℝ, G (y/r) := by
    simpa [sub_eq_add_neg] using
      (integral_sub_right_eq_self
        (fun y : ℝ => G (y/r)) t).symm
  have hscale :=
    Measure.integral_comp_div G r
  rw [hshift, hscale, abs_of_pos hr, hGmass]
  dsimp [r,P]
  ring

/--
The global centered-cubic quotient defect is exactly the zero-frequency second
derivative of the signed combined profile.
-/
theorem QuarticFourSignedPolePair.globalCubicModeDefect_eq_profile_secondDeriv
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.globalCubicModeDefect
      =
    6 * Real.pi * (t/16)
      * deriv (deriv
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t)) 0 := by
  unfold QuarticFourSignedPolePair.globalCubicModeDefect
  rw [W.integral_signedOrdinateTest_centeredSq_eq_profile_secondDeriv ht]
  ring

theorem QuarticFourSignedPolePair.globalCubicModeDefect_eq_zero_iff
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.globalCubicModeDefect = 0
      ↔
    deriv (deriv
      (quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t)) 0 = 0 := by
  rw [W.globalCubicModeDefect_eq_profile_secondDeriv ht]
  have hcoef :
      6 * Real.pi * (t/16) ≠ 0 := by
    positivity
  exact mul_eq_zero_iff_right_nonzero hcoef

end Synthesis

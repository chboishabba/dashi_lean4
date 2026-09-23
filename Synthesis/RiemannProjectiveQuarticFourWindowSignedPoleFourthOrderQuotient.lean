import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleAbel

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

end Synthesis

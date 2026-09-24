import Synthesis.RiemannProjectiveQuarticUniformNegativeWindow
import Synthesis.RiemannZetaWindowNegativeMass
import Synthesis.RiemannZetaMuZeroCountOneSided

/-!
# Physical negative zero window for the quartic base kernel

A normalized uniform quartic window

  |q-q0| < delta,  Phi_Q(q) <= -eta

is transported to physical ordinate at radius r=t/16.  To avoid endpoint
issues we use the inner half-window

  A_t = t + r (q0-delta/2),
  B_t = t + r (q0+delta/2).

Every ordinate gamma in (A_t,B_t] then satisfies the strict normalized window
condition, and the physical q-only test

  phi_t(gamma)
    = r^-2 Phi_Q((gamma-t)/r)

obeys

  phi_t(gamma) <= -eta/r^2.

Therefore the literal multiplicity-weighted zeta contribution on that physical
window satisfies

  Z_phi(A_t,B_t) <= -(eta/r^2) N(A_t,B_t).

Combined with the existing one-sided N-mu theorem, this is the bridge from
quartic local sign to a quantitative negative actual-zero contribution.
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace Synthesis

open Zeta23

def quarticNegativeWindowRadius (t : ℝ) : ℝ := t / 16

def quarticNegativeWindowA
    {W : QuarticHighWitness}
    (U : QuarticBaseUniformNegativeWindow W)
    (t : ℝ) : ℝ :=
  t + quarticNegativeWindowRadius t * (U.q0 - U.delta/2)

def quarticNegativeWindowB
    {W : QuarticHighWitness}
    (U : QuarticBaseUniformNegativeWindow W)
    (t : ℝ) : ℝ :=
  t + quarticNegativeWindowRadius t * (U.q0 + U.delta/2)

def quarticNegativeOrdinateTest
    (W : QuarticHighWitness)
    (t gamma : ℝ) : ℝ :=
  let r := quarticNegativeWindowRadius t
  (1 / r^2) *
    genericProjectiveBaseKernel
      (quarticThreeWindowProfile W.R W.lam)
      1
      ((gamma-t)/r)

theorem quarticNegativeWindowA_lt_B
    {W : QuarticHighWitness}
    (U : QuarticBaseUniformNegativeWindow W)
    {t : ℝ} (ht : 0 < t) :
    quarticNegativeWindowA U t
      < quarticNegativeWindowB U t := by
  unfold quarticNegativeWindowA quarticNegativeWindowB
    quarticNegativeWindowRadius
  have hr : 0 < t/16 := by positivity
  have hd : 0 < U.delta := U.deltaPos
  nlinarith

theorem quarticNegativeWindow_normalizedGap_mem
    {W : QuarticHighWitness}
    (U : QuarticBaseUniformNegativeWindow W)
    {t gamma : ℝ} (ht : 0 < t)
    (hgamma :
      gamma ∈ Set.Ioc
        (quarticNegativeWindowA U t)
        (quarticNegativeWindowB U t)) :
    |((gamma-t) / quarticNegativeWindowRadius t) - U.q0|
      < U.delta := by
  unfold quarticNegativeWindowA quarticNegativeWindowB
    quarticNegativeWindowRadius at hgamma ⊢
  have hr : 0 < t/16 := by positivity
  rcases hgamma with ⟨hlo,hhi⟩
  rw [abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt]
    rw [lt_div_iff₀ hr]
    have hd : 0 < U.delta := U.deltaPos
    nlinarith
  · rw [sub_lt_iff_lt_add]
    rw [div_lt_iff₀ hr]
    have hd : 0 < U.delta := U.deltaPos
    nlinarith

theorem quarticNegativeOrdinateTest_le
    {W : QuarticHighWitness}
    (U : QuarticBaseUniformNegativeWindow W)
    {t gamma : ℝ} (ht : 0 < t)
    (hgamma :
      gamma ∈ Set.Ioc
        (quarticNegativeWindowA U t)
        (quarticNegativeWindowB U t)) :
    quarticNegativeOrdinateTest W t gamma
      <=
    -(U.eta / (quarticNegativeWindowRadius t)^2) := by
  have hr : 0 < quarticNegativeWindowRadius t := by
    unfold quarticNegativeWindowRadius
    positivity
  have hq :=
    quarticNegativeWindow_normalizedGap_mem U ht hgamma
  have hk :=
    U.upper
      (((gamma-t) / quarticNegativeWindowRadius t))
      hq
  unfold quarticNegativeOrdinateTest
  have hcoef : 0 <= 1 / (quarticNegativeWindowRadius t)^2 := by
    positivity
  have hm :=
    mul_le_mul_of_nonneg_left hk hcoef
  field_simp [hr.ne'] at hm ⊢
  nlinarith

/--
Exact negative actual-zero mass on the physical quartic subwindow.
-/
theorem quarticNegativeWindow_zeroPair_le
    (W : QuarticHighWitness)
    (U : QuarticBaseUniformNegativeWindow W)
    {t : ℝ} (ht : 0 < t) :
    zetaWindowWeightedPair
        (quarticNegativeWindowA U t)
        (quarticNegativeWindowB U t)
        (quarticNegativeOrdinateTest W t)
      <=
    -(U.eta / (quarticNegativeWindowRadius t)^2)
      * (Ncount
          (quarticNegativeWindowA U t)
          (quarticNegativeWindowB U t) : ℝ) := by
  apply zetaWindowWeightedPair_le_neg_mul_Ncount
  · positivity
  · intro rho hrho
    have hgamma :
        rho.im ∈ Set.Ioc
          (quarticNegativeWindowA U t)
          (quarticNegativeWindowB U t) := by
      exact ⟨hrho.2.1, hrho.2.2⟩
    exact quarticNegativeOrdinateTest_le U ht hgamma

end Synthesis

import Integration.Paper9ActualJSourceJet
import Integration.Paper9LiteralFactorialPrefix

/-! SOURCE-WRITTEN, UNCOMPILED.
Endpoint consumer on the actual CM point and original j/jet. The
remaining analytic producers are precisely j(cmTau)=-C and the
signed transverse jet equation; no assumption of the desired period,
hypergeometric value or a Bishop/Lean carrier equality. -/
namespace Integration.Paper9SignedCMPeriod

open Complex Function Filter UpperHalfPlane
open scoped Real Topology
open Integration.Paper9ActualCMPoint
open Integration.Paper9ActualJSourceJet
open Integration.Paper9OriginalEisensteinDerivative
open Integration.Paper9BracketCuspClosure
open Integration.Paper9EulerMobiusTransport
open Integration.Paper9E2CorrectedClosure
open Integration.Paper9HypergeometricQTransport
open Integration.Paper9CuspOrderFactorial
open Integration.Paper9RootODE
open Integration.Paper9HypergeometricSeriesODE
open Integration.Paper9SelectedCMDomain
open Integration.Paper9CM163CertificateConsumer

local notation "q" => qExt (cmTau : ℂ)
local notation "X" => x q
local notation "Y" => y q
local notation "E" => e2Q q
local notation "F" => rootF q
local notation "K" => (-(640320 : ℂ)^3)
local notation "p" => ((Real.pi * root163 / 2 : ℝ) : ℂ)
local notation "κ" => (-(77859659565707 : ℂ)/19943834790540897829879824384000)

noncomputable section

theorem cmBands : ‖X-1‖ ≤ 1/16 ∧ ‖Y-1‖ ≤ 1/16 :=
  originalBands q cmQSmall.le

theorem cmQNonzero : q ≠ 0 := Periodic.qParam_ne_zero 1 cmTau

theorem cmXPositive : 0 < X.re := positiveRe X cmBands.1
theorem cmYPositive : 0 < Y.re := positiveRe Y cmBands.2

theorem cmXNonzero : X ≠ 0 := by
  intro h
  have hp := cmXPositive
  rw [h] at hp
  simp at hp

theorem cmYNonzero : Y ≠ 0 := by
  intro h
  have hp := cmYPositive
  rw [h] at hp
  simp at hp

-- Same original q parameter under negative conjugation; E4/E6 reality
-- uses the pinned source conjugation law, not a replacement real series.
theorem cmNegConjQ : qExt (Integration.MoonshineEisensteinAgdaTarget.negConj cmTau : ℂ) = q := by
  have h (t : ℍ) : Integration.MoonshineEisensteinAgdaTarget.qOfTarget t = qExt t := by
    rw [Integration.MoonshineEisensteinAgdaTarget.qOfTarget_eq_qParam]
    simp [qExt, Integration.MoonshineEisensteinAnalytic.qParam, Periodic.qParam]
  rw [← h, Integration.MoonshineEisensteinAgdaTarget.qOfTarget_negConj, h]
  change conj (Periodic.qParam 1 (cmTau : ℂ)) = _
  rw [cmQPhase]
  simp [qExt,cmQPhase]

theorem cmXReal : ((X.re : ℝ) : ℂ) = X := by
  have h := Integration.MoonshineEisensteinAgdaTarget.mathlib_E4_negConj cmTau
  rw [← xAtQ,← xAtQ] at h
  change x (qExt (Integration.MoonshineEisensteinAgdaTarget.negConj cmTau : ℂ)) = conj X at h
  rw [cmNegConjQ] at h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  apply Complex.ext <;> simp
  linarith

theorem cmYReal : ((Y.re : ℝ) : ℂ) = Y := by
  have h := Integration.MoonshineEisensteinAgdaTarget.mathlib_E6_negConj cmTau
  rw [← yAtQ,← yAtQ] at h
  change y (qExt (Integration.MoonshineEisensteinAgdaTarget.negConj cmTau : ℂ)) = conj Y at h
  rw [cmNegConjQ] at h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  apply Complex.ext <;> simp
  linarith

-- Actual chosen branch is positive on the real-positive x slice.
def fReal : ℝ := Real.exp (Real.log X.re/2)
theorem fRealPositive : 0 < fReal := Real.exp_pos _
theorem cmFReal : (fReal : ℂ) = F := by
  unfold fReal rootF
  rw [Complex.ofReal_exp,Complex.ofReal_div,
    Complex.ofReal_log cmXPositive.le,cmXReal]
  norm_num

theorem cmFSquare : fReal^2 = X.re := by
  have h := rootFSquare q cmXNonzero
  rw [← cmFReal,← cmXReal] at h
  exact_mod_cast h

theorem cmPPositive : 0 < Real.pi*root163/2 := by
  have hr := root163_gt
  positivity

theorem cmPNonzero : p ≠ 0 := by exact_mod_cast cmPPositive.ne'

theorem cmJReal : ((Integration.MoonshineEisensteinAgdaTarget.jTarget cmTau).re : ℂ) = Integration.MoonshineEisensteinAgdaTarget.jTarget cmTau := by
  have h := Integration.MoonshineEisensteinAgdaTarget.jTarget_negConj cmTau
  rw [← jExtAt,← jExtAt] at h
  change jQ (qExt (Integration.MoonshineEisensteinAgdaTarget.negConj cmTau : ℂ)) = conj (jQ q) at h
  rw [cmNegConjQ] at h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  rw [← jExtAt]
  apply Complex.ext <;> simp [jExt]
  linarith

-- Actual first derivative, second derivative, and signed correction.
-- This closes the rational elimination from the Taylor source witness,
-- not the proof of that witness from the Hecke analytic identity.
theorem actualCMCorrection
    (hj : Integration.MoonshineEisensteinAgdaTarget.jTarget cmTau = K)
    (hκ : κ = deriv (deriv jExt) (cmTau : ℂ) /
      (deriv jExt (cmTau : ℂ))^2 +
      2/((2*cmPoint+1)*deriv jExt (cmTau : ℂ))) :
    (X/Y)*(E-3/p) = (77265280/90856689 : ℂ) := by
  have hq : ‖q‖ < 1 := qNorm cmTau
  have ha := (jExtDeriv (cmTau : ℂ) hq cmQNonzero cmXNonzero).deriv
  have hb := jExtSecond (cmTau : ℂ) hq cmQNonzero cmXNonzero
  have hJ : jQ q = K := (jExtAt cmTau).trans hj
  have hp : root163 ≠ 0 := by linarith [root163_gt]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hr : (root163 : ℂ) ≠ 0 := by exact_mod_cast hp
  have hgamma : 2*cmPoint+1 = Complex.I*(root163 : ℂ) := by
    unfold cmPoint
    ring
  rw [ha,hb,hgamma] at hκ
  unfold jFirst secondEuler jExt at hκ
  rw [hJ] at hκ
  have hκ' : κ = (K*(-E*X*Y+3*X^3+4*Y^2)/(6*X^2))/
      (K*Y/X)^2+X/(2*K*p*Y) := by
    rw [hκ]
    unfold scaleD
    field_simp [cmXNonzero,cmYNonzero,hπ,hr,Complex.I_ne_zero] <;>
      ring_nf <;> simp [Complex.I_sq]
  have h := correctionFromJet X Y E K p κ cmXNonzero cmYNonzero
    (by norm_num) cmPNonzero hκ'
  have hz := actualJZ cmTau cmXNonzero
    (Integration.MoonshineDeltaFinalMinCut.normalizedDelta_ne_zero_canonical cmTau)
  rw [hj] at hz
  change K*(1-Y^2/X^3)=1728 at hz
  have hr : X^3/Y^2 = K/(K-1728) := by
    field_simp [cmXNonzero,cmYNonzero] at hz ⊢
    linear_combination hz
  rw [hr] at h
  norm_num at h
  exact h.symm

-- Reverse solve the final positive ratio, retaining F*x/y and its sign.
theorem actualPositiveRatio (hj : Integration.MoonshineEisensteinAgdaTarget.jTarget cmTau = K) :
    F*X/Y =
      ((1/Real.sqrt (1+1728/(640320^3 : ℝ)) : ℝ) : ℂ) := by
  have hz := actualJZ cmTau cmXNonzero
    (Integration.MoonshineDeltaFinalMinCut.normalizedDelta_ne_zero_canonical cmTau)
  rw [hj] at hz
  change K*(1-Y^2/X^3)=1728 at hz
  rw [← cmXReal,← cmYReal] at hz
  have hxy : (-(640320 : ℝ)^3)*(1-Y.re^2/X.re^3)=1728 := by exact_mod_cast hz
  let v : ℝ := Real.sqrt (1+1728/(640320^3 : ℝ))
  have hv : 0 < v := Real.sqrt_pos.2 (by positivity)
  have hs : v^2=1+1728/(640320^3 : ℝ) := Real.sq_sqrt (by positivity)
  have hpos : 0 < fReal*X.re/Y.re := by
    exact div_pos (mul_pos fRealPositive cmXPositive) cmYPositive
  have hsq : (fReal*X.re/Y.re)^2=(1/v)^2 := by
    rw [mul_pow,div_pow,cmFSquare,div_pow,hs]
    field_simp [cmXPositive.ne',cmYPositive.ne'] at hxy ⊢
    nlinarith [hxy]
  have he : fReal*X.re/Y.re=1/v := by
    have hn : 0 < 1/v := by positivity
    have hprod : (fReal*X.re/Y.re-1/v)*(fReal*X.re/Y.re+1/v)=0 := by nlinarith [hsq]
    have hsum : fReal*X.re/Y.re+1/v ≠ 0 := ne_of_gt (add_pos hpos hn)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hsum)
  rw [← cmFReal,← cmXReal,← cmYReal]
  exact_mod_cast he

end
end Integration.Paper9SignedCMPeriod

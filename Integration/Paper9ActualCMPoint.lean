import Integration.Paper9CM163CertificateConsumer

/-! SOURCE-WRITTEN, UNCOMPILED.
The actual upper-half-plane CM163 point, its q phase, and the original
degree-41 fixed Hecke chart. No replacement CM point or inverse j.
The analytic Hecke product and dyadic source reflection remain separate.
-/
namespace Integration.Paper9ActualCMPoint

open Complex Function UpperHalfPlane
open scoped Real Topology
open Integration.Paper9OriginalEisensteinDerivative
open Integration.Paper9HypergeometricQTransport
open Integration.Paper9CuspOrderFactorial
open Integration.Paper9SelectedCMDomain

noncomputable section

def root163 : ℝ := Real.sqrt 163
theorem root163_sq : root163^2 = 163 := by
  unfold root163
  exact Real.sq_sqrt (by norm_num)
theorem root163_gt : 12 < root163 := by
  have hp : 0 ≤ root163 := Real.sqrt_nonneg _
  nlinarith [root163_sq]

def cmPoint : ℂ := (-1+Complex.I*(root163 : ℂ))/2
theorem cmPoint_re : cmPoint.re = -1/2 := by
  simp [cmPoint,Complex.div_re]
theorem cmPoint_im : cmPoint.im = root163/2 := by
  simp [cmPoint,Complex.div_im]
def cmTau : ℍ := ⟨cmPoint, by rw [cmPoint_im]; linarith [root163_gt]⟩

theorem cmQuadratic : cmPoint^2+cmPoint+41 = 0 := by
  have hs : (root163 : ℂ)^2 = 163 := by exact_mod_cast root163_sq
  unfold cmPoint
  linear_combination (Complex.I^2/4)*hs +
    (163/4 : ℂ)*Complex.I_sq

theorem cmApart : cmPoint+1 ≠ 0 := by
  intro he
  have h : cmPoint = -1 := by linear_combination he
  have hz := cmQuadratic
  rw [h] at hz
  norm_num at hz

def hecke (t : ℂ) := -41/(t+1)
def tangent (t : ℂ) := 41/(t+1)^2
def secondTangent (t : ℂ) := -82/(t+1)^3

theorem heckeDerivative (t : ℂ) (ht : t+1 ≠ 0) :
    HasDerivAt hecke (tangent t) t := by
  have h := (hasDerivAt_const t (-41 : ℂ)).div
    ((hasDerivAt_id t).add_const 1) ht
  convert h using 1 <;> simp [hecke,tangent] <;> ring

theorem heckeSecondDerivative (t : ℂ) (ht : t+1 ≠ 0) :
    HasDerivAt tangent (secondTangent t) t := by
  have h := (hasDerivAt_const t (41 : ℂ)).div
    (((hasDerivAt_id t).add_const 1).pow 2) (pow_ne_zero 2 ht)
  convert h using 1 <;> simp [tangent,secondTangent] <;>
    field_simp [ht] <;> ring

theorem fixedPoint : hecke cmPoint = cmPoint := by
  unfold hecke
  apply (div_eq_iff cmApart).2
  linear_combination -cmQuadratic

theorem tangentRatio : tangent cmPoint = -cmPoint/(cmPoint+1) := by
  unfold tangent
  field_simp [cmApart]
  linear_combination cmQuadratic

-- The actual signed branch, not a square-root choice made by the consumer.
theorem signedOrientation :
    82*tangent cmPoint+81 = -(2*cmPoint+1) := by
  rw [tangentRatio]
  field_simp [cmApart]
  linear_combination 2*cmQuadratic

theorem signedOrientationActual :
    82*tangent cmPoint+81 = -Complex.I*(root163 : ℂ) := by
  rw [signedOrientation]
  unfold cmPoint
  ring

theorem tangentPolynomial :
    41*(tangent cmPoint)^2+81*tangent cmPoint+41 = 0 := by
  rw [tangentRatio]
  field_simp [cmApart]
  linear_combination cmQuadratic

theorem gammaIdentity :
    secondTangent cmPoint*(2*cmPoint+1) =
      2*((tangent cmPoint)^2-tangent cmPoint) := by
  rw [tangentRatio]
  unfold secondTangent
  field_simp [cmApart]
  linear_combination -(4*cmPoint+2)*cmQuadratic

-- q is the actual pinned level-one parameter; keep its negative phase.
theorem cmQPhase : Periodic.qParam 1 (cmTau : ℂ) =
    -(Real.exp (-Real.pi*root163) : ℂ) := by
  change Periodic.qParam 1 cmPoint = _
  unfold Periodic.qParam
  have he : 2*(Real.pi : ℂ)*Complex.I*cmPoint/1 =
      ((-Real.pi*root163 : ℝ) : ℂ)+(-((Real.pi : ℂ)*Complex.I)) := by
    unfold cmPoint
    push_cast
    linear_combination ((Real.pi : ℂ)*(root163 : ℂ))*Complex.I_sq
  rw [he,Complex.exp_add,← Complex.ofReal_exp,Complex.exp_neg,
    Complex.exp_pi_mul_I]
  norm_num

theorem cmQSmall : ‖Periodic.qParam 1 (cmTau : ℂ)‖ < (1/2 : ℝ)^36 := by
  rw [cmQPhase,norm_neg,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hp := Real.pi_gt_three
  have hr := root163_gt
  have ht : 36 < Real.pi*root163 := by nlinarith
  have hExp : (2 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    linarith
  calc
    Real.exp (-Real.pi*root163) < Real.exp (-36) :=
      Real.exp_lt_exp.mpr (by linarith)
    _ = ((Real.exp 1)⁻¹)^36 := by
      rw [Real.exp_neg,show (36 : ℝ)=(36 : ℕ)*(1 : ℝ) by norm_num,
        Real.exp_nat_mul,inv_pow]
    _ < (1/2 : ℝ)^36 := by
      apply pow_lt_pow_left₀
      · exact inv_nonneg.mpr (Real.exp_pos _).le
      · simpa [one_div] using (inv_lt_inv₀ (Real.exp_pos 1)
          (by norm_num : (0:ℝ)<2)).2 hExp
      · decide

theorem selectedHyperAtCM :
    rootF (Periodic.qParam 1 (cmTau : ℂ)) =
      H (zCoord (Periodic.qParam 1 (cmTau : ℂ))) :=
  actualHyperIdentitySelected _ cmQSmall

theorem selectedFirstJetAtCM :
    L rootF (Periodic.qParam 1 (cmTau : ℂ)) =
      Integration.Paper9HypergeometricSeriesODE.jet 1
        (zCoord (Periodic.qParam 1 (cmTau : ℂ))) :=
  actualHyperFirstJetSelected _ cmQSmall

end
end Integration.Paper9ActualCMPoint

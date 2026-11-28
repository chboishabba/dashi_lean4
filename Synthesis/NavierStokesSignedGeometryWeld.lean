import Synthesis.MillenniumNSSignedSpectralResidualExact
import Synthesis.NavierStokesR854RealTimeIntegratedRateConditionalExact
import Mathlib

/-! Native proof lane. Classical curl bilinearity and ordered field
arithmetic; DASHI signed residual and R853/R854 source specialization.
No numerical profile or global PDE existence is assumed to have been proved. -/
namespace Synthesis
noncomputable section

abbrev NSVec := Fin 3 → ℝ

def nsCross (u v : NSVec) : NSVec :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

/-- Three actual vector grades, with the zero grade retained.
Curl images are supplied by the differential owner, not assigned eigenvalues. -/
theorem nsThreeGradeSignedCurl
    (u v w cu cv cw : NSVec) (a b c : ℝ)
    (ru rv rw : NSVec)
    (hu : cu = a • u + ru)
    (hv : cv = b • v + rv)
    (hw : cw = c • w + rw) :
    nsCross (u + v + w) (cu + cv + cw) =
      nsCross u ru + nsCross v rv + nsCross w rw +
      (b-a) • nsCross u v + (c-a) • nsCross u w +
      (c-b) • nsCross v w +
      nsCross u rv + nsCross v ru +
      nsCross u rw + nsCross w ru +
      nsCross v rw + nsCross w rv := by
  rw [hu, hv, hw]
  funext i
  fin_cases i <;> simp [nsCross, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

/-- Recover the physical residual from its signed curl split; no
loss of the residual in a Beltrami approximation. -/
theorem nsCurlResidualBidi (u cu r : NSVec) (a : ℝ) :
    cu = a • u + r ↔ r = cu - a • u := by
  constructor
  · intro h
    rw [h]
    abel
  · intro h
    rw [h]
    abel

def nsSelectedRate (C P D : ℝ) : ℝ := 6 * (12*C-P+D)

/-- The signed one-sided increments are the sufficient observation.
No absolute-value estimate on the whole nonlinear expression is needed. -/
theorem nsSelectedRateIncrement
    (C P D C₀ P₀ D₀ lC lP lD t : ℝ)
    (hC : C-C₀ ≤ lC*t)
    (hP : P₀-P ≤ lP*t)
    (hD : D-D₀ ≤ lD*t) :
    nsSelectedRate C P D ≤
      nsSelectedRate C₀ P₀ D₀ + 6*(12*lC+lP+lD)*t := by
  unfold nsSelectedRate
  linarith

/-- Reverse-solve the exact combined budget into the existing real
R854 consumer, using the original signed R853 normal form. -/
theorem nsR854SignedGeometryEnvelope
    (C P D rate : ℝ → ℝ) (lC lP lD : ℝ)
    (hform : ∀ t, rate t = nsSelectedRate (C t) (P t) (D t))
    (hinit : rate 0 = nsR854InitialRate)
    (hbudget : 6*(12*lC+lP+lD) ≤ nsR854Lipschitz)
    (hC : ∀ t ∈ Set.Icc (0 : ℝ) nsR854Horizon, C t-C 0 ≤ lC*t)
    (hP : ∀ t ∈ Set.Icc (0 : ℝ) nsR854Horizon, P 0-P t ≤ lP*t)
    (hD : ∀ t ∈ Set.Icc (0 : ℝ) nsR854Horizon, D t-D 0 ≤ lD*t) :
    ∀ t ∈ Set.Icc (0 : ℝ) nsR854Horizon,
      rate t ≤ nsR854InitialRate + nsR854Lipschitz*t := by
  intro t ht
  have h := nsSelectedRateIncrement (C t) (P t) (D t)
    (C 0) (P 0) (D 0) lC lP lD t (hC t ht) (hP t ht) (hD t ht)
  rw [← hform t, ← hform 0, hinit] at h
  exact h.trans (add_le_add_left (mul_le_mul_of_nonneg_right hbudget ht.1) _)

open MeasureTheory intervalIntegral in
theorem nsR854SignedGeometryIntegral
    (C P D rate : ℝ → ℝ) (lC lP lD : ℝ)
    (hform : ∀ t, rate t = nsSelectedRate (C t) (P t) (D t))
    (hinit : rate 0 = nsR854InitialRate)
    (hbudget : 6*(12*lC+lP+lD) ≤ nsR854Lipschitz)
    (hC : ∀ t ∈ Set.Icc (0 : ℝ) nsR854Horizon, C t-C 0 ≤ lC*t)
    (hP : ∀ t ∈ Set.Icc (0 : ℝ) nsR854Horizon, P 0-P t ≤ lP*t)
    (hD : ∀ t ∈ Set.Icc (0 : ℝ) nsR854Horizon, D t-D 0 ≤ lD*t)
    (hi : IntervalIntegrable rate volume 0 nsR854Horizon) :
    (∫ t in (0 : ℝ)..nsR854Horizon, rate t) < 0 := by
  exact nsR854OriginalRealRateIntegralStrictlyNegative rate hi
    (nsR854SignedGeometryEnvelope C P D rate lC lP lD
      hform hinit hbudget hC hP hD)

/-- Exact scalar coercivity under a signed perturbation; reverse implication
recovers the precise required lower bound on the perturbation. -/
theorem nsCoercivityResidualBidi (base perturb mass gap : ℝ) :
    gap*mass ≤ base+perturb ↔ gap*mass-base ≤ perturb := by
  constructor <;> intro h <;> linarith

end
end Synthesis

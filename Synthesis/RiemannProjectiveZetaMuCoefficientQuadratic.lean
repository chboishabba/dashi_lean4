import Synthesis.RiemannProjectiveBaseCoefficientQuadratic
import Synthesis.RiemannZetaMuPairingLinearity

/-!
# Quadratic taper-coefficient law for the finite projective N-mu residual

For a projective base test

  phi_g(x) = Phi_{g,r}(x-t),

define the literal finite zero-minus-mu residual

  E_{A,B}(g) = L_{A,B}(phi_g).

If g_lambda=f+lambda h, the projective kernel is exactly quadratic in lambda,
and L_{A,B} is linear.  Therefore

  E(g_lambda)
    = E(f) + lambda E_cross(f,h) + lambda^2 E(h).

This turns finite-window signed-discrepancy cancellation into an ordinary
quadratic-root problem in a taper coefficient.
-/

noncomputable section

open MeasureTheory
open scoped Interval Real

namespace Synthesis

def genericProjectiveBaseOrdinateTest
    (g : ℝ -> ℝ) (r t : ℝ) : ℝ -> ℝ :=
  fun x => genericProjectiveBaseKernel g r (x-t)

def genericProjectiveBaseCrossOrdinateTest
    (f h : ℝ -> ℝ) (r t : ℝ) : ℝ -> ℝ :=
  fun x => genericProjectiveBaseKernelCross f h r (x-t)

def genericProjectiveBaseZetaMuWindowResidual
    (g : ℝ -> ℝ) (r t A B : ℝ) : ℝ :=
  zetaWindowMinusMuPair A B
    (genericProjectiveBaseOrdinateTest g r t)

def genericProjectiveBaseCrossZetaMuWindowResidual
    (f h : ℝ -> ℝ) (r t A B : ℝ) : ℝ :=
  zetaWindowMinusMuPair A B
    (genericProjectiveBaseCrossOrdinateTest f h r t)

theorem genericProjectiveBaseKernel_continuous
    {g : ℝ -> ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (r : ℝ) :
    Continuous (genericProjectiveBaseKernel g r) := by
  let P := genericProjectivePhysicalProfile g r
  have hP : Continuous P :=
    genericProjectivePhysicalProfile_continuous hg r
  have hPc : HasCompactSupport P :=
    genericProjectivePhysicalProfile_compact hgc r
  apply continuous_of_forall_continuousAt
  intro q
  exact (compactCosineTransform_hasDerivAt hP hPc q).continuousAt

theorem genericProjectiveBaseKernelCross_continuous
    {f h : ℝ -> ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hh : Continuous h) (hhc : HasCompactSupport h)
    (r : ℝ) :
    Continuous (genericProjectiveBaseKernelCross f h r) := by
  let P := genericProjectivePhysicalProfileCross f h r
  have hP : Continuous P :=
    genericProjectivePhysicalProfileCross_continuous hf hh r
  have hPc : HasCompactSupport P :=
    genericProjectivePhysicalProfileCross_compact hfc hhc r
  apply continuous_of_forall_continuousAt
  intro q
  exact (compactCosineTransform_hasDerivAt hP hPc q).continuousAt

theorem genericProjectiveBaseOrdinateTest_continuous
    {g : ℝ -> ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (r t : ℝ) :
    Continuous (genericProjectiveBaseOrdinateTest g r t) := by
  unfold genericProjectiveBaseOrdinateTest
  exact
    (genericProjectiveBaseKernel_continuous hg hgc r).comp
      (continuous_id.sub continuous_const)

theorem genericProjectiveBaseCrossOrdinateTest_continuous
    {f h : ℝ -> ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hh : Continuous h) (hhc : HasCompactSupport h)
    (r t : ℝ) :
    Continuous (genericProjectiveBaseCrossOrdinateTest f h r t) := by
  unfold genericProjectiveBaseCrossOrdinateTest
  exact
    (genericProjectiveBaseKernelCross_continuous hf hfc hh hhc r).comp
      (continuous_id.sub continuous_const)

theorem genericProjectiveBase_mu_intervalIntegrable
    {g : ℝ -> ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (r t A B : ℝ) :
    IntervalIntegrable
      (fun x =>
        genericProjectiveBaseOrdinateTest g r t x * Zeta23.mu x)
      volume A B := by
  exact
    ((genericProjectiveBaseOrdinateTest_continuous hg hgc r t).mul
      Zeta23.gammaFacts.smooth.continuous).intervalIntegrable A B

theorem genericProjectiveBaseCross_mu_intervalIntegrable
    {f h : ℝ -> ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hh : Continuous h) (hhc : HasCompactSupport h)
    (r t A B : ℝ) :
    IntervalIntegrable
      (fun x =>
        genericProjectiveBaseCrossOrdinateTest f h r t x * Zeta23.mu x)
      volume A B := by
  exact
    ((genericProjectiveBaseCrossOrdinateTest_continuous
        hf hfc hh hhc r t).mul
      Zeta23.gammaFacts.smooth.continuous).intervalIntegrable A B

theorem genericProjectiveBaseOrdinateTest_mix_quadratic
    {f h : ℝ -> ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hh : Continuous h) (hhc : HasCompactSupport h)
    (lam r t x : ℝ) :
    genericProjectiveBaseOrdinateTest
        (projectiveMixedTaper f h lam) r t x
      =
    genericProjectiveBaseOrdinateTest f r t x
      + lam * genericProjectiveBaseCrossOrdinateTest f h r t x
      + lam^2 * genericProjectiveBaseOrdinateTest h r t x := by
  unfold genericProjectiveBaseOrdinateTest
    genericProjectiveBaseCrossOrdinateTest
  exact genericProjectiveBaseKernel_mix_quadratic
    hf hfc hh hhc lam r (x-t)

/--
Exact quadratic polynomial law for the literal finite N-mu residual.
-/
theorem genericProjectiveBaseZetaMuWindowResidual_mix_quadratic
    {f h : ℝ -> ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hh : Continuous h) (hhc : HasCompactSupport h)
    (lam r t A B : ℝ) :
    genericProjectiveBaseZetaMuWindowResidual
        (projectiveMixedTaper f h lam) r t A B
      =
    genericProjectiveBaseZetaMuWindowResidual f r t A B
      + lam *
        genericProjectiveBaseCrossZetaMuWindowResidual f h r t A B
      + lam^2 *
        genericProjectiveBaseZetaMuWindowResidual h r t A B := by
  let phiF := genericProjectiveBaseOrdinateTest f r t
  let phiX := genericProjectiveBaseCrossOrdinateTest f h r t
  let phiH := genericProjectiveBaseOrdinateTest h r t

  have hF :=
    genericProjectiveBase_mu_intervalIntegrable hf hfc r t A B
  have hX :=
    genericProjectiveBaseCross_mu_intervalIntegrable
      hf hfc hh hhc r t A B
  have hH :=
    genericProjectiveBase_mu_intervalIntegrable hh hhc r t A B

  have hXlam :
      IntervalIntegrable
        (fun x => (lam * phiX x) * Zeta23.mu x)
        volume A B := by
    have hpoint :
        (fun x : ℝ => (lam * phiX x) * Zeta23.mu x)
          =
        fun x => lam * (phiX x * Zeta23.mu x) := by
      funext x
      ring
    rw [hpoint]
    exact hX.const_mul lam

  have hHlam :
      IntervalIntegrable
        (fun x => (lam^2 * phiH x) * Zeta23.mu x)
        volume A B := by
    have hpoint :
        (fun x : ℝ => (lam^2 * phiH x) * Zeta23.mu x)
          =
        fun x => lam^2 * (phiH x * Zeta23.mu x) := by
      funext x
      ring
    rw [hpoint]
    exact hH.const_mul (lam^2)

  unfold genericProjectiveBaseZetaMuWindowResidual
    genericProjectiveBaseCrossZetaMuWindowResidual
  have hfun :
      genericProjectiveBaseOrdinateTest
          (projectiveMixedTaper f h lam) r t
        =
      fun x =>
        phiF x + lam*phiX x + lam^2*phiH x := by
    funext x
    dsimp [phiF,phiX,phiH]
    exact genericProjectiveBaseOrdinateTest_mix_quadratic
      hf hfc hh hhc lam r t x
  rw [hfun]
  rw [zetaWindowMinusMuPair_add
      (hF.add hXlam) hHlam]
  rw [zetaWindowMinusMuPair_add hF hXlam]
  rw [zetaWindowMinusMuPair_smul hX]
  rw [zetaWindowMinusMuPair_smul hH]
  ring

end Synthesis

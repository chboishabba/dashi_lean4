import Mathlib
import RequestProject.NavierStokes.WaleffeAmplitude
import RequestProject.NavierStokes.R571PairedSecondMoment

noncomputable section

namespace RequestProject.NavierStokes.R571HermitianStateVariation

open ClayNS.Waleffe
open RequestProject.NavierStokes.R571

/-- The literal scalarized transported-state observable used by the R571
Hermitian lane. -/
def hermitianStateScalar (X D : Fin 3 → ℂ) : ℝ :=
  (herm X D).re

/-- Pointwise vector subtraction on the exact C^3 carrier. -/
def vecSub (X Y : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i => X i - Y i

/-- Hermitian Cauchy-Schwarz in the exact unsquared form needed by the
state-amplitude and state-difference leaves. -/
theorem abs_hermitianStateScalar_le (X D : Fin 3 → ℂ) :
    |hermitianStateScalar X D| ≤ nrm X * nrm D := by
  have h1 : (hermitianStateScalar X D) ^ 2 ≤ Complex.normSq (herm X D) := by
    rw [Complex.normSq_apply]
    have hi := sq_nonneg (herm X D).im
    simp only [hermitianStateScalar, pow_two]
    nlinarith
  have h2 := normSq_herm_le X D
  have h3 : (hermitianStateScalar X D) ^ 2 ≤ nsq X * nsq D :=
    le_trans h1 h2
  calc
    |hermitianStateScalar X D|
        = Real.sqrt ((hermitianStateScalar X D) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (nsq X * nsq D) := Real.sqrt_le_sqrt h3
    _ = nrm X * nrm D := by
      rw [Real.sqrt_mul (nsq_nonneg X)]
      rfl

/-- The real Hermitian scalar is additive in the transported state slot. -/
theorem hermitianStateScalar_sub (X Y D : Fin 3 → ℂ) :
    hermitianStateScalar X D - hermitianStateScalar Y D
      = hermitianStateScalar (vecSub X Y) D := by
  simp only [hermitianStateScalar, herm, vecSub, map_sub, mul_sub,
    Finset.sum_sub_distrib, Complex.sub_re]

/-- The exact G2 bridge on the physical C^3 carrier:

  |Re<X+,D> - Re<X-,D>| <= ||X+ - X-|| ||D||.

No state scalar derivative is postulated.  The only remaining variation is the
norm of the actual transported vector difference. -/
theorem abs_hermitianStateScalar_difference_le
    (XPlus XMinus D : Fin 3 → ℂ) :
    |hermitianStateScalar XPlus D - hermitianStateScalar XMinus D|
      ≤ nrm (vecSub XPlus XMinus) * nrm D := by
  rw [hermitianStateScalar_sub]
  exact abs_hermitianStateScalar_le (vecSub XPlus XMinus) D

/-- A displacement-scaled vector variation envelope pays the R571 G2 scalar
leaf with coefficient GX * ||D||. -/
theorem hermitian_g2_of_vectorVariation
    {XPlus XMinus D : Fin 3 → ℂ} {y GX : ℝ}
    (hy : 0 ≤ y) (hGX : 0 ≤ GX)
    (hX : nrm (vecSub XPlus XMinus) ≤ y * GX) :
    |hermitianStateScalar XPlus D - hermitianStateScalar XMinus D|
      ≤ y * (GX * nrm D) := by
  calc
    |hermitianStateScalar XPlus D - hermitianStateScalar XMinus D|
        ≤ nrm (vecSub XPlus XMinus) * nrm D :=
          abs_hermitianStateScalar_difference_le XPlus XMinus D
    _ ≤ (y * GX) * nrm D :=
      mul_le_mul_of_nonneg_right hX (nrm_nonneg D)
    _ = y * (GX * nrm D) := by ring

/-- A common vector-amplitude envelope pays the R571 G1 scalar leaf with
coefficient AX * ||D||. -/
theorem hermitian_g1_of_vectorAmplitude
    {X D : Fin 3 → ℂ} {AX : ℝ}
    (hAX : 0 ≤ AX) (hX : nrm X ≤ AX) :
    |hermitianStateScalar X D| ≤ AX * nrm D := by
  calc
    |hermitianStateScalar X D| ≤ nrm X * nrm D :=
      abs_hermitianStateScalar_le X D
    _ ≤ AX * nrm D :=
      mul_le_mul_of_nonneg_right hX (nrm_nonneg D)

/-- Full R571 StateDerivativeEnvelope from actual vector-state amplitude and
variation bounds.  This discharges both scalar G1/G2 leaves by C^3 geometry;
the remaining PDE obligation is now exactly to prove AX and GX for the
transported vector state. -/
theorem stateDerivativeEnvelope_of_vectorState
    {XPlus XMinus D : Fin 3 → ℂ} {y AX GX : ℝ}
    (hy : 0 ≤ y) (hAX : 0 ≤ AX) (hGX : 0 ≤ GX)
    (hPlus : nrm XPlus ≤ AX)
    (hMinus : nrm XMinus ≤ AX)
    (hVariation : nrm (vecSub XPlus XMinus) ≤ y * GX) :
    StateDerivativeEnvelope
      (AX * nrm D)
      (GX * nrm D)
      (hermitianStateScalar XPlus D)
      (hermitianStateScalar XMinus D)
      y := by
  refine
    { g1_nonneg := mul_nonneg hAX (nrm_nonneg D)
      g2_nonneg := mul_nonneg hGX (nrm_nonneg D)
      plus_le := hermitian_g1_of_vectorAmplitude hAX hPlus
      minus_le := hermitian_g1_of_vectorAmplitude hAX hMinus
      difference_le := ?_ }
  exact hermitian_g2_of_vectorVariation hy hGX hVariation

/-- Direct insertion into the already-proved R571 radial payment. -/
theorem r571_pairedSecondMoment_of_vectorState
    (s : DASHI.NS.Unforced.HelicitySign)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k yv : E} {w y AX GX : ℝ}
    {XPlus XMinus D : Fin 3 → ℂ}
    (hw : 0 ≤ w) (hk : 1 ≤ ‖k‖)
    (hy : 0 ≤ y) (hAX : 0 ≤ AX) (hGX : 0 ≤ GX)
    (hPlus : nrm XPlus ≤ AX)
    (hMinus : nrm XMinus ≤ AX)
    (hVariation : nrm (vecSub XPlus XMinus) ≤ y * GX)
    (hyMatch : ‖yv‖ = y) :
    w * (|radialSymbol s (k + yv) - radialSymbol s k|
            * |hermitianStateScalar XPlus D - hermitianStateScalar XMinus D|
          + |centeredRadialDefect s k yv|
            * |hermitianStateScalar XMinus D|)
      ≤ w * (‖yv‖ * ‖yv‖)
          * ((GX * nrm D) + (AX * nrm D)) := by
  have hstate :=
    stateDerivativeEnvelope_of_vectorState
      hy hAX hGX hPlus hMinus hVariation
  rw [← hyMatch] at hstate
  exact r571_pairedSecondMoment_of_stateEnvelope s hw hk hstate

end RequestProject.NavierStokes.R571HermitianStateVariation

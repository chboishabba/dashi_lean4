import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleFourierMass

/-!
# A same-object no-go for direct positive-definite trace transports

The selected signed quartic cosine has C_W(0)=0 (zeroth-moment puncture),
while its full Fourier mass is negative for negative physical origin.
A positive-semidefinite translation-invariant Gram kernel K(x-y) with
K(0)=0 must be identically zero, already by the 2x2 quadratic tests
(1,1) and (1,-1). Thus the actual signed RH kernel C_W CANNOT itself
be a PSD Toeplitz kernel.

This is a falsification of a *direct* Heisenberg/Weil positivity transport.
It does not exclude a completed operator with horizontal/Gamma compensation,
nor a signed/indefinite trace or an independent positivity theorem.
-/

noncomputable section

open MeasureTheory

namespace Synthesis

/-- The two-point principal quadratic form of an even translation-invariant
real kernel. The symmetry of the kernel is built into this scalar test. -/
def RealKernelTwoPointPSD (K : ℝ → ℝ) : Prop :=
  ∀ (q a b : ℝ),
    0 ≤ (a*a + b*b)*K 0 + 2*a*b*K q

theorem twoPointPSD_zeroOrigin_forces_zero
    {K : ℝ → ℝ}
    (hPSD : RealKernelTwoPointPSD K)
    (h0 : K 0 = 0) :
    ∀ q : ℝ, K q = 0 := by
  intro q
  have hp := hPSD q 1 1
  have hm := hPSD q 1 (-1)
  rw [h0] at hp hm
  nlinarith

theorem QuarticFourSignedPolePair.normalizedCosine_not_twoPointPSD_of_negativeOrigin
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hOrigin :
      quarticFourSmoothFinitePoleCancelledOrigin
        W.R W.muHalf W.muTwo t < 0) :
    ¬ RealKernelTwoPointPSD W.normalizedOrdinateCosine := by
  intro hPSD
  have hall :
      ∀ q : ℝ, W.normalizedOrdinateCosine q = 0 :=
    twoPointPSD_zeroOrigin_forces_zero hPSD
      W.normalizedOrdinateCosine_zero
  have hmass0 :
      (∫ q : ℝ, W.normalizedOrdinateCosine q) = 0 := by
    simp [hall]
  have hmassNeg :=
    W.normalizedOrdinateCosine_mass_neg_of_origin_neg hOrigin
  linarith

theorem exists_quarticSignedPole_negativeOrigin_not_directPSD
    {t : ℝ}
    (ht : 200 ≤ t) :
    ∃ W : QuarticFourSignedPolePair t,
      7 * Real.pi^4 / 1600 ≤ W.targetStrength
      ∧ ¬ RealKernelTwoPointPSD W.normalizedOrdinateCosine := by
  obtain ⟨W,hstrength,hneg⟩ :=
    exists_quarticFourSignedPolePair_with_strength_floor_and_negative_origin ht
  exact ⟨W,hstrength,
    W.normalizedCosine_not_twoPointPSD_of_negativeOrigin hneg⟩

end Synthesis

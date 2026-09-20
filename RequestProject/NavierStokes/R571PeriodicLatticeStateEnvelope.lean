import Mathlib
import RequestProject.NavierStokes.WaleffeNetworkForcingBudget
import RequestProject.NavierStokes.R571StateVariation

noncomputable section

namespace RequestProject.NavierStokes.R571PeriodicLattice

open ClayNS.Waleffe
open RequestProject.NavierStokes.R571

/-- A nonzero integer Fourier wave has squared Euclidean length at least one. -/
theorem one_le_wsq_of_ne_zero {k : Wave} (hk : k ≠ 0) :
    1 ≤ wsq k := by
  have hcoord : k 0 ≠ 0 ∨ k 1 ≠ 0 ∨ k 2 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hk
    funext i
    fin_cases i
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  simp only [wsq, Fin.sum_univ_three]
  rcases hcoord with h0 | h1 | h2
  · have ha : (1 : ℝ) ≤ |(k 0 : ℝ)| := by
      have hz : (1 : ℤ) ≤ |k 0| := Int.one_le_abs h0
      exact_mod_cast hz
    nlinarith [sq_nonneg (k 1 : ℝ), sq_nonneg (k 2 : ℝ)]
  · have ha : (1 : ℝ) ≤ |(k 1 : ℝ)| := by
      have hz : (1 : ℤ) ≤ |k 1| := Int.one_le_abs h1
      exact_mod_cast hz
    nlinarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 2 : ℝ)]
  · have ha : (1 : ℝ) ≤ |(k 2 : ℝ)| := by
      have hz : (1 : ℤ) ≤ |k 2| := Int.one_le_abs h2
      exact_mod_cast hz
    nlinarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 1 : ℝ)]

/-- Consequently every nonzero periodic Fourier displacement has Euclidean
length at least one. -/
theorem one_le_wlen_of_ne_zero {k : Wave} (hk : k ≠ 0) :
    1 ≤ wlen k := by
  have hs := one_le_wsq_of_ne_zero hk
  have hsq : 0 ≤ wsq k := by
    unfold wsq
    positivity
  unfold wlen
  have hsqrt := Real.sq_sqrt hsq
  have hroot := Real.sqrt_nonneg (wsq k)
  nlinarith

/-- On the literal periodic lattice, G2 is automatically paid by G1 for every
nonzero opposite shift.  No derivative with respect to the Fourier index is
used or required. -/
theorem stateEnvelope_nonzeroWave_of_amplitude
    {g1 gPlus gMinus : ℝ} {shift : Wave}
    (hshift : shift ≠ 0)
    (hg1 : 0 ≤ g1)
    (hPlus : |gPlus| ≤ g1)
    (hMinus : |gMinus| ≤ g1) :
    StateDerivativeEnvelope g1 (2 * g1) gPlus gMinus (wlen shift) := by
  exact stateDerivativeEnvelope_of_amplitude_of_one_le_displacement
    hg1 (one_le_wlen_of_ne_zero hshift) hPlus hMinus

/-- Pointwise R571 payment on a nonzero literal integer displacement. -/
theorem r571_nonzeroWave_pairedSecondMoment_of_amplitude
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : DASHI.NS.Unforced.HelicitySign)
    {k y : E} {shift : Wave} {w g1 gPlus gMinus : ℝ}
    (hshift : shift ≠ 0)
    (hy : ‖y‖ = wlen shift)
    (hw : 0 ≤ w)
    (hk : 1 ≤ ‖k‖)
    (hg1 : 0 ≤ g1)
    (hPlus : |gPlus| ≤ g1)
    (hMinus : |gMinus| ≤ g1) :
    w * (|radialSymbol s (k + y) - radialSymbol s k|
            * |gPlus - gMinus|
          + |centeredRadialDefect s k y| * |gMinus|)
      ≤ w * (‖y‖ * ‖y‖) * (3 * g1) := by
  apply r571_pairedSecondMoment_of_amplitude_of_one_le_norm
    s hw hk
  · rw [hy]
    exact one_le_wlen_of_ne_zero hshift
  · exact hg1
  · exact hPlus
  · exact hMinus

/-- Zero shift is harmless once the two samples are definitionally/equationally
the same physical sample: the state-difference branch vanishes. -/
theorem stateEnvelope_zeroShift_of_same_sample
    {g1 g : ℝ} (hg1 : 0 ≤ g1) (hg : |g| ≤ g1) :
    StateDerivativeEnvelope g1 0 g g 0 := by
  refine
    { g1_nonneg := hg1
      g2_nonneg := le_rfl
      plus_le := hg
      minus_le := hg
      difference_le := ?_ }
  simp

/-- Full periodic opposite-shift state envelope.  This theorem has no G2
hypothesis at all: zero shift is exact equality; nonzero shift uses integer
lattice discreteness. -/
theorem periodicOppositeShiftStateEnvelope
    (state : Wave → ℝ) (center shift : Wave) {g1 : ℝ}
    (hg1 : 0 ≤ g1)
    (hamp : ∀ mode, |state mode| ≤ g1) :
    StateDerivativeEnvelope g1 (2 * g1)
      (state (center + shift))
      (state (center - shift))
      (wlen shift) := by
  by_cases hshift : shift = 0
  · subst hshift
    simpa using
      (stateEnvelope_zeroShift_of_same_sample
        (g := state center) hg1 (hamp center))
  · exact stateEnvelope_nonzeroWave_of_amplitude
      hshift hg1 (hamp (center + shift)) (hamp (center - shift))

/-- The R571 radial payment on the literal periodic opposite-shift scalar state.
The independent G2 leaf has disappeared; only a G1 amplitude envelope remains. -/
theorem r571_periodicOppositeShift_of_amplitude
    (s : DASHI.NS.Unforced.HelicitySign)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k y : E} {center shift : Wave} {w g1 : ℝ}
    (state : Wave → ℝ)
    (hy : ‖y‖ = wlen shift)
    (hw : 0 ≤ w)
    (hk : 1 ≤ ‖k‖)
    (hg1 : 0 ≤ g1)
    (hamp : ∀ mode, |state mode| ≤ g1) :
    w * (|radialSymbol s (k + y) - radialSymbol s k|
            * |state (center + shift) - state (center - shift)|
          + |centeredRadialDefect s k y|
            * |state (center - shift)|)
      ≤ w * (‖y‖ * ‖y‖) * (3 * g1) := by
  have hstate := periodicOppositeShiftStateEnvelope
    state center shift hg1 hamp
  rw [← hy] at hstate
  have h := r571_pairedSecondMoment_of_stateEnvelope s hw hk hstate
  convert h using 1 <;> ring

end RequestProject.NavierStokes.R571PeriodicLattice

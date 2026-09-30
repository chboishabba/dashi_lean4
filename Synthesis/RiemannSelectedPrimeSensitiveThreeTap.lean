import Synthesis.RiemannMarkedArithmeticCompletedOperatorAudit

/-!
# RH selected detector: first nonlocal prime-sensitive three-tap experiment

The marked selected detectors are supported inside (-log 2,log 2) for
t >= 200. Multiplication cannot change that support. A symmetric translate

  T_(eps,L) g(u) = g(u) + eps*g(u-L) + eps*g(u+L)

can instead produce a nonzero actual sample at log 2, without identifying
that sample with the sign of the entire explicit-formula prime sum.

The exponential eigenfunction identity below supplies the exact
Fourier/Laplace multiplier. Nonvanishing of this multiplier is strictly weaker
than preservation of the original signed terminal margin. In particular
none of the new theorems asserts an RH contradiction.
-/

noncomputable section

namespace Synthesis

/-- Real three-tap operator, whose taps can later be labelled by signed
SSP/FRACTRAN words without changing its analytic semantics. -/
def detectorThreeTap (g : ℝ → ℝ) (eps L : ℝ) (u : ℝ) : ℝ :=
  g u + eps * g (u-L) + eps * g (u+L)

/-- Exact first-prime sample.  In contrast to pointwise reweighting, the
translated copy g(u-L) contributes the literal centre g(0) at u=L. -/
theorem detectorThreeTap_at_firstPrime
    (g : ℝ → ℝ) (eps L : ℝ)
    (hL : g L = 0)
    (h2L : g (L+L) = 0) :
    detectorThreeTap g eps L L = eps * g 0 := by
  simp [detectorThreeTap, hL, h2L]

theorem detectorThreeTap_firstPrime_nonzero
    (g : ℝ → ℝ) (eps L : ℝ)
    (hL : g L = 0)
    (h2L : g (L+L) = 0)
    (heps : eps ≠ 0)
    (hcentre : g 0 ≠ 0) :
    detectorThreeTap g eps L L ≠ 0 := by
  rw [detectorThreeTap_at_firstPrime g eps L hL h2L]
  exact mul_ne_zero heps hcentre

/-- The same geometric short-support condition that annihilates the
old prime sum makes the shifted prime sample equal eps*g(0). -/
theorem detectorThreeTap_firstPrime_of_shortSupport
    (g : ℝ → ℝ) (eps L : ℝ)
    (hLpos : 0 < L)
    (hshort : ∀ u : ℝ, g u ≠ 0 → |u| < L) :
    detectorThreeTap g eps L L = eps * g 0 := by
  have hzL : g L = 0 := by
    by_contra hnon
    have h := hshort L hnon
    rw [abs_of_pos hLpos] at h
    exact (lt_irrefl L h)
  have hz2L : g (L+L) = 0 := by
    by_contra hnon
    have h := hshort (L+L) hnon
    have hsum : 0 ≤ L+L := by positivity
    rw [abs_of_nonneg hsum] at h
    linarith
  exact detectorThreeTap_at_firstPrime g eps L hzL hz2L

theorem detectorThreeTap_on_source_shortDetector
    (g : ℝ → ℝ) (eps : ℝ)
    (hshort : ∀ u : ℝ, g u ≠ 0 → |u| < Real.log 2) :
    detectorThreeTap g eps (Real.log 2) (Real.log 2)
      = eps * g 0 := by
  exact detectorThreeTap_firstPrime_of_shortSupport
    g eps (Real.log 2) (by positivity) hshort

/-- Complex three-tap operation for testing the exact exponential symbol.
This is NOT an identification with the completed zeta explicit formula. -/
def complexDetectorThreeTap
    (g : ℂ → ℂ) (eps L : ℂ) (u : ℂ) : ℂ :=
  g u + eps * g (u-L) + eps * g (u+L)

def threeTapSpectralMultiplier (eps L z : ℂ) : ℂ :=
  1 + eps*(Complex.exp (-z*L) + Complex.exp (z*L))

/-- Actual exponential response. This is the Fourier/Mellin-relevant
calculation for the shift operator; it has no unproven prime-sign premise. -/
theorem threeTap_exponential_symbol
    (eps L z u : ℂ) :
    complexDetectorThreeTap
      (fun v : ℂ => Complex.exp (z*v)) eps L u
      =
    Complex.exp (z*u) * threeTapSpectralMultiplier eps L z := by
  unfold complexDetectorThreeTap threeTapSpectralMultiplier
  rw [show z*(u-L) = z*u + (-z*L) by ring]
  rw [show z*(u+L) = z*u + z*L by ring]
  rw [Complex.exp_add,Complex.exp_add]
  ring

/-- The symbol cannot cancel a selected nonzero spectral response if
its perturbation is strictly smaller than 1 in complex modulus. -/
theorem threeTapSpectralMultiplier_ne_zero
    {eps L z : ℂ}
    (hsmall :
      ‖eps*(Complex.exp (-z*L)+Complex.exp (z*L))‖ < 1) :
    threeTapSpectralMultiplier eps L z ≠ 0 := by
  intro hzero
  have hpert :
      eps*(Complex.exp (-z*L)+Complex.exp (z*L)) = -1 := by
    have h := hzero
    unfold threeTapSpectralMultiplier at h
    apply add_left_cancel (a := (1 : ℂ))
    simpa using h
  rw [hpert] at hsmall
  norm_num at hsmall

theorem threeTap_exponential_nonzero
    {eps L z u : ℂ}
    (hsmall :
      ‖eps*(Complex.exp (-z*L)+Complex.exp (z*L))‖ < 1) :
    complexDetectorThreeTap
      (fun v : ℂ => Complex.exp (z*v)) eps L u ≠ 0 := by
  rw [threeTap_exponential_symbol]
  exact mul_ne_zero (Complex.exp_ne_zero _) 
    (threeTapSpectralMultiplier_ne_zero hsmall)

/-!
This is the exact scope firewall:

* detectorThreeTap_on_source_shortDetector makes a literal sample at log 2
  equal to eps*g(0), potentially nonzero.
* threeTap_exponential_symbol controls the pointwise spectral multiplier.
* Neither proves that the COMPLETED prime-power sum is nonzero, nor gives
  the selected signed high estimate. That requires the existing Zeta23
  source functional and the entire transformed Gamma/pole/zero balance.
-/

end Synthesis

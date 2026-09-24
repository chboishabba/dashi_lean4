import Integration.MoonshineEta24Pinned
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Concrete sixfold phase theorem from the fixed-locus reflection identity

This module closes the phase readout that was previously left abstract.

The branch-safe theorem is first stated exponentially:

  exp (I * (2 arg v + 12 arg z)) = 1

for nonzero v, unit z, and the fixed-locus value identity

  v = conj (z^12 * v).

Mathlib's exact kernel theorem for complex exponential then gives an integer k
such that

  arg v + 6 arg z = k * pi.

Specialising v to eta^24(z) yields the formal version of

  arg Delta(e^{i theta}) = -6 theta mod pi.

No choice of a continuous argument branch is smuggled into the theorem:
the branch ambiguity is represented exactly by the integer multiple of pi.
-/

namespace Integration.MoonshineEta24SixfoldPhase

open Complex Real
open UpperHalfPlane hiding I
open ModularForm
open scoped Real Topology

noncomputable section

/-- Unit norm extracted from the norm-square fixed-locus hypothesis. -/
theorem norm_eq_one_of_normSq_eq_one
    {z : ℂ}
    (hunit : Complex.normSq z = 1) :
    ‖z‖ = 1 := by
  have hsquare : ‖z‖ ^ 2 = 1 := by
    simpa [Complex.normSq_eq_norm_sq] using hunit
  exact (sq_eq_one_iff.mp hsquare).resolve_right (by positivity)

/-- Polar form on the unit circle. -/
theorem exp_arg_eq_self_of_normSq_one
    {z : ℂ}
    (hunit : Complex.normSq z = 1) :
    Complex.exp (Complex.arg z * I) = z := by
  have hpolar := Complex.norm_mul_exp_arg_mul_I z
  rw [norm_eq_one_of_normSq_eq_one hunit, one_mul] at hpolar
  exact hpolar

/-- Polar form with the nonzero radial factor exposed. -/
theorem polar_nonzero
    {v : ℂ}
    (hv : v ≠ 0) :
    Complex.exp (Complex.arg v * I) = v / ‖v‖ := by
  have hpolar := Complex.norm_mul_exp_arg_mul_I v
  have hnorm : (‖v‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hv
  apply (eq_div_iff hnorm).2
  simpa [mul_comm] using hpolar.symm

/-- General branch-free phase compiler for a weight-12 reciprocal-conjugate
fixed-locus identity. -/
theorem phase_exp_eq_one_of_fixed
    {z v : ℂ}
    (hunit : Complex.normSq z = 1)
    (hv : v ≠ 0)
    (hfixed : v = conj (z ^ 12 * v)) :
    Complex.exp
      (((2 * Complex.arg v + 12 * Complex.arg z : ℝ) : ℂ) * I) = 1 := by
  have hz :
      Complex.exp (Complex.arg z * I) = z :=
    exp_arg_eq_self_of_normSq_one hunit

  have hvp :
      Complex.exp (Complex.arg v * I) = v / ‖v‖ :=
    polar_nonzero hv

  have hnormv : (‖v‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hv

  have hnormv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv

  have hfixedNorm :
      v / ‖v‖ =
        conj (z ^ 12 * v) / ‖v‖ := by
    rw [hfixed]

  have hconjNorm : ‖conj (z ^ 12 * v)‖ = ‖v‖ := by
    rw [Complex.norm_conj, norm_mul, norm_pow]
    have hznorm := norm_eq_one_of_normSq_eq_one hunit
    simp [hznorm]

  have hphase :
      Complex.exp (Complex.arg v * I) =
        conj (z ^ 12 * v) / ‖v‖ := by
    rw [hvp, hfixedNorm]

  have hzpow :
      z ^ 12 =
        Complex.exp ((12 * Complex.arg z : ℝ) * I) := by
    rw [← hz]
    rw [← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring

  have hvconj :
      conj v / ‖v‖ =
        Complex.exp ((- Complex.arg v : ℝ) * I) := by
    have h :=
      congrArg conj hvp
    simp only [map_div₀, map_norm, map_ofNat, Complex.conj_exp,
      map_mul, Complex.conj_ofReal, Complex.conj_I, neg_mul] at h
    simpa [mul_comm] using h.symm

  have hphase' :
      Complex.exp (Complex.arg v * I) =
        Complex.exp
          (((-12 * Complex.arg z - Complex.arg v : ℝ) : ℂ) * I) := by
    calc
      Complex.exp (Complex.arg v * I)
          = conj (z ^ 12 * v) / ‖v‖ := hphase
      _ = conj (z ^ 12) * (conj v / ‖v‖) := by
            rw [map_mul]
            field_simp
      _ = Complex.exp (((-12 * Complex.arg z : ℝ) : ℂ) * I) *
            Complex.exp (((- Complex.arg v : ℝ) : ℂ) * I) := by
            rw [hzpow, Complex.conj_exp, hvconj]
            congr 2
            simp
            ring
      _ = Complex.exp
            (((-12 * Complex.arg z - Complex.arg v : ℝ) : ℂ) * I) := by
            rw [← Complex.exp_add]
            congr 2
            push_cast
            ring

  have hratio :
      Complex.exp
        ((((2 * Complex.arg v + 12 * Complex.arg z : ℝ) : ℂ) * I)) = 1 := by
    calc
      Complex.exp
          ((((2 * Complex.arg v + 12 * Complex.arg z : ℝ) : ℂ) * I))
          =
        Complex.exp (Complex.arg v * I) /
          Complex.exp
            (((-12 * Complex.arg z - Complex.arg v : ℝ) : ℂ) * I) := by
              rw [← Complex.exp_sub]
              congr 2
              push_cast
              ring
      _ = 1 := by rw [hphase']; simp
  exact hratio

/-- Exact modulo-pi consequence of the branch-free exponential theorem. -/
theorem phase_mod_pi_of_fixed
    {z v : ℂ}
    (hunit : Complex.normSq z = 1)
    (hv : v ≠ 0)
    (hfixed : v = conj (z ^ 12 * v)) :
    ∃ k : ℤ,
      Complex.arg v + 6 * Complex.arg z =
        (k : ℝ) * Real.pi := by
  have hexp :=
    phase_exp_eq_one_of_fixed hunit hv hfixed
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexp
  refine ⟨k, ?_⟩
  have hkIm := congrArg Complex.im hk
  simp at hkIm
  linarith

/-- The same sixfold phase compiler applies to the normalized E4/E6 Delta
target as soon as nonvanishing is supplied.  Reflection/fixed-locus mathematics
is already owned; this theorem isolates nonvanishing as the only additional
input for the unconditional phase statement on that target. -/
theorem normalizedDelta_sixfold_phase_of_ne
    (z : ℍ)
    (hunit : Complex.normSq (z : ℂ) = 1)
    (hne :
      Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaLimit z ≠ 0) :
    ∃ k : ℤ,
      Complex.arg
          (Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaLimit z)
        + 6 * Complex.arg (z : ℂ)
      =
        (k : ℝ) * Real.pi := by
  apply phase_mod_pi_of_fixed hunit hne
  exact
    Integration.MoonshineEisensteinAgdaTarget.normalizedDelta_unitCircle_fixed
      z hunit

/-- Equivalent normalized-Delta congruence form. -/
theorem normalizedDelta_arg_congruent_neg_six_of_ne
    (z : ℍ)
    (hunit : Complex.normSq (z : ℂ) = 1)
    (hne :
      Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaLimit z ≠ 0) :
    ∃ k : ℤ,
      Complex.arg
          (Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaLimit z)
      =
        -6 * Complex.arg (z : ℂ) +
          (k : ℝ) * Real.pi := by
  obtain ⟨k, hk⟩ :=
    normalizedDelta_sixfold_phase_of_ne z hunit hne
  exact ⟨k, by linarith⟩

/-- Sixfold phase law for eta^24 on the unit-circle fixed locus. -/
theorem eta24_sixfold_phase
    (z : ℍ)
    (hunit : Complex.normSq (z : ℂ) = 1) :
    ∃ k : ℤ,
      Complex.arg
          (Integration.MoonshineEta24Pinned.eta24 z)
        + 6 * Complex.arg (z : ℂ)
      =
        (k : ℝ) * Real.pi := by
  apply phase_mod_pi_of_fixed hunit
  · exact pow_ne_zero 24 (ModularForm.eta_ne_zero z.2)
  · exact Integration.MoonshineEta24Pinned.eta24_unitCircle_fixed z hunit

/-- Equivalent congruence presentation. -/
theorem eta24_arg_congruent_neg_six
    (z : ℍ)
    (hunit : Complex.normSq (z : ℂ) = 1) :
    ∃ k : ℤ,
      Complex.arg
          (Integration.MoonshineEta24Pinned.eta24 z)
      =
        -6 * Complex.arg (z : ℂ) +
          (k : ℝ) * Real.pi := by
  obtain ⟨k, hk⟩ := eta24_sixfold_phase z hunit
  exact ⟨k, by linarith⟩

structure Eta24SixfoldPhaseBoundary where
  branchFreePhaseExponentialOwned : Bool
  integerPiCongruenceOwned : Bool
  normalizedDeltaConditionalSixfoldCompilerOwned : Bool
  normalizedDeltaNonvanishingStillRequired : Bool
  eta24NonvanishingUsed : Bool
  eta24UnitCircleFixedValueUsed : Bool
  concreteSixfoldPhaseTheoremOwned : Bool
  continuousArgumentBranchChosen : Bool

def eta24SixfoldPhaseBoundary : Eta24SixfoldPhaseBoundary where
  branchFreePhaseExponentialOwned := true
  integerPiCongruenceOwned := true
  normalizedDeltaConditionalSixfoldCompilerOwned := true
  normalizedDeltaNonvanishingStillRequired := true
  eta24NonvanishingUsed := true
  eta24UnitCircleFixedValueUsed := true
  concreteSixfoldPhaseTheoremOwned := true
  continuousArgumentBranchChosen := false

end

end Integration.MoonshineEta24SixfoldPhase

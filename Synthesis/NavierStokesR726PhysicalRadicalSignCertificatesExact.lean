import Mathlib
import Synthesis.NavierStokesR726SignedDefectViscosityNoGoExact

/-!
# Exact Q(sqrt2,sqrt3) sign certificates for a genuine C=1 R726 source

The 316 original ordered incidences and every modal value are generated in
Agda #1551 scripts/check_ns_r726_signed_defect_physical_source_exact_20261128.py.
This file proves the strictly ordered REAL RADICAL ENDPOINTS displayed by
that independent exact physical source checker, not a second independent
reconstruction of the original Fourier M/D and p+q=k witnesses.

Finite physical source producer + this coefficient certification + Galerkin
ODE continuity refute an unconditional zero-defect R726 inequality for ALL
physical-real periodic trajectories/terminal times. They do NOT refute a
nonzero cutoff-uniform time-dependent defect ceiling (the corrected R726
physical payment) or prove NS regularity. No field naturality/kernels claimed.
-/

namespace DASHI.NavierStokes.R726PhysicalSign

private theorem sqrt2_lt_two : Real.sqrt (2 : ℝ) < 2 := by
  have hs : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  nlinarith only [hs, hsq]

private theorem sqrt3_lt_two : Real.sqrt (3 : ℝ) < 2 := by
  have hs : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  nlinarith only [hs, hsq]

private theorem one_lt_sqrt2 : (1 : ℝ) < Real.sqrt 2 := by
  have hs : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  nlinarith only [hs, hsq]

/-- True Fourier coefficient source: R406 original ν=1 from witness A. -/
def witnessA_R406 : ℝ :=
  - (368 : ℝ) / 3 * Real.sqrt 3
  - (164 : ℝ) / 3 * Real.sqrt 2 + 7558 / 9

/-- True source R722/R723 combined = 12*R691 original coherent commutator. -/
def witnessA_combined : ℝ :=
  - (552 : ℝ) * Real.sqrt 3 + 138 * Real.sqrt 2 + 3734

theorem witnessA_R406_positive : 0 < witnessA_R406 := by
  dsimp [witnessA_R406]
  have h2 := sqrt2_lt_two
  have h3 := sqrt3_lt_two
  nlinarith only [h2, h3]

theorem witnessA_combined_positive : 0 < witnessA_combined := by
  dsimp [witnessA_combined]
  have h3 := sqrt3_lt_two
  have h2 : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  nlinarith only [h3, h2]

/-- Cutoff C=1, ν=1, original 316-incidence complete physical witness A:
the R406-minus-combined signed defect is strictly NEGATIVE. -/
theorem original_witnessA_negative_defect :
    - (26048 : ℝ) / 9
      - (578 : ℝ) / 3 * Real.sqrt 2
      + (1288 : ℝ) / 3 * Real.sqrt 3 < 0 := by
  have h3 := sqrt3_lt_two
  have h2 : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  nlinarith only [h3, h2]

/-- Different original physical Fourier initial witness B at ν=1:
the literal difference is POSITIVE, so a zero-defect universal cannot
be recovered from positive Cauchy rates or input energy/helicity alone. -/
theorem original_witnessB_positive_defect :
    0 < - (4267 : ℝ) / 9
      + (385 : ℝ) / 4 * Real.sqrt 6
      + (2113 : ℝ) / 9 * Real.sqrt 3
      + (12401 : ℝ) / 12 * Real.sqrt 2 := by
  have h2 := one_lt_sqrt2
  have h3 : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
  have h6 : 0 ≤ Real.sqrt (6 : ℝ) := Real.sqrt_nonneg _
  nlinarith only [h2, h3, h6]

/-- SAME original witness A, ONLY ν changed from 1 to 1/10.
The R406 Cauchy resolvent is inverse-linear in ν and R723's coherent
commutator has no such rate denominator. Thus defect reverses sign. -/
theorem original_witnessA_small_viscosity_positive_defect :
    0 < (41974 : ℝ) / 9
      - (2054 : ℝ) / 3 * Real.sqrt 2
      - (2024 : ℝ) / 3 * Real.sqrt 3 := by
  have h2 := sqrt2_lt_two
  have h3 := sqrt3_lt_two
  nlinarith only [h2, h3]

theorem witnessA_viscosity_bidi :
    ∃ ν₊ ν₋ : ℝ,
      0 < ν₊ ∧ 0 < ν₋ ∧
      0 < witnessA_R406 / ν₊ - witnessA_combined ∧
      witnessA_R406 / ν₋ - witnessA_combined < 0 := by
  exact DASHI.NavierStokes.R726Defect.same_source_two_viscosities_opposite_defects
    witnessA_R406 witnessA_combined
    witnessA_R406_positive witnessA_combined_positive

end DASHI.NavierStokes.R726PhysicalSign

import Synthesis.RiemannNormalizedCenteredOffShell
import Synthesis.RiemannQuantitativeTaperMixingBound

/-!
# Exact fixed-profile form of the normalized canonical taper

After v = t u, the canonical shrinking affine bumps stop shrinking.

For t > 0,

  inner:
    ((v/t) - pi/t) / (pi/(4t)) = 4 (v-pi) / pi,

  outer:
    ((v/t) - 2pi/t) / (pi/(4t)) = 4 (v-2pi) / pi,

and the reflected halves give the corresponding negative translates.

Thus the normalized canonical taper is literally a fixed two-window profile with
only the scalar mixing coefficient lambda(t) left variable.  This is the
correct same-object surface for H2d Fourier analysis.
-/

noncomputable section

open scoped Real

namespace Synthesis

def normalizedInnerFixedProfile (v : ℝ) : ℝ :=
  unitBump (4 * (v - Real.pi) / Real.pi)
    + unitBump (-4 * (v + Real.pi) / Real.pi)

def normalizedOuterFixedProfile (v : ℝ) : ℝ :=
  unitBump (4 * (v - 2 * Real.pi) / Real.pi)
    + unitBump (-4 * (v + 2 * Real.pi) / Real.pi)

def normalizedCanonicalFixedProfile (t v : ℝ) : ℝ :=
  normalizedInnerFixedProfile v
    + quantitativeLambda t * normalizedOuterFixedProfile v

def normalizedCenteredFixedProfile (t v : ℝ) : ℝ :=
  normalizedCanonicalFixedProfile t v * (Real.cos (v / 16) - 1)


/-- The fixed normalized inner window is literally the symmetric affine bump
with centre pi and radius pi/4. -/
theorem normalizedInnerFixedProfile_eq_symBump :
    normalizedInnerFixedProfile
      = quantitativeSymBump Real.pi (Real.pi / 4) := by
  funext v
  unfold normalizedInnerFixedProfile quantitativeSymBump
    Zeta23Bridge.LiteralWeilOddChannelTaper.symmetrize
    scaledUnitBump
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  congr 1 <;> congr 1 <;>
    field_simp [hpi] <;> ring

/-- The fixed normalized outer window is literally the symmetric affine bump
with centre 2*pi and radius pi/4. -/
theorem normalizedOuterFixedProfile_eq_symBump :
    normalizedOuterFixedProfile
      = quantitativeSymBump (2 * Real.pi) (Real.pi / 4) := by
  funext v
  unfold normalizedOuterFixedProfile quantitativeSymBump
    Zeta23Bridge.LiteralWeilOddChannelTaper.symmetrize
    scaledUnitBump
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  congr 1 <;> congr 1 <;>
    field_simp [hpi] <;> ring

theorem normalized_inner_scaled_argument_pos
    {t v : ℝ} (ht : 0 < t) :
    ((v / t) - quantitativeTaperInnerCenter t) / quantitativeTaperR t
      = 4 * (v - Real.pi) / Real.pi := by
  unfold quantitativeTaperInnerCenter quantitativeTaperR
  field_simp [ne_of_gt ht, ne_of_gt Real.pi_pos]
  ring

theorem normalized_inner_scaled_argument_neg
    {t v : ℝ} (ht : 0 < t) :
    ((-(v / t)) - quantitativeTaperInnerCenter t) / quantitativeTaperR t
      = -4 * (v + Real.pi) / Real.pi := by
  unfold quantitativeTaperInnerCenter quantitativeTaperR
  field_simp [ne_of_gt ht, ne_of_gt Real.pi_pos]
  ring

theorem normalized_outer_scaled_argument_pos
    {t v : ℝ} (ht : 0 < t) :
    ((v / t) - quantitativeTaperOuterCenter t) / quantitativeTaperR t
      = 4 * (v - 2 * Real.pi) / Real.pi := by
  unfold quantitativeTaperOuterCenter quantitativeTaperR
  field_simp [ne_of_gt ht, ne_of_gt Real.pi_pos]
  ring

theorem normalized_outer_scaled_argument_neg
    {t v : ℝ} (ht : 0 < t) :
    ((-(v / t)) - quantitativeTaperOuterCenter t) / quantitativeTaperR t
      = -4 * (v + 2 * Real.pi) / Real.pi := by
  unfold quantitativeTaperOuterCenter quantitativeTaperR
  field_simp [ne_of_gt ht, ne_of_gt Real.pi_pos]
  ring

theorem normalized_inner_bump_eq_fixed
    {t v : ℝ} (ht : 0 < t) :
    quantitativeInnerBump t (v / t) = normalizedInnerFixedProfile v := by
  unfold quantitativeInnerBump quantitativeSymBump symmetrize
    scaledUnitBump normalizedInnerFixedProfile
  rw [normalized_inner_scaled_argument_pos ht,
      normalized_inner_scaled_argument_neg ht]

theorem normalized_outer_bump_eq_fixed
    {t v : ℝ} (ht : 0 < t) :
    quantitativeOuterBump t (v / t) = normalizedOuterFixedProfile v := by
  unfold quantitativeOuterBump quantitativeSymBump symmetrize
    scaledUnitBump normalizedOuterFixedProfile
  rw [normalized_outer_scaled_argument_pos ht,
      normalized_outer_scaled_argument_neg ht]

theorem normalizedCanonicalTaper_eq_fixedProfile
    {t v : ℝ} (ht : 0 < t) :
    normalizedCanonicalTaper t v = normalizedCanonicalFixedProfile t v := by
  unfold normalizedCanonicalTaper quantitativeCanonicalTaper
    normalizedCanonicalFixedProfile
  rw [normalized_inner_bump_eq_fixed ht,
      normalized_outer_bump_eq_fixed ht]

theorem normalizedCenteredCanonicalTaper_eq_fixedProfile
    {t v : ℝ} (ht : 0 < t) :
    normalizedCenteredCanonicalTaper t v
      = normalizedCenteredFixedProfile t v := by
  unfold normalizedCenteredCanonicalTaper normalizedCenteredFixedProfile
  rw [normalizedCanonicalTaper_eq_fixedProfile ht]

theorem normalizedInnerFixedProfile_nonneg (v : ℝ) :
    0 <= normalizedInnerFixedProfile v := by
  unfold normalizedInnerFixedProfile
  positivity

theorem normalizedOuterFixedProfile_nonneg (v : ℝ) :
    0 <= normalizedOuterFixedProfile v := by
  unfold normalizedOuterFixedProfile
  positivity

theorem normalizedCanonicalFixedProfile_nonneg
    {t v : ℝ} (ht : 18 <= t) :
    0 <= normalizedCanonicalFixedProfile t v := by
  unfold normalizedCanonicalFixedProfile
  have hlam := quantitativeLambda_pos ht
  positivity

theorem normalizedCanonicalFixedProfile_lambda_bounded
    {t : ℝ} (ht : 18 <= t) :
    0 < quantitativeLambda t ∧ quantitativeLambda t <= quantitativeMixUpper :=
  ⟨quantitativeLambda_pos ht, quantitativeLambda_le ht⟩

end Synthesis

import Synthesis.RiemannNormalizedRvMZeroModeFourier
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Schwartz realization of the normalized centered canonical profile

The canonical unit bump is a Mathlib `ContDiffBump`, hence C-infinity, although
the earlier RH files exposed only the C2 surface needed by integration by parts.

This file restores the full regularity through the affine/symmetric/fixed-profile
construction, then packages the compactly supported complex profile

  f_t(v) = 4 H_t(v)

as a Schwartz function.  Its Fourier transform is therefore again Schwartz and
in particular integrable.  This pays the L1 hypothesis left explicit by the
zero-mode Fourier inversion compiler.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

theorem unitBump_contDiff_top :
    ContDiff ℝ (⊤ : ℕ∞) unitBump := by
  exact unitContDiffBump.contDiff

theorem normalizedInnerFixedProfile_contDiff_top :
    ContDiff ℝ (⊤ : ℕ∞) normalizedInnerFixedProfile := by
  unfold normalizedInnerFixedProfile unitBump
  fun_prop

theorem normalizedOuterFixedProfile_contDiff_top :
    ContDiff ℝ (⊤ : ℕ∞) normalizedOuterFixedProfile := by
  unfold normalizedOuterFixedProfile unitBump
  fun_prop

theorem normalizedCanonicalFixedProfile_contDiff_top (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (normalizedCanonicalFixedProfile t) := by
  unfold normalizedCanonicalFixedProfile
  exact normalizedInnerFixedProfile_contDiff_top.add
    (contDiff_const.mul normalizedOuterFixedProfile_contDiff_top)

theorem normalizedCenteredFixedProfile_contDiff_top (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (normalizedCenteredFixedProfile t) := by
  unfold normalizedCenteredFixedProfile
  exact (normalizedCanonicalFixedProfile_contDiff_top t).mul (by fun_prop)

theorem normalizedCenteredComplexProfile_contDiff_top (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (normalizedCenteredComplexProfile t) := by
  unfold normalizedCenteredComplexProfile
  exact (contDiff_const.mul
    (normalizedCenteredFixedProfile_contDiff_top t)).ofReal

def normalizedCenteredSchwartz (t : ℝ) : SchwartzMap ℝ ℂ :=
  (normalizedCenteredComplexProfile_compact t).toSchwartzMap
    (normalizedCenteredComplexProfile_contDiff_top t)

@[simp] theorem normalizedCenteredSchwartz_apply (t v : ℝ) :
    normalizedCenteredSchwartz t v = normalizedCenteredComplexProfile t v := by
  rfl

theorem normalizedCenteredSchwartz_fourier_coe (t : ℝ) :
    (fun w : ℝ =>
      (FourierTransform.fourier (normalizedCenteredSchwartz t)) w)
      =
    FourierTransform.fourier (normalizedCenteredComplexProfile t) := by
  funext w
  rw [SchwartzMap.fourier_coe]
  rfl

theorem normalizedCenteredComplexProfile_fourier_integrable (t : ℝ) :
    Integrable
      (FourierTransform.fourier
        (normalizedCenteredComplexProfile t)) := by
  have hs :
      Integrable
        (fun w : ℝ =>
          (FourierTransform.fourier
            (normalizedCenteredSchwartz t)) w) :=
    (FourierTransform.fourier (normalizedCenteredSchwartz t)).integrable
  rw [normalizedCenteredSchwartz_fourier_coe] at hs
  exact hs

theorem normalizedCenteredComplexProfile_fourier_total_zero_unconditional
    (t : ℝ) :
    (∫ w : ℝ,
      FourierTransform.fourier
        (normalizedCenteredComplexProfile t) w) = 0 := by
  exact normalizedCenteredComplexProfile_fourier_total_zero t
    (normalizedCenteredComplexProfile_fourier_integrable t)

end Synthesis

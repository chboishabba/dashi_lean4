import Synthesis.RiemannQuantitativeSymmetricBumpMass
import Synthesis.RiemannQuantitativeScaledBumpPositivity
import Zeta23Bridge.LiteralWeilNormalizedWindowBounds
import Synthesis.RiemannSmoothShortWindowSchurLift

/-!
# Smooth normalized modulus-window tapers

This module closes the regularity mismatch in the imported narrow-window Schur
construction. Instead of normalized tents, use the repository fixed C^2 bump

  symBump(c,e)(u) = psi((u-c)/e) + psi((-u-c)/e),

supported in the modulus window c-e < |u| < c+e.

After positive-mass normalization the taper remains C^2, even, nonnegative,
compactly supported, and has unit mass. Hence it inhabits the exact
NormalizedWindowTaper interface used by all endpoint cap/floor and Schur
separation theorems.
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilWindowRatioSeparation
open Zeta23Bridge.LiteralWeilNormalizedWindowBounds
open Zeta23Bridge.NormalizedNarrowWindowCertificate
open Zeta23Bridge.LiteralWeilOddChannelTaper

def smoothWindowRaw (c e : ℝ) : ℝ → ℝ :=
  quantitativeSymBump c e

def smoothWindow (c e : ℝ) : ℝ → ℝ :=
  normalized (smoothWindowRaw c e)

theorem smoothWindowRaw_contDiff {c e : ℝ} (he : 0 < e) :
    ContDiff ℝ 2 (smoothWindowRaw c e) := by
  exact quantitativeSymBump_contDiff he.ne'

theorem smoothWindowRaw_even (c e u : ℝ) :
    smoothWindowRaw c e (-u) = smoothWindowRaw c e u := by
  unfold smoothWindowRaw quantitativeSymBump symmetrize
  ring

theorem smoothWindowRaw_nonneg (c e u : ℝ) :
    0 ≤ smoothWindowRaw c e u :=
  quantitativeSymBump_nonneg c e u

theorem smoothWindowRaw_compact {c e : ℝ} (he : 0 < e) :
    HasCompactSupport (smoothWindowRaw c e) :=
  quantitativeSymBump_hasCompactSupport he

theorem smoothWindowRaw_support_modulus
    {c e u : ℝ} (hc : 0 < c - e) (he : 0 < e)
    (hu : smoothWindowRaw c e u ≠ 0) :
    |u| ∈ Icc (c - e) (c + e) := by
  unfold smoothWindowRaw quantitativeSymBump symmetrize at hu
  by_cases hp : scaledUnitBump c e u = 0
  · have hm : scaledUnitBump c e (-u) ≠ 0 := by
      intro hm
      apply hu
      simp [hp, hm]
    have hs := scaledUnitBump_support he hm
    have habs : |u| = |-u| := by simp
    rw [habs]
    constructor
    · have htri : c ≤ |-u| + |-u - c| := by
        have h := abs_add (-u - c) u
        have hcabs : |c| = c := abs_of_pos (by linarith : 0 < c)
        rw [show (-u-c)+u = -c by ring, abs_neg, hcabs] at h
        exact h
      linarith
    · have htri : |-u| ≤ |-u - c| + |c| := by
        have h := abs_add (-u - c) c
        simpa using h
      rw [abs_of_pos (by linarith : 0 < c)] at htri
      linarith
  · have hs := scaledUnitBump_support he hp
    constructor
    · have htri : c ≤ |u| + |u - c| := by
        have h := abs_add (u - c) (-u)
        have hcabs : |c| = c := abs_of_pos (by linarith : 0 < c)
        rw [show (u-c)+(-u) = -c by ring, abs_neg, hcabs] at h
        simpa [abs_neg] using h
      linarith
    · have htri : |u| ≤ |u - c| + |c| := by
        have h := abs_add (u - c) c
        simpa using h
      rw [abs_of_pos (by linarith : 0 < c)] at htri
      linarith

theorem smoothWindowRaw_mass_pos
    {c e : ℝ} (he : 0 < e) :
    0 < ∫ u : ℝ, smoothWindowRaw c e u := by
  have hbase :
      0 < ∫ u : ℝ, scaledUnitBump c e u := by
    simpa using
      scaledUnitBump_positive_integral
        (c := c) (R := e) he
        (w := fun _ : ℝ => 1)
        continuous_const
        (by intro u hu; norm_num)
  unfold smoothWindowRaw quantitativeSymBump symmetrize
  have hi : Integrable (scaledUnitBump c e) :=
    (scaledUnitBump_continuous he.ne' c).integrable_of_hasCompactSupport
      (scaledUnitBump_hasCompactSupport he)
  have hiref : Integrable (fun u : ℝ => scaledUnitBump c e (-u)) :=
    ((scaledUnitBump_continuous he.ne' c).comp continuous_neg)
      .integrable_of_hasCompactSupport
        ((scaledUnitBump_hasCompactSupport he).comp_homeomorph (Homeomorph.neg ℝ))
  rw [integral_add hi hiref]
  have href :
      (∫ u : ℝ, scaledUnitBump c e (-u))
        = ∫ u : ℝ, scaledUnitBump c e u := by
    simpa using
      MeasureTheory.integral_neg_eq_self
        (fun u : ℝ => scaledUnitBump c e (-u))
        (volume : Measure ℝ)
  rw [href]
  linarith

theorem smoothWindow_contDiff {c e : ℝ} (he : 0 < e) :
    ContDiff ℝ 2 (smoothWindow c e) := by
  unfold smoothWindow normalized
  exact contDiff_const.mul (smoothWindowRaw_contDiff he)

theorem smoothWindow_even (c e u : ℝ) :
    smoothWindow c e (-u) = smoothWindow c e u := by
  unfold smoothWindow normalized
  rw [smoothWindowRaw_even]

theorem smoothWindow_normalizedWindow
    {c e : ℝ} (hc : 0 < c - e) (he : 0 < e) :
    NormalizedWindowTaper
      (smoothWindow c e) (c - e) (c + e) := by
  have hraw : WindowTaper
      (smoothWindowRaw c e) (c - e) (c + e) := by
    refine ⟨(smoothWindowRaw_contDiff he).continuous,
      smoothWindowRaw_compact he,
      smoothWindowRaw_nonneg c e,
      ?_, smoothWindowRaw_mass_pos he⟩
    intro u hu
    exact smoothWindowRaw_support_modulus hc he hu
  refine ⟨windowTaper_normalized hraw, ?_⟩
  exact integral_normalized (smoothWindowRaw_mass_pos he)

theorem smoothWindow_short
    {c e u : ℝ}
    (hc : 0 < c - e) (he : 0 < e)
    (hupper : c + e < Real.log 2)
    (hu : smoothWindow c e u ≠ 0) :
    |u| < Real.log 2 := by
  have hw := (smoothWindow_normalizedWindow hc he).window.supp u hu
  exact lt_of_le_of_lt hw.2 hupper


theorem smoothWindowRaw_pos_at_center
    {c e : ℝ} (he : 0 < e) :
    0 < smoothWindowRaw c e c := by
  unfold smoothWindowRaw quantitativeSymBump
    Zeta23Bridge.LiteralWeilOddChannelTaper.symmetrize
  rw [scaledUnitBump_at_center he.ne']
  have hother : 0 ≤ scaledUnitBump c e (-c) :=
    scaledUnitBump_nonneg c e (-c)
  linarith

theorem smoothWindow_pos_at_center
    {c e : ℝ} (he : 0 < e) :
    0 < smoothWindow c e c := by
  unfold smoothWindow
    Zeta23Bridge.LiteralWeilNormalizedWindowBounds.normalized
  have hmass := smoothWindowRaw_mass_pos (c := c) he
  have hinv : 0 < (∫ u : ℝ, smoothWindowRaw c e u)⁻¹ :=
    inv_pos.mpr hmass
  exact mul_pos hinv (smoothWindowRaw_pos_at_center (c := c) he)

theorem smoothWindow_nonneg
    (c e u : ℝ) :
    0 ≤ smoothWindow c e u := by
  unfold smoothWindow
    Zeta23Bridge.LiteralWeilNormalizedWindowBounds.normalized
  by_cases hm : (∫ x : ℝ, smoothWindowRaw c e x) = 0
  · simp [hm]
  · have hraw : 0 ≤ smoothWindowRaw c e u :=
      smoothWindowRaw_nonneg c e u
    have hmass : 0 ≤ ∫ x : ℝ, smoothWindowRaw c e x := by
      exact integral_nonneg (fun x => smoothWindowRaw_nonneg c e x)
    exact mul_nonneg (inv_nonneg.mpr hmass) hraw


theorem smoothWindowRaw_windowTaper
    {c e : ℝ} (hc : 0 < c - e) (he : 0 < e) :
    Zeta23Bridge.LiteralWeilWindowRatioSeparation.WindowTaper
      (smoothWindowRaw c e) (c - e) (c + e) := by
  refine ⟨(smoothWindowRaw_contDiff he).continuous,
    smoothWindowRaw_compact he,
    smoothWindowRaw_nonneg c e,
    ?_,
    smoothWindowRaw_mass_pos he⟩
  intro u hu
  exact smoothWindowRaw_support_modulus hc he hu

end Synthesis

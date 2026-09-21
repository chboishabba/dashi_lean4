import Synthesis.RiemannProjectiveQuarticAtomicCertificate
import Synthesis.RiemannQuantitativeSymmetricBumpMass

/-!
# Quantitative localization of the repo scaled bump

This is the atom-to-smooth bridge needed by the quartic-escape construction.

For the nonnegative affine bump psi_{c,R}, R>0, its exact mass is

  integral psi_{c,R} = R * M0.

If a continuous weight w varies by at most eps across the bump support, then

  | integral psi_{c,R}(u) w(u) du
      - R*M0*w(c) |
    <= R*M0*eps.

For an even weight, the symmetric bump centered at +/-c therefore satisfies

  | integral symBump(c,R)(u) w(u) du
      - 2*R*M0*w(c) |
    <= 2*R*M0*eps.

No limiting measure or distribution is introduced: this is a direct finite-R
estimate on the actual C^2 compact bump used elsewhere in the repository.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

theorem integral_scaledUnitBump
    {c R : ℝ} (hR : 0 < R) :
    (∫ u : ℝ, scaledUnitBump c R u)
      = R * unitBumpMass0 := by
  have hmass := taperMass_scaledUnitBump (c := c) hR
  unfold taperMass at hmass
  have habs :
      (fun u : ℝ => |scaledUnitBump c R u|)
        = scaledUnitBump c R := by
    funext u
    rw [abs_of_nonneg (scaledUnitBump_nonneg c R u)]
  rw [habs] at hmass
  exact hmass

/--
Single-window localization against an arbitrary continuous weight.
-/
theorem scaledUnitBump_weighted_localization
    {c R eps : ℝ} (hR : 0 < R) (heps : 0 ≤ eps)
    {w : ℝ → ℝ}
    (hw : Continuous w)
    (hosc :
      ∀ u : ℝ, scaledUnitBump c R u ≠ 0 ->
        |w u - w c| ≤ eps) :
    |(∫ u : ℝ, scaledUnitBump c R u * w u)
        - (R * unitBumpMass0) * w c|
      ≤ (R * unitBumpMass0) * eps := by
  let phi : ℝ → ℝ := scaledUnitBump c R
  have hphiC : Continuous phi :=
    scaledUnitBump_continuous hR.ne' c
  have hphiK : HasCompactSupport phi :=
    scaledUnitBump_hasCompactSupport hR
  have hphiI : Integrable phi :=
    hphiC.integrable_of_hasCompactSupport hphiK
  have hweighted :
      Integrable (fun u : ℝ => phi u * w u) :=
    (hphiC.mul hw).integrable_of_hasCompactSupport hphiK.mul_right
  have hdiff :
      Integrable (fun u : ℝ => phi u * (w u - w c)) :=
    (hphiC.mul (hw.sub continuous_const))
      .integrable_of_hasCompactSupport hphiK.mul_right
  have hid :
      (∫ u : ℝ, phi u * w u)
          - (∫ u : ℝ, phi u) * w c
        =
      ∫ u : ℝ, phi u * (w u - w c) := by
    rw [integral_sub hweighted (hphiI.const_mul (w c))]
    rw [integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by ring
  have hdom :
      ∀ u : ℝ,
        |phi u * (w u - w c)| ≤ phi u * eps := by
    intro u
    by_cases hu : phi u = 0
    · simp [hu, heps]
    · rw [abs_mul, abs_of_nonneg (scaledUnitBump_nonneg c R u)]
      exact mul_le_mul_of_nonneg_left
        (hosc u hu) (scaledUnitBump_nonneg c R u)
  have hphiEps : Integrable (fun u : ℝ => phi u * eps) :=
    hphiI.mul_const eps
  calc
    |(∫ u : ℝ, scaledUnitBump c R u * w u)
        - (R * unitBumpMass0) * w c|
      =
    |(∫ u : ℝ, phi u * w u)
        - (∫ u : ℝ, phi u) * w c| := by
          rw [show (∫ u : ℝ, phi u) = R * unitBumpMass0 by
            simpa [phi] using integral_scaledUnitBump (c := c) hR]
    _ = |∫ u : ℝ, phi u * (w u - w c)| := by rw [hid]
    _ ≤ ∫ u : ℝ, |phi u * (w u - w c)| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ u : ℝ, phi u * eps := by
      apply integral_mono hdiff.abs hphiEps hdom
    _ = (R * unitBumpMass0) * eps := by
      rw [integral_mul_const, integral_scaledUnitBump (c := c) hR]

/--
Symmetric-window localization for even weights.
-/
theorem quantitativeSymBump_weighted_localization
    {c R eps : ℝ} (hR : 0 < R) (heps : 0 ≤ eps)
    {w : ℝ → ℝ}
    (hw : Continuous w)
    (heven : ∀ u, w (-u) = w u)
    (hosc :
      ∀ u : ℝ, scaledUnitBump c R u ≠ 0 ->
        |w u - w c| ≤ eps) :
    |(∫ u : ℝ, quantitativeSymBump c R u * w u)
        - (2 * R * unitBumpMass0) * w c|
      ≤ (2 * R * unitBumpMass0) * eps := by
  have hsingle :=
    scaledUnitBump_weighted_localization
      (c := c) hR heps hw hosc
  have hsym :
      (∫ u : ℝ, quantitativeSymBump c R u * w u)
        =
      2 * ∫ u : ℝ, scaledUnitBump c R u * w u := by
    unfold quantitativeSymBump
    exact integral_symmetrize
      (scaledUnitBump_continuous hR.ne' c)
      (scaledUnitBump_hasCompactSupport hR)
      hw heven
  rw [hsym]
  have htwo :
      |2 * ((∫ u : ℝ, scaledUnitBump c R u * w u)
        - (R * unitBumpMass0) * w c)|
        ≤ 2 * ((R * unitBumpMass0) * eps) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hsingle (by norm_num)
  convert htwo using 1 <;> ring


def normalizedSymBumpPairing
    (c R : ℝ) (w : ℝ → ℝ) : ℝ :=
  (∫ u : ℝ, quantitativeSymBump c R u * w u)
    / (2 * R * unitBumpMass0)

/--
For every continuous even weight, the mass-normalized symmetric bump pairing
approaches evaluation at its centre as the radius shrinks from the right.
This epsilon-radius form is convenient for finite families of moment weights.
-/
theorem exists_radius_normalizedSymBumpPairing_close
    {c : ℝ} {w : ℝ → ℝ}
    (hw : Continuous w)
    (heven : ∀ u, w (-u) = w u)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ R : ℝ, 0 < R → R < delta →
        |normalizedSymBumpPairing c R w - w c| ≤ eps := by
  have hca := hw.continuousAt
  rw [Metric.continuousAt_iff] at hca
  obtain ⟨delta, hdelta, hclose⟩ := hca eps heps
  refine ⟨delta, hdelta, ?_⟩
  intro R hR hRdelta
  have hosc :
      ∀ u : ℝ, scaledUnitBump c R u ≠ 0 ->
        |w u - w c| ≤ eps := by
    intro u hu
    have hsup := scaledUnitBump_support hR hu
    have hdist : dist u c < delta := by
      rw [Real.dist_eq]
      exact hsup.trans hRdelta
    have hwclose := hclose hdist
    simpa [Real.dist_eq] using hwclose.le
  have hloc :=
    quantitativeSymBump_weighted_localization
      (c := c) hR heps.le hw heven hosc
  have hmass : 0 < 2 * R * unitBumpMass0 := by
    have hM := unitBumpMass0_pos
    positivity
  unfold normalizedSymBumpPairing
  rw [abs_sub_comm] at hloc ⊢
  have hrewrite :
      (∫ u : ℝ, quantitativeSymBump c R u * w u)
          - (2 * R * unitBumpMass0) * w c
        =
      (2 * R * unitBumpMass0) *
        ((∫ u : ℝ, quantitativeSymBump c R u * w u)
            / (2 * R * unitBumpMass0) - w c) := by
    field_simp [ne_of_gt hmass]
    ring
  rw [hrewrite, abs_mul, abs_of_pos hmass] at hloc
  have := (mul_le_mul_left hmass).mp hloc
  simpa [abs_sub_comm] using this

end Synthesis

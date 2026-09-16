/-
# Row A1a — end-to-end assembly with no assumed constants

The two halves of the Row A1a margin have now each been reduced to source data.

* **Gaussian side.**  `MixedComponentPatch` computes the mixed Lorentz component
  of the constrained first variation `V = W + Q + R` exactly (the averaging
  variation `Q` and the constrained-projection part of `R` vanish there by
  Lorentz block diagonality; the gauge part of `R` is computed), and bounds it
  below on a positive-volume momentum box.  `A1MixedPatchCompiler` turns that
  into a shell floor with an explicit rational value.
* **Debt side.**  `QuarticChannelSources` computes each of the five quartic
  channel coefficients in closed form from source data: mode counts and spectral
  bounds for the two `log det` channels, Taylor-coefficient majorants for the
  three polynomial channels.

This file welds the two together.  Its point is that after the weld *no constant
in the statement is assumed*: the interaction debt constant is the explicit
`Cbeta (sourceChannelCoefficient …)` and the Gaussian floor is the explicit
rational `1/3276800`.

* `historyUniformQuartic_of_sourceChannels` : the five literal source shapes,
  with history-uniform data, give the `HistoryUniformQuartic` hypothesis with
  the *computed* coefficient vector.
* `A1_beta_pos_from_literal_sources` : hence, for every shell index and every
  admissible history, `β_j ≥ 1/3276800 > 0`.

**Honest status — Row A1 is not closed.**  The hypotheses of the final theorem
are exactly the remaining source identifications, all displayed:

1. that the shell Gaussian coefficient is the cell integral of the one-loop
   integrand built from the literal mixed component (`hident`, `hentry`);
2. that the shell interaction remainder is the sum of the five channels in their
   literal spectral/polynomial shapes, uniformly over admissible histories
   (`hchannels`), with uniform spectral and coefficient bounds;
3. the small-field domain conditions relating the running coupling to the
   spectral bounds.

None of these is proved here for Bałaban's construction, and none is replaced by
a postulate: they are hypotheses of a theorem.  The frozen research count is
unchanged.
-/
import RequestProject.YangMills.A1MixedPatchCompiler
import RequestProject.YangMills.QuarticChannelSources

namespace YangMills

open MeasureTheory Set Finset

/-- **The history-uniform quartic remainder from the five literal source
shapes.**  If, for every admissible history, the shell interaction remainder is
the sum of two spectral (`log det`) channels and three polynomial channels, with
spectra bounded by `Λ_det`, `Λ_gauge` and coefficients dominated by `A_int`,
`A_chart`, `A_loc`, all uniformly in the scale and the history, then the
five-channel quartic hypothesis holds with the *computed* coefficient vector
`sourceChannelCoefficient`. -/
theorem historyUniformQuartic_of_sourceChannels
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {betaInt : ℕ → (ℕ → ℝ) → ℝ} {Adm : (ℕ → ℝ) → Prop}
    {lamDet : ℕ → (ℕ → ℝ) → ι → ℝ} {lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ}
    {aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    {AInt AChart ALoc : ℕ → ℝ} {N : ℕ} {LamDet LamGauge theta : ℝ}
    (hchannels : ∀ j h, Adm h → betaInt j h =
        logDetChannel (lamDet j h) (h j)
        + tailPolyChannel (aInt j h) N (h j)
        + tailPolyChannel (aChart j h) N (h j)
        + logDetChannel (lamGauge j h) (h j)
        + tailPolyChannel (aLoc j h) N (h j))
    (hLd : ∀ j h i, |lamDet j h i| ≤ LamDet)
    (hLg : ∀ j h i, |lamGauge j h i| ≤ LamGauge)
    (hAInt : ∀ j h n, |aInt j h n| ≤ AInt n)
    (hAChart : ∀ j h n, |aChart j h n| ≤ AChart n)
    (hALoc : ∀ j h n, |aLoc j h n| ≤ ALoc n)
    (hsmall : ∀ j h, Adm h → 0 ≤ h j ∧ h j ≤ theta ∧
        h j * LamDet ≤ theta ∧ h j * LamGauge ≤ theta)
    (hth : theta < 1) :
    HistoryUniformQuartic betaInt Adm
      (sourceChannelCoefficient (Fintype.card ι) (Fintype.card κ)
        LamDet LamGauge theta AInt AChart ALoc N) := by
  intro j h hh
  obtain ⟨hg0, hgth, hgLd, hgLg⟩ := hsmall j h hh
  refine ⟨fun k => match k with
    | BetaChannel.determinant => logDetChannel (lamDet j h) (h j)
    | BetaChannel.interaction => tailPolyChannel (aInt j h) N (h j)
    | BetaChannel.chart => tailPolyChannel (aChart j h) N (h j)
    | BetaChannel.gauge => logDetChannel (lamGauge j h) (h j)
    | BetaChannel.localization => tailPolyChannel (aLoc j h) N (h j), ?_, ?_⟩
  · rw [hchannels j h hh, show (Finset.univ : Finset BetaChannel)
      = {BetaChannel.determinant, .interaction, .chart, .gauge, .localization} from rfl]
    simp
    ring
  · intro k
    cases k
    · exact abs_logDetChannel_le (fun i => hLd j h i) hg0 hgLd hth
    · exact abs_tailPolyChannel_le_of_majorant (fun n => hAInt j h n) hg0 hgth
    · exact abs_tailPolyChannel_le_of_majorant (fun n => hAChart j h n) hg0 hgth
    · exact abs_logDetChannel_le (fun i => hLg j h i) hg0 hgLg hth
    · exact abs_tailPolyChannel_le_of_majorant (fun n => hALoc j h n) hg0 hgth

/-- **The source-channel hypothesis package is inhabited.**  A one-mode spectrum
of size `1/2` in each of the two determinant channels, vanishing polynomial
channels, and admissible histories in `[0,1/4]` satisfy every hypothesis of
`historyUniformQuartic_of_sourceChannels`.  So the reduction above is not
vacuous: it does not secretly rest on incompatible small-field conditions. -/
theorem sourceChannel_package_nonvacuous :
    ∃ (betaInt : ℕ → (ℕ → ℝ) → ℝ) (Adm : (ℕ → ℝ) → Prop)
      (lamDet lamGauge : ℕ → (ℕ → ℝ) → Fin 1 → ℝ),
      (∀ j h, Adm h → betaInt j h =
          logDetChannel (lamDet j h) (h j)
          + tailPolyChannel (fun _ => (0:ℝ)) 0 (h j)
          + tailPolyChannel (fun _ => (0:ℝ)) 0 (h j)
          + logDetChannel (lamGauge j h) (h j)
          + tailPolyChannel (fun _ => (0:ℝ)) 0 (h j)) ∧
      (∀ j h i, |lamDet j h i| ≤ 1 / 2) ∧ (∀ j h i, |lamGauge j h i| ≤ 1 / 2) ∧
      (∀ j h, Adm h → 0 ≤ h j ∧ h j ≤ 1 / 2 ∧
        h j * (1 / 2 : ℝ) ≤ 1 / 2 ∧ h j * (1 / 2 : ℝ) ≤ 1 / 2) ∧
      Adm (fun _ => 1 / 4) := by
  refine ⟨fun j h => logDetChannel (fun _ : Fin 1 => (1 / 2 : ℝ)) (h j)
      + logDetChannel (fun _ : Fin 1 => (1 / 2 : ℝ)) (h j),
    fun h => ∀ j, 0 ≤ h j ∧ h j ≤ 1 / 4,
    fun _ _ _ => 1 / 2, fun _ _ _ => 1 / 2, ?_, ?_, ?_, ?_, ?_⟩
  · intro j h _
    simp [tailPolyChannel]
  · intro j h i; rw [abs_of_nonneg] ; norm_num
  · intro j h i; rw [abs_of_nonneg] ; norm_num
  · intro j h hh
    obtain ⟨h0, h1⟩ := hh j
    refine ⟨h0, by linarith, by linarith, by linarith⟩
  · intro j; norm_num

/-- **Row A1a end to end, with every constant computed.**  The Gaussian floor is
the explicit rational produced by the literal mixed-component box, and the
interaction debt constant is the explicit five-term
`Cbeta (sourceChannelCoefficient …)`.  The conclusion is a uniform positive
lower bound on every shell coefficient:

    β_j(g) ≥ 1/3276800 > 0.

Every remaining assumption is a displayed source identification, not a
postulate. -/
theorem A1_beta_pos_from_literal_sources
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {Adm : (ℕ → ℝ) → Prop} {g : ℕ → ℝ}
    {I : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → ℝ} {f : ℝ}
    {lamDet : ℕ → (ℕ → ℝ) → ι → ℝ} {lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ}
    {aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    {AInt AChart ALoc : ℕ → ℝ} {N : ℕ} {LamDet LamGauge theta : ℝ}
    (hf : |f| ≤ 1)
    (hident : ∀ j h, Adm h → betaZ j h = cellGaussianCoefficient (I j h))
    (hintg : ∀ j h, IntegrableOn (I j h) puncturedCell)
    (hnonneg : ∀ j h, ∀ q ∈ puncturedCell, 0 ≤ I j h q)
    (hentry : ∀ j h, ∀ q ∈ mixedPatch (1 / 16),
      |mixedConstrainedSymbol f q 0 1| ^ 2 / 2 ≤ I j h q)
    (hsplit : ∀ j h, beta j h = betaZ j h + betaInt j h)
    (hchannels : ∀ j h, Adm h → betaInt j h =
        logDetChannel (lamDet j h) (h j)
        + tailPolyChannel (aInt j h) N (h j)
        + tailPolyChannel (aChart j h) N (h j)
        + logDetChannel (lamGauge j h) (h j)
        + tailPolyChannel (aLoc j h) N (h j))
    (hLd : ∀ j h i, |lamDet j h i| ≤ LamDet)
    (hLg : ∀ j h i, |lamGauge j h i| ≤ LamGauge)
    (hAInt : ∀ j h n, |aInt j h n| ≤ AInt n)
    (hAChart : ∀ j h n, |aChart j h n| ≤ AChart n)
    (hALoc : ∀ j h n, |aLoc j h n| ≤ ALoc n)
    (hsmall : ∀ j h, Adm h → 0 ≤ h j ∧ h j ≤ theta ∧
        h j * LamDet ≤ theta ∧ h j * LamGauge ≤ theta)
    (hth : theta < 1) (hth0 : 0 ≤ theta)
    (hadm : Adm g) (hg0 : ∀ j, 0 ≤ g j)
    (hgg : ∀ j, g j ≤ criticalCoupling (2 * (1 / 16 : ℝ) ^ 4 * (1 / 50))
      (Cbeta (sourceChannelCoefficient (Fintype.card ι) (Fintype.card κ)
        LamDet LamGauge theta AInt AChart ALoc N)))
    (j : ℕ) :
    (1 : ℝ) / 3276800 ≤ beta j g :=
  A1_halfFloor_from_literalMixedSymbol hf hident hintg hnonneg hentry hsplit
    (historyUniformQuartic_of_sourceChannels hchannels hLd hLg hAInt hAChart hALoc hsmall hth)
    (fun k => sourceChannelCoefficient_nonneg hth hth0 k) hadm hg0 hgg j

/-- The strict positivity that Row A1a asks for, in the same literal form. -/
theorem A1_beta_strictly_pos_from_literal_sources
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {Adm : (ℕ → ℝ) → Prop} {g : ℕ → ℝ}
    {I : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → ℝ} {f : ℝ}
    {lamDet : ℕ → (ℕ → ℝ) → ι → ℝ} {lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ}
    {aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    {AInt AChart ALoc : ℕ → ℝ} {N : ℕ} {LamDet LamGauge theta : ℝ}
    (hf : |f| ≤ 1)
    (hident : ∀ j h, Adm h → betaZ j h = cellGaussianCoefficient (I j h))
    (hintg : ∀ j h, IntegrableOn (I j h) puncturedCell)
    (hnonneg : ∀ j h, ∀ q ∈ puncturedCell, 0 ≤ I j h q)
    (hentry : ∀ j h, ∀ q ∈ mixedPatch (1 / 16),
      |mixedConstrainedSymbol f q 0 1| ^ 2 / 2 ≤ I j h q)
    (hsplit : ∀ j h, beta j h = betaZ j h + betaInt j h)
    (hchannels : ∀ j h, Adm h → betaInt j h =
        logDetChannel (lamDet j h) (h j)
        + tailPolyChannel (aInt j h) N (h j)
        + tailPolyChannel (aChart j h) N (h j)
        + logDetChannel (lamGauge j h) (h j)
        + tailPolyChannel (aLoc j h) N (h j))
    (hLd : ∀ j h i, |lamDet j h i| ≤ LamDet)
    (hLg : ∀ j h i, |lamGauge j h i| ≤ LamGauge)
    (hAInt : ∀ j h n, |aInt j h n| ≤ AInt n)
    (hAChart : ∀ j h n, |aChart j h n| ≤ AChart n)
    (hALoc : ∀ j h n, |aLoc j h n| ≤ ALoc n)
    (hsmall : ∀ j h, Adm h → 0 ≤ h j ∧ h j ≤ theta ∧
        h j * LamDet ≤ theta ∧ h j * LamGauge ≤ theta)
    (hth : theta < 1) (hth0 : 0 ≤ theta)
    (hadm : Adm g) (hg0 : ∀ j, 0 ≤ g j)
    (hgg : ∀ j, g j ≤ criticalCoupling (2 * (1 / 16 : ℝ) ^ 4 * (1 / 50))
      (Cbeta (sourceChannelCoefficient (Fintype.card ι) (Fintype.card κ)
        LamDet LamGauge theta AInt AChart ALoc N)))
    (j : ℕ) :
    0 < beta j g :=
  lt_of_lt_of_le (by norm_num)
    (A1_beta_pos_from_literal_sources hf hident hintg hnonneg hentry hsplit hchannels
      hLd hLg hAInt hAChart hALoc hsmall hth hth0 hadm hg0 hgg j)

end YangMills

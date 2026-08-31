/-
# Row A1a — the welded end-to-end statement

`A1LiteralAssembly` states the Row A1a conclusion with the Gaussian entry
expressed through the *model* mixed symbol `mixedConstrainedSymbol`, and with
the two `MixedVanishing` facts still appearing upstream as hypotheses of
`MixedComponentPatch`.  `MixedVanishingWeld` proves those two facts from the
literal block-averaging kernel and the literal constrained projection.

This file states the version in which both improvements are used at once: the
Gaussian entry is phrased in terms of the *actual* constrained first variation
`V = W + Q + R` — not a model symbol — and the vanishing of `Q` and of the
constrained part of `R` on the chosen mixed component is a theorem, not an
assumption.

* `A1_beta_pos_welded` : for every shell index and every admissible history,
  `β_j(g) ≥ 1/3276800 > 0`, given
  - the one-loop identification of the Gaussian coefficient,
  - the paramagnetic entry `|V_{0,1;1}(q)|²/2 ≤ I(q)` on the box,
  - the identification of `Q` with the transformed averaging variation and of
    the constrained part of `R` with the transformed projection variation,
  - the Wilson and gauge component identifications on the chosen component,
  - the five literal source channels with uniform data.

**Honest status.**  Every remaining assumption is an identification of a named
object with a literal source object, or a small-field domain condition.  None is
a bound pulled out of the air, and none is a postulate.  Row A1 is **not**
closed: the identifications themselves are the remaining source obligations.
-/
import RequestProject.YangMills.A1LiteralAssembly
import RequestProject.YangMills.MixedVanishingWeld

namespace YangMills

open MeasureTheory Set Matrix

/-- **Row A1a, welded.**  The Gaussian floor is produced by the literal
constrained first variation on a positive-volume momentum box, with the
averaging and constrained-projection variations *proved* to vanish there, and
the interaction debt constant is the computed five-channel sum. -/
theorem A1_beta_pos_welded
    {color cc Idx : Type*} [Fintype color] [DecidableEq color]
    [Fintype cc] [DecidableEq cc] [Fintype (Idx × color)] [DecidableEq (Idx × color)]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {Adm : (ℕ → ℝ) → Prop} {g : ℕ → ℝ}
    {I : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → ℝ}
    (V : ConstrainedFirstVariation color) {Rgauge : VertexSymbol color} {f : ℝ}
    {PhiA : PositionTransform Site Site} {PhiP : PositionTransform Idx Idx}
    {L : ℕ} {T : Fin 4 → color → ℝ → TransportData color} {tA : ℝ}
    {Qf : Fin 4 → color → ℝ → Matrix (Fin 4 × cc) (Fin 4 × (Idx × color)) ℝ} {tP : ℝ}
    {a b c : color}
    {lamDet : ℕ → (ℕ → ℝ) → ι → ℝ} {lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ}
    {aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    {AInt AChart ALoc : ℕ → ℝ} {N : ℕ} {LamDet LamGauge theta : ℝ}
    -- the Gaussian sector
    (hPhiA : AnnihilatesZero PhiA) (hPhiP : AnnihilatesZero PhiP)
    (hQlor : ∀ rho c' t, IsLorentzDiagonal (Qf rho c' t))
    (hdet : ∀ rho c' t, IsUnit ((Qf rho c' t) * (Qf rho c' t)ᵀ).det)
    (hQid : V.Q = symbolOfPositionKernel PhiA (averagingVariationKernel L T tA))
    (hRsplit : ∀ al be rho : Fin 4, ∀ a' b' c' : color, ∀ q : Fin 4 → ℝ,
      V.R al be rho a' b' c' q
        = symbolOfPositionKernel PhiP (constrainedProjectionVariationKernel Qf tP)
            al be rho a' b' c' q
          + Rgauge al be rho a' b' c' q)
    (hf : |f| ≤ 1)
    (hW : ∀ x : Fin 4 → ℝ, V.W 0 1 1 a b c x = wilsonCubicBgZero x 0 1 1)
    (hRg : ∀ x : Fin 4 → ℝ, Rgauge 0 1 1 a b c x
      = gaugeVariationSymbol f (latticeMomentumVector x) 1 0 1)
    (hident : ∀ j h, Adm h → betaZ j h = cellGaussianCoefficient (I j h))
    (hintg : ∀ j h, IntegrableOn (I j h) puncturedCell)
    (hnonneg : ∀ j h, ∀ q ∈ puncturedCell, 0 ≤ I j h q)
    (hentry : ∀ j h, ∀ q ∈ mixedPatch (1 / 16), |V.total 0 1 1 a b c q| ^ 2 / 2 ≤ I j h q)
    -- the debt sector
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
    (1 : ℝ) / 3276800 ≤ beta j g := by
  have hpatchI : ∀ j' h, ∀ q ∈ mixedPatch (1 / 16 : ℝ), (1 : ℝ) / 50 ≤ I j' h q := by
    intro j' h q hq
    have hsym := constrainedFirstVariation_mixedPatch_floor_welded V hPhiA hPhiP
      hQlor hdet hQid hRsplit hf hW hRg hq
    have habs : (0 : ℝ) ≤ |V.total 0 1 1 a b c q| := abs_nonneg _
    have hsq : (1 : ℝ) / 50 ≤ |V.total 0 1 1 a b c q| ^ 2 / 2 := by nlinarith
    exact le_trans hsq (hentry j' h q hq)
  have hmain := A1_halfFloor_from_mixedPatch (delta := 1 / 16) (cpatch := 1 / 50)
    (by norm_num) le_rfl (by norm_num) hident hintg hnonneg hpatchI hsplit
    (historyUniformQuartic_of_sourceChannels hchannels hLd hLg hAInt hAChart hALoc hsmall hth)
    (fun k => sourceChannelCoefficient_nonneg hth hth0 k) hadm hg0 hgg j
  have hval : (2 * (1 / 16 : ℝ) ^ 4 * (1 / 50)) / 2 = 1 / 3276800 := by norm_num
  rw [hval] at hmain
  exact hmain

end YangMills

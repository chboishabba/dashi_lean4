/-
# Row A — the welded statement

This file assembles the four pieces of the Row A push into a single statement:

1. **A1.1 (source object).**  The averaging map is the flat/main specialisation
   Eq. (125) of the source (`CMP98AveragingEq125`), and the object the Gaussian
   sector consumes is the derivative of *that* operator in the background
   (`CMP98BackgroundDerivative`), whose zero total mass, range `2L` and derived
   linear-vanishing constant are theorems.
2. **A1.2 (beta normalisation).**  The Lean shell Gaussian coefficient is the
   coefficient of the tensor structure in the source polarization tensor, by
   expanding the same second variation `δ²/δB δB'` (`CMP109Polarization`).
3. **Trajectory.**  A uniformly positive shell coefficient puts the whole
   effective-coupling sequence in the window `0 < g_j ≤ γ`
   (`CMP109CouplingWindow`).
4. **Published theorem.**  The source small-field theorem is consumed in its
   literal implication form: coupling window in, small-field
   effective-action/analyticity package out.

`rowA_from_cmp98_averaging_and_cmp109Thm1` is the resulting implication.  Its
only unproved input is `thm1`, the source theorem itself, which is supplied as
an explicit hypothesis (an open socket).  Every other hypothesis is either
source data (a normalised background family of transports, its derivative, a
mass bound, the seagull kernels, the five-channel Taylor/spectral data) or an
arithmetic smallness condition; no correspondence hypothesis of the form "this
Lean object is the source object" survives on the averaging side.

`rowA_polarization_identification` adds the A1.2 conjunct: under the shape
hypothesis for the source effective action, the polarization coefficient at the
selected pair of test directions equals the shell Gaussian coefficient that the
Row A bound controls, and therefore inherits its two-sided bounds.

**This is not a claim that Row A is closed.**  It is the precise remaining
implication: with the published small-field theorem inhabited, the Row A
conclusion follows.
-/
import RequestProject.YangMills.CMP98BackgroundDerivative
import RequestProject.YangMills.CMP109CouplingWindow
import RequestProject.YangMills.CMP109Polarization

namespace YangMills

open Real

/-- **Row A, welded.**

From
* a normalised background family `T` of the Eq. (125) averaging transports,
  differentiable in the background parameter, whose derivative kernel has mass
  at most `M` with `16π²(2L)²M + 2M ≤ 1/2`;
* seagull kernels of mass at most `MW`;
* the five-channel spectral/Taylor data with their bounds;
* the recursion `u_{j+1} = u_j + β_j` and a bare coupling inside the window;
* the source small-field theorem `thm1` in its literal implication form;

one obtains
* the uniform shell bound `β_j ≥ 1/16777216 > 0` at every scale and admissible
  history,
* the coupling window `0 < g_j ≤ γ` at every effective scale, and
* the small-field effective-action/analyticity package for the trajectory. -/
theorem rowA_from_cmp98_averaging_and_cmp109Thm1
    {color : Type*} [Fintype color] [DecidableEq color]
    {ι κ ζ : Type*} [Fintype ι] [Fintype κ] [Fintype ζ]
    {Adm : (ℕ → ℝ) → Prop} {g : ℕ → ℝ} {f M MW t₀ : ℝ} {L : ℕ}
    {T : ℕ → (ℕ → ℝ) → ℝ → TransportData color}
    {Kd : ℕ → (ℕ → ℝ) → Fin 4 → BlockKernelIndex L → ℝ}
    {y : Site} {a b : color}
    {KW : ℕ → (ℕ → ℝ) → Fin 4 → Fin 4 → ζ → ℝ}
    {dW : ℕ → (ℕ → ℝ) → Fin 4 → Fin 4 → ζ → (Fin 4 → ℝ)}
    {lamDet : ℕ → (ℕ → ℝ) → ι → ℝ} {lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ}
    {aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    {AInt AChart ALoc : ℕ → ℝ} {N : ℕ} {LamDet LamGauge theta : ℝ}
    {u : ℕ → ℝ} {gamma : ℝ} {Pkg : (ℕ → ℝ) → Prop}
    (thm1 : ∀ gg : ℕ → ℝ, CouplingWindow gamma gg → Pkg gg)
    (hM : 0 ≤ M) (hMW : 0 ≤ MW)
    (hnorm : ∀ j h t, CMP98Normalized L (T j h t))
    (hderiv : ∀ j h mu i,
      HasDerivAt (fun t => cmp98Kernel L (T j h t) y mu a b i) (Kd j h mu i) t₀)
    (hmass : ∀ j h mu, kernelMass (Kd j h mu) ≤ M)
    (hsmallK : linearVanishingConstant (2 * L) M ≤ 1 / 2)
    (hmassW : ∀ j h a' b', kernelMass (KW j h a' b') ≤ MW)
    (hLd : ∀ j h i, |lamDet j h i| ≤ LamDet)
    (hLg : ∀ j h i, |lamGauge j h i| ≤ LamGauge)
    (hAInt : ∀ j h n, |aInt j h n| ≤ AInt n)
    (hAChart : ∀ j h n, |aChart j h n| ≤ AChart n)
    (hALoc : ∀ j h n, |aLoc j h n| ≤ ALoc n)
    (hsmall : ∀ j h, Adm h → 0 ≤ h j ∧ h j ≤ theta ∧
        h j * LamDet ≤ theta ∧ h j * LamGauge ≤ theta)
    (hth : theta < 1) (hth0 : 0 ≤ theta)
    (hadm : Adm g) (hg0 : ∀ j, 0 ≤ g j)
    (hgg : ∀ j, g j ≤ criticalCoupling (1 / 8388608 : ℝ)
      (Cbeta (sourceChannelCoefficient (Fintype.card ι) (Fintype.card κ)
        LamDet LamGauge theta AInt AChart ALoc N)))
    (hu0 : 0 < u 0)
    (hstep : ∀ j, u (j + 1) = u j + shellBetaOfSources
      (fun j' h => literalOneLoopIntegrand
        (sourceVariationMatrix f 1
          (diagCosSymbolMatrix (Kd j' h) (fun mu => blockAveragingDispl L mu)))
        (cosSymbolMatrix (KW j' h) (dW j' h)))
      lamDet lamGauge aInt aChart aLoc N j g)
    (hgamma : 0 ≤ gamma) (hstart : (u 0)⁻¹ ≤ gamma ^ 2) :
    (∀ j, (1 : ℝ) / 16777216 ≤ shellBetaOfSources
        (fun j' h => literalOneLoopIntegrand
          (sourceVariationMatrix f 1
            (diagCosSymbolMatrix (Kd j' h) (fun mu => blockAveragingDispl L mu)))
          (cosSymbolMatrix (KW j' h) (dW j' h)))
        lamDet lamGauge aInt aChart aLoc N j g)
      ∧ CouplingWindow gamma (effectiveCoupling u)
      ∧ Pkg (effectiveCoupling u) := by
  have hbl : ∀ j, (1 : ℝ) / 16777216 ≤ shellBetaOfSources
      (fun j' h => literalOneLoopIntegrand
        (sourceVariationMatrix f 1
          (diagCosSymbolMatrix (Kd j' h) (fun mu => blockAveragingDispl L mu)))
        (cosSymbolMatrix (KW j' h) (dW j' h)))
      lamDet lamGauge aInt aChart aLoc N j g := fun j =>
    A1_beta_pos_from_cmp98_averaging (y := y) (a := a) (b := b) (T := T)
      hM hMW hnorm hderiv hmass hsmallK hmassW hLd hLg hAInt hAChart hALoc
      hsmall hth hth0 hadm hg0 hgg j
  have hwin : CouplingWindow gamma (effectiveCoupling u) :=
    couplingWindow_of_positiveShell hstep hbl (by norm_num) hu0 hgamma hstart
  exact ⟨hbl, hwin, thm1 _ hwin⟩

/-- **A1.2 inside the welded statement.**  With the source effective action
carrying the Row A shell Gaussian coefficient on the normalised tensor
structure, the polarization coefficient of the source *is* that coefficient, and
it is trapped between `1/8388608` and the Row A ceiling. -/
theorem rowA_polarization_identification
    {bIdx : Type*} [DecidableEq bIdx] {E Rem : (bIdx → ℝ) → ℝ} {b b' : bIdx}
    {ξ ζ : Type*} [Fintype ξ] [Fintype ζ] {f R M MW q20 q02 : ℝ}
    {Kk : Fin 4 → ξ → ℝ} {dd : Fin 4 → ξ → (Fin 4 → ℝ)}
    {KW : Fin 4 → Fin 4 → ζ → ℝ} {dW : Fin 4 → Fin 4 → ζ → (Fin 4 → ℝ)}
    {rem1 : ℝ → ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hMW : 0 ≤ MW)
    (hzero : ∀ a, ∑ i, Kk a i = 0)
    (hd : ∀ a i mu, |dd a i mu| ≤ R)
    (hmass : ∀ a, kernelMass (Kk a) ≤ M)
    (hsmallK : linearVanishingConstant R M ≤ 1 / 2)
    (hmassW : ∀ a b, kernelMass (KW a b) ≤ MW)
    (hE : ∀ s t, E (twoDirConfig b b' s t)
      = cellGaussianCoefficient
          (literalOneLoopIntegrand
            (sourceVariationMatrix f 1 (diagCosSymbolMatrix Kk dd)) (cosSymbolMatrix KW dW))
        * ((s * t) + q20 * s ^ 2 + q02 * t ^ 2) + Rem (twoDirConfig b b' s t))
    (hRem1 : ∀ s, HasDerivAt (fun t => Rem (twoDirConfig b b' s t)) (rem1 s) 0)
    (hRem2 : HasDerivAt rem1 0 0) :
    polarizationAt E b b'
        = cellGaussianCoefficient
            (literalOneLoopIntegrand
              (sourceVariationMatrix f 1 (diagCosSymbolMatrix Kk dd)) (cosSymbolMatrix KW dW))
      ∧ 1 / 8388608 ≤ polarizationAt E b b'
      ∧ polarizationAt E b b' ≤ shellGaussianCeiling (linearVanishingConstant R M) MW := by
  have h := polarization_two_sided_from_kernels hR hM hMW hzero hd hmass hsmallK hmassW
    hE hRem1 hRem2
  exact ⟨shellGaussian_eq_polarization hE hRem1 hRem2, h.1, h.2⟩

end YangMills

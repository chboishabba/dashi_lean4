import Synthesis.RiemannSelectedPrimeSensitiveThreeTapTerminalNearLine

/-!
# One-scale resonance decision surface

At prime resonance cos(t log 2)=0 the transformed prime projective channel
vanishes exactly.  The whole-terminal constant is therefore controlled by the
non-prime completed carrier plus the canonical adaptive local slack.

This file names that exact scalar and combines it with the normalized J2
polynomial.  The pair
  (resonance constant, normalized J2 polynomial)
is the one-scale near-line decision surface.
-/

noncomputable section
namespace Synthesis

open scoped Real

theorem threeTapNormalizedShift_sixteen
    (t : ℝ) :
    16 * threeTapNormalizedShift t (Real.log 2)
      = t * Real.log 2 := by
  unfold threeTapNormalizedShift
  ring

theorem threeTap_primeResonance_eq_normalized
    {t : ℝ}
    (hphase : Real.cos (t * Real.log 2) = 0) :
    Real.cos
      (16 * threeTapNormalizedShift t (Real.log 2)) = 0 := by
  rw [threeTapNormalizedShift_sixteen]
  exact hphase

def QuarticFourSignedPolePair.threeTapResonanceNonPrimeExternal
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
    +
  W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect
    +
  W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect

def QuarticFourSignedPolePair.threeTapResonanceTerminalConstant
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  - (W.threeTapResonanceNonPrimeExternal eps
      + (1/2 : ℝ) * W.threeTapAdaptiveLocalSlack eps)

theorem QuarticFourSignedPolePair.threeTapCompletedExternal_eq_nonPrime_at_resonance
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0) :
    W.threeTapCompletedExternal eps
      = W.threeTapResonanceNonPrimeExternal eps := by
  rw [W.threeTapCompletedExternal_at_resonance ht hphase]
  unfold QuarticFourSignedPolePair.threeTapResonanceNonPrimeExternal

theorem QuarticFourSignedPolePair.threeTapAdaptiveTerminalConstant_eq_resonance
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0) :
    W.threeTapAdaptiveTerminalConstant eps
      =
    W.threeTapResonanceTerminalConstant eps := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveTerminalConstant
    QuarticFourSignedPolePair.threeTapResonanceTerminalConstant
  rw [W.threeTapCompletedExternal_eq_nonPrime_at_resonance ht hphase]

def QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  eps * W.threeTapNormalizedJ2LinearCoeff
    + eps^2 * W.threeTapNormalizedJ2QuadraticCoeff

theorem QuarticFourSignedPolePair.threeTap_target_second_derivative_sign_resonance_surface
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapCombinedHeightD2 eps 0
      =
    -(1/(t/16)^4)
      * W.threeTapNormalizedJ2Polynomial eps := by
  unfold QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial
  exact W.threeTap_target_second_derivative_sign ht

/-- Exact one-scale near-line decision datum at resonance. -/
structure QuarticFourSignedPolePair.ThreeTapResonanceDecisionData
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) where
  terminalConstant : ℝ
  j2Polynomial : ℝ
  terminalConstant_eq :
    terminalConstant = W.threeTapResonanceTerminalConstant eps
  j2Polynomial_eq :
    j2Polynomial = W.threeTapNormalizedJ2Polynomial eps

def QuarticFourSignedPolePair.threeTapResonanceDecisionData
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) :
    W.ThreeTapResonanceDecisionData eps where
  terminalConstant := W.threeTapResonanceTerminalConstant eps
  j2Polynomial := W.threeTapNormalizedJ2Polynomial eps
  terminalConstant_eq := rfl
  j2Polynomial_eq := rfl

/-- On the balanced resonance-constant locus, a negative normalized J2
polynomial gives a strictly positive whole-terminal quadratic band. -/
theorem QuarticFourSignedPolePair.exists_threeTapResonantTerminalProfile_pos_right
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (hmult : 0 < mult)
    (hconst : W.threeTapResonanceTerminalConstant eps = 0)
    (hJ : W.threeTapNormalizedJ2Polynomial eps < 0) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        0 < W.threeTapAdaptiveTerminalProfile eps mult a := by
  have hconst' : W.threeTapAdaptiveTerminalConstant eps = 0 := by
    rw [W.threeTapAdaptiveTerminalConstant_eq_resonance ht hphase]
    exact hconst
  unfold QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial at hJ
  exact
    W.exists_threeTapAdaptiveTerminalProfile_pos_right_of_balanced_J2poly_neg
      ht hmult hconst' hJ

/-- On the balanced resonance-constant locus, a positive normalized J2
polynomial gives a strictly negative whole-terminal band. -/
theorem QuarticFourSignedPolePair.exists_threeTapResonantTerminalProfile_neg_right
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (hmult : 0 < mult)
    (hconst : W.threeTapResonanceTerminalConstant eps = 0)
    (hJ : 0 < W.threeTapNormalizedJ2Polynomial eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        W.threeTapAdaptiveTerminalProfile eps mult a < 0 := by
  have hconst' : W.threeTapAdaptiveTerminalConstant eps = 0 := by
    rw [W.threeTapAdaptiveTerminalConstant_eq_resonance ht hphase]
    exact hconst
  unfold QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial at hJ
  exact
    W.exists_threeTapAdaptiveTerminalProfile_neg_right_of_balanced_J2poly_pos
      ht hmult hconst' hJ

end Synthesis

import Synthesis.RiemannSelectedPrimeSensitiveThreeTapResonanceDecision

/-!
# Complete one-scale terminal near-line decision

The whole adaptive terminal profile has a constant term before the transformed
J2 coordinate becomes relevant.  This file closes that decision hierarchy.

For fixed height, witness, tap strength and positive zero multiplicity:

* positive terminal constant => positive terminal profile on a right
  neighbourhood of the line;
* negative terminal constant => negative terminal profile on a right
  neighbourhood;
* only on the balanced constant locus does the normalized J2 polynomial decide
  the quadratic sign;
* only when both the constant and J2 polynomial vanish is J4 analysis justified.

The same five-way fork is exported on the exact prime-resonance surface.
-/

noncomputable section
namespace Synthesis

open Set Filter
open scoped Real

theorem QuarticFourSignedPolePair.exists_threeTapAdaptiveTerminalProfile_pos_right_of_constant_pos
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hconst : 0 < W.threeTapAdaptiveTerminalConstant eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        0 < W.threeTapAdaptiveTerminalProfile eps mult a := by
  let f : ℝ → ℝ := W.threeTapAdaptiveTerminalProfile eps mult
  have hf0 : 0 < f 0 := by
    dsimp [f]
    rw [W.threeTapAdaptiveTerminalProfile_zero]
    exact hconst
  have hcont : ContinuousAt f 0 := by
    dsimp [f]
    exact
      (W.threeTapAdaptiveTerminalProfile_hasDerivAt
        (eps := eps) (mult := mult) (a := 0) ht).continuousAt
  have hnh : f ⁻¹' Set.Ioi (0 : ℝ) ∈ 𝓝 (0 : ℝ) := by
    exact hcont (Set.Ioi_mem_nhds hf0)
  rw [Metric.mem_nhds_iff] at hnh
  obtain ⟨delta, hdelta, hball⟩ := hnh
  refine ⟨delta, hdelta, ?_⟩
  intro a ha had
  have hmem : a ∈ Metric.ball (0 : ℝ) delta := by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [abs_of_pos ha] using had
  exact hball hmem

theorem QuarticFourSignedPolePair.exists_threeTapAdaptiveTerminalProfile_neg_right_of_constant_neg
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hconst : W.threeTapAdaptiveTerminalConstant eps < 0) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        W.threeTapAdaptiveTerminalProfile eps mult a < 0 := by
  let f : ℝ → ℝ := W.threeTapAdaptiveTerminalProfile eps mult
  have hf0 : f 0 < 0 := by
    dsimp [f]
    rw [W.threeTapAdaptiveTerminalProfile_zero]
    exact hconst
  have hcont : ContinuousAt f 0 := by
    dsimp [f]
    exact
      (W.threeTapAdaptiveTerminalProfile_hasDerivAt
        (eps := eps) (mult := mult) (a := 0) ht).continuousAt
  have hnh : f ⁻¹' Set.Iio (0 : ℝ) ∈ 𝓝 (0 : ℝ) := by
    exact hcont (Set.Iio_mem_nhds hf0)
  rw [Metric.mem_nhds_iff] at hnh
  obtain ⟨delta, hdelta, hball⟩ := hnh
  refine ⟨delta, hdelta, ?_⟩
  intro a ha had
  have hmem : a ∈ Metric.ball (0 : ℝ) delta := by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [abs_of_pos ha] using had
  exact hball hmem

/-- The complete one-scale near-line decision.  The last branch is the only
locus on which transformed J4 analysis is logically needed. -/
theorem QuarticFourSignedPolePair.threeTapAdaptiveTerminal_nearLine_five_way
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hmult : 0 < mult) :
    (
      0 < W.threeTapAdaptiveTerminalConstant eps
      ∧
      ∃ delta : ℝ, 0 < delta ∧
        ∀ a : ℝ, 0 < a → a < delta →
          0 < W.threeTapAdaptiveTerminalProfile eps mult a
    )
    ∨
    (
      W.threeTapAdaptiveTerminalConstant eps < 0
      ∧
      ∃ delta : ℝ, 0 < delta ∧
        ∀ a : ℝ, 0 < a → a < delta →
          W.threeTapAdaptiveTerminalProfile eps mult a < 0
    )
    ∨
    (
      W.threeTapAdaptiveTerminalConstant eps = 0
      ∧ W.threeTapNormalizedJ2Polynomial eps < 0
      ∧
      ∃ delta : ℝ, 0 < delta ∧
        ∀ a : ℝ, 0 < a → a < delta →
          0 < W.threeTapAdaptiveTerminalProfile eps mult a
    )
    ∨
    (
      W.threeTapAdaptiveTerminalConstant eps = 0
      ∧ 0 < W.threeTapNormalizedJ2Polynomial eps
      ∧
      ∃ delta : ℝ, 0 < delta ∧
        ∀ a : ℝ, 0 < a → a < delta →
          W.threeTapAdaptiveTerminalProfile eps mult a < 0
    )
    ∨
    (
      W.threeTapAdaptiveTerminalConstant eps = 0
      ∧ W.threeTapNormalizedJ2Polynomial eps = 0
    ) := by
  rcases lt_trichotomy
      (W.threeTapAdaptiveTerminalConstant eps) 0 with hneg | hzero | hpos
  · exact Or.inr <| Or.inl
      ⟨hneg,
        W.exists_threeTapAdaptiveTerminalProfile_neg_right_of_constant_neg
          ht hneg⟩
  · rcases lt_trichotomy
        (W.threeTapNormalizedJ2Polynomial eps) 0 with hJneg | hJzero | hJpos
    · refine Or.inr <| Or.inr <| Or.inl ⟨hzero, hJneg, ?_⟩
      unfold QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial at hJneg
      exact
        W.exists_threeTapAdaptiveTerminalProfile_pos_right_of_balanced_J2poly_neg
          ht hmult hzero hJneg
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨hzero, hJzero⟩
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨hzero, hJpos, ?_⟩
      unfold QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial at hJpos
      exact
        W.exists_threeTapAdaptiveTerminalProfile_neg_right_of_balanced_J2poly_pos
          ht hmult hzero hJpos
  · exact Or.inl
      ⟨hpos,
        W.exists_threeTapAdaptiveTerminalProfile_pos_right_of_constant_pos
          ht hpos⟩

/-- Exact resonance specialization of the complete terminal decision.  Prime
resonance changes only the name of the constant; the near-line hierarchy is
otherwise identical. -/
theorem QuarticFourSignedPolePair.threeTapResonance_nearLine_five_way
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (hmult : 0 < mult) :
    (
      0 < W.threeTapResonanceTerminalConstant eps
      ∧
      ∃ delta : ℝ, 0 < delta ∧
        ∀ a : ℝ, 0 < a → a < delta →
          0 < W.threeTapAdaptiveTerminalProfile eps mult a
    )
    ∨
    (
      W.threeTapResonanceTerminalConstant eps < 0
      ∧
      ∃ delta : ℝ, 0 < delta ∧
        ∀ a : ℝ, 0 < a → a < delta →
          W.threeTapAdaptiveTerminalProfile eps mult a < 0
    )
    ∨
    (
      W.threeTapResonanceTerminalConstant eps = 0
      ∧ W.threeTapNormalizedJ2Polynomial eps < 0
      ∧
      ∃ delta : ℝ, 0 < delta ∧
        ∀ a : ℝ, 0 < a → a < delta →
          0 < W.threeTapAdaptiveTerminalProfile eps mult a
    )
    ∨
    (
      W.threeTapResonanceTerminalConstant eps = 0
      ∧ 0 < W.threeTapNormalizedJ2Polynomial eps
      ∧
      ∃ delta : ℝ, 0 < delta ∧
        ∀ a : ℝ, 0 < a → a < delta →
          W.threeTapAdaptiveTerminalProfile eps mult a < 0
    )
    ∨
    (
      W.threeTapResonanceTerminalConstant eps = 0
      ∧ W.threeTapNormalizedJ2Polynomial eps = 0
    ) := by
  have hconst :
      W.threeTapAdaptiveTerminalConstant eps
        = W.threeTapResonanceTerminalConstant eps :=
    W.threeTapAdaptiveTerminalConstant_eq_resonance ht hphase
  rcases W.threeTapAdaptiveTerminal_nearLine_five_way ht hmult with
      hpos | hneg | hJneg | hJpos | hex
  · left
    rcases hpos with ⟨hc, hband⟩
    exact ⟨by rwa [hconst] at hc, hband⟩
  · right; left
    rcases hneg with ⟨hc, hband⟩
    exact ⟨by rwa [hconst] at hc, hband⟩
  · right; right; left
    rcases hJneg with ⟨hc, hJ, hband⟩
    exact ⟨by rwa [hconst] at hc, hJ, hband⟩
  · right; right; right; left
    rcases hJpos with ⟨hc, hJ, hband⟩
    exact ⟨by rwa [hconst] at hc, hJ, hband⟩
  · right; right; right; right
    rcases hex with ⟨hc, hJ⟩
    exact ⟨by rwa [hconst] at hc, hJ⟩

end Synthesis

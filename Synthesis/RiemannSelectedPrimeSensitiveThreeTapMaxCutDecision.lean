import Synthesis.RiemannSelectedPrimeSensitiveThreeTapTerminalDecision

/-!
# One-scale three-tap max-cut sign compilers

The adaptive-local compiler has already paid the transformed local source and
proved its slack nonnegative.  Hence at prime resonance the whole terminal
constant has the exact form

  C_res = -(N_res + (1/2) L_slack),

where N_res is the completed non-prime external channel and L_slack >= 0.

This file extracts the strongest immediate consequences:

* a nonnegative non-prime resonance carrier rules out a positive constant;
* a strictly positive non-prime carrier forces a strictly negative terminal
  band near the line;
* even in the boundary case C_res = 0, a positive normalized J2 polynomial
  forces a strictly negative quadratic band;
* therefore N_res >= 0 together with J2_eps > 0 is already a complete local
  one-scale FAIL certificate;
* the exceptional quartic locus is exactly eps = 0 or A + eps B = 0, and for
  nonzero eps with B != 0 it is the unique strength eps = -A/B.

No sign of N_res or of the oscillatory J2 phase is assumed here.
-/

noncomputable section
namespace Synthesis

open scoped Real


/-- The fully paid resonance cost.  This is the single scalar that must be
negative for a positive constant-term pass and nonnegative for the J2-based
fail compiler above. -/
def QuarticFourSignedPolePair.threeTapResonancePaidCost
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  W.threeTapResonanceNonPrimeExternal eps
    + (1/2 : ℝ) * W.threeTapAdaptiveLocalSlack eps


theorem QuarticFourSignedPolePair.threeTapResonancePaidCost_eq_adaptive_far_local
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapResonancePaidCost eps
      =
    W.threeTapAdaptiveFarExact eps
      +
    W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect
      +
    W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
      +
    (1/2 : ℝ) *
      (W.threeTapAdaptiveLocalExact eps
        + W.threeTapAdaptiveLocalBudget eps) := by
  unfold QuarticFourSignedPolePair.threeTapResonancePaidCost
    QuarticFourSignedPolePair.threeTapResonanceNonPrimeExternal
    QuarticFourSignedPolePair.threeTapAdaptiveLocalSlack
  rw [W.threeTap_offOrd_eq_local_add_far]
  ring

theorem QuarticFourSignedPolePair.threeTapResonancePaidCost_ge_nonPrime
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapResonanceNonPrimeExternal eps
      <= W.threeTapResonancePaidCost eps := by
  unfold QuarticFourSignedPolePair.threeTapResonancePaidCost
  have hs : 0 <= W.threeTapAdaptiveLocalSlack eps :=
    W.threeTapAdaptiveLocalSlack_nonneg
  linarith

theorem QuarticFourSignedPolePair.threeTapResonanceTerminalConstant_eq_neg_paidCost
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapResonanceTerminalConstant eps
      = - W.threeTapResonancePaidCost eps := by
  rfl

theorem QuarticFourSignedPolePair.threeTapResonanceTerminalConstant_pos_iff_paidCost_neg
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 < W.threeTapResonanceTerminalConstant eps
      ↔ W.threeTapResonancePaidCost eps < 0 := by
  rw [W.threeTapResonanceTerminalConstant_eq_neg_paidCost]
  linarith

theorem QuarticFourSignedPolePair.threeTapResonanceTerminalConstant_neg_iff_paidCost_pos
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapResonanceTerminalConstant eps < 0
      ↔ 0 < W.threeTapResonancePaidCost eps := by
  rw [W.threeTapResonanceTerminalConstant_eq_neg_paidCost]
  linarith

/-- Direct one-scale PASS compiler at resonance: a negative fully paid
non-target cost gives a positive terminal band without consulting J2. -/
theorem QuarticFourSignedPolePair.exists_threeTapResonantTerminalProfile_pos_right_of_paidCost_neg
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (hcost : W.threeTapResonancePaidCost eps < 0) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        0 < W.threeTapAdaptiveTerminalProfile eps mult a := by
  have hcres : 0 < W.threeTapResonanceTerminalConstant eps :=
    (W.threeTapResonanceTerminalConstant_pos_iff_paidCost_neg).2 hcost
  have hcadaptive : 0 < W.threeTapAdaptiveTerminalConstant eps := by
    rw [W.threeTapAdaptiveTerminalConstant_eq_resonance ht hphase]
    exact hcres
  exact
    W.exists_threeTapAdaptiveTerminalProfile_pos_right_of_constant_pos
      ht hcadaptive

/-- Direct strict FAIL compiler at resonance: a positive fully paid cost gives
a negative terminal band without consulting J2. -/
theorem QuarticFourSignedPolePair.exists_threeTapResonantTerminalProfile_neg_right_of_paidCost_pos
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (hcost : 0 < W.threeTapResonancePaidCost eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        W.threeTapAdaptiveTerminalProfile eps mult a < 0 := by
  have hcres : W.threeTapResonanceTerminalConstant eps < 0 :=
    (W.threeTapResonanceTerminalConstant_neg_iff_paidCost_pos).2 hcost
  have hcadaptive : W.threeTapAdaptiveTerminalConstant eps < 0 := by
    rw [W.threeTapAdaptiveTerminalConstant_eq_resonance ht hphase]
    exact hcres
  exact
    W.exists_threeTapAdaptiveTerminalProfile_neg_right_of_constant_neg
      ht hcadaptive

/-- On the exactly paid boundary, J2 is the first decision coordinate. -/
theorem QuarticFourSignedPolePair.exists_threeTapResonantTerminalProfile_neg_right_of_paidCost_zero_J2_pos
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (hmult : 0 < mult)
    (hcost : W.threeTapResonancePaidCost eps = 0)
    (hJ : 0 < W.threeTapNormalizedJ2Polynomial eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        W.threeTapAdaptiveTerminalProfile eps mult a < 0 := by
  have hc : W.threeTapResonanceTerminalConstant eps = 0 := by
    rw [W.threeTapResonanceTerminalConstant_eq_neg_paidCost, hcost]
    ring
  exact
    W.exists_threeTapResonantTerminalProfile_neg_right
      ht hphase hmult hc hJ

theorem QuarticFourSignedPolePair.exists_threeTapResonantTerminalProfile_pos_right_of_paidCost_zero_J2_neg
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (hmult : 0 < mult)
    (hcost : W.threeTapResonancePaidCost eps = 0)
    (hJ : W.threeTapNormalizedJ2Polynomial eps < 0) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        0 < W.threeTapAdaptiveTerminalProfile eps mult a := by
  have hc : W.threeTapResonanceTerminalConstant eps = 0 := by
    rw [W.threeTapResonanceTerminalConstant_eq_neg_paidCost, hcost]
    ring
  exact
    W.exists_threeTapResonantTerminalProfile_pos_right
      ht hphase hmult hc hJ


theorem QuarticFourSignedPolePair.threeTapResonanceTerminalConstant_eq_neg_sum
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapResonanceTerminalConstant eps
      =
    -(
      W.threeTapResonanceNonPrimeExternal eps
        + (1/2 : ℝ) * W.threeTapAdaptiveLocalSlack eps
    ) := by
  rfl

theorem QuarticFourSignedPolePair.threeTapResonanceTerminalConstant_nonpos_of_nonPrime_nonneg
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hnonprime : 0 <= W.threeTapResonanceNonPrimeExternal eps) :
    W.threeTapResonanceTerminalConstant eps <= 0 := by
  rw [W.threeTapResonanceTerminalConstant_eq_neg_sum]
  have hslack : 0 <= W.threeTapAdaptiveLocalSlack eps :=
    W.threeTapAdaptiveLocalSlack_nonneg
  linarith

theorem QuarticFourSignedPolePair.threeTapResonanceTerminalConstant_neg_of_nonPrime_pos
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hnonprime : 0 < W.threeTapResonanceNonPrimeExternal eps) :
    W.threeTapResonanceTerminalConstant eps < 0 := by
  rw [W.threeTapResonanceTerminalConstant_eq_neg_sum]
  have hslack : 0 <= W.threeTapAdaptiveLocalSlack eps :=
    W.threeTapAdaptiveLocalSlack_nonneg
  linarith

theorem QuarticFourSignedPolePair.threeTapResonanceTerminalConstant_neg_of_slack_pos
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hnonprime : 0 <= W.threeTapResonanceNonPrimeExternal eps)
    (hslack : 0 < W.threeTapAdaptiveLocalSlack eps) :
    W.threeTapResonanceTerminalConstant eps < 0 := by
  rw [W.threeTapResonanceTerminalConstant_eq_neg_sum]
  linarith

theorem QuarticFourSignedPolePair.threeTapResonanceTerminalConstant_pos_iff
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 < W.threeTapResonanceTerminalConstant eps
      ↔
    W.threeTapResonanceNonPrimeExternal eps
        + (1/2 : ℝ) * W.threeTapAdaptiveLocalSlack eps < 0 := by
  rw [W.threeTapResonanceTerminalConstant_eq_neg_sum]
  linarith


/-- The strongest fully-paid local fail compiler: if the exact adaptive
far/local resonance cost is nonnegative and J2 has the wrong sign, the whole
one-scale terminal profile is strictly negative near the critical line. -/
theorem QuarticFourSignedPolePair.exists_threeTapResonantTerminalProfile_neg_right_of_paidCost_nonneg_J2_pos
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (hmult : 0 < mult)
    (hcost : 0 <= W.threeTapResonancePaidCost eps)
    (hJ : 0 < W.threeTapNormalizedJ2Polynomial eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        W.threeTapAdaptiveTerminalProfile eps mult a < 0 := by
  rcases lt_or_eq_of_le hcost with hcostpos | hcostzero
  · exact
      W.exists_threeTapResonantTerminalProfile_neg_right_of_paidCost_pos
        ht hphase hcostpos
  · exact
      W.exists_threeTapResonantTerminalProfile_neg_right_of_paidCost_zero_J2_pos
        ht hphase hmult hcostzero hJ

/-- A nonnegative completed non-prime resonance carrier plus the wrong J2 sign
is already enough to force a strict negative near-line terminal band.  This
covers both possibilities for the constant: strictly negative, or exactly
balanced. -/
theorem QuarticFourSignedPolePair.exists_threeTapResonantTerminalProfile_neg_right_of_nonPrime_nonneg_J2_pos
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (hmult : 0 < mult)
    (hnonprime : 0 <= W.threeTapResonanceNonPrimeExternal eps)
    (hJ : 0 < W.threeTapNormalizedJ2Polynomial eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        W.threeTapAdaptiveTerminalProfile eps mult a < 0 := by
  have hc :
      W.threeTapResonanceTerminalConstant eps <= 0 :=
    W.threeTapResonanceTerminalConstant_nonpos_of_nonPrime_nonneg hnonprime
  rcases lt_or_eq_of_le hc with hcneg | hczero
  · have hadaptive :
        W.threeTapAdaptiveTerminalConstant eps < 0 := by
      rw [W.threeTapAdaptiveTerminalConstant_eq_resonance ht hphase]
      exact hcneg
    exact
      W.exists_threeTapAdaptiveTerminalProfile_neg_right_of_constant_neg
        ht hadaptive
  · exact
      W.exists_threeTapResonantTerminalProfile_neg_right
        ht hphase hmult hczero hJ

/-- Atomic positive margin version of the preceding fail certificate. -/
theorem QuarticFourSignedPolePair.exists_threeTapResonantTerminalProfile_neg_right_of_nonPrime_nonneg_atomic_J2_margin
    {t eps mult delta : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (hmult : 0 < mult)
    (hnonprime : 0 <= W.threeTapResonanceNonPrimeExternal eps)
    (hatom : delta <= W.threeTapAtomicJ2Polynomial eps)
    (herr :
      |W.threeTapNormalizedJ2Polynomial eps
        - W.threeTapAtomicJ2Polynomial eps| < delta) :
    ∃ d : ℝ, 0 < d ∧
      ∀ a : ℝ, 0 < a → a < d →
        W.threeTapAdaptiveTerminalProfile eps mult a < 0 := by
  have hJ : 0 < W.threeTapNormalizedJ2Polynomial eps :=
    W.threeTapNormalizedJ2Polynomial_pos_of_atomic_margin hatom herr
  exact
    W.exists_threeTapResonantTerminalProfile_neg_right_of_nonPrime_nonneg_J2_pos
      ht hphase hmult hnonprime hJ

/-- The normalized transformed J2 polynomial factors exactly as
eps * (A + eps*B). -/
theorem QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial_factor
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapNormalizedJ2Polynomial eps
      =
    eps *
      (W.threeTapNormalizedJ2LinearCoeff
        + eps * W.threeTapNormalizedJ2QuadraticCoeff) := by
  unfold QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial
  ring

/-- Exact quartic exceptional locus. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial_eq_zero_iff
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapNormalizedJ2Polynomial eps = 0
      ↔
    eps = 0
      ∨
    W.threeTapNormalizedJ2LinearCoeff
        + eps * W.threeTapNormalizedJ2QuadraticCoeff = 0 := by
  rw [W.threeTapNormalizedJ2Polynomial_factor, mul_eq_zero]

theorem QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial_eq_zero_iff_nonzeroStrength
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (heps : eps ≠ 0) :
    W.threeTapNormalizedJ2Polynomial eps = 0
      ↔
    W.threeTapNormalizedJ2LinearCoeff
        + eps * W.threeTapNormalizedJ2QuadraticCoeff = 0 := by
  rw [W.threeTapNormalizedJ2Polynomial_eq_zero_iff]
  simp [heps]

/-- If the quadratic coefficient is nonzero, there is exactly one nonzero
candidate strength for the exceptional quartic branch. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial_eq_zero_iff_uniqueStrength
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (heps : eps ≠ 0)
    (hB : W.threeTapNormalizedJ2QuadraticCoeff ≠ 0) :
    W.threeTapNormalizedJ2Polynomial eps = 0
      ↔
    eps
      =
    - W.threeTapNormalizedJ2LinearCoeff
      / W.threeTapNormalizedJ2QuadraticCoeff := by
  rw [W.threeTapNormalizedJ2Polynomial_eq_zero_iff_nonzeroStrength heps]
  constructor
  · intro h
    apply (eq_div_iff hB).2
    linarith
  · intro h
    have hm :
        eps * W.threeTapNormalizedJ2QuadraticCoeff
          = - W.threeTapNormalizedJ2LinearCoeff :=
      (eq_div_iff hB).1 h
    linarith

/-- If B vanishes but A does not, no nonzero tap strength reaches the quartic
exceptional locus. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial_ne_zero_of_quadratic_zero_linear_ne
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (heps : eps ≠ 0)
    (hB : W.threeTapNormalizedJ2QuadraticCoeff = 0)
    (hA : W.threeTapNormalizedJ2LinearCoeff ≠ 0) :
    W.threeTapNormalizedJ2Polynomial eps ≠ 0 := by
  rw [W.threeTapNormalizedJ2Polynomial_factor, hB]
  simp [heps, hA]

end Synthesis

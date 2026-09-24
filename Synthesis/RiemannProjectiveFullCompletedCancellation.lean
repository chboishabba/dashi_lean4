import Synthesis.RiemannProjectiveCompletedSmoothResidual
import Zeta23Bridge.LiteralWeilPrimeEvenCone

/-!
# Full-carrier completed projective cancellation

On the exact projective test

  k_proj = sampleTest (projTaper g r) t 0,

the literal zeta explicit formula says that the full zero carrier equals pole
minus prime plus Gamma.  For a short taper the prime term vanishes exactly.
The named projective Gamma and pole welds then give

  Z_full^proj + D_Gamma^proj + D_pole^proj = 0.

Equivalently, the full actual projective zero carrier equals the completed
smooth density mu + Pi_X with the precise sign used by the high consumer.

This is stronger than a discrepancy estimate: no N-mu or tail bound appears.
The remaining nontrivial object is produced only after splitting the full zero
carrier into its q-only base and horizontal parts and/or deleting the
same-ordinate fibre.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilPrimeEvenCone

/-- Full actual zero pairing on the exact literal projective test, in the
same doubled-real normalization as the projective channel defects. -/
def projectiveFullZeroSignedPair
    (g : ℝ → ℝ) (t r : ℝ) : ℝ :=
  2 * reim
    (∑' rho : Zeros,
      zeroTerm (literalProjectiveSampleTest g t r) rho)

/-- Projectivization preserves short support because the projective bracket can
only remove support. -/
theorem projTaper_short_of_short
    {g : ℝ → ℝ} {r : ℝ}
    (hshort : ∀ u, g u ≠ 0 -> |u| < Real.log 2) :
    ∀ u, projTaper g r u ≠ 0 -> |u| < Real.log 2 := by
  intro u hu
  apply hshort u
  intro hg
  apply hu
  simp [Zeta23Bridge.LiteralWeilProjectiveTaper.projTaper, hg]

/-- The literal prime term is exactly absent on the projective test whenever the
underlying taper is short. -/
theorem literalProjectiveSampleTest_primeTerm_zero
    {g : ℝ → ℝ}
    (hshort : ∀ u, g u ≠ 0 -> |u| < Real.log 2)
    (t r : ℝ) :
    primeTerm (literalProjectiveSampleTest g t r) = 0 := by
  unfold literalProjectiveSampleTest
  exact primeTerm_sampleTest_eq_zero_of_short_taper
    (projTaper_short_of_short hshort) t 0

/-- Exact full-carrier explicit-formula cancellation at the projective
consumer. -/
theorem projectiveFullZeroSignedPair_add_gamma_add_pole_eq_zero
    {g : ℝ → ℝ} {L : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hshort : ∀ u, g u ≠ 0 -> |u| < Real.log 2)
    (hsupp : ∀ u, g u ≠ 0 -> |u| ≤ L)
    (hL : 0 < L)
    (t r : ℝ) :
    projectiveFullZeroSignedPair g t r
      + gammaProjectiveDefect g t r
      + poleProjectiveDefect g t r
      = 0 := by
  let k := literalProjectiveSampleTest g t r
  have hk : ContDiff ℝ 2 k :=
    literalProjectiveSampleTest_contDiff hgs t r
  have hkc : HasCompactSupport k :=
    literalProjectiveSampleTest_hasCompactSupport hgc t r
  have hprime : primeTerm k = 0 := by
    dsimp [k]
    exact literalProjectiveSampleTest_primeTerm_zero hshort t r
  have hEF := literalWeilExplicitFormula hk hkc
  rw [hprime, sub_zero] at hEF
  have hre := congrArg reim hEF
  rw [reim_add] at hre

  rw [gammaProjectiveDefect_eq_two_projectiveRvMMuSignedPair
      hgs heven hsupp hL.le t r,
    poleProjectiveDefect_eq_two_projectiveRvMPiXSignedPair
      hgs hgc heven hsupp hL t r]
  rw [projectiveRvMMuSignedPair_eq_literalGammaSignedPair]
  rw [projectiveRvMPiXSignedPair_eq_literalPoleSignedPair
      hgs hgc hsupp hL t r]
  unfold projectiveFullZeroSignedPair
  dsimp [k] at hre
  linarith

/-- The full actual projective zero carrier is exactly the negative of the
completed signed smooth pairing. -/
theorem projectiveFullZeroSignedPair_eq_neg_completedSmooth
    {g : ℝ → ℝ} {L : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hshort : ∀ u, g u ≠ 0 -> |u| < Real.log 2)
    (hsupp : ∀ u, g u ≠ 0 -> |u| ≤ L)
    (hL : 0 < L)
    (t r : ℝ) :
    projectiveFullZeroSignedPair g t r
      =
    - 2 * projectiveRvMCompletedSmoothSignedPair g t r L := by
  have h :=
    projectiveFullZeroSignedPair_add_gamma_add_pole_eq_zero
      hgs hgc heven hshort hsupp hL t r
  have hsmooth :=
    gamma_add_pole_projectiveDefect_eq_completedSmoothPair
      hgs hgc heven hsupp hL t r
  linarith

/-- Canonical specialization: the completed full-carrier discrepancy vanishes
exactly before any absolute value or RvM asymptotic decomposition. -/
theorem canonical_projectiveFullZeroSignedPair_eq_neg_completedSmooth
    {t : ℝ} (ht : 18 ≤ t) :
    projectiveFullZeroSignedPair
        (quantitativeCanonicalTaper t)
        t (quantitativeSampleRadius t)
      =
    - 2 * projectiveRvMCompletedSmoothSignedPair
      (quantitativeCanonicalTaper t)
      t (quantitativeSampleRadius t)
      (canonicalProjectiveCompletedRadius t) := by
  exact projectiveFullZeroSignedPair_eq_neg_completedSmooth
    (quantitativeCanonicalTaper_contDiff ht)
    (quantitativeCanonicalTaper_compact ht)
    quantitativeCanonicalTaper_even
    (quantitativeCanonicalTaper_short_high ht)
    (quantitativeCanonicalTaper_support_completedRadius ht)
    (canonicalProjectiveCompletedRadius_pos ht)
    t (quantitativeSampleRadius t)

end Synthesis

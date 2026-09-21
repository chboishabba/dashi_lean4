import Synthesis.RiemannProjectiveRvMMuGammaSameObject
import Zeta23Bridge.LiteralWeilPoleProjectiveCancellation
import Zeta23.ExplicitFormula.Bridge

/-!
# Projective same-object weld: Pi_X = literal pole on the actual consumer

Zeta23's explicit-formula bridge does for the pole term exactly what the
RvM/Gamma weld does for the Gamma term. For every compactly supported C2 test
k whose support lies in [-L,L],

  poleTerm k = integral paperFT(k)(tau) * PiX(exp L,tau) d tau.

Specialize this to the same projective test consumed by the high cut,

  k_proj = sampleTest (projTaper g r) t 0.

The Fourier-L1 hypothesis of pole_term is discharged by Zeta23's theorem
integrable_fourier_of_contDiff_two; no additional analytic assumption is
introduced.

At the named projective cone normalization one obtains the exact identity

  poleProjectiveDefect g t r
    = 2 * projectiveRvMPiXSignedPair g t r L.

The factor 2 is the same even-cone normalization that appears in the
Gamma/mu weld. Thus the natural completed smooth density at the literal
projective consumer is mu + PiX(exp L), not mu with a separately budgeted
pole channel.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real FourierTransform

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilPoleProjectiveCancellation

def projectiveRvMPiXPair
    (g : ℝ → ℝ) (t r L : ℝ) : ℂ :=
  ∫ tau : ℝ,
    paperFT (literalProjectiveSampleTest g t r) tau
      * (PiX (Real.exp L) tau : ℂ)

def projectiveRvMPiXSignedPair
    (g : ℝ → ℝ) (t r L : ℝ) : ℝ :=
  - reim (projectiveRvMPiXPair g t r L)

theorem literalProjectiveSampleTest_contDiff
    {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (t r : ℝ) :
    ContDiff ℝ 2 (literalProjectiveSampleTest g t r) := by
  unfold literalProjectiveSampleTest
  exact sampleTest_contDiff (projTaper_contDiff hgs r) t 0

theorem literalProjectiveSampleTest_hasCompactSupport
    {g : ℝ → ℝ} (hgc : HasCompactSupport g)
    (t r : ℝ) :
    HasCompactSupport (literalProjectiveSampleTest g t r) := by
  unfold literalProjectiveSampleTest
  exact sampleTest_hasCompactSupport
    (projTaper_hasCompactSupport hgc r) t 0

theorem literalProjectiveSampleTest_tsupport
    {g : ℝ → ℝ} {L : ℝ}
    (hsupp : ∀ u, g u ≠ 0 -> |u| ≤ L)
    (t r : ℝ) :
    tsupport (literalProjectiveSampleTest g t r)
      ⊆ Set.Icc (-L) L := by
  apply closure_minimal
  · intro u hu
    have hk : literalProjectiveSampleTest g t r u ≠ 0 := hu
    have hp : projTaper g r u ≠ 0 := by
      intro hp0
      apply hk
      simp [literalProjectiveSampleTest, sampleTest, hp0]
    have hg : g u ≠ 0 := by
      intro hg0
      apply hp
      simp [projTaper, hg0]
    have huabs := hsupp u hg
    constructor
    · have hneg := neg_abs_le u
      linarith
    · exact (le_abs_self u).trans huabs
  · exact isClosed_Icc

theorem projectiveRvMPiXPair_eq_literalPoleTerm
    {g : ℝ → ℝ} {L : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (hsupp : ∀ u, g u ≠ 0 -> |u| ≤ L)
    (hL : 0 < L)
    (t r : ℝ) :
    projectiveRvMPiXPair g t r L
      =
    poleTerm (literalProjectiveSampleTest g t r) := by
  let k := literalProjectiveSampleTest g t r
  have hk : ContDiff ℝ 2 k :=
    literalProjectiveSampleTest_contDiff hgs t r
  have hkc : HasCompactSupport k :=
    literalProjectiveSampleTest_hasCompactSupport hgc t r
  have hks : tsupport k ⊆ Set.Icc (-L) L :=
    literalProjectiveSampleTest_tsupport hsupp t r
  have hFk : Integrable (FourierTransform.fourier k) :=
    Zeta23.EF.integrable_fourier_of_contDiff_two hk hkc
  unfold projectiveRvMPiXPair
  exact (Zeta23.EF.pole_term hL hk.continuous hks hFk).symm

theorem projectiveRvMPiXSignedPair_eq_literalPoleSignedPair
    {g : ℝ → ℝ} {L : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (hsupp : ∀ u, g u ≠ 0 -> |u| ≤ L)
    (hL : 0 < L)
    (t r : ℝ) :
    projectiveRvMPiXSignedPair g t r L
      =
    - reim (poleTerm (literalProjectiveSampleTest g t r)) := by
  unfold projectiveRvMPiXSignedPair
  rw [projectiveRvMPiXPair_eq_literalPoleTerm
    hgs hgc hsupp hL t r]

/--
Named projective pole defect = twice the signed theorem-bearing Pi_X pairing.
-/
theorem poleProjectiveDefect_eq_two_projectiveRvMPiXSignedPair
    {g : ℝ → ℝ} {L : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hsupp : ∀ u, g u ≠ 0 -> |u| ≤ L)
    (hL : 0 < L)
    (t r : ℝ) :
    poleProjectiveDefect g t r
      =
    2 * projectiveRvMPiXSignedPair g t r L := by
  have hproj :=
    poleProjectiveDefect_eq_projTaper
      hgs.continuous hgc heven t r
  rw [hproj]
  rw [projectiveRvMPiXSignedPair_eq_literalPoleSignedPair
    hgs hgc hsupp hL t r]
  have hpole :=
    poleTerm_sampleTest
      (projTaper_continuous hgs.continuous r)
      (projTaper_hasCompactSupport hgc r)
      (projTaper_even heven r)
      t 0
  unfold literalProjectiveSampleTest
  rw [hpole]
  simp [reim]
  ring

/--
The Gamma and pole channels are one completed-density pairing before estimates.
-/
theorem gamma_add_pole_projectiveDefect_eq_completedSmoothPair
    {g : ℝ → ℝ} {L : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hsupp : ∀ u, g u ≠ 0 -> |u| ≤ L)
    (hL : 0 < L)
    (t r : ℝ) :
    gammaProjectiveDefect g t r
      + poleProjectiveDefect g t r
      =
    2 * (projectiveRvMMuSignedPair g t r
      + projectiveRvMPiXSignedPair g t r L) := by
  rw [gammaProjectiveDefect_eq_two_projectiveRvMMuSignedPair
      hgs heven hsupp hL.le t r,
    poleProjectiveDefect_eq_two_projectiveRvMPiXSignedPair
      hgs hgc heven hsupp hL t r]
  ring

end Synthesis

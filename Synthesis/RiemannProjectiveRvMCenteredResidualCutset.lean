import Synthesis.RiemannProjectiveRvMMuNamedGammaDefect
import Synthesis.RiemannReflectionPairSignedResidualCutset
import Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition

/-!
# Projective zero-minus-mu centered residual

At the actual reflection-pair projective consumer the literal Gamma channel is
not an independent analytic budget.  The exact same-object identity is

  gammaProjectiveDefect g t r
    = 2 * projectiveRvMMuSignedPair g t r.

Therefore the cluster balance should be centered BEFORE estimates:

  clusterHeightDefect
    = projectiveZeroMuResidual + poleProjectiveDefect,

where

  projectiveZeroMuResidual
    := offOrdProjectiveDefect + 2 * projectiveRvMMuSignedPair.

The factor 2 is the even-cone/reflection-pair normalization.  This file keeps
that normalization explicit so later N-mu discrepancy estimates cannot silently
mix single-sample and paired-orbit conventions.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone

def projectiveZeroMuResidual
    (g : ℝ → ℝ) (t r : ℝ) : ℝ :=
  offOrdProjectiveDefect g t r
    + 2 * projectiveRvMMuSignedPair g t r

theorem offOrd_add_gamma_eq_projectiveZeroMuResidual
    {g : ℝ → ℝ} {Λ : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (heven : ∀ u, g (-u) = g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ)
    (hΛ : 0 ≤ Λ)
    (t r : ℝ) :
    offOrdProjectiveDefect g t r
        + gammaProjectiveDefect g t r
      =
    projectiveZeroMuResidual g t r := by
  rw [gammaProjectiveDefect_eq_two_projectiveRvMMuSignedPair
    hgs heven hsupp hΛ t r]
  rfl

/--
Exact pre-estimation projective balance:
all smooth RvM/Gamma material has been absorbed into one centered zero-minus-mu
residual; only the pole remains as a separate literal channel.
-/
theorem clusterHeightDefect_eq_projectiveZeroMuResidual_add_pole
    {g : ℝ → ℝ} {Λ : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hshort : ∀ u, g u ≠ 0 → |u| < Real.log 2)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ)
    (hΛ : 0 ≤ Λ)
    (t r : ℝ) :
    clusterHeightDefect g t r
      =
    projectiveZeroMuResidual g t r
      + poleProjectiveDefect g t r := by
  rw [clusterHeightDefect_eq_threeProjectiveChannels
    hgs hgc heven hshort t r]
  rw [offOrd_add_gamma_eq_projectiveZeroMuResidual
    hgs heven hsupp hΛ t r]
  ring

/--
Signed contradiction compiler in the centered accounting.
-/
theorem false_of_projectiveZeroMuResidual_add_pole_lt_two_target
    {g : ℝ → ℝ} {t r Λ : ℝ} {rho : Zeros}
    (hd : GateData g t r Λ)
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ)
    (hstrict :
      projectiveZeroMuResidual g t r
        + poleProjectiveDefect g t r
        < 2 * zeroHeightDefect g r rho) :
    False := by
  have hcluster :
      clusterHeightDefect g t r
        =
      projectiveZeroMuResidual g t r
        + poleProjectiveDefect g t r := by
    exact clusterHeightDefect_eq_projectiveZeroMuResidual_add_pole
      hd.smooth hd.compactSupport hd.isEven hd.short
      hsupp hd.lambdaNonneg t r
  have hlo :
      2 * zeroHeightDefect g r rho
        <= clusterHeightDefect g t r :=
    gateData_two_targetDefect_le_cluster hd him hoff
  rw [hcluster] at hlo
  linarith

end Synthesis

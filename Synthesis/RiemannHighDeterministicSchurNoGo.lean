import Synthesis.RiemannHighSchurMinCut

/-!
# Deterministic Schur strict-comparison firewall

The deterministic pole/Gamma Schur quotient is an exact identity:

  elim2 pole gamma cluster = elim2 pole gamma offOrd.

Consequently the previous provisional min-cut

  ||elim2 ... offOrd||^2 < margin <= ||elim2 ... cluster||^2

is inconsistent.  This is not an analytic frontier and must not be advertised as
one.  The useful Schur move is instead to eliminate selected *zero-response*
nuisance directions while retaining the target response and the signed residual.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23Bridge.MultiTaperSchurCore
open Zeta23Bridge.LiteralWeilDeterministicProjectiveSchur

theorem deterministicSchur_projected_energy_eq
    {t : ℝ} (S : HighSchurSubstrate t) :
    normSqP
        (elim2 (poleVec3 S.g t S.r) (gammaVec3 S.g t S.r)
          (clusterVec3 S.g t S.r))
      =
    normSqP
        (elim2 (poleVec3 S.g t S.r) (gammaVec3 S.g t S.r)
          (offOrdVec3 S.g t S.r)) := by
  exact congrArg normSqP
    (elim2_cluster_eq_offOrd S.g t S.r
      S.smooth S.compact S.even S.short
      S.poleIndependent S.gammaIndependent)

theorem no_highSchurFarTail
    {t : ℝ} (S : HighSchurSubstrate t)
    (G : HighSchurGeometry S) :
    ¬ HighSchurFarTail S G := by
  intro F
  have heq := deterministicSchur_projected_energy_eq S
  have hcluster := G.margin_le_projectedCluster
  have hoff := F.projectedOffOrd_below_margin
  rw [heq] at hcluster
  linarith

theorem no_highSchurPayments
    {t : ℝ} (S : HighSchurSubstrate t) :
    ¬ (∃ G : HighSchurGeometry S, HighSchurFarTail S G) := by
  rintro ⟨G, F⟩
  exact no_highSchurFarTail S G F

end Synthesis

/-
# Exact Schur elimination of the deterministic projective nuisances

Backward from a uniform RH contradiction, separate O(r^2) bounds for the Gamma
and pole channels are not enough when the target horizontal displacement can be
arbitrarily small.  This module therefore uses the existing multi-taper Schur
operator in the direction for which it has the highest leverage: eliminate the
*deterministic* projective Gamma and pole response vectors exactly.

For three short positive tapers `g j`, the literal two-radius identity holds in
each coordinate:

  D_cluster(j) = D_off(j) + D_Gamma(j) + D_pole(j).

Vectorizing over `Fin 3` and applying `elim2` with nuisance vectors
`D_pole` and `D_Gamma` gives, under their two ordinary independence side
conditions,

  elim2 D_pole D_Gamma D_cluster = elim2 D_pole D_Gamma D_off.

Thus once a three-taper family is constructed for which the projected cluster
survives with a strict margin, *the only remaining payment is the signed
reflection-symmetrized zero carrier*.  Prime is already zero coordinatewise in
the high-ordinate short-support lane.

This file closes the exact compiler, not the analytic construction of such a
three-taper family.
-/
import Zeta23Bridge.MultiTaperSchurCore
import Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition

noncomputable section

open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilDeterministicProjectiveSchur

open Zeta23Bridge.MultiTaperSchurCore
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile

variable (g : Fin 3 → ℝ → ℝ) (t r : ℝ)

def clusterVec3 : Fin 3 → ℝ := fun j => clusterHeightDefect (g j) t r
def offOrdVec3 : Fin 3 → ℝ := fun j => offOrdProjectiveDefect (g j) t r
def gammaVec3 : Fin 3 → ℝ := fun j => gammaProjectiveDefect (g j) t r
def poleVec3 : Fin 3 → ℝ := fun j => poleProjectiveDefect (g j) t r

/-- Coordinatewise short support promotes the literal scalar projective identity
to one exact vector identity. -/
theorem projectiveBalanceVec3
    (hgs : ∀ j, ContDiff ℝ 2 (g j))
    (hgc : ∀ j, HasCompactSupport (g j))
    (heven : ∀ j u, g j (-u) = g j u)
    (hshort : ∀ j u, g j u ≠ 0 → |u| < Real.log 2) :
    clusterVec3 g t r = offOrdVec3 g t r + gammaVec3 g t r + poleVec3 g t r := by
  funext j
  exact clusterHeightDefect_eq_threeProjectiveChannels
    (hgs j) (hgc j) (heven j) (hshort j) t r

/-- Exact deterministic-nuisance removal.  No Gamma or pole budget survives the
Schur step. -/
theorem elim2_cluster_eq_offOrd
    (hgs : ∀ j, ContDiff ℝ 2 (g j))
    (hgc : ∀ j, HasCompactSupport (g j))
    (heven : ∀ j u, g j (-u) = g j u)
    (hshort : ∀ j u, g j u ≠ 0 → |u| < Real.log 2)
    (hpole : poleVec3 g t r ≠ 0)
    (hgamma : perp2 (poleVec3 g t r) (gammaVec3 g t r) ≠ 0) :
    elim2 (poleVec3 g t r) (gammaVec3 g t r) (clusterVec3 g t r)
      = elim2 (poleVec3 g t r) (gammaVec3 g t r) (offOrdVec3 g t r) := by
  rw [projectiveBalanceVec3 g t r hgs hgc heven hshort]
  have hreorder :
      offOrdVec3 g t r + gammaVec3 g t r + poleVec3 g t r
        = poleVec3 g t r + gammaVec3 g t r + offOrdVec3 g t r := by
    apply funext
    intro j
    simp only [Pi.add_apply]
    ring
  rw [hreorder]
  exact elim2_add_nuisance hpole hgamma (offOrdVec3 g t r)

/-- A literal margin compiler after deterministic nuisance elimination. -/
theorem false_of_signedOffOrd_below_survivingCluster
    (hgs : ∀ j, ContDiff ℝ 2 (g j))
    (hgc : ∀ j, HasCompactSupport (g j))
    (heven : ∀ j u, g j (-u) = g j u)
    (hshort : ∀ j u, g j u ≠ 0 → |u| < Real.log 2)
    (hpole : poleVec3 g t r ≠ 0)
    (hgamma : perp2 (poleVec3 g t r) (gammaVec3 g t r) ≠ 0)
    (margin : ℝ)
    (hcluster : margin ≤ normSqP
      (elim2 (poleVec3 g t r) (gammaVec3 g t r) (clusterVec3 g t r)))
    (hoff : normSqP
      (elim2 (poleVec3 g t r) (gammaVec3 g t r) (offOrdVec3 g t r)) < margin) : False := by
  have heq := congrArg normSqP (elim2_cluster_eq_offOrd g t r hgs hgc heven hshort hpole hgamma)
  linarith

end LiteralWeilDeterministicProjectiveSchur
end Zeta23Bridge

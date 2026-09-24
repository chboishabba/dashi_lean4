import Synthesis.RiemannRvMMuGammaEvenConeWeld
import Zeta23Bridge.LiteralWeilSameOrdinateEvenCone

/-!
# Exact RvM centering of the zero channel

The previous high-side bookkeeping treated

  smooth RvM main term
  and
  literal Gamma term

as separate quantities.  They are the same analytic measure with opposite
placement in the explicit-formula balance.

For any actual four-sample zero vector Z and test family kFam define

  centeredResidualVec Z kFam := Z + rvMMuVec kFam.

Since rvMMuVec = gammaVec exactly, this is definitionally the literal
zero-plus-Gamma channel:

  Z + gammaVec = centeredResidualVec Z kFam.

Applying the even-cone functional preserves the identity by linearity.  Thus
the high analytic consumer should estimate a SINGLE centered zero-count
discrepancy against mu, not first estimate a smooth RvM main term and then
compare the same smooth measure again against an independent Gamma margin.
-/

noncomputable section

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone

def rvMCenteredResidualVec
    (actualZeroVec : Fin 4 -> ℝ)
    (kFam : Fin 4 -> ℝ -> ℂ) :
    Fin 4 -> ℝ :=
  actualZeroVec + rvMMuVec kFam

theorem actualZero_add_gamma_eq_rvMCenteredResidual
    (actualZeroVec : Fin 4 -> ℝ)
    (kFam : Fin 4 -> ℝ -> ℂ) :
    actualZeroVec + gammaVec kFam
      =
    rvMCenteredResidualVec actualZeroVec kFam := by
  unfold rvMCenteredResidualVec
  rw [rvMMuVec_eq_gammaVec]

theorem evenCone_actualZero_add_gamma_eq_rvMCenteredResidual
    (actualZeroVec : Fin 4 -> ℝ)
    (kFam : Fin 4 -> ℝ -> ℂ) :
    evenConeFunctional (actualZeroVec + gammaVec kFam)
      =
    evenConeFunctional (rvMCenteredResidualVec actualZeroVec kFam) := by
  rw [actualZero_add_gamma_eq_rvMCenteredResidual]

theorem evenCone_rvMCenteredResidual_expand
    (actualZeroVec : Fin 4 -> ℝ)
    (kFam : Fin 4 -> ℝ -> ℂ) :
    evenConeFunctional (rvMCenteredResidualVec actualZeroVec kFam)
      =
    evenConeFunctional actualZeroVec
      + evenConeFunctional (rvMMuVec kFam) := by
  unfold rvMCenteredResidualVec
  exact LinearMap.map_add evenConeFunctional actualZeroVec (rvMMuVec kFam)

/--
Same statement with the literal Gamma vector exposed on the right, useful for
rewriting existing high-side consumers without changing their vector surface.
-/
theorem evenCone_rvMCenteredResidual_eq_actual_add_gamma
    (actualZeroVec : Fin 4 -> ℝ)
    (kFam : Fin 4 -> ℝ -> ℂ) :
    evenConeFunctional (rvMCenteredResidualVec actualZeroVec kFam)
      =
    evenConeFunctional actualZeroVec
      + evenConeFunctional (gammaVec kFam) := by
  rw [evenCone_rvMCenteredResidual_expand, rvMMuVec_eq_gammaVec]

end Synthesis

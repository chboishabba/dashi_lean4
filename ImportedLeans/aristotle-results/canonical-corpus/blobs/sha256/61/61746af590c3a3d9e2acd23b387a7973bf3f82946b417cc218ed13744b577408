/-
# The literal surviving margin after deterministic pole/Gamma elimination

`LiteralWeilDeterministicProjectiveSchur` proves that on three short even tapers
the literal two-radius identity

    D_cluster = D_off + D_Gamma + D_pole

is a coordinatewise vector identity in `Fin 3 → ℝ`, and that exact `elim2`
elimination of the two deterministic columns leaves

    elim2 D_pole D_Gamma D_cluster = elim2 D_pole D_Gamma D_off.

`ThreeTaperSchurMargin` computes the energy of that common vector exactly.  This
module puts the two together on the literal zeta channels.  Three consequences
are recorded, and the third is the sharp one.

1. `literal_surviving_cluster_energy`: the surviving cluster energy is the
   explicit determinant ratio `det3(D_pole, D_Gamma, D_cluster)² / wedgeSq`.

2. `literal_det3_cluster_eq_det3_offOrd`: that determinant is *equal* to the
   determinant taken on the off-ordinate column.  So the "surviving cluster
   margin" and the "projected far tail" are one and the same real number; the
   determinant algebra buys no further cancellation.

3. `literal_survivingMargin_le_offOrd_energy`: unconditionally,

       det3(D_pole, D_Gamma, D_cluster)² / wedgeSq(D_pole, D_Gamma)
         ≤ ‖D_off‖²,

   because the elimination is a contraction.  Hence any strict surviving margin
   `M` for an off-line cluster forces `M < ‖D_off‖²` — that is, a *lower* bound
   for the raw off-ordinate zero energy.  This is the precise shape of the
   remaining analytic obligation: the far-tail estimate has to beat a quantity
   which is itself the same projected number, so it cannot be obtained from the
   selected-column algebra alone.

No `sorry`, no `axiom`, no Boolean receipt, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilDeterministicProjectiveSchur
import Zeta23Bridge.ThreeTaperSchurMargin
import Zeta23Bridge.ProjectedTwoZeroCutsetCore

noncomputable section

open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilDeterministicSchurMarginInstance

open Zeta23Bridge.MultiTaperSchurCore
open Zeta23Bridge.ThreeTaperSchurCore
open Zeta23Bridge.ThreeTaperSchurMargin
open Zeta23Bridge.ProjectedTwoZeroCutsetCore
open Zeta23Bridge.LiteralWeilDeterministicProjectiveSchur

variable (g : Fin 3 → ℝ → ℝ) (t r : ℝ)

/-- The literal projective balance, written in the nuisance-first order used by
the elimination lemmas. -/
theorem literal_balance_nuisance_order
    (hgs : ∀ j, ContDiff ℝ 2 (g j))
    (hgc : ∀ j, HasCompactSupport (g j))
    (heven : ∀ j u, g j (-u) = g j u)
    (hshort : ∀ j u, g j u ≠ 0 → |u| < Real.log 2) :
    clusterVec3 g t r
      = offOrdVec3 g t r + poleVec3 g t r + gammaVec3 g t r := by
  have h := projectiveBalanceVec3 g t r hgs hgc heven hshort
  funext j
  have hj := congrFun h j
  simp only [Pi.add_apply] at hj ⊢
  linarith

/-- **The literal surviving energy is an explicit determinant ratio.** -/
theorem literal_surviving_cluster_energy
    (hpole : poleVec3 g t r ≠ 0)
    (hgamma : perp2 (poleVec3 g t r) (gammaVec3 g t r) ≠ 0) :
    normSqP (elim2 (poleVec3 g t r) (gammaVec3 g t r) (clusterVec3 g t r))
      = det3 (poleVec3 g t r) (gammaVec3 g t r) (clusterVec3 g t r) ^ 2
          / wedgeSq (poleVec3 g t r) (gammaVec3 g t r) :=
  normSqP_elim2_eq_det3_sq_div _ _ _ hpole hgamma

/-- **The cluster determinant is the off-ordinate determinant.** -/
theorem literal_det3_cluster_eq_det3_offOrd
    (hgs : ∀ j, ContDiff ℝ 2 (g j))
    (hgc : ∀ j, HasCompactSupport (g j))
    (heven : ∀ j u, g j (-u) = g j u)
    (hshort : ∀ j u, g j u ≠ 0 → |u| < Real.log 2) :
    det3 (poleVec3 g t r) (gammaVec3 g t r) (clusterVec3 g t r)
      = det3 (poleVec3 g t r) (gammaVec3 g t r) (offOrdVec3 g t r) :=
  det3_eq_of_balance (literal_balance_nuisance_order g t r hgs hgc heven hshort)

/-- **The sharp shape of the remaining obligation.**  The surviving margin never
exceeds the raw off-ordinate zero energy. -/
theorem literal_survivingMargin_le_offOrd_energy
    (hgs : ∀ j, ContDiff ℝ 2 (g j))
    (hgc : ∀ j, HasCompactSupport (g j))
    (heven : ∀ j u, g j (-u) = g j u)
    (hshort : ∀ j u, g j u ≠ 0 → |u| < Real.log 2)
    (hpole : poleVec3 g t r ≠ 0)
    (hgamma : perp2 (poleVec3 g t r) (gammaVec3 g t r) ≠ 0) :
    det3 (poleVec3 g t r) (gammaVec3 g t r) (clusterVec3 g t r) ^ 2
        / wedgeSq (poleVec3 g t r) (gammaVec3 g t r)
      ≤ normSqP (offOrdVec3 g t r) := by
  have hsurv := literal_surviving_cluster_energy g t r hpole hgamma
  have heq : elim2 (poleVec3 g t r) (gammaVec3 g t r) (clusterVec3 g t r)
      = elim2 (poleVec3 g t r) (gammaVec3 g t r) (offOrdVec3 g t r) :=
    elim2_cluster_eq_offOrd g t r hgs hgc heven hshort hpole hgamma
  have hcontr : normSqP (elim2 (poleVec3 g t r) (gammaVec3 g t r) (offOrdVec3 g t r))
      ≤ normSqP (offOrdVec3 g t r) := normSqP_elim2_le hpole hgamma
  rw [heq] at hsurv
  linarith

/-- **Endpoint compiler in literal form.**  A strict surviving margin for the
off-line cluster together with an off-ordinate energy below that margin is
impossible.  The two hypotheses are the two genuinely analytic obligations: the
first must come from the off-line target's own two-radius height defect, the
second from the signed reflection-symmetrized zero-tail estimate. -/
theorem literal_false_of_offOrd_energy_below_margin
    (hgs : ∀ j, ContDiff ℝ 2 (g j))
    (hgc : ∀ j, HasCompactSupport (g j))
    (heven : ∀ j u, g j (-u) = g j u)
    (hshort : ∀ j u, g j u ≠ 0 → |u| < Real.log 2)
    (hpole : poleVec3 g t r ≠ 0)
    (hgamma : perp2 (poleVec3 g t r) (gammaVec3 g t r) ≠ 0)
    (margin : ℝ)
    (hmargin : margin ≤ det3 (poleVec3 g t r) (gammaVec3 g t r) (clusterVec3 g t r) ^ 2
        / wedgeSq (poleVec3 g t r) (gammaVec3 g t r))
    (hfar : normSqP (offOrdVec3 g t r) < margin) : False := by
  have h := literal_survivingMargin_le_offOrd_energy g t r hgs hgc heven hshort hpole hgamma
  linarith

end LiteralWeilDeterministicSchurMarginInstance
end Zeta23Bridge

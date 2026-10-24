import QuantumChannels.MMPDiracFockParityChannel
import QuantumChannels.MMPDiracChargeSuperselection

/-!
BIDI regression for physical-channel source selection.
The full-loss counterexample is deliberate: accepting even output parity
does not imply successful transfer of a four-Majorana code state.
-/ 

namespace MMPQuantumChannel

theorem regression_completeLoss_is_parity_false_positive :
    singleParticleSuccess completeLoss = 0 ∧
    evenParityAcceptanceProbability completeLoss = 1 ∧
    noLossHeraldProbability completeLoss = 1 / 2 := by
  exact ⟨completeLoss_single_success_zero,
    completeLoss_even_parity_always_accepted,
    completeLoss_noLoss_only_vacuum⟩

theorem regression_doubleLoss_is_exact_excess
    (a : IndependentFermionLoss) :
    evenParityAcceptanceProbability a -
      noLossHeraldProbability a =
        (a.s1 * a.s2) ^ 2 / 2 := by
  rw [evenParity_eq_noLoss_add_doubleLoss]
  ring

end MMPQuantumChannel


theorem regression_chargeHalfTurn_forbids_even_coherence
    (rho : CondensedMatter.CMatrix2)
    (h : chargedEvenHalfTurnConjugate rho = rho) :
    rho.a12 = 0 :=
  chargedEvenHalfTurn_invariant_offDiagonal_zero rho h

theorem regression_oneParticleDualRail_remains_sameCharge
    (z : ℂ) :
    (-1 : ℂ) * z * (-1) = z :=
  equalChargeDualRail_coherence_preserved z

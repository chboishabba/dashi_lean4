import NSBControl.CombinedSpacetimePayment

namespace NSBControl
namespace CombinedPaymentToWeightedWork

theorem combined_and_initial_build_weighted
    (combined commutator initialMass weighted bound initialBound : ℝ)
    (hCombined : combined = 12 * commutator)
    (hCombinedPayment : combined ≤ 12 * bound)
    (hInitial : initialMass ≤ initialBound)
    (hWeighted : weighted ≤ commutator + initialMass) :
    weighted ≤ bound + initialBound := by
  have hComm : commutator ≤ bound :=
    CombinedSpacetimePayment.combined_payment_builds_commutator_payment
      combined commutator bound hCombined hCombinedPayment
  linarith

end CombinedPaymentToWeightedWork
end NSBControl

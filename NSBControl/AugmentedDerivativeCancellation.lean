import NSBControl.SharedWeightedCut

namespace NSBControl
namespace AugmentedDerivativeCancellation

theorem qdot_eq_commutator_sub_weighted
    (qdot comm weighted : ℝ)
    (hWeighted : weighted = comm - qdot) :
    qdot = comm - weighted := by
  linarith

theorem augmented_derivative_collected
    (adot xdot qdot prod twoNu diss comm weighted : ℝ)
    (hA : adot = xdot - 12 * qdot)
    (hX : xdot = prod - twoNu * diss)
    (hQ : qdot = comm - weighted) :
    adot = prod - twoNu * diss - 12 * comm + 12 * weighted := by
  linarith

theorem pointwise_w2_iff_production_commutator
    (adot prod twoNu diss comm weighted margin : ℝ)
    (hCollected :
      adot = prod - twoNu * diss - 12 * comm + 12 * weighted) :
    (adot + margin * diss ≤ 12 * weighted) ↔
      (prod ≤ (twoNu - margin) * diss + 12 * comm) := by
  constructor <;> intro h <;> linarith

theorem strict_surplus_form
    (prod twoNu diss comm margin : ℝ) :
    (prod ≤ (twoNu - margin) * diss + 12 * comm) ↔
      (prod - (twoNu - margin) * diss ≤ 12 * comm) := by
  constructor <;> intro h <;> linarith

/--
Abstract integrated form of R742. Once the physical packet integral is exactly
identified with critical growth and the combined integral with the direct
consumer, the two payment statements are the same inequality.
-/
theorem integrated_packet_combined_transport
    (packet growth combined : ℝ)
    (hPacketGrowth : packet = growth) :
    (packet ≤ combined) ↔ (growth ≤ combined) := by
  simpa [hPacketGrowth]

end AugmentedDerivativeCancellation
end NSBControl

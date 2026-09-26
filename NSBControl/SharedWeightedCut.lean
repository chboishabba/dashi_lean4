import NSBControl.DirectCombinedCut

namespace NSBControl
namespace SharedWeightedCut

/-- R734 scalar normal form:
    growth <= 12 * (weighted + endpointDelta)
iff growth - 12*endpointDelta <= 12*weighted. -/
theorem direct_iff_augmented_weighted
    (growth weighted endpointDelta : ℝ) :
    growth ≤ 12 * (weighted + endpointDelta) ↔
      growth - 12 * endpointDelta ≤ 12 * weighted := by
  constructor <;> intro h <;> linarith

/-- Shared weighted cut:
    augmented critical growth <= 12W and W+E_T <= B,
    with nonnegative initial mixed mass, imply the ordinary barrier. -/
theorem shared_weighted_builds_barrier
    (xT x0 diss margin weighted eT e0 bound : ℝ)
    (hAugmented :
      (xT - 12 * eT) - (x0 - 12 * e0) + margin * diss
        ≤ 12 * weighted)
    (hPaid : weighted + eT ≤ bound)
    (hInitialMass : 0 ≤ e0) :
    xT + margin * diss ≤ x0 + 12 * bound := by
  linarith

/-- The endpoint may remain inseparable from the signed weighted scalar.
No inference of weighted <= bound is needed. -/
theorem signed_weighted_plus_endpoint_stays_joint
    (weighted endpoint bound : ℝ)
    (h : weighted + endpoint ≤ bound) :
    weighted + endpoint ≤ bound := h

end SharedWeightedCut
end NSBControl

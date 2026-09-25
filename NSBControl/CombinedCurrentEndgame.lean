import NSBControl.CombinedPaymentToWeightedWork

namespace NSBControl
namespace CombinedCurrentEndgame

theorem quartic_mass_not_same_degree_as_quintic_signed_cross :
    (4 : Nat) ≠ 5 := by decide

theorem combined_to_remainder_builds_cancellation
    (combined remainder bound : ℝ)
    (hTransport : remainder ≤ combined)
    (hCombined : combined ≤ 12 * bound) :
    remainder ≤ 12 * bound := by
  linarith

theorem c1_c2_build_critical_barrier
    (remainder production dissipation initial terminal nu margin bound initialBound : ℝ)
    (hMargin : 0 < margin)
    (hRemainder : remainder ≤ 12 * bound)
    (hProduction :
      production ≤ (2 * nu - margin) * dissipation + remainder)
    (hEnergy :
      terminal + 2 * nu * dissipation ≤ initial + production)
    (hInitial : initial ≤ initialBound) :
    terminal + margin * dissipation ≤ initialBound + 12 * bound := by
  linarith

/--
The current combined lane has three proof-bearing analytic coordinates:
(1) combined/global commutator payment, (2) transport to the literal remainder,
and (3) strict-margin production.  Once supplied, the remaining barrier step is
pure ordered-ring algebra.
-/
theorem current_three_coordinate_endgame
    (combined remainder production dissipation initial terminal nu margin bound initialBound : ℝ)
    (hCombined : combined ≤ 12 * bound)
    (hTransport : remainder ≤ combined)
    (hMargin : 0 < margin)
    (hProduction :
      production ≤ (2 * nu - margin) * dissipation + remainder)
    (hEnergy :
      terminal + 2 * nu * dissipation ≤ initial + production)
    (hInitial : initial ≤ initialBound) :
    terminal + margin * dissipation ≤ initialBound + 12 * bound := by
  exact c1_c2_build_critical_barrier
    remainder production dissipation initial terminal nu margin bound initialBound
    hMargin
    (combined_to_remainder_builds_cancellation
      combined remainder bound hTransport hCombined)
    hProduction hEnergy hInitial

end CombinedCurrentEndgame
end NSBControl

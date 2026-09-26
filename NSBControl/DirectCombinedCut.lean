import NSBControl.CombinedCurrentEndgame

namespace NSBControl
namespace DirectCombinedCut

theorem r406_factorization_builds_direct
    (growth r406 combined : ℝ)
    (hGrowth : growth ≤ r406)
    (hTransport : r406 ≤ combined) :
    growth ≤ combined := by
  linarith

theorem direct_combined_builds_barrier
    (xT x0 diss margin combined bound : ℝ)
    (hDirect : xT - x0 + margin * diss ≤ combined)
    (hCombined : combined ≤ 12 * bound) :
    xT + margin * diss ≤ x0 + 12 * bound := by
  linarith

/--
The former three-coordinate factorization
  growth <= R406 <= combined <= 12 B
compresses to the two terminal analytic leaves
  growth <= combined
and
  combined <= 12 B.
-/
theorem two_leaf_pareto_endgame
    (xT x0 diss margin r406 combined bound : ℝ)
    (hGrowthByR406 : xT - x0 + margin * diss ≤ r406)
    (hR406ToCombined : r406 ≤ combined)
    (hCombined : combined ≤ 12 * bound) :
    xT + margin * diss ≤ x0 + 12 * bound := by
  exact direct_combined_builds_barrier
    xT x0 diss margin combined bound
    (r406_factorization_builds_direct
      (xT - x0 + margin * diss) r406 combined
      hGrowthByR406 hR406ToCombined)
    hCombined

theorem commutator_below_weighted_plus_terminal
    (weighted comm terminalMass initialMass : ℝ)
    (hBalance : weighted = comm - (terminalMass - initialMass))
    (hInitial : 0 ≤ initialMass) :
    comm ≤ weighted + terminalMass := by
  linarith

theorem weighted_terminal_builds_combined_payment
    (weighted comm terminalMass weightedBound terminalBound : ℝ)
    (hBalance : weighted = comm - (terminalMass - 0))
    (hWeighted : weighted ≤ weightedBound)
    (hTerminal : terminalMass ≤ terminalBound) :
    12 * comm ≤ 12 * (weightedBound + terminalBound) := by
  have hComm : comm ≤ weighted + terminalMass := by
    linarith
  linarith

end DirectCombinedCut
end NSBControl

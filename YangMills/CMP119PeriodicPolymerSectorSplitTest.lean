import Mathlib
import YangMills.CMP119PeriodicPolymerSectorSplit

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n]
    (source : CMP119PeriodicPolymerSectorSource n)
    (links : SU2TorusLinks (2 * n)) :
    source.action links =
      source.placementAction CMP119PolymerPlacement.positive links +
      source.placementAction CMP119PolymerPlacement.negative links +
      source.placementAction CMP119PolymerPlacement.crossing links +
      source.placementAction CMP119PolymerPlacement.empty links :=
  source.action_eq_sum_placements links

end RequestProject.YangMills

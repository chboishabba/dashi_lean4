import Mathlib
import YangMills.LiteralSU2OrientedLinkReflection

/-!
# Compatibility bridge for literal plaquette reflection transport

The canonical orientation-sensitive calculations are now owned by
\`LiteralSU2OrientedLinkReflection.lean\`.  This module supplies the shorter
consumer names used by the plaquette-index assembly and does not duplicate
the underlying reflected-link definitions.
-/

namespace RequestProject.YangMills

theorem su2_reflected_spatial_plaquette_cost
    {n : ℕ}
    (links : SU2TorusLinks (2 * n))
    (x : SU2TorusSite (2 * n))
    (μ ν : Fin 4)
    (hμ : μ ≠ su2TimeDirection)
    (hν : ν ≠ su2TimeDirection) :
    su2PositivePlaquetteCost
      (su2Plaquette (su2EvenTimeReflectLinks links) x μ ν) =
    su2PositivePlaquetteCost
      (su2Plaquette links (su2EvenTimeReflectSite x) μ ν) :=
  su2_even_time_reflect_spatial_plaquette_cost
    links x μ ν hμ hν

theorem su2_reflected_temporal_plaquette_cost
    {n : ℕ}
    (links : SU2TorusLinks (2 * n))
    (x : SU2TorusSite (2 * n))
    (ν : Fin 4)
    (hν : ν ≠ su2TimeDirection) :
    su2PositivePlaquetteCost
      (su2Plaquette
        (su2EvenTimeReflectLinks links)
        x su2TimeDirection ν) =
    su2PositivePlaquetteCost
      (su2Plaquette links
        (su2ShiftBackward
          (su2EvenTimeReflectSite x)
          su2TimeDirection)
        su2TimeDirection ν) :=
  su2_even_time_reflect_temporal_plaquette_cost
    links x ν hν

end RequestProject.YangMills

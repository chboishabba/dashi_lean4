import Mathlib
import YangMills.LiteralSU2ReflectedLinks

/-!
# Literal plaquette transport under even Euclidean-time reflection

This file proves the orientation-sensitive local transport that the global
finite Wilson OS2 theorem needs.

Spatial plaquettes are sent directly to the plaquette at the reflected site.
Temporal plaquettes are sent to a conjugate of the inverse plaquette at the
reflected backward-time base point. Since the SU(2) Wilson cost is invariant
under both conjugation and inversion, every plaquette cost is transported
exactly by the literal reflected-link involution.

The remaining global step is purely finite index assembly: transport the
positive noncrossing plaquette set bijectively onto the negative set.
-/

namespace RequestProject.YangMills

theorem su2_shift_backward_spatial_commute
    {L : ℕ}
    (x : SU2TorusSite L)
    (spatial : Fin 4)
    (hSpatial : spatial ≠ su2TimeDirection) :
    su2ShiftBackward
        (su2Shift x spatial) su2TimeDirection =
      su2Shift
        (su2ShiftBackward x su2TimeDirection) spatial := by
  classical
  funext i
  by_cases hiTime : i = su2TimeDirection
  · subst i
    simp [su2ShiftBackward, su2Shift,
      Function.update_noteq hSpatial]
  · by_cases hiSpatial : i = spatial
    · subst i
      simp [su2ShiftBackward, su2Shift,
        Function.update_same, Function.update_noteq hSpatial,
        Function.update_noteq hiTime]
    · simp [su2ShiftBackward, su2Shift,
        Function.update_noteq hiTime,
        Function.update_noteq hiSpatial]

theorem su2_reflected_spatial_plaquette
    {n : ℕ}
    (links : SU2TorusLinks (2 * n))
    (x : SU2TorusSite (2 * n))
    (μ ν : Fin 4)
    (hμ : μ ≠ su2TimeDirection)
    (hν : ν ≠ su2TimeDirection) :
    su2Plaquette (su2EvenTimeReflectLinks links) x μ ν =
      su2Plaquette links (su2EvenTimeReflectSite x) μ ν := by
  unfold su2Plaquette
  rw [su2_even_time_reflect_spatial_link _ _ _ hμ,
    su2_even_time_reflect_spatial_link _ _ _ hν,
    su2_even_time_reflect_spatial_link _ _ _ hμ,
    su2_even_time_reflect_spatial_link _ _ _ hν,
    su2_even_time_reflect_spatial_shift x μ hμ,
    su2_even_time_reflect_spatial_shift x ν hν]

theorem su2_reflected_temporal_plaquette
    {n : ℕ}
    (links : SU2TorusLinks (2 * n))
    (x : SU2TorusSite (2 * n))
    (ν : Fin 4)
    (hν : ν ≠ su2TimeDirection) :
    su2Plaquette
        (su2EvenTimeReflectLinks links)
        x su2TimeDirection ν =
      let y :=
        su2ShiftBackward
          (su2EvenTimeReflectSite x)
          su2TimeDirection
      (links y su2TimeDirection)⁻¹ *
        (su2Plaquette links y su2TimeDirection ν)⁻¹ *
        links y su2TimeDirection := by
  let y :=
    su2ShiftBackward
      (su2EvenTimeReflectSite x)
      su2TimeDirection
  have hReflectForward :
      su2EvenTimeReflectSite (su2Shift x su2TimeDirection) = y := by
    simpa [y] using su2_even_time_reflect_forward_time_shift x
  have hReflectSpatial :
      su2EvenTimeReflectSite (su2Shift x ν) =
        su2Shift (su2EvenTimeReflectSite x) ν :=
    su2_even_time_reflect_spatial_shift x ν hν
  have hBackwardSpatial :
      su2ShiftBackward
          (su2EvenTimeReflectSite (su2Shift x ν))
          su2TimeDirection =
        su2Shift y ν := by
    rw [hReflectSpatial, y,
      su2_shift_backward_spatial_commute _ ν hν]
  have hForwardY :
      su2Shift y su2TimeDirection =
        su2EvenTimeReflectSite x := by
    dsimp [y]
    exact su2_shift_forward_after_backward
      (su2EvenTimeReflectSite x) su2TimeDirection
  unfold su2Plaquette
  rw [su2_even_time_reflect_temporal_link,
    su2_even_time_reflect_spatial_link _ _ _ hν,
    su2_even_time_reflect_temporal_link,
    su2_even_time_reflect_spatial_link _ _ _ hν,
    hReflectForward, hBackwardSpatial]
  rw [hForwardY]
  group

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
      (su2Plaquette links (su2EvenTimeReflectSite x) μ ν) := by
  rw [su2_reflected_spatial_plaquette links x μ ν hμ hν]

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
        su2TimeDirection ν) := by
  rw [su2_reflected_temporal_plaquette links x ν hν]
  let y :=
    su2ShiftBackward
      (su2EvenTimeReflectSite x)
      su2TimeDirection
  calc
    su2PositivePlaquetteCost
      ((links y su2TimeDirection)⁻¹ *
        (su2Plaquette links y su2TimeDirection ν)⁻¹ *
        links y su2TimeDirection) =
      su2PositivePlaquetteCost
        ((su2Plaquette links y su2TimeDirection ν)⁻¹) := by
          exact su2_plaquette_cost_conjugation
            (links y su2TimeDirection)⁻¹
            ((su2Plaquette links y su2TimeDirection ν)⁻¹)
    _ = su2PositivePlaquetteCost
        (su2Plaquette links y su2TimeDirection ν) :=
      su2_plaquette_cost_inverse _

end RequestProject.YangMills

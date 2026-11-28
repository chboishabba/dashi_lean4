import Mathlib
import YangMills.LiteralSU2EvenTimeReflectionGeometry

/-!
# Orientation-sensitive link reflection on the even 4D SU(2) torus

This file descends the even-time site involution to the ACTUAL oriented link
field.  Spatial links retain orientation; temporal links reverse orientation
and are therefore read from the reflected backward edge with group inverse.

This is the missing geometric ingredient between the existing plaquette-cut
partition and a literal full-lattice Wilson reflection theorem.  The file proves
that the link reflection is an involution and records the exact spatial-link
transport.  The remaining local calculation is the temporal plaquette
orientation identity used to pair positive and negative noncrossing plaquettes.
-/

namespace RequestProject.YangMills

def su2EvenTimeReflectLinks {n : ℕ}
    (links : SU2TorusLinks (2 * n)) : SU2TorusLinks (2 * n) :=
  fun x direction =>
    if h : direction = su2TimeDirection then
      (links
        (su2ShiftBackward (su2EvenTimeReflectSite x) su2TimeDirection)
        su2TimeDirection)⁻¹
    else
      links (su2EvenTimeReflectSite x) direction

theorem su2_shift_backward_forward_cancel {L : ℕ}
    (x : SU2TorusSite L) (direction : Fin 4) :
    su2ShiftBackward (su2Shift x direction) direction = x := by
  classical
  funext i
  by_cases hi : i = direction
  · subst i
    simp [su2ShiftBackward, su2Shift]
  · simp [su2ShiftBackward, su2Shift,
      Function.update_noteq hi]

theorem su2_shift_forward_backward_cancel {L : ℕ}
    (x : SU2TorusSite L) (direction : Fin 4) :
    su2Shift (su2ShiftBackward x direction) direction = x := by
  classical
  funext i
  by_cases hi : i = direction
  · subst i
    simp [su2ShiftBackward, su2Shift]
  · simp [su2ShiftBackward, su2Shift,
      Function.update_noteq hi]

theorem su2_even_time_reflect_backward_time_shift
    {n : ℕ} (x : SU2TorusSite (2 * n)) :
    su2EvenTimeReflectSite
        (su2ShiftBackward x su2TimeDirection) =
      su2Shift (su2EvenTimeReflectSite x) su2TimeDirection := by
  classical
  funext i
  by_cases hi : i = su2TimeDirection
  · subst i
    simp [su2EvenTimeReflectSite, su2ShiftBackward, su2Shift]
    ring
  · simp [su2EvenTimeReflectSite, su2ShiftBackward, su2Shift,
      Function.update_noteq hi]

theorem su2_even_time_reflect_links_spatial
    {n : ℕ} (links : SU2TorusLinks (2 * n))
    (x : SU2TorusSite (2 * n)) (direction : Fin 4)
    (hSpatial : direction ≠ su2TimeDirection) :
    su2EvenTimeReflectLinks links x direction =
      links (su2EvenTimeReflectSite x) direction := by
  simp [su2EvenTimeReflectLinks, hSpatial]

theorem su2_even_time_reflect_links_temporal
    {n : ℕ} (links : SU2TorusLinks (2 * n))
    (x : SU2TorusSite (2 * n)) :
    su2EvenTimeReflectLinks links x su2TimeDirection =
      (links
        (su2ShiftBackward (su2EvenTimeReflectSite x) su2TimeDirection)
        su2TimeDirection)⁻¹ := by
  simp [su2EvenTimeReflectLinks]

theorem su2_even_time_reflect_links_involutive
    {n : ℕ} (links : SU2TorusLinks (2 * n)) :
    su2EvenTimeReflectLinks (su2EvenTimeReflectLinks links) = links := by
  classical
  funext x direction
  by_cases hTime : direction = su2TimeDirection
  · subst direction
    simp only [su2_even_time_reflect_links_temporal]
    rw [su2_even_time_reflect_backward_time_shift]
    rw [su2_even_time_reflect_site_involutive]
    rw [su2_shift_backward_forward_cancel]
    simp
  · rw [su2_even_time_reflect_links_spatial _ _ _ hTime]
    rw [su2_even_time_reflect_links_spatial _ _ _ hTime]
    rw [su2_even_time_reflect_site_involutive]

/--
Spatial plaquette transport is already literal: for two spatial directions the
reflected plaquette is the plaquette of the original links at the reflected
site.  This removes the entire spatial noncrossing sector from the remaining
orientation audit.
-/
theorem su2_even_time_reflect_spatial_plaquette
    {n : ℕ} (links : SU2TorusLinks (2 * n))
    (x : SU2TorusSite (2 * n)) (μ ν : Fin 4)
    (hμ : μ ≠ su2TimeDirection)
    (hν : ν ≠ su2TimeDirection) :
    su2Plaquette (su2EvenTimeReflectLinks links) x μ ν =
      su2Plaquette links (su2EvenTimeReflectSite x) μ ν := by
  dsimp [su2Plaquette]
  rw [su2_even_time_reflect_links_spatial _ _ _ hμ]
  rw [su2_even_time_reflect_links_spatial _ _ _ hν]
  rw [su2_even_time_reflect_spatial_shift x μ hμ]
  rw [su2_even_time_reflect_links_spatial _ _ _ hν]
  rw [su2_even_time_reflect_spatial_shift x ν hν]
  rw [su2_even_time_reflect_links_spatial _ _ _ hμ]
  rw [su2_even_time_reflect_links_spatial _ _ _ hν]

theorem su2_even_time_reflect_spatial_plaquette_cost
    {n : ℕ} (links : SU2TorusLinks (2 * n))
    (x : SU2TorusSite (2 * n)) (μ ν : Fin 4)
    (hμ : μ ≠ su2TimeDirection)
    (hν : ν ≠ su2TimeDirection) :
    su2PositivePlaquetteCost
        (su2Plaquette (su2EvenTimeReflectLinks links) x μ ν) =
      su2PositivePlaquetteCost
        (su2Plaquette links (su2EvenTimeReflectSite x) μ ν) := by
  rw [su2_even_time_reflect_spatial_plaquette links x μ ν hμ hν]

/--
A spatial forward shift commutes with the backward time shift.  This is the
remaining square-geometry identity needed in the reflected temporal plaquette.
-/
theorem su2_shift_backward_time_spatial_commute
    {L : ℕ} (x : SU2TorusSite L) (direction : Fin 4)
    (hSpatial : direction ≠ su2TimeDirection) :
    su2ShiftBackward (su2Shift x direction) su2TimeDirection =
      su2Shift (su2ShiftBackward x su2TimeDirection) direction := by
  classical
  funext i
  by_cases hiTime : i = su2TimeDirection
  · subst i
    simp [su2ShiftBackward, su2Shift,
      Function.update_noteq hSpatial]
  · by_cases hiDir : i = direction
    · subst i
      simp [su2ShiftBackward, su2Shift,
        Function.update_same, Function.update_noteq hSpatial,
        Function.update_noteq hiTime]
    · simp [su2ShiftBackward, su2Shift,
        Function.update_noteq hiTime, Function.update_noteq hiDir]

/--
For a temporal/spatial plaquette, time reflection reverses its orientation.
The reflected plaquette is conjugate to the inverse of the literal plaquette
based at the reflected-backward site.  This is stronger than equality of
Wilson costs and is the exact orientation-sensitive same-object statement.
-/
theorem su2_even_time_reflect_temporal_plaquette_conjugate_inverse
    {n : ℕ} (links : SU2TorusLinks (2 * n))
    (x : SU2TorusSite (2 * n)) (ν : Fin 4)
    (hν : ν ≠ su2TimeDirection) :
    let y :=
      su2ShiftBackward (su2EvenTimeReflectSite x) su2TimeDirection
    su2Plaquette (su2EvenTimeReflectLinks links)
        x su2TimeDirection ν =
      (links y su2TimeDirection)⁻¹ *
        (su2Plaquette links y su2TimeDirection ν)⁻¹ *
        links y su2TimeDirection := by
  dsimp
  rw [su2Plaquette]
  rw [su2_even_time_reflect_links_temporal]
  rw [su2_even_time_reflect_links_spatial _ _ _ hν]
  rw [su2_even_time_reflect_forward_time_shift]
  rw [su2_even_time_reflect_links_temporal]
  rw [su2_even_time_reflect_spatial_shift _ ν hν]
  rw [su2_even_time_reflect_links_spatial _ _ _ hν]
  rw [su2_shift_backward_time_spatial_commute _ ν hν]
  rw [su2_shift_forward_backward_cancel]
  dsimp [su2Plaquette]
  group

/--
The temporal noncrossing Wilson cost is therefore exactly reflection
invariant: conjugation and orientation reversal are invisible to the
trace-normalized positive plaquette cost.
-/
theorem su2_even_time_reflect_temporal_plaquette_cost
    {n : ℕ} (links : SU2TorusLinks (2 * n))
    (x : SU2TorusSite (2 * n)) (ν : Fin 4)
    (hν : ν ≠ su2TimeDirection) :
    let y :=
      su2ShiftBackward (su2EvenTimeReflectSite x) su2TimeDirection
    su2PositivePlaquetteCost
        (su2Plaquette (su2EvenTimeReflectLinks links)
          x su2TimeDirection ν) =
      su2PositivePlaquetteCost
        (su2Plaquette links y su2TimeDirection ν) := by
  dsimp
  rw [su2_even_time_reflect_temporal_plaquette_conjugate_inverse
    links x ν hν]
  rw [su2_plaquette_cost_conjugation]
  exact su2_plaquette_cost_inverse _


end RequestProject.YangMills

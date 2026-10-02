import Mathlib
import YangMills.LiteralSU2EvenTimeReflectionGeometry

/-!
# Orientation-sensitive reflection of literal SU(2) link configurations

A site reflection reverses the orientation of temporal links but preserves
spatial-link orientation.  For the even time reflection theta(t)=-t-1:

* spatial reflected link at x is U(theta x, i);
* temporal reflected link at x is
    U(theta(x+e0),0)^(-1)
  equivalently U(theta x-e0,0)^(-1).

This is the actual lattice link involution needed to compare the positive and
negative noncrossing Wilson half-actions.  The main theorem here proves that
the reflected-link map is itself involutive.

The next theorem in the global Wilson RP lane is the plaquette transport
identity under this link reflection, including the temporal orientation
reversal.  No statement about CMP119 residual sectors is made here.
-/

namespace RequestProject.YangMills

theorem su2_shift_backward_after_forward
    {L : ℕ} (x : SU2TorusSite L) (direction : Fin 4) :
    su2ShiftBackward (su2Shift x direction) direction = x := by
  classical
  funext i
  by_cases hi : i = direction
  · subst i
    simp [su2ShiftBackward, su2Shift]
    ring
  · simp [su2ShiftBackward, su2Shift,
      Function.update_noteq hi]

theorem su2_shift_forward_after_backward
    {L : ℕ} (x : SU2TorusSite L) (direction : Fin 4) :
    su2Shift (su2ShiftBackward x direction) direction = x := by
  classical
  funext i
  by_cases hi : i = direction
  · subst i
    simp [su2ShiftBackward, su2Shift]
    ring
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
    simp [su2EvenTimeReflectSite, su2Shift, su2ShiftBackward]
    ring
  · simp [su2EvenTimeReflectSite, su2Shift, su2ShiftBackward,
      Function.update_noteq hi]

theorem su2_backward_reflect_backward_reflect
    {n : ℕ} (x : SU2TorusSite (2 * n)) :
    su2ShiftBackward
        (su2EvenTimeReflectSite
          (su2ShiftBackward
            (su2EvenTimeReflectSite x)
            su2TimeDirection))
        su2TimeDirection = x := by
  rw [su2_even_time_reflect_backward_time_shift,
    su2_even_time_reflect_site_involutive,
    su2_shift_backward_after_forward]

/-- Orientation-sensitive Euclidean-time reflection of actual link fields. -/
def su2EvenTimeReflectLinks
    {n : ℕ}
    (links : SU2TorusLinks (2 * n)) :
    SU2TorusLinks (2 * n) :=
  fun x direction =>
    if h : direction = su2TimeDirection then
      (links
        (su2ShiftBackward
          (su2EvenTimeReflectSite x)
          su2TimeDirection)
        su2TimeDirection)⁻¹
    else
      links (su2EvenTimeReflectSite x) direction

theorem su2_even_time_reflect_spatial_link
    {n : ℕ}
    (links : SU2TorusLinks (2 * n))
    (x : SU2TorusSite (2 * n))
    (direction : Fin 4)
    (hSpatial : direction ≠ su2TimeDirection) :
    su2EvenTimeReflectLinks links x direction =
      links (su2EvenTimeReflectSite x) direction := by
  simp [su2EvenTimeReflectLinks, hSpatial]

theorem su2_even_time_reflect_temporal_link
    {n : ℕ}
    (links : SU2TorusLinks (2 * n))
    (x : SU2TorusSite (2 * n)) :
    su2EvenTimeReflectLinks links x su2TimeDirection =
      (links
        (su2ShiftBackward
          (su2EvenTimeReflectSite x)
          su2TimeDirection)
        su2TimeDirection)⁻¹ := by
  simp [su2EvenTimeReflectLinks]

/--
The reflected link configuration is an involution on the SAME literal
finite 4D configuration space.
-/
theorem su2_even_time_reflect_links_involutive
    {n : ℕ}
    (links : SU2TorusLinks (2 * n)) :
    su2EvenTimeReflectLinks
        (su2EvenTimeReflectLinks links) = links := by
  funext x direction
  by_cases hTime : direction = su2TimeDirection
  · subst direction
    rw [su2_even_time_reflect_temporal_link,
      su2_even_time_reflect_temporal_link,
      su2_backward_reflect_backward_reflect]
    simp
  · rw [su2_even_time_reflect_spatial_link _ _ _ hTime,
      su2_even_time_reflect_spatial_link _ _ _ hTime,
      su2_even_time_reflect_site_involutive]

end RequestProject.YangMills

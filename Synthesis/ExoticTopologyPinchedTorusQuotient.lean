import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

/-!
# A genuine point-set pinched-torus quotient

Classical object: collapse one essential meridian circle in S¹ × S¹
to a single point, with the QUOTIENT TOPOLOGY.

This is not merely an Euler characteristic, finite cell count,
combinatorial homology or an untyped pinching label. The underlying
topological type is a quotient of an actual product of complex unit
circles and has Mathlib's coinduced quotient topology.

We distinguish this choice (one essential circle collapsed) from
collapsing a null-homotopic circle, collapsing all of one factor,
or an algebraic nodal cubic. Those need not be the same space.
No cellular/singular homology theorem or classification/homeomorphism
to a wedge is imported or claimed.

Sources: standard topological quotient/torus construction (Hatcher,
Algebraic Topology), and Mathlib quotient topology implementation.
-/

namespace Synthesis.ExoticTopology

/-- Literal complex unit circle, with inherited subspace topology. -/
abbrev TopologicalUnitCircle := {z : ℂ // ‖z‖ = 1}

/-- Literal product torus S¹ × S¹, prior to quotient. -/
abbrev TopologicalTorus := TopologicalUnitCircle × TopologicalUnitCircle

def markedCirclePoint : TopologicalUnitCircle :=
  ⟨1, by norm_num⟩

/-- The circle that gets collapsed is {basepoint} × S¹. -/
def meridian (p : TopologicalTorus) : Prop :=
  p.1 = markedCirclePoint

/-- Labels are only used to generate the desired equivalence
    relation; the actual output space has the quotient topology. -/
noncomputable def pinchLabel (p : TopologicalTorus) :
    Option TopologicalTorus :=
  if meridian p then none else some p

/-- Equivalent iff their label agrees. This explicitly collapses the
    entire selected meridian, leaving all other points distinct. -/
noncomputable def pinchedTorusSetoid : Setoid TopologicalTorus where
  r p q := pinchLabel p = pinchLabel q
  iseqv := ⟨by intro p; rfl,
    by intro p q h; exact h.symm,
    by intro p q r h k; exact h.trans k⟩

/-- Literal pinched-torus quotient type, automatically equipped with
    Mathlib's coinduced quotient topology. -/
abbrev PinchedTorus := Quotient pinchedTorusSetoid

def torusPinch (p : TopologicalTorus) : PinchedTorus :=
  Quotient.mk pinchedTorusSetoid p

/-- Any two points on the selected meridian become identical. -/
theorem meridian_collapses (a b : TopologicalUnitCircle) :
    torusPinch (markedCirclePoint, a) =
      torusPinch (markedCirclePoint, b) := by
  apply Quotient.sound
  simp [pinchedTorusSetoid, pinchLabel, meridian]

/-- Away from the collapsed meridian, the quotient does not
    identify different source points. -/
theorem torusPinch_injective_away
    (p q : TopologicalTorus)
    (hp : ¬ meridian p) (hq : ¬ meridian q)
    (heq : torusPinch p = torusPinch q) : p = q := by
  have h := Quotient.exact heq
  simpa [pinchedTorusSetoid, pinchLabel, hp, hq] using h

/-- No point outside the meridian becomes the singular pinch point. -/
theorem torusPinch_nonmeridian_ne_pinched
    (p : TopologicalTorus) (hp : ¬ meridian p)
    (a : TopologicalUnitCircle) :
    torusPinch p ≠ torusPinch (markedCirclePoint, a) := by
  intro h
  have hh := Quotient.exact h
  simpa [pinchedTorusSetoid, pinchLabel, meridian, hp] using hh

end Synthesis.ExoticTopology

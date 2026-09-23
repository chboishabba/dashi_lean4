/-
# The hypercubic invariance is not vacuous

`Lattice/HypercubicLoop.lean` proves that Euclidean related based loops have the
same literal Wilson expectation.  This file checks that the relation genuinely
relates *different* loops, so that the invariance statements are not empty: the
elementary plaquette loop in the `(0,1)` plane is carried by the axis
transposition `0 ↔ 2` to the plaquette loop in the `(2,1)` plane, a different
loop, and by the reflection in the hyperplane orthogonal to direction `0` to the
plaquette loop traversed with the two `0`-steps reversed, again a different
loop.
-/
import Mathlib
import RequestProject.YangMills.Lattice.HypercubicLoop

namespace RequestProject.YangMills.Lattice

/-- The axis transposition exchanging the directions `0` and `2`. -/
def swap02 : Equiv.Perm (Fin 4) := Equiv.swap 0 2

/-- The elementary plaquette loop in the `(0,1)` plane. -/
def plaq01 : List Step := [(0, true), (1, true), (0, false), (1, false)]

theorem plaq01_rotate : plaq01.map (rotStep swap02)
    = [(2, true), (1, true), (2, false), (1, false)] := by
  decide

/-- The rotated plaquette is a genuinely different loop. -/
theorem plaq01_rotate_ne : plaq01.map (rotStep swap02) ≠ plaq01 := by
  decide

theorem plaq01_reflect : plaq01.map (refStep 0)
    = [(0, false), (1, true), (0, true), (1, false)] := by
  decide

/-- The reflected plaquette is a genuinely different loop. -/
theorem plaq01_reflect_ne : plaq01.map (refStep 0) ≠ plaq01 := by
  decide

/-- The two different loops are Euclidean related, so the invariance of the
Wilson expectation under the point group has non-trivial content. -/
theorem euclideanRelated_plaq01_rotate (n : ℕ) (x : Site n) :
    EuclideanRelated n (x, plaq01) (rotSite swap02 x, plaq01.map (rotStep swap02)) :=
  EuclideanRelated.rotate x plaq01 swap02

theorem euclideanRelated_plaq01_reflect (n : ℕ) (x : Site n) :
    EuclideanRelated n (x, plaq01) (refSite 0 x, plaq01.map (refStep 0)) :=
  EuclideanRelated.reflect x plaq01 0

/-! ## Axiom audit -/

#print axioms plaq01_rotate_ne
#print axioms plaq01_reflect_ne
#print axioms euclideanRelated_plaq01_rotate

end RequestProject.YangMills.Lattice

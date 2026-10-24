import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Sets.Closeds
import Mathlib.Tactic

/-!
# Warsaw circle: literal planar compactum candidate

Mathematical sources: the topologist's sine curve and the Warsaw circle,
historically associated with Karol Borsuk (shape theory).
The planar set uses the CLOSURE in the actual real-product topology,
not a finite sampled polyline or a combinatorial graph label.

S = closure {(x, sin(1/x)) | 0 < x ≤ 1}.
The polygonal closing arc follows:
 (0,-1) -> (0,-2) -> (1,-2) -> (1,sin 1).

Theorems in this file establish source-level inclusions and basic
pointwise separation. The exact identification of the sine-curve
closure with its oscillating graph plus the vertical segment, the
compact/connected continuum proof, trivial homotopy groups and the
failure of CW homotopy type remain independent obligations. In
particular, a point-set definition is NOT a Whitehead theorem.
-/

namespace Synthesis.ExoticTopology

abbrev Plane2 := ℝ × ℝ

def warsawSineGraph : Set Plane2 :=
  {p | 0 < p.1 ∧ p.1 ≤ 1 ∧ p.2 = Real.sin (1 / p.1)}

def warsawVerticalSegment : Set Plane2 :=
  {p | p.1 = 0 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1}

def warsawConnectorLeft : Set Plane2 :=
  {p | p.1 = 0 ∧ -2 ≤ p.2 ∧ p.2 ≤ -1}

def warsawConnectorBottom : Set Plane2 :=
  {p | p.2 = -2 ∧ 0 ≤ p.1 ∧ p.1 ≤ 1}

def warsawConnectorRight : Set Plane2 :=
  {p | p.1 = 1 ∧ -2 ≤ p.2 ∧ p.2 ≤ Real.sin 1}

def warsawClosingArc : Set Plane2 :=
  warsawConnectorLeft ∪ warsawConnectorBottom ∪ warsawConnectorRight

/-- A literal subset of the real plane with its actual subspace topology. -/
def warsawCircle : Set Plane2 :=
  closure warsawSineGraph ∪ warsawClosingArc

abbrev WarsawCircleSpace := {p : Plane2 // p ∈ warsawCircle}

/-- The oscillating graph is included, by the genuine closure operation. -/
theorem warsawGraph_subset : warsawSineGraph ⊆ warsawCircle := by
  intro p hp
  exact Or.inl (subset_closure hp)

/-- The polygonal closing arc is included by construction. -/
theorem warsawClosingArc_subset : warsawClosingArc ⊆ warsawCircle := by
  intro p hp
  exact Or.inr hp

/-- The graph itself never touches the x=0 axis. Its closure can. -/
theorem warsawSineGraph_positive_x
    {p : Plane2} (hp : p ∈ warsawSineGraph) : 0 < p.1 :=
  hp.1

/-- The connector starts at the lower endpoint of the limiting segment. -/
theorem warsawLowerEndpoint_in_closingArc :
    ((0 : ℝ), (-1 : ℝ)) ∈ warsawClosingArc := by
  left
  simp [warsawConnectorLeft]

/-- The connector terminates at the right end of the oscillating graph. -/
theorem warsawRightEndpoint_in_graph :
    ((1 : ℝ), Real.sin 1) ∈ warsawSineGraph := by
  simp [warsawSineGraph]

theorem warsawRightEndpoint_in_closingArc :
    ((1 : ℝ), Real.sin 1) ∈ warsawClosingArc := by
  right
  right
  simp [warsawConnectorRight, Real.neg_one_le_sin]

end Synthesis.ExoticTopology

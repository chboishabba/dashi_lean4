import Mathlib
import Integration.DASHITOE.HornHopfClaspVsHatcherF2NoGoCut

/-!
# Hatcher local F₂: exact ribbon-source boundary versus pants/hopf no-go

Original topological source: Hatcher, Algebraic Topology Example 2B.2,
pp171–172: a punctured-torus boundary alpha represents NONTRIVIAL
[alpha_1,alpha_2] in the actual local F₂ attachment Z.
Classical oriented ribbon-graph rotation systems encode an
orientable surface thickening by sigma (vertex rotation) and
flip (edge reversal); boundary traversal phi=sigma ∘ flip.
Sage's Ribbon Graphs manual is a later documentation of the
classical permutation convention, not original theorem priority.

Agda topology #1254 owns existing finite PL pants/gluings;
horn original geometry #1244 owns the actual satellite C3
placement, Hatcher-at based group/path glue and true source
geometry contracts. This module does not duplicate their
PL implementations or claim a physical Hatcher wild stage.

NEW finite counter/positive source pair on the SAME
one-vertex, two-edge bouquet:
* ALTERNATING cyclic rotation (a,B,A,b) has ONE boundary
  traversed as (a,b,A,B), hence (by the original classical
  surface-thickening theorem) genus1, one boundary, incoming
  word [a,b]. This is a combinatorial *punctured torus*.
* NONALTERNATING cyclic rotation (a,A,b,B) has THREE
  boundaries; classical thickening is genus0 three-boundary
  pants. Identical ABSTRACT free F₂ and identical local
  geometric generator lengths therefore do not imply the
  correct peripheral Hatcher incoming annulus map.

The Lean code proves the FINITE DECISION TABLE and
integer Euler/genus arithmetic, not the classical
ribbon-graph-topological-realization equivalence nor
source same-object ambient Hatcher embedding.
Lean/Lake kernel NOT run.
-/

namespace DASHIHornHatcherRibbonBoundary

inductive Dart where
  | a | A | b | B
  deriving DecidableEq, Repr

open Dart

def flip : Dart → Dart
  | a => A
  | A => a
  | b => B
  | B => b

/-- One-vertex cyclic order a -> B -> A -> b -> a. -/
def torusRotation : Dart → Dart
  | a => B
  | B => A
  | A => b
  | b => a

/-- One-vertex cyclic order a -> A -> b -> B -> a. -/
def pantsRotation : Dart → Dart
  | a => A
  | A => b
  | b => B
  | B => a

def torusBoundaryNext (d : Dart) : Dart :=
  torusRotation (flip d)

def pantsBoundaryNext (d : Dart) : Dart :=
  pantsRotation (flip d)

/-- All four half-edges form ONE boundary cycle a,b,A,B. -/
theorem alternatingBoundaryWordIsCommutator :
    torusBoundaryNext a = b ∧
    torusBoundaryNext b = A ∧
    torusBoundaryNext A = B ∧
    torusBoundaryNext B = a := by
  decide

/-- Same two formal edges, but boundary cycles (a,b), (A), (B).
This is THREE components, not the single Hatcher commutator. -/
theorem nonalternatingBoundaryHasThreeCycles :
    pantsBoundaryNext a = b ∧
    pantsBoundaryNext b = a ∧
    pantsBoundaryNext A = A ∧
    pantsBoundaryNext B = B := by
  decide

theorem edgeFlipInvolutive (d : Dart) : flip (flip d) = d := by
  cases d <;> rfl

/-- The bouquet has V=1 and E=2, so its orientable
ribbon thickening has Euler characteristic -1. -/
theorem bouquetEulerCharacteristic :
    (1:ℤ) - 2 = -1 := by norm_num

/-- Given boundary count b, orientable thickening satisfies
chi=2-2g-b. For the one-boundary case g=1. -/
theorem alternatingSurfaceGenus :
    (2:ℤ) - 2*1 - 1 = (1:ℤ)-2 := by norm_num

/-- For the three-boundary case the same bouquet has g=0. -/
theorem nonalternatingSurfaceGenus :
    (2:ℤ) - 2*0 - 3 = (1:ℤ)-2 := by norm_num

/-- Exact positivity of straight tube model length cap:
each circle radius 1/4 after source-coordinate scale 1/8
has length pi/16 < 11/56 from pi<22/7, well below
781/1000. The actual Hatcher Euclidean embedding/map
has NOT been constructed; this is the model metric. -/
theorem straightTubeModelLengthWithinSelectedCap :
    (11/56 : ℚ) < 781/1000 := by norm_num

end DASHIHornHatcherRibbonBoundary

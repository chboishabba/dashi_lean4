import Mathlib.Tactic

/-!
# Euler-Maxwell identity for triangulated compact bordered surfaces

Source genealogy:
- Brahana (1921): classification of compact bordered orientable surfaces;
- elementary Euler/incidence counting of triangulated surfaces;
- Stephen C. Power (2025), "Noncompact surfaces, triangulations and
  rigidity", Bull. London Math. Soc. 57, 2097--2115,
  DOI 10.1112/blms.70083, preprint arXiv:2403.11986 (2024):
  proves EXISTENCE of special countable (3,6)-tight triangulations.

For *any* connected orientable finite triangular-face surface of
genus g with b boundary circles and total boundary EDGE count L:
  3F = 2E - L, Euler V-E+F = 2-2g-b,
hence 3V-E = 3(2-2g-b)+L.

If EVERY boundary circle is a 3-edge triangle (L=3b), this
simplifies to 3V-E=6-6g. Thus for g>=1 the entire graph
violates the necessary (3,6)-sparsity condition >=6.

For g=0, the WHOLE-graph count equals 6. To infer that the
chosen graph is (3,6)-tight additionally use planarity and
the classical planar subgraph edge bound E'<=3V'-6
for each subgraph with >=3 vertices. These geometric
hypotheses are NOT discharged in this numerical Lean module:
the source PL mesh checker provides bounded finite instances,
not a general planar embedding/rigidity certificate.

No equivalence of source meshes with Power's particular
minimally rigid triangulations is asserted.
-/

namespace Synthesis.ExoticTopology

/-- Pure Euler/face-incidence algebra, for arbitrary total boundary
edge length L and number of connected boundary curves b. -/
theorem eulerMaxwellWithBoundaryLength
    (V E F L g b : ℤ)
    (incidence : 3 * F = 2 * E - L)
    (euler : V - E + F = 2 - 2 * g - b) :
    3 * V - E = 3 * (2 - 2 * g - b) + L := by
  omega

/-- Every three-edge boundary loop removes a boundary contribution
from the global Maxwell count; genus is the remaining obstruction. -/
theorem triangularBoundaryMaxwellGenus
    (V E F L g b : ℤ)
    (incidence : 3 * F = 2 * E - L)
    (euler : V - E + F = 2 - 2 * g - b)
    (triangularBoundary : L = 3 * b) :
    3 * V - E = 6 - 6 * g := by
  omega

/-- A positive-genus selected finite mesh with triangular boundaries
cannot even meet the necessary whole-graph (3,6)-sparsity inequality.
This is a strict numerical no-go for the SELECTED triangulation,
not for all triangulations of that topological surface. -/
theorem positiveGenusViolates36WholeGraph
    (V E F L g b : ℤ)
    (incidence : 3 * F = 2 * E - L)
    (euler : V - E + F = 2 - 2 * g - b)
    (triangularBoundary : L = 3 * b)
    (positiveGenus : 0 < g) :
    3 * V - E < 6 := by
  have hm := triangularBoundaryMaxwellGenus
    V E F L g b incidence euler triangularBoundary
  omega

/-- Genus-zero finite stages satisfy the global necessary count;
this alone does NOT certify the all-subgraph (3,6)-sparsity
inequalities unless a genuine planar embedding is supplied. -/
theorem zeroGenusHasWholeGraphMaxwellSix
    (V E F L b : ℤ)
    (incidence : 3 * F = 2 * E - L)
    (euler : V - E + F = 2 - b)
    (triangularBoundary : L = 3 * b) :
    3 * V - E = 6 := by
  omega

end Synthesis.ExoticTopology

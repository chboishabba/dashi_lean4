import Mathlib
import Integration.DASHITOE.HornSelectedWSpectralCubicCut

/-!
# Peripheral localisation and free-meridian length interface

Original mathematics: J. W. Alexander (1924), Allen Hatcher
Algebraic Topology Example 2B.2 pp171-172; classic path metric
triangle inequality, unitary holonomy/parallel-transport norm.
Existing owner Agda horn PR #1244 establishes the SAME concrete
three-sector coordinates, pierced-shell chart and paper-level central
simply-connected tame-tree replacement; its actual linked
satellite meridian/π1 map remains unproved. Original selected
matrix belongs to neutrino Agda #1247; the >781/1000 exact
source-selected child bound belongs to Agda #1249 / Lean #84.

The results in this file pay only exact RATIONAL consequences of
the source point coordinates and of EXPLICITLY SUPPLIED genuine
geometric/analytic hypotheses. This does NOT posit an actual wild
Hatcher meridian, a bounded gauge, a physical field, or a kernel pass.
-/

namespace DASHIHornPeripheralLocality

/-- Squared Euclidean source-centre distance:
| (20,20,20)-(9,0,0) |² = 921, and C3 permutes the centres. -/
theorem sourceCentreDistanceSquared :
    ((20-9:ℚ)^2+20^2+20^2)=921 := by norm_num

/-- Strict rational lower substitute for sqrt(921): no floating
point or unproved square-root normalization required. -/
theorem centreDistanceStrictLower
    (d : ℚ) (hNonneg : 0 ≤ d) (hSq : d^2=921) :
    (303/10 : ℚ) < d := by
  by_contra h
  have hle : d ≤ (303/10 : ℚ) := le_of_not_gt h
  nlinarith

/-- SOURCE-CONDITIONAL point-set geometry:
if a rectifiable based x0-loop reaches one inner closed satellite
cut ball radius 15/4, triangle inequality bounds the centre
distance by its excursion plus 15/4; outward and return arcs
each have at least excursion length. The metric hypotheses here
must be supplied by true Euclidean paths in E. -/
theorem basedLoopEnteringInnerCutLong
    (dCentre dExcursion loopLength : ℚ)
    (hCentreNonneg : 0 ≤ dCentre)
    (hCentreSq : dCentre^2=921)
    (hTriangle : dCentre ≤ dExcursion+15/4)
    (hOutAndBack : 2*dExcursion ≤ loopLength) :
    (531/10 : ℚ) < loopLength := by
  have hStrict := centreDistanceStrictLower dCentre hCentreNonneg hCentreSq
  linarith

/-- The original owner's chosen C3-equivariant collar terminal
p_i=13e_i lies a squared Euclidean distance 16 from c_i=9e_i.
Thus it is strictly inside the literal shell 15/4<r<17/4. -/
theorem overlapTerminalStrictShell :
    (15/4 : ℚ)^2 < (13-9 : ℚ)^2 ∧
    (13-9 : ℚ)^2 < (17/4 : ℚ)^2 := by
  constructor <;> norm_num

/-- The selected-W child obstruction is on a SHORT LOCAL
free-meridian representative, not on the long based loop.
To inhabit the hLength hypothesis one must construct that
ACTUAL exterior curve with a compatible bounded flat gauge.
The direct analytic SU3 norm estimate is the external hDirect. -/
theorem markedLocalMeridianRequiresML
    (rootSq childGap M L : ℚ)
    (hRoot : DASHIHornSelectedWSpectralCubic.selectedRootSqThreshold
       < rootSq)
    (hNonneg : 0 ≤ childGap)
    (hDirect : rootSq ≤
      DASHIHornSelectedWSpectralCubic.directArcSquared childGap)
    (hSourceLength : childGap ≤ M*L) :
    (781/1000 : ℚ) < M*L := by
  have hgap :=
    DASHIHornSelectedWSpectralCubic.selectedWChildGapExceeds781
      rootSq childGap hRoot hNonneg hDirect
  exact lt_of_lt_of_le hgap hSourceLength

/-- If a selected marked meridian has local length <= Lcap and a
bounded compatible source M obeys M Lcap<=781/1000,
the selected representation is impossible. The actual
source loop and gauge are explicitly necessary premises. -/
theorem selectedRootLocalMeridianFlatReject
    (rootSq childGap M L Lcap : ℚ)
    (hRoot : DASHIHornSelectedWSpectralCubic.selectedRootSqThreshold
       < rootSq)
    (hNonneg : 0 ≤ childGap)
    (hDirect : rootSq ≤
      DASHIHornSelectedWSpectralCubic.directArcSquared childGap)
    (hSourceLength : childGap ≤ M*L)
    (hM : 0 ≤ M)
    (hL : L ≤ Lcap)
    (hCap : M*Lcap ≤ 781/1000) :
    False := by
  have hProduct := markedLocalMeridianRequiresML
    rootSq childGap M L hRoot hNonneg hDirect hSourceLength
  have hBound : M*L ≤ M*Lcap := mul_le_mul_of_nonneg_left hL hM
  linarith

/-- The SHARP sibling asymptotic proof is owned by prior Agda
#1249 / Lean #84. Here its RATIONAL 31/60 strict threshold is
presented as a geometrically typed systolic test: for any
source-proved sibling gap>31/60 and a compatible gauge bound,
a local marked free-homotopy representative cannot be too short. -/
theorem siblingMarkedSystoleLower
    (gap M ell : ℚ)
    (hGap : 31/60 < gap)
    (hUnitaryTransport : gap ≤ M*ell) :
    (31/60 : ℚ) < M*ell := by
  linarith

end DASHIHornPeripheralLocality

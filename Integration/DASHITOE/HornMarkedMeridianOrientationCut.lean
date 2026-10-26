import Mathlib
import Integration.DASHITOE.HornSelectedWSpectralCubicCut

/-!
# Hatcher marked-meridian orientation/basing normalisation for the
# existing selected-W SU3 obstruction

Original mathematical source: Allen Hatcher, Algebraic Topology
Example 2B.2, pp171-172, source van Kampen punctured-torus
commutator with child generators. Ordinary free homotopy changes
loop basing by conjugation; loop orientation reverses/inverts.

PR lineage: Agda horn owner #1244 already supplies abstract
commutator marked sector group and explicit C3 *central collar*
basing paths. Agda neutrino #1247 owns the selected exact W.
Agda #1249 / Lean #84 own its direct SU3 child gap and exact
spectral-cubic certificate. Exotic Agda #1254 / Lean #86
identified the prepend versus chronological-append address
orientation problem; the original
AlexanderHornedBinaryPadicCylinderExact.chronological transport
already solves the literal list reversal at the address level.

NEW typed finite group-algebra bridge: a common source whisker and
whole-word inverse do NOT change the unitary operator-norm gap.
A source meridian record must STILL be inhabited by the actual
Hatcher exterior generator map. An arbitrary independently
whiskered pair of children is NOT supplied by this bridge.
The norm-invariance and analytic direct SU3 estimates are
explicitly supplied premises, not fabricated theorem authority.
No Lean/Lake kernel receipt or physical gauge/measurement.
-/

namespace DASHIHornMeridianOrientation

variable {G : Type*} [Group G]

/-- The exact commutator convention used in the Hatcher symbolic
tower. The group-theoretic class is source-independent, whereas
realising it by source loops is a separate geometry obligation. -/
def comm (a b : G) : G := a * b * a⁻¹ * b⁻¹

/-- Reversing children inverts the whole commutator. -/
theorem swap_comm (a b : G) :
    comm b a = (comm a b)⁻¹ := by
  dsimp [comm]
  group

/-- Coherently transporting BOTH children by one common basing
path transports the WHOLE parent commutator by that conjugacy. -/
theorem whisker_comm (g a b : G) :
    comm (g * a * g⁻¹) (g * b * g⁻¹) =
      g * comm a b * g⁻¹ := by
  dsimp [comm]
  group

/-- Inverting both child orientations gives a conjugate, not
literally the same word. This is the correct noncommutative
replacement for the tempting but FALSE equality without basing. -/
theorem invert_both_comm (a b : G) :
    comm a⁻¹ b⁻¹ =
      (a*b)⁻¹ * comm a b * (a*b) := by
  dsimp [comm]
  group

/-- The ACTUAL Hatcher relative satellite-to-free-group map must
supply this equality. The source interface deliberately allows
an orientation reversal and a COMMON basepoint whisker. -/
structure SourceMarkedCommutator (G : Type*) [Group G] where
  root : G
  childLeft : G
  childRight : G
  whisker : G
  reversed : Bool
  sourceWord :
    root =
      whisker *
        (if reversed then (comm childLeft childRight)⁻¹
         else comm childLeft childRight) *
        whisker⁻¹

/-- Unitary gap invariance is a consumer-supplied source theorem
rather than a generic fact about an arbitrary function G→ℚ. -/
theorem markedRootGapIndependentOfBasingAndOrientation
    (gap : G → ℚ)
    (hConj : ∀ (g x : G), gap (g*x*g⁻¹) = gap x)
    (hInv : ∀ x : G, gap x⁻¹ = gap x)
    (m : SourceMarkedCommutator G) :
    gap m.root = gap (comm m.childLeft m.childRight) := by
  calc
    gap m.root =
        gap (m.whisker *
          (if m.reversed then
             (comm m.childLeft m.childRight)⁻¹
           else comm m.childLeft m.childRight) *
          m.whisker⁻¹) := by rw [m.sourceWord]
    _ = gap (if m.reversed then
           (comm m.childLeft m.childRight)⁻¹
           else comm m.childLeft m.childRight) :=
          hConj m.whisker _
    _ = gap (comm m.childLeft m.childRight) := by
          cases h : m.reversed with
          | false => simp [h]
          | true => simp [h, hInv]

/-- Exact selected-W flat child floor from the existing spectral
source, now invariant under the whole-loop marking choices of the
real based Hatcher group. The analytic inequalities are PREMISES. -/
theorem markedLeftChildExceeds781
    (gap : G → ℚ)
    (hConj : ∀ (g x : G), gap (g*x*g⁻¹) = gap x)
    (hInv : ∀ x : G, gap x⁻¹ = gap x)
    (m : SourceMarkedCommutator G)
    (hRootSq :
      DASHIHornSelectedWSpectralCubic.selectedRootSqThreshold <
        (gap m.root)^2)
    (hChildNonneg : 0 ≤ gap m.childLeft)
    (hDirect :
      (gap (comm m.childLeft m.childRight))^2 ≤
        DASHIHornSelectedWSpectralCubic.directArcSquared
          (gap m.childLeft)) :
    (781 / 1000 : ℚ) < gap m.childLeft := by
  apply DASHIHornSelectedWSpectralCubic.selectedWChildGapExceeds781
    ((gap m.root)^2) (gap m.childLeft)
    hRootSq hChildNonneg
  rw [markedRootGapIndependentOfBasingAndOrientation gap hConj hInv m]
  exact hDirect

/-- The opposite child has the same scalar obstruction, with
the source group relation consumed once and the direct analytic
bound supplied separately for that child. -/
theorem markedRightChildExceeds781
    (gap : G → ℚ)
    (hConj : ∀ (g x : G), gap (g*x*g⁻¹) = gap x)
    (hInv : ∀ x : G, gap x⁻¹ = gap x)
    (m : SourceMarkedCommutator G)
    (hRootSq :
      DASHIHornSelectedWSpectralCubic.selectedRootSqThreshold <
        (gap m.root)^2)
    (hChildNonneg : 0 ≤ gap m.childRight)
    (hDirect :
      (gap (comm m.childLeft m.childRight))^2 ≤
        DASHIHornSelectedWSpectralCubic.directArcSquared
          (gap m.childRight)) :
    (781 / 1000 : ℚ) < gap m.childRight := by
  apply DASHIHornSelectedWSpectralCubic.selectedWChildGapExceeds781
    ((gap m.root)^2) (gap m.childRight)
    hRootSq hChildNonneg
  rw [markedRootGapIndependentOfBasingAndOrientation gap hConj hInv m]
  exact hDirect

end DASHIHornMeridianOrientation

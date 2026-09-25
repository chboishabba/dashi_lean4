import NSBControl.SelfOrbitCommutatorCarrier
import Mathlib.Tactic.Ring

namespace NSBControl
namespace SingleSelfCommutatorOrbit

open CyclicHelicalVectorTransform
open SelfOrbitCommutatorCarrier

section

variable
  (pairFour pairOne : Triad → Triad → ℝ)
  (mask : Triad → ℝ → ℝ)
  (fibre : Mode → List Triad)
  (factor : ℝ)

theorem spectatorRow_factor
    (hPair : ∀ alpha beta, pairFour alpha beta = factor * pairOne alpha beta)
    (beta : Triad)
    (items : List Triad) :
    spectatorRow pairFour beta items =
      factor * spectatorRow pairOne beta items := by
  induction items with
  | nil =>
      simp [spectatorRow]
  | cons alpha rest ih =>
      simp [spectatorRow, hPair alpha beta, ih]
      ring

theorem outerRow_factor
    (hPair : ∀ alpha beta, pairFour alpha beta = factor * pairOne alpha beta)
    (beta : Triad) :
    outerRow fibre pairFour beta =
      factor * outerRow fibre pairOne beta := by
  exact spectatorRow_factor
    pairFour pairOne factor hPair beta (fibre beta.k)

theorem maskedOuterRow_factor
    (hPair : ∀ alpha beta, pairFour alpha beta = factor * pairOne alpha beta)
    (hMask :
      ∀ beta value,
        mask beta (factor * value) = factor * mask beta value)
    (beta : Triad) :
    maskedOuterRow mask fibre pairFour beta =
      factor * maskedOuterRow mask fibre pairOne beta := by
  unfold maskedOuterRow
  rw [outerRow_factor pairFour pairOne fibre factor hPair beta]
  exact hMask beta (outerRow fibre pairOne beta)

theorem orbitResidue_factor
    (hPair : ∀ alpha beta, pairFour alpha beta = factor * pairOne alpha beta)
    (hMask :
      ∀ beta value,
        mask beta (factor * value) = factor * mask beta value)
    (beta : Triad) :
    orbitResidue mask fibre pairFour beta =
      factor * orbitResidue mask fibre pairOne beta := by
  unfold orbitResidue
  rw [
    maskedOuterRow_factor
      pairFour pairOne mask fibre factor hPair hMask beta,
    maskedOuterRow_factor
      pairFour pairOne mask fibre factor hPair hMask (pEnergyLeg beta),
    maskedOuterRow_factor
      pairFour pairOne mask fibre factor hPair hMask (qEnergyLeg beta)
  ]
  ring

theorem completeOrbit_factor
    (items : List Triad)
    (hPair : ∀ alpha beta, pairFour alpha beta = factor * pairOne alpha beta)
    (hMask :
      ∀ beta value,
        mask beta (factor * value) = factor * mask beta value) :
    foldOrbit mask fibre pairFour items =
      factor * foldOrbit mask fibre pairOne items := by
  induction items with
  | nil =>
      simp [foldOrbit]
  | cons beta rest ih =>
      simp only [foldOrbit, List.map_cons, List.sum_cons]
      rw [
        orbitResidue_factor
          pairFour pairOne mask fibre factor hPair hMask beta,
        ih
      ]
      ring

end

end SingleSelfCommutatorOrbit
end NSBControl

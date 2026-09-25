import NSBControl.SelfOrbitCommutatorCarrier
import Mathlib.Tactic.Ring

namespace NSBControl
namespace CompleteSelfOrbitCollapse

open CyclicHelicalVectorTransform
open SelfOrbitCommutatorCarrier

section

variable
  (mask : Triad → ℝ → ℝ)
  (fibre : Mode → List Triad)
  (pair : Triad → Triad → ℝ)

def maskedRow (beta : Triad) : ℝ :=
  maskedOuterRow mask fibre pair beta

def baseFold (items : List Triad) : ℝ :=
  (items.map (maskedRow mask fibre pair)).sum

def pLegFold (items : List Triad) : ℝ :=
  (items.map (fun beta => maskedRow mask fibre pair (pEnergyLeg beta))).sum

def qLegFold (items : List Triad) : ℝ :=
  (items.map (fun beta => maskedRow mask fibre pair (qEnergyLeg beta))).sum

theorem foldOrbit_split
    (items : List Triad) :
    foldOrbit mask fibre pair items =
      baseFold mask fibre pair items +
      pLegFold mask fibre pair items +
      qLegFold mask fibre pair items := by
  induction items with
  | nil =>
      simp [foldOrbit, baseFold, pLegFold, qLegFold]
  | cons beta rest ih =>
      simp only [foldOrbit, orbitResidue, List.map_cons, List.sum_cons,
        baseFold, pLegFold, qLegFold]
      rw [ih]
      ring

theorem completeOrbit_eq_three_base
    (items : List Triad)
    (hP : pLegFold mask fibre pair items = baseFold mask fibre pair items)
    (hQ : qLegFold mask fibre pair items = baseFold mask fibre pair items) :
    foldOrbit mask fibre pair items =
      3 * baseFold mask fibre pair items := by
  rw [foldOrbit_split mask fibre pair items, hP, hQ]
  ring

end

end CompleteSelfOrbitCollapse
end NSBControl

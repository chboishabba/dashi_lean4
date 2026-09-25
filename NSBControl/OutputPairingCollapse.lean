import NSBControl.SelfOrbitCommutatorCarrier
import Mathlib.Tactic.Ring

namespace NSBControl
namespace OutputPairingCollapse

open CyclicHelicalVectorTransform
open SelfOrbitCommutatorCarrier

section

variable {V : Type*}
variable [AddCommMonoid V]

def foldV (value : Triad → V) (items : List Triad) : V :=
  (items.map value).sum

variable
  (pairing : V → V → ℝ)
  (pairAddLeft :
    ∀ a b c, pairing (a + b) c = pairing a c + pairing b c)
  (pairAddRight :
    ∀ a b c, pairing a (b + c) = pairing a b + pairing a c)
  (pairZeroLeft :
    ∀ c, pairing 0 c = 0)
  (pairZeroRight :
    ∀ a, pairing a 0 = 0)

variable
  (mixed selfCell : Triad → V)

def pair (alpha beta : Triad) : ℝ :=
  pairing (mixed alpha) (selfCell beta)

theorem spectatorRow_factor_left
    (beta : Triad)
    (items : List Triad) :
    spectatorRow (pair pairing mixed selfCell) beta items =
      pairing (foldV mixed items) (selfCell beta) := by
  induction items with
  | nil =>
      simp [spectatorRow, foldV, pair, pairZeroLeft]
  | cons alpha rest ih =>
      simp only [spectatorRow, foldV, List.map_cons, List.sum_cons, pair]
      rw [ih, pairAddLeft]

theorem doubleRow_collapse
    (items : List Triad) :
    (items.map
      (fun beta =>
        spectatorRow (pair pairing mixed selfCell) beta items)).sum =
      pairing (foldV mixed items) (foldV selfCell items) := by
  induction items with
  | nil =>
      simp [foldV, pairZeroRight]
  | cons beta rest ih =>
      let M := foldV mixed (beta :: rest)
      have hrow :
          spectatorRow (pair pairing mixed selfCell) beta (beta :: rest) =
            pairing M (selfCell beta) := by
        exact spectatorRow_factor_left
          pairing pairAddLeft mixed selfCell beta (beta :: rest)
      have htail :
          ((rest.map
            (fun gamma =>
              spectatorRow (pair pairing mixed selfCell) gamma (beta :: rest))).sum) =
            pairing M (foldV selfCell rest) := by
        induction rest with
        | nil =>
            simp [foldV, pairZeroRight]
        | cons gamma tail tailIH =>
            simp only [List.map_cons, List.sum_cons]
            rw [spectatorRow_factor_left
              pairing pairAddLeft mixed selfCell gamma (beta :: gamma :: tail)]
            rw [tailIH]
            rw [← pairAddRight]
            rfl
      simp only [List.map_cons, List.sum_cons]
      rw [hrow, htail]
      rw [← pairAddRight]
      rfl

end

section OutputRegroup

variable {K : Type*}

def outputIndexedSum
    (local : K → ℝ)
    (outputs : List K) : ℝ :=
  (outputs.map local).sum

theorem concat_fibre_regroup
    (fibre : K → List Triad)
    (row : Triad → ℝ)
    (local : K → ℝ)
    (outputs : List K)
    (hLocal :
      ∀ k, ((fibre k).map row).sum = local k) :
    ((outputs.flatMap fibre).map row).sum =
      outputIndexedSum local outputs := by
  induction outputs with
  | nil =>
      simp [outputIndexedSum]
  | cons k rest ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, outputIndexedSum]
      rw [hLocal k, ih]

end OutputRegroup

end OutputPairingCollapse
end NSBControl

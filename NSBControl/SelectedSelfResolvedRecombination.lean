import NSBControl.OutputPairingCollapse
import Mathlib.Tactic.Ring

namespace NSBControl
namespace SelectedSelfResolvedRecombination

section Multiplier

variable {V : Type*} [AddCommMonoid V]

def foldV := OutputPairingCollapse.foldV

theorem fold_double_cell
    (self multiplier : Triad → V)
    (items : List Triad)
    (hCell : ∀ tau, multiplier tau = self tau + self tau) :
    foldV multiplier items = foldV self items + foldV self items := by
  induction items with
  | nil =>
      simp [foldV, OutputPairingCollapse.foldV]
  | cons tau rest ih =>
      simp only [foldV, OutputPairingCollapse.foldV, List.map_cons, List.sum_cons]
      rw [hCell tau, ih]
      ac_rfl

variable
  (pairing : V → V → ℝ)
  (pairAddRight :
    ∀ a b c, pairing a (b + c) = pairing a b + pairing a c)

theorem multiplier_work_is_double_self
    (mixed self multiplier : V)
    (hMultiplier : multiplier = self + self) :
    pairing mixed multiplier =
      pairing mixed self + pairing mixed self := by
  rw [hMultiplier, pairAddRight]

theorem resolved_helicity_split
    (mixed self multiplier homochiral heterochiral : V)
    (hDouble : multiplier = self + self)
    (hSplit : multiplier = homochiral + heterochiral) :
    pairing mixed self + pairing mixed self =
      pairing mixed homochiral + pairing mixed heterochiral := by
  rw [← pairAddRight, ← hDouble, hSplit, pairAddRight]

end Multiplier

section Recombine

theorem self_orbit_is_twelve_output_sum
    (selfOrbit singleOrbit maskedRows outputSum : ℝ)
    (hFour : selfOrbit = 4 * singleOrbit)
    (hThree : singleOrbit = 3 * maskedRows)
    (hOutput : maskedRows = outputSum) :
    selfOrbit = 12 * outputSum := by
  rw [hFour, hThree, hOutput]
  ring

theorem self_external_recombine
    (nested selfOrbit externalOrbit globalCommutator outputSum : ℝ)
    (hSplit : nested = selfOrbit + externalOrbit)
    (hGlobal : nested = 12 * globalCommutator)
    (hSelf : selfOrbit = 12 * outputSum) :
    12 * outputSum + externalOrbit =
      12 * globalCommutator := by
  rw [← hSelf, ← hSplit, hGlobal]

theorem global_commutator_is_only_combined_residue
    (nested selfOrbit externalOrbit globalCommutator outputSum : ℝ)
    (hSplit : nested = selfOrbit + externalOrbit)
    (hGlobal : nested = 12 * globalCommutator)
    (hSelf : selfOrbit = 12 * outputSum) :
    12 * globalCommutator =
      12 * outputSum + externalOrbit := by
  symm
  exact self_external_recombine
    nested selfOrbit externalOrbit globalCommutator outputSum
    hSplit hGlobal hSelf

end Recombine

end SelectedSelfResolvedRecombination
end NSBControl

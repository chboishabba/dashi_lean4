import Solution

/-!
Source-local admission of Alpöge–Buckmaster's original *conditional* results.
Build in their pinned v4.33.1 package, not DASHI's root toolchain.
Do not import Challenge or CellLayerTheorems: those are comparator statements
with sorry bodies. No external certificate is claimed to be inhabited here.
-/

open scoped ContDiff ENNReal
open MeasureTheory
open Breakdown Breakdown.CertCell Breakdown.CertCell.GivenShape

namespace DASHI.AlpogeBuckmaster

/-- Literal positive whole-space claim on the original unforced carrier,
restricted to compactly supported smooth solenoidal data. -/
def PositiveSpace : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : Space → Space,
    ContDiff ℝ ∞ u₀ → HasCompactSupport u₀ →
    (∀ x, divergenceAt u₀ x = 0) →
    ∃ (u : ℝ → Space → Space) (p : ℝ → Space → ℝ),
      IsSmoothSolution ν u₀ u p ∧
      ∃ C : ℝ, ∀ t ≥ 0, ∫⁻ x, ENNReal.ofReal (‖u t x‖ ^ 2) ≤ ENNReal.ofReal C

/-- Periodic velocity with arbitrary pressure, as in the original source. -/
def PositiveTorus : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : Space → Space,
    ContDiff ℝ ∞ u₀ →
    (∀ i x, u₀ (x + unitVector i) = u₀ x) →
    (∀ x, divergenceAt u₀ x = 0) →
    ∃ (u : ℝ → Space → Space) (p : ℝ → Space → ℝ),
      IsSmoothSolution ν u₀ u p ∧
      ∀ t ≥ 0, ∀ i x, u t (x + unitVector i) = u t x

theorem space_refutes_positive (h : BreakdownOnSpace) : ¬ PositiveSpace := by
  intro hpos
  obtain ⟨u₀, hs, hc, hd, hn⟩ := h 1 (by norm_num)
  exact hn (hpos 1 (by norm_num) u₀ hs hc hd)

theorem torus_refutes_positive (h : BreakdownOnTorus) : ¬ PositiveTorus := by
  intro hpos
  obtain ⟨u₀, hs, hp, hd, hn⟩ := h 1 (by norm_num)
  exact hn (hpos 1 (by norm_num) u₀ hs hp hd)

theorem from_profile (h : PeriodicSimilarityProfileExists) :
    BreakdownOnSpace ∧ BreakdownOnTorus :=
  ⟨Breakdown.breakdown_on_space h, Breakdown.breakdown_on_torus h⟩

open Breakdown.CellLayerSystem

/-- Same seven dependent source objects, same fifteen-condition hypothesis,
both original unforced terminals, and their positive-claim refutations.
No manufactured numerical bounds and no premise hidden behind an axiom. -/
theorem from_original_cell_condition {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM)
    (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R)
    (Y : CellLayerEntries D R T) (N : CoerciveNumbers) (B : ReductionEntries k)
    (h : CellSystemCondition D X R T Y N B) :
    BreakdownOnSpace ∧ BreakdownOnTorus ∧ ¬ PositiveSpace ∧ ¬ PositiveTorus := by
  obtain ⟨hs, ht⟩ :=
    Breakdown.CellLayerSystem.breakdownOnSpaceAndTorus_of_cell_system_condition D X R T Y N B h
  exact ⟨hs, ht, space_refutes_positive hs, torus_refutes_positive ht⟩

#print axioms Breakdown.breakdown_on_space
#print axioms Breakdown.breakdown_on_torus
#print axioms Breakdown.CellLayerSystem.breakdownOnSpaceAndTorus_of_cell_system_condition
#print axioms DASHI.AlpogeBuckmaster.from_profile
#print axioms DASHI.AlpogeBuckmaster.from_original_cell_condition

end DASHI.AlpogeBuckmaster

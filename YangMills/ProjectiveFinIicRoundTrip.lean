import Mathlib
import YangMills.ProjectiveFinIicBridge

/-!
# Round-trip the conditional continuum law back to the original `Fin` marginals

The physical compactness lane speaks in `Fin m → ℝ`; the sequential extension
lane speaks in `Iic n → ℝ`.  The bridge already constructs the latter from the
former.  This file proves that the final Ionescu--Tulcea law recovers the
original nonempty finite marginals exactly after the canonical natural-prefix
map.
-/

open Set MeasureTheory Preorder

namespace RequestProject.YangMills

/-- The first `m` coordinates of a countable real sequence. -/
def realNatPrefix
    (m : ℕ) : (ℕ → ℝ) → (Fin m → ℝ) :=
  fun x i => x i.1

/-- Natural prefix projection is continuous. -/
theorem real_nat_prefix_continuous
    (m : ℕ) : Continuous (realNatPrefix m) := by
  fun_prop

/-- The Fin/Iic reindexings cancel at the level of probability laws. -/
theorem realFinSuccLawToIic_map_back
    (n : ℕ)
    (μ : ProbabilityMeasure (Fin (n + 1) → ℝ)) :
    Measure.map (realIicToFinSucc n)
      ((realFinSuccLawToIic n μ :
        ProbabilityMeasure ((i : Set.Iic n) → ℝ)) :
        Measure ((i : Set.Iic n) → ℝ)) =
      (μ : Measure (Fin (n + 1) → ℝ)) := by
  unfold realFinSuccLawToIic
  rw [Measure.map_map]
  · have hfun :
        realIicToFinSucc n ∘ realFinSuccToIic n =
          id := by
        funext x
        exact real_iic_to_fin_succ_to_iic n x
    rw [hfun, Measure.map_id]
  all_goals fun_prop

/-- The natural `(n+1)`-prefix factors through the `Iic n` prefix exactly. -/
theorem real_nat_prefix_succ_factor
    (n : ℕ) :
    realNatPrefix (n + 1) =
      realIicToFinSucc n ∘ frestrictLe n := by
  funext x i
  rfl

namespace RealSimultaneousMarginalSubsequence

/--
The conditional continuum law recovers the original simultaneous `Fin (n+1)`
limit, with no residual presentation change.
-/
theorem conditionalGlobalMeasure_finSucc_prefix
    {Ω : Type*} [MeasurableSpace Ω]
    {family : RealCanonicalProjectiveMarginalFamily Ω}
    (diag : RealSimultaneousMarginalSubsequence family)
    (n : ℕ) :
    Measure.map (realNatPrefix (n + 1)) diag.conditionalGlobalMeasure =
      (diag.limit (n + 1) : Measure (Fin (n + 1) → ℝ)) := by
  rw [real_nat_prefix_succ_factor]
  rw [Measure.map_map]
  · rw [diag.conditionalGlobalMeasure_prefix n]
    exact realFinSuccLawToIic_map_back n (diag.limit (n + 1))
  all_goals fun_prop

end RealSimultaneousMarginalSubsequence

end RequestProject.YangMills

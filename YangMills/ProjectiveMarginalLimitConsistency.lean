import Mathlib
import YangMills.CanonicalProjectiveMarginals

/-!
# Simultaneous subsequences and compatibility of projective marginal limits

Once one subsequence works for every selected finite marginal, compatibility of
its weak limits is no longer an independent physical assumption.  The finite
cutoff laws are canonically projective, finite prefix projection is continuous,
and the continuous mapping theorem transports the larger marginal limit to the
smaller one.  Hausdorffness of weak convergence on Euclidean spaces identifies
the two limits.

The genuinely remaining diagonal step is therefore isolated as existence of a
`RealSimultaneousMarginalSubsequence`.
-/

open Filter Set MeasureTheory

namespace RequestProject.YangMills

/-- One cutoff subsequence along which every selected finite marginal converges. -/
structure RealSimultaneousMarginalSubsequence
    {Ω : Type*} [MeasurableSpace Ω]
    (family : RealCanonicalProjectiveMarginalFamily Ω) where
  subsequence : ℕ → ℕ
  strictMono : StrictMono subsequence
  limit : (m : ℕ) → ProbabilityMeasure (Fin m → ℝ)
  converges :
    ∀ m : ℕ,
      Tendsto (family.marginal m ∘ subsequence)
        atTop (𝓝 (limit m))

/-- The exact D3.3 diagonal-extraction obligation. -/
def RealDiagonalSubsequenceExistenceObligation
    {Ω : Type*} [MeasurableSpace Ω]
    (family : RealCanonicalProjectiveMarginalFamily Ω) : Prop :=
  Nonempty (RealSimultaneousMarginalSubsequence family)

namespace RealSimultaneousMarginalSubsequence

/--
D3.4 closes automatically after D3.3: all simultaneous weak marginal limits
inherit the finite-cutoff prefix identities.
-/
theorem limit_consistent
    {Ω : Type*} [MeasurableSpace Ω]
    {family : RealCanonicalProjectiveMarginalFamily Ω}
    (diag : RealSimultaneousMarginalSubsequence family)
    (m n : ℕ) (h : m ≤ n) :
    realFinPrefixMap m n h (diag.limit n) = diag.limit m := by
  have hMap :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (family.marginal n ∘ diag.subsequence)
      (diag.limit n)
      (diag.converges n)
      (real_fin_prefix_projection_continuous m n h)
  have hSeq :
      (fun r =>
        realFinPrefixMap m n h
          (family.marginal n (diag.subsequence r))) =
      (family.marginal m ∘ diag.subsequence) := by
    funext r
    exact family.finiteCutoffConsistency' m n h (diag.subsequence r)
  have hMapped :
      Tendsto (family.marginal m ∘ diag.subsequence)
        atTop (𝓝 (realFinPrefixMap m n h (diag.limit n))) := by
    simpa [realFinPrefixMap, Function.comp_def, hSeq] using hMap
  exact tendsto_nhds_unique hMapped (diag.converges m)

/-- All selected weak limits form a canonically prefix-consistent family. -/
theorem all_limits_consistent
    {Ω : Type*} [MeasurableSpace Ω]
    {family : RealCanonicalProjectiveMarginalFamily Ω}
    (diag : RealSimultaneousMarginalSubsequence family) :
    ∀ (m n : ℕ) (h : m ≤ n),
      realFinPrefixMap m n h (diag.limit n) = diag.limit m := by
  intro m n h
  exact diag.limit_consistent m n h

end RealSimultaneousMarginalSubsequence

end RequestProject.YangMills

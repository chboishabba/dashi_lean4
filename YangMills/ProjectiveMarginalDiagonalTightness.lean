import Mathlib
import YangMills.CanonicalProjectiveMarginals
import YangMills.ProjectiveMarginalLimitConsistency

/-!
# Simultaneous marginal convergence from coordinatewise tightness

Instead of repeatedly extracting and hand-diagonalizing subsequences, package
all finite-dimensional laws at cutoff `k` as one point of the dependent product

  Π m, ProbabilityMeasure (Fin m → ℝ).

For each coordinate `m`, Prokhorov makes the closure of the range compact.
Tychonoff makes the product of those compact closures compact.  Compactness
then extracts one strict subsequence in the product topology, and convergence
in the product topology is exactly coordinatewise weak convergence.

Thus D3.3 is a theorem from the already-selected per-marginal tightness; it is
not an additional physical assumption.
-/

open Filter Set MeasureTheory

namespace RequestProject.YangMills

/-- All selected finite-dimensional laws at one cutoff, as one product point. -/
def realAllMarginals
    {Ω : Type*} [MeasurableSpace Ω]
    (family : RealCanonicalProjectiveMarginalFamily Ω)
    (k : ℕ) :
    (m : ℕ) → ProbabilityMeasure (Fin m → ℝ) :=
  fun m => family.marginal m k

/--
Coordinatewise tightness yields one strict cutoff subsequence along which every
finite marginal converges simultaneously.
-/
theorem exists_simultaneous_marginal_subsequence_of_tight
    {Ω : Type*} [MeasurableSpace Ω]
    (family : RealCanonicalProjectiveMarginalFamily Ω)
    (hTight :
      ∀ m : ℕ,
        IsTightMeasureSet
          {ν : Measure (Fin m → ℝ) |
            ∃ p ∈ Set.range (family.marginal m),
              ((p : ProbabilityMeasure (Fin m → ℝ)) :
                Measure (Fin m → ℝ)) = ν}) :
    Nonempty (RealSimultaneousMarginalSubsequence family) := by
  let K : Set ((m : ℕ) → ProbabilityMeasure (Fin m → ℝ)) :=
    {x | ∀ m, x m ∈ closure (Set.range (family.marginal m))}
  have hCoordinateCompact :
      ∀ m : ℕ, IsCompact (closure (Set.range (family.marginal m))) := by
    intro m
    exact isCompact_closure_of_isTightMeasureSet (hTight m)
  have hCompact : IsCompact K := by
    simpa [K] using isCompact_pi_infinite hCoordinateCompact
  have hMem : ∀ k : ℕ, realAllMarginals family k ∈ K := by
    intro k m
    exact subset_closure (Set.mem_range_self k)
  rcases hCompact.tendsto_subseq hMem with
    ⟨limit, _hLimit, φ, hφ, hconv⟩
  refine ⟨{
    subsequence := φ
    strictMono := hφ
    limit := limit
    converges := ?_ }⟩
  intro m
  have hm := (tendsto_pi_nhds.mp hconv) m
  simpa [realAllMarginals, Function.comp_def] using hm

/--
Canonical projective consistency of all simultaneous limits now follows with no
new source hypothesis.
-/
theorem exists_simultaneous_consistent_marginal_limits_of_tight
    {Ω : Type*} [MeasurableSpace Ω]
    (family : RealCanonicalProjectiveMarginalFamily Ω)
    (hTight :
      ∀ m : ℕ,
        IsTightMeasureSet
          {ν : Measure (Fin m → ℝ) |
            ∃ p ∈ Set.range (family.marginal m),
              ((p : ProbabilityMeasure (Fin m → ℝ)) :
                Measure (Fin m → ℝ)) = ν}) :
    ∃ diag : RealSimultaneousMarginalSubsequence family,
      ∀ (m n : ℕ) (h : m ≤ n),
        realFinPrefixMap m n h (diag.limit n) = diag.limit m := by
  rcases exists_simultaneous_marginal_subsequence_of_tight family hTight with
    ⟨diag⟩
  exact ⟨diag, diag.all_limits_consistent⟩

end RequestProject.YangMills

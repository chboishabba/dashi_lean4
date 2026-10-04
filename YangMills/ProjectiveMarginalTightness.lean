import Mathlib
import YangMills.ContinuumProkhorov

/-!
# D3 projective finite-marginal compactness producer

This is the countable finite-marginal alternative to a single global coercive
observable.  Every marginal is an actual `ProbabilityMeasure` on a finite real
coordinate space and carries its own uniform tightness theorem.  Prokhorov then
extracts a weakly convergent subsequence for every fixed marginal.

Crucially, this file does NOT claim that the independently extracted
subsequences are already diagonal-compatible, and it does NOT postulate the
countable-product continuum measure.  The final projective-limit existence
statement is exposed as a named obligation on the candidate marginal limits.
-/

open Filter Set MeasureTheory

namespace RequestProject.YangMills

/-- A countable family of actual finite-dimensional marginal laws with tightness. -/
structure RealProjectiveMarginalTightnessProducer where
  marginal : (m : ℕ) → ℕ → ProbabilityMeasure (Fin m → ℝ)
  tight :
    ∀ m : ℕ,
      IsTightMeasureSet
        {ν : Measure (Fin m → ℝ) |
          ∃ p ∈ Set.range (marginal m),
            ((p : ProbabilityMeasure (Fin m → ℝ)) :
              Measure (Fin m → ℝ)) = ν}

/--
For every fixed finite marginal, D3 gives a genuine Prokhorov subsequence and
an actual probability-measure weak limit.  This theorem intentionally does not
claim that the returned subsequences are the same for all `m`.
-/
theorem exists_each_real_finite_marginal_weak_subsequence
    (producer : RealProjectiveMarginalTightnessProducer) :
    ∀ m : ℕ,
      ∃ μ∞ : ProbabilityMeasure (Fin m → ℝ),
        ∃ φ : ℕ → ℕ,
          StrictMono φ ∧
          Tendsto (producer.marginal m ∘ φ) atTop (𝓝 μ∞) := by
  intro m
  exact exists_weakly_convergent_subsequence_of_tight
    (producer.marginal m) (producer.tight m)

/-- Prefix projection from the countable real product to its first `m` coordinates. -/
def realSequencePrefix
    (m : ℕ) : (ℕ → ℝ) → (Fin m → ℝ) :=
  fun x i => x i.1

/-- The finite prefix projection is measurable in the product Borel structures. -/
theorem real_sequence_prefix_measurable
    (m : ℕ) : Measurable (realSequencePrefix m) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply i.1

/--
The honest remaining D3 projective-limit theorem.  A solution provides one
probability law on the countable product whose every finite prefix pushforward
is the selected marginal limit.

Keeping this as a proposition prevents per-marginal tightness from being
misreported as a constructed continuum measure.
-/
def RealProjectiveLimitExistenceObligation
    (limits : (m : ℕ) → ProbabilityMeasure (Fin m → ℝ)) : Prop :=
  ∃ μ∞ : ProbabilityMeasure (ℕ → ℝ),
    ∀ m : ℕ,
      Measure.map (realSequencePrefix m)
        (((μ∞ : ProbabilityMeasure (ℕ → ℝ)) : Measure (ℕ → ℝ))) =
      (((limits m : ProbabilityMeasure (Fin m → ℝ)) :
        Measure (Fin m → ℝ)))

/--
A complete D3 package separates finite-marginal limits, projective consistency,
and the still-global existence theorem.
-/
structure RealProjectiveMarginalLimitCandidate where
  limit : (m : ℕ) → ProbabilityMeasure (Fin m → ℝ)
  consistentPrefix :
    ∀ (m n : ℕ), m ≤ n →
      ∃ projection : (Fin n → ℝ) → (Fin m → ℝ),
        Measurable projection ∧
        Measure.map projection
          (((limit n : ProbabilityMeasure (Fin n → ℝ)) :
            Measure (Fin n → ℝ))) =
          (((limit m : ProbabilityMeasure (Fin m → ℝ)) :
            Measure (Fin m → ℝ)))

/-- The candidate is globally realized exactly when the named projective-limit obligation holds. -/
def RealProjectiveMarginalLimitCandidate.globallyRealized
    (candidate : RealProjectiveMarginalLimitCandidate) : Prop :=
  RealProjectiveLimitExistenceObligation candidate.limit

end RequestProject.YangMills

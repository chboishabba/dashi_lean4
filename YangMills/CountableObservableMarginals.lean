import Mathlib
import YangMills.CanonicalProjectiveMarginals

/-!
# Canonical finite marginals from one countable selected observable family

The physical D3 family is most naturally specified by one countable sequence of
real scalar cylinder observables.  Its `m`-dimensional marginal is the first
`m` observables evaluated on the same cutoff configuration.  Prefix consistency
is then definitional rather than another source theorem.
-/

open MeasureTheory

namespace RequestProject.YangMills

/-- First `m` coordinates of one countable scalar observable family. -/
def countableObservablePrefix
    {Ω : Type*}
    (observable : ℕ → Ω → ℝ)
    (m : ℕ) : Ω → (Fin m → ℝ) :=
  fun x i => observable i.1 x

/-- Measurability of every scalar observable gives measurability of every finite prefix. -/
theorem countable_observable_prefix_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (observable : ℕ → Ω → ℝ)
    (hObservable : ∀ i, Measurable (observable i))
    (m : ℕ) :
    Measurable (countableObservablePrefix observable m) := by
  apply measurable_pi_lambda
  intro i
  exact hObservable i.1

/-- Prefix projection of a longer selected vector is literally the shorter selected vector. -/
theorem countable_observable_prefix_projective
    {Ω : Type*}
    (observable : ℕ → Ω → ℝ)
    (m n : ℕ) (h : m ≤ n) :
    realFinPrefixProjection m n h ∘ countableObservablePrefix observable n =
      countableObservablePrefix observable m := by
  funext x i
  rfl

/--
One cutoff-law sequence plus one countable selected scalar observable sequence
canonically generates the entire D3 finite-dimensional projective family.
-/
noncomputable def countableObservableMarginalFamily
    {Ω : Type*} [MeasurableSpace Ω]
    (cutoffLaw : ℕ → ProbabilityMeasure Ω)
    (observable : ℕ → Ω → ℝ)
    (hObservable : ∀ i, Measurable (observable i)) :
    RealCanonicalProjectiveMarginalFamily Ω where
  cutoffLaw := cutoffLaw
  observable := countableObservablePrefix observable
  observableMeasurable := countable_observable_prefix_measurable observable hObservable
  finiteCutoffConsistency := by
    intro m n h k
    unfold realFinPrefixMap RealCanonicalProjectiveMarginalFamily.marginal
    rw [ProbabilityMeasure.map_map]
    · have hfun := countable_observable_prefix_projective observable m n h
      rw [hfun]
    all_goals fun_prop

/-- The resulting marginal is exactly the law of the selected finite prefix. -/
theorem countableObservableMarginalFamily_marginal
    {Ω : Type*} [MeasurableSpace Ω]
    (cutoffLaw : ℕ → ProbabilityMeasure Ω)
    (observable : ℕ → Ω → ℝ)
    (hObservable : ∀ i, Measurable (observable i))
    (m k : ℕ) :
    (countableObservableMarginalFamily cutoffLaw observable hObservable).marginal m k =
      (cutoffLaw k).map
        (countable_observable_prefix_measurable observable hObservable m).aemeasurable := rfl

end RequestProject.YangMills

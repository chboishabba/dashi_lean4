import Mathlib
import YangMills.ProjectiveMarginalTightness

/-!
# Canonical finite-dimensional marginals from one selected cutoff family

D3 must not allow independently selected finite-dimensional measures.  This
file fixes one cutoff law and one nested countable observable family.  Every
finite marginal is the pushforward of that SAME cutoff law.

The finite-cutoff projective identity is carried explicitly because it is a
physical/source property of the selected observable family.  The prefix map
itself is canonical and continuous, so once one simultaneous subsequence is
available, compatibility of weak limits can be proved by the continuous
mapping theorem rather than postulated again.
-/

open Filter Set MeasureTheory

namespace RequestProject.YangMills

/-- Canonical restriction from `n` real coordinates to the first `m`. -/
def realFinPrefixProjection
    (m n : ℕ) (h : m ≤ n) :
    (Fin n → ℝ) → (Fin m → ℝ) :=
  fun x i => x ⟨i.1, lt_of_lt_of_le i.2 h⟩

/-- Prefix restriction is continuous in the product topology. -/
theorem real_fin_prefix_projection_continuous
    (m n : ℕ) (h : m ≤ n) :
    Continuous (realFinPrefixProjection m n h) := by
  fun_prop

/-- Prefix restriction is measurable for the product Borel structures. -/
theorem real_fin_prefix_projection_measurable
    (m n : ℕ) (h : m ≤ n) :
    Measurable (realFinPrefixProjection m n h) :=
  (real_fin_prefix_projection_continuous m n h).measurable

/-- Push a probability law forward along the canonical finite prefix map. -/
noncomputable def realFinPrefixMap
    (m n : ℕ) (h : m ≤ n)
    (μ : ProbabilityMeasure (Fin n → ℝ)) :
    ProbabilityMeasure (Fin m → ℝ) :=
  μ.map (real_fin_prefix_projection_measurable m n h).aemeasurable

/--
One selected cutoff probability family together with one nested countable
family of real observables.  `finiteCutoffConsistency` is the exact D3.4
identity at finite cutoff; it is not inferred from notation.
-/
structure RealCanonicalProjectiveMarginalFamily
    (Ω : Type*) [MeasurableSpace Ω] where
  cutoffLaw : ℕ → ProbabilityMeasure Ω
  observable : (m : ℕ) → Ω → (Fin m → ℝ)
  observableMeasurable : ∀ m, Measurable (observable m)
  finiteCutoffConsistency :
    ∀ (m n : ℕ) (h : m ≤ n) (k : ℕ),
      realFinPrefixMap m n h
        ((cutoffLaw k).map (observableMeasurable n).aemeasurable) =
      (cutoffLaw k).map (observableMeasurable m).aemeasurable

namespace RealCanonicalProjectiveMarginalFamily

/-- The actual selected `m`-dimensional law at cutoff `k`. -/
noncomputable def marginal
    {Ω : Type*} [MeasurableSpace Ω]
    (family : RealCanonicalProjectiveMarginalFamily Ω)
    (m k : ℕ) : ProbabilityMeasure (Fin m → ℝ) :=
  (family.cutoffLaw k).map
    (family.observableMeasurable m).aemeasurable

/-- Read the finite-cutoff projective identity using the canonical marginal name. -/
theorem finiteCutoffConsistency'
    {Ω : Type*} [MeasurableSpace Ω]
    (family : RealCanonicalProjectiveMarginalFamily Ω)
    (m n : ℕ) (h : m ≤ n) (k : ℕ) :
    realFinPrefixMap m n h (family.marginal n k) =
      family.marginal m k := by
  exact family.finiteCutoffConsistency m n h k

/-- Forgetting the common source still yields the previous per-marginal API. -/
def toTightnessProducer
    {Ω : Type*} [MeasurableSpace Ω]
    (family : RealCanonicalProjectiveMarginalFamily Ω)
    (hTight :
      ∀ m : ℕ,
        IsTightMeasureSet
          {ν : Measure (Fin m → ℝ) |
            ∃ p ∈ Set.range (family.marginal m),
              ((p : ProbabilityMeasure (Fin m → ℝ)) :
                Measure (Fin m → ℝ)) = ν}) :
    RealProjectiveMarginalTightnessProducer where
  marginal := family.marginal
  tight := hTight

end RealCanonicalProjectiveMarginalFamily

end RequestProject.YangMills

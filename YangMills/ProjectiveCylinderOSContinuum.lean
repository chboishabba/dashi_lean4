import Mathlib
import YangMills.CountableObservableNormMomentContinuum

/-!
# Projective finite-prefix OS positivity at the continuum limit

The bounded/countable D route constructs one simultaneous subsequence whose
every finite observable marginal converges weakly.  Therefore any bounded
continuous finite-prefix reflected Gram observable that is nonnegative in
expectation at every selected cutoff remains nonnegative under the corresponding
continuum marginal.

This is the E1 bridge needed by the bounded-cylinder route.  It does not yet
construct the OS Hilbert completion or translation semigroup.
-/

open Filter MeasureTheory

namespace RequestProject.YangMills

namespace RealCountableObservableNormMomentSource

/-- A cutoff-uniform nonnegative expectation passes to the selected finite-prefix weak limit. -/
theorem diagonal_limit_nonnegative
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableNormMomentSource Ω)
    (m : ℕ)
    (observable : BoundedContinuousFunction (Fin m → ℝ) ℝ)
    (hcutoff : ∀ k : ℕ,
      0 ≤ ∫ x, observable x
        ∂(((source.family.marginal m (source.diagonal.subsequence k) :
          ProbabilityMeasure (Fin m → ℝ)) : Measure (Fin m → ℝ)))) :
    0 ≤ ∫ x, observable x
      ∂(((source.diagonal.limit m : ProbabilityMeasure (Fin m → ℝ)) :
        Measure (Fin m → ℝ))) := by
  have hconv :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto).1
      (source.diagonal_converges m) observable
  exact ge_of_tendsto hconv (Filter.Eventually.of_forall hcutoff)

/--
Finite-family OS2 specialization on one selected prefix.  The reflected Gram
sum is supplied as the SAME bounded continuous prefix observable at cutoff and
limit; no replacement continuum kernel is selected.
-/
theorem diagonal_limit_os2_gram
    {Ω Test : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableNormMomentSource Ω)
    (m r : ℕ)
    (tests : Fin r → Test)
    (coeff : Fin r → ℝ)
    (reflectedProduct : Test → Test →
      BoundedContinuousFunction (Fin m → ℝ) ℝ)
    (hcutoff : ∀ k : ℕ,
      0 ≤ ∫ x,
        (∑ i : Fin r, ∑ j : Fin r,
          (coeff i * coeff j) • reflectedProduct (tests i) (tests j)) x
        ∂(((source.family.marginal m (source.diagonal.subsequence k) :
          ProbabilityMeasure (Fin m → ℝ)) : Measure (Fin m → ℝ)))) :
    0 ≤ ∫ x,
      (∑ i : Fin r, ∑ j : Fin r,
        (coeff i * coeff j) • reflectedProduct (tests i) (tests j)) x
      ∂(((source.diagonal.limit m : ProbabilityMeasure (Fin m → ℝ)) :
        Measure (Fin m → ℝ))) := by
  let gram : BoundedContinuousFunction (Fin m → ℝ) ℝ :=
    ∑ i : Fin r, ∑ j : Fin r,
      (coeff i * coeff j) • reflectedProduct (tests i) (tests j)
  exact source.diagonal_limit_nonnegative m gram hcutoff

/--
All finite-prefix bounded cylinder Gram inequalities can be carried at once.
This is the projective observable-algebra version of continuum OS positivity.
-/
def ProjectiveCylinderOSPositive
    {Ω Test : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableNormMomentSource Ω)
    (reflectedProduct : ∀ m, Test → Test →
      BoundedContinuousFunction (Fin m → ℝ) ℝ) : Prop :=
  ∀ (m r : ℕ) (tests : Fin r → Test) (coeff : Fin r → ℝ),
    0 ≤ ∫ x,
      (∑ i : Fin r, ∑ j : Fin r,
        (coeff i * coeff j) • reflectedProduct m (tests i) (tests j)) x
      ∂(((source.diagonal.limit m : ProbabilityMeasure (Fin m → ℝ)) :
        Measure (Fin m → ℝ)))

/-- Cutoff OS2 on every selected prefix compiles to projective continuum cylinder OS positivity. -/
theorem projective_cylinder_os_positive_of_cutoff
    {Ω Test : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableNormMomentSource Ω)
    (reflectedProduct : ∀ m, Test → Test →
      BoundedContinuousFunction (Fin m → ℝ) ℝ)
    (hcutoff :
      ∀ (m r : ℕ) (tests : Fin r → Test) (coeff : Fin r → ℝ) (k : ℕ),
        0 ≤ ∫ x,
          (∑ i : Fin r, ∑ j : Fin r,
            (coeff i * coeff j) •
              reflectedProduct m (tests i) (tests j)) x
          ∂(((source.family.marginal m (source.diagonal.subsequence k) :
            ProbabilityMeasure (Fin m → ℝ)) : Measure (Fin m → ℝ)))) :
    ProjectiveCylinderOSPositive source reflectedProduct := by
  intro m r tests coeff
  exact source.diagonal_limit_os2_gram m r tests coeff
    (reflectedProduct m) (hcutoff m r tests coeff)

end RealCountableObservableNormMomentSource

end RequestProject.YangMills

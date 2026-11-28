import Mathlib
import Mathlib.Analysis.InnerProductSpace.Completion
import YangMills.OSGramHilbertCompletion
import YangMills.OSGramQuotientTranslation

/-!
# Extend OS Gram contractions to the reconstructed Hilbert completion

A positive-time translation that is contractive for the reflected Gram form
already descends to the null quotient.  With the canonical quotient norm now
installed, the descended map is norm-contracting, hence continuous, and extends
uniquely to the Hilbert completion.

This closes the generic bounded-extension part of E2.  Strong continuity,
self-adjoint semigroup structure in physical Euclidean time, and the generator
identification remain the analytic OS reconstruction boundary.
-/

namespace RequestProject.YangMills

namespace OSGramData

/-- Algebraic quotient translation written on the bundled pre-Hilbert space. -/
def quotientTranslation
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V)
    (T : V →ₗ[ℝ] V)
    (hContract : ∀ v : V,
      data.gram (T v) (T v) ≤ data.gram v v) :
    data.PreHilbert →ₗ[ℝ] data.PreHilbert :=
  osGramQuotientTranslation
    data.gram data.positive data.symmetric T hContract

/-- The descended quotient translation is a contraction in the induced OS norm. -/
theorem quotientTranslation_norm_le
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V)
    (T : V →ₗ[ℝ] V)
    (hContract : ∀ v : V,
      data.gram (T v) (T v) ≤ data.gram v v)
    (q : data.PreHilbert) :
    ‖data.quotientTranslation T hContract q‖ ≤ ‖q‖ := by
  have hsquares :
      ‖data.quotientTranslation T hContract q‖ ^ 2 ≤ ‖q‖ ^ 2 := by
    rw [InnerProductSpace.norm_sq_eq_re_inner,
      InnerProductSpace.norm_sq_eq_re_inner]
    refine Quotient.inductionOn q ?_
    intro v
    change data.gram (T v) (T v) ≤ data.gram v v
    exact hContract v
  nlinarith [norm_nonneg (data.quotientTranslation T hContract q), norm_nonneg q]

/-- The quotient translation as a bounded operator of norm at most one. -/
noncomputable def preHilbertTranslation
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V)
    (T : V →ₗ[ℝ] V)
    (hContract : ∀ v : V,
      data.gram (T v) (T v) ≤ data.gram v v) :
    data.PreHilbert →L[ℝ] data.PreHilbert :=
  (data.quotientTranslation T hContract).mkContinuous 1 fun q => by
    simpa using data.quotientTranslation_norm_le T hContract q

/-- Canonical extension of a Gram-contractive translation to the completed OS Hilbert space. -/
noncomputable def hilbertTranslation
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V)
    (T : V →ₗ[ℝ] V)
    (hContract : ∀ v : V,
      data.gram (T v) (T v) ≤ data.gram v v) :
    data.Hilbert →L[ℝ] data.Hilbert :=
  (data.preHilbertTranslation T hContract).completion

/-- On the dense quotient image the Hilbert extension is literally the descended translation. -/
theorem hilbertTranslation_coe
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V)
    (T : V →ₗ[ℝ] V)
    (hContract : ∀ v : V,
      data.gram (T v) (T v) ≤ data.gram v v)
    (q : data.PreHilbert) :
    data.hilbertTranslation T hContract
        (UniformSpace.Completion.coe q) =
      UniformSpace.Completion.coe
        (data.quotientTranslation T hContract q) := by
  simp [hilbertTranslation, preHilbertTranslation, quotientTranslation]

end OSGramData

end RequestProject.YangMills

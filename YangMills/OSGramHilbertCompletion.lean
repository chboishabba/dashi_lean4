import Mathlib
import Mathlib.Analysis.InnerProductSpace.Completion
import YangMills.OSGramQuotientInnerProduct

/-!
# Canonical Hilbert completion of the OS quotient

Bundle the reflected positive semidefinite Gram form together with positivity
and symmetry, quotient by its radical, install the positive-definite inner
product-induced norm, and take Mathlib's uniform completion.  This is the
canonical Hilbert-space construction underlying E2 before physical Euclidean
time translations are extended and identified with a self-adjoint generator.
-/

namespace RequestProject.YangMills

/-- Physical positive-time Gram data sufficient for the algebraic OS Hilbert construction. -/
structure OSGramData (V : Type*) [AddCommGroup V] [Module ℝ V] where
  gram : LinearMap.BilinForm ℝ V
  positive : ∀ v : V, 0 ≤ gram v v
  symmetric : gram.IsSymm

namespace OSGramData

/-- Null-quotiented positive-time test space. -/
abbrev PreHilbert
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V) :=
  V ⧸ data.gram.ker

/-- Positive-definite inner product core inherited from the reflected Gram form. -/
noncomputable def innerProductCore
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V) :
    InnerProductSpace.Core ℝ data.PreHilbert :=
  osGramQuotientInnerProductCore data.gram data.positive data.symmetric

noncomputable instance preHilbertNormedAddCommGroup
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V) :
    NormedAddCommGroup data.PreHilbert :=
  data.innerProductCore.toNormedAddCommGroup

noncomputable instance preHilbertInnerProductSpace
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V) :
    InnerProductSpace ℝ data.PreHilbert :=
  InnerProductSpace.ofCore data.innerProductCore

/-- Canonical OS Hilbert space: completion of the null-quotiented positive-time tests. -/
abbrev Hilbert
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V) :=
  UniformSpace.Completion data.PreHilbert

/-- The canonical embedding of the pre-Hilbert quotient into its completion. -/
noncomputable def toHilbert
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V) :
    data.PreHilbert →ₗ[ℝ] data.Hilbert :=
  UniformSpace.Completion.coeLM ℝ data.PreHilbert

/-- The canonical pre-Hilbert image is dense in the reconstructed Hilbert space. -/
theorem denseRange_toHilbert
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V) :
    DenseRange data.toHilbert :=
  UniformSpace.Completion.denseRange_coe

end OSGramData

end RequestProject.YangMills

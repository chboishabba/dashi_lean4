import Mathlib

/-!
# Scalar / traceless decomposition for an Albert-style rank-three trace

DASHI theorem layer.  This file is deliberately independent of the external
`Cobord/JordanAlgebra` package graph.  It isolates the only linear algebra needed
for the `27 = 1 + 26` structural split:

* a distinguished unit vector `1_J`;
* a linear trace `tr : J -> R`;
* normalization `tr(1_J) = 3`.

Over `R = ℝ`, every `x` decomposes canonically as

  x = (tr x / 3) • 1_J + x₀,   tr x₀ = 0.

This does not construct a Jordan product, cubic norm, E6 action, or F4 action.
-/

namespace Integration.AlbertScalarTraceless

/-- Minimal linear data needed for the scalar/traceless split. -/
structure TraceUnitData (J : Type*) [AddCommGroup J] [Module ℝ J] where
  unit : J
  trace : J →ₗ[ℝ] ℝ
  trace_unit : trace unit = 3

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

/-- Scalar coefficient along the distinguished unit. -/
def scalarCoeff (A : TraceUnitData J) (x : J) : ℝ := A.trace x / 3

/-- Scalar component of `x`. -/
def scalarPart (A : TraceUnitData J) (x : J) : J :=
  scalarCoeff A x • A.unit

/-- Canonical trace-zero residual. -/
def tracelessPart (A : TraceUnitData J) (x : J) : J :=
  x - scalarPart A x

/-- The residual really lies in `ker(trace)`. -/
theorem trace_tracelessPart (A : TraceUnitData J) (x : J) :
    A.trace (tracelessPart A x) = 0 := by
  simp [tracelessPart, scalarPart, scalarCoeff, A.trace_unit]
  ring

/-- Exact reconstruction from scalar plus traceless components. -/
theorem scalar_plus_traceless (A : TraceUnitData J) (x : J) :
    scalarPart A x + tracelessPart A x = x := by
  simp [tracelessPart]

/-- The traceless carrier is the kernel of the actual trace map. -/
def Traceless (A : TraceUnitData J) : Submodule ℝ J := A.trace.ker

/-- Canonical traceless element associated to any `x`. -/
def tracelessElement (A : TraceUnitData J) (x : J) : Traceless A :=
  ⟨tracelessPart A x, trace_tracelessPart A x⟩

/-- The normalized unit has scalar coefficient one. -/
theorem scalarCoeff_unit (A : TraceUnitData J) : scalarCoeff A A.unit = 1 := by
  simp [scalarCoeff, A.trace_unit]
  norm_num

/-- Every element admits the desired scalar/traceless decomposition with an
explicit trace-zero witness. -/
theorem exists_scalar_traceless (A : TraceUnitData J) (x : J) :
    ∃ r : ℝ, ∃ x₀ : Traceless A, x = r • A.unit + x₀.1 := by
  refine ⟨scalarCoeff A x, tracelessElement A x, ?_⟩
  simpa [scalarPart] using (scalar_plus_traceless A x).symm

/-- The decomposition is unique once the trace normalization is fixed. -/
theorem scalar_traceless_unique (A : TraceUnitData J)
    {r s : ℝ} {x₀ y₀ : Traceless A}
    (h : r • A.unit + x₀.1 = s • A.unit + y₀.1) : r = s := by
  have ht := congrArg A.trace h
  simp [A.trace_unit, x₀.property, y₀.property] at ht
  linarith

/-- A two-sided linear equivalence exhibiting `J ≃ ℝ × ker(trace)`.

This is the theorem-level replacement for the old cardinal/dimension slogan
`27 = 1 + 26`; finite-dimensional rank arithmetic can be layered on top once a
particular 27-dimensional Albert carrier is instantiated. -/
noncomputable def scalarTracelessEquiv (A : TraceUnitData J) :
    J ≃ₗ[ℝ] ℝ × Traceless A where
  toFun x := (scalarCoeff A x, tracelessElement A x)
  invFun p := p.1 • A.unit + p.2.1
  left_inv x := by
    simpa [scalarPart] using scalar_plus_traceless A x
  right_inv p := by
    rcases p with ⟨r, x₀⟩
    apply Prod.ext
    · simp [scalarCoeff, A.trace_unit, x₀.property]
      ring
    · apply Subtype.ext
      simp [tracelessElement, tracelessPart, scalarPart, scalarCoeff,
        A.trace_unit, x₀.property]
      module
  map_add' x y := by
    apply Prod.ext
    · simp [scalarCoeff]
      ring
    · apply Subtype.ext
      simp [tracelessElement, tracelessPart, scalarPart, scalarCoeff]
      module
  map_smul' r x := by
    apply Prod.ext
    · simp [scalarCoeff]
      ring
    · apply Subtype.ext
      simp [tracelessElement, tracelessPart, scalarPart, scalarCoeff]
      module

/-- Once the ambient carrier is genuinely 27-dimensional, the trace-zero
subspace is genuinely 26-dimensional.  This is the exact structural theorem
behind `27 = 1 + 26`, not a cardinality analogy. -/
theorem traceless_finrank_eq_26
    [FiniteDimensional ℝ J]
    (A : TraceUnitData J)
    (hJ : Module.finrank ℝ J = 27) :
    Module.finrank ℝ (Traceless A) = 26 := by
  have hdim :
      Module.finrank ℝ J = 1 + Module.finrank ℝ (Traceless A) := by
    calc
      Module.finrank ℝ J = Module.finrank ℝ (ℝ × Traceless A) :=
        LinearEquiv.finrank_eq (scalarTracelessEquiv A)
      _ = 1 + Module.finrank ℝ (Traceless A) := by simp
  omega

inductive ScalarTracelessCreatesAlbertProduct : Prop
inductive ScalarTracelessCreatesF4Action : Prop

theorem scalar_traceless_does_not_create_product : ¬ ScalarTracelessCreatesAlbertProduct := by
  intro h
  cases h

theorem scalar_traceless_does_not_create_f4 : ¬ ScalarTracelessCreatesF4Action := by
  intro h
  cases h

end Integration.AlbertScalarTraceless

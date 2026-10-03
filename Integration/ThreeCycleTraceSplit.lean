import Mathlib

/-!
# Three-cycle trace splitting in characteristic two

Attribution / provenance:
* visual and conceptual prompt: JMD's supplied Frobenius-orbit diagrams;
* finite-field/Frobenius identities: standard mathematics;
* the characteristic-two three-cycle trace split proved here is generic linear algebra;
* any application to the DASHI 2B three-Tate-fibre lane is a derived cross-pollination,
  not a same-object finite-field identification.

Let `tau` be an F2-linear operator with `tau^3 = 1`.  Define

  N = 1 + tau + tau^2.

Because the coefficient field has characteristic two, `N` is idempotent.  Hence

  V = range(N) ⊕ ker(N).

On the trace-zero summand `ker(N)`, the operator satisfies

  tau^2 + tau + 1 = 0,

which is the quadratic relation underlying the F4 phase interpretation.
-/

namespace Integration.ThreeCycleTraceSplit

abbrev F2 := ZMod 2

variable {V : Type*} [AddCommGroup V] [Module F2 V]

structure ThreeCycleData where
  tau : V →ₗ[F2] V
  orderThree : ∀ x, tau (tau (tau x)) = x

open ThreeCycleData

/-- The three-cycle orbit sum / trace operator `1 + tau + tau^2`. -/
def threeTrace (D : ThreeCycleData (V := V)) : V →ₗ[F2] V :=
  LinearMap.id + D.tau + D.tau.comp D.tau

@[simp]
theorem threeTrace_apply (D : ThreeCycleData (V := V)) (x : V) :
    threeTrace D x = x + D.tau x + D.tau (D.tau x) := by
  rfl

/-- The orbit sum is fixed by the three-cycle. -/
theorem tau_threeTrace_fixed (D : ThreeCycleData (V := V)) (x : V) :
    D.tau (threeTrace D x) = threeTrace D x := by
  rw [threeTrace_apply]
  simp only [map_add]
  rw [D.orderThree]
  module

/-- On a fixed vector the characteristic-two three-trace is the identity:
`x+x+x=x`. -/
theorem threeTrace_of_fixed
    (D : ThreeCycleData (V := V)) (x : V)
    (hx : D.tau x = x) :
    threeTrace D x = x := by
  rw [threeTrace_apply, hx]
  simp only [hx]
  module

/-- Pointwise idempotence of the orbit-sum projector. -/
theorem threeTrace_idempotent_apply
    (D : ThreeCycleData (V := V)) (x : V) :
    threeTrace D (threeTrace D x) = threeTrace D x :=
  threeTrace_of_fixed D (threeTrace D x) (tau_threeTrace_fixed D x)

/-- Ring-level idempotence, so Mathlib's projection machinery applies. -/
theorem threeTrace_isIdempotent
    (D : ThreeCycleData (V := V)) :
    IsIdempotentElem (threeTrace D) := by
  rw [IsIdempotentElem, LinearMap.ext_iff]
  intro x
  simp only [Module.End.mul_apply]
  exact threeTrace_idempotent_apply D x

/-- Canonical direct-sum decomposition into invariant image and trace-zero kernel. -/
theorem threeTrace_range_ker_isCompl
    (D : ThreeCycleData (V := V)) :
    IsCompl (LinearMap.range (threeTrace D)) (LinearMap.ker (threeTrace D)) :=
  (threeTrace_isIdempotent D).isCompl

/-- Every image vector is fixed by the C3 generator. -/
theorem range_threeTrace_is_fixed
    (D : ThreeCycleData (V := V))
    {y : V} (hy : y ∈ LinearMap.range (threeTrace D)) :
    D.tau y = y := by
  rcases hy with ⟨x, rfl⟩
  exact tau_threeTrace_fixed D x

/-- Every fixed vector is hit by the trace projector. -/
theorem fixed_mem_range_threeTrace
    (D : ThreeCycleData (V := V))
    {y : V} (hy : D.tau y = y) :
    y ∈ LinearMap.range (threeTrace D) := by
  refine ⟨y, ?_⟩
  exact threeTrace_of_fixed D y hy

/-- The image of the three-trace is exactly the invariant subspace, expressed
pointwise without introducing a second submodule owner. -/
theorem mem_range_threeTrace_iff_fixed
    (D : ThreeCycleData (V := V)) (y : V) :
    y ∈ LinearMap.range (threeTrace D) ↔ D.tau y = y := by
  constructor
  · exact range_threeTrace_is_fixed D
  · exact fixed_mem_range_threeTrace D

/-- On the trace-zero piece, tau satisfies the irreducible quadratic
`X^2 + X + 1`.  This is the exact algebraic seam to an F4-module structure;
no particular finite-field scalar action is chosen here. -/
theorem quadratic_phase_relation_of_mem_ker
    (D : ThreeCycleData (V := V))
    {x : V} (hx : x ∈ LinearMap.ker (threeTrace D)) :
    D.tau (D.tau x) + D.tau x + x = 0 := by
  have hx' : threeTrace D x = 0 := by
    simpa using hx
  rw [threeTrace_apply] at hx'
  calc
    D.tau (D.tau x) + D.tau x + x =
        x + D.tau x + D.tau (D.tau x) := by abel
    _ = 0 := hx'

/-- The trace-zero subspace is tau-stable. -/
theorem ker_threeTrace_tau_stable
    (D : ThreeCycleData (V := V))
    {x : V} (hx : x ∈ LinearMap.ker (threeTrace D)) :
    D.tau x ∈ LinearMap.ker (threeTrace D) := by
  have hx' : threeTrace D x = 0 := by simpa using hx
  have hcomm : threeTrace D (D.tau x) = D.tau (threeTrace D x) := by
    rw [threeTrace_apply, threeTrace_apply]
    simp only [map_add]
    rw [D.orderThree]
    module
  rw [hcomm, hx']
  simp

/-- Finite-dimensional dimension accounting for the canonical split. -/
theorem finrank_range_add_finrank_ker
    (D : ThreeCycleData (V := V))
    [FiniteDimensional F2 V] :
    Module.finrank F2 (LinearMap.range (threeTrace D))
      + Module.finrank F2 (LinearMap.ker (threeTrace D))
      = Module.finrank F2 V :=
  Submodule.finrank_add_eq_of_isCompl (threeTrace_range_ker_isCompl D)

/-- Attribution boundary: JMD supplied the Frobenius-orbit visual/conceptual
prompt, but no compiler-semantics identification is constructed by this file. -/
def jmdFrobeniusVisualPromptCredited : Bool := true

def compilerSemanticsIdentificationPaid : Bool := false

def finiteFieldSameObjectIdentificationPaid : Bool := false

end Integration.ThreeCycleTraceSplit

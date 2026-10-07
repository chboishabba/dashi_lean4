import Mathlib

/-!
# Concrete strongly-continuous OS semigroup interface

Mathlib v4.28 does not provide a ready-made C₀-semigroup/generator package for
this lane.  We therefore make the part that can be stated directly completely
concrete: actual bounded operators indexed by nonnegative real Euclidean time,
identity and additive-time composition, contraction, and pointwise strong
continuity.

A separate extension record ties this continuous family to the already-built
discrete OS transfer family.  Symmetry and positivity are bundled in a stronger
Hilbert-space record.  The unbounded self-adjoint generator theorem remains an
external functional-analytic authority rather than being replaced by a fake
bounded Hamiltonian.
-/

namespace RequestProject.YangMills

/-- A strongly continuous contraction semigroup on nonnegative Euclidean time. -/
structure OSStronglyContinuousSemigroup
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  transfer : ℝ≥0 → H →L[ℝ] H
  transfer_zero : transfer 0 = ContinuousLinearMap.id ℝ H
  transfer_add : ∀ s t : ℝ≥0,
    transfer (s + t) = (transfer s).comp (transfer t)
  contractive : ∀ t x, ‖transfer t x‖ ≤ ‖x‖
  stronglyContinuous : ∀ x : H, Continuous (fun t : ℝ≥0 => transfer t x)

namespace OSStronglyContinuousSemigroup

@[simp]
theorem zero_apply
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (S : OSStronglyContinuousSemigroup H) (x : H) :
    S.transfer 0 x = x := by
  rw [S.transfer_zero]
  rfl

/-- Exact semigroup composition on vectors. -/
theorem add_apply
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (S : OSStronglyContinuousSemigroup H) (s t : ℝ≥0) (x : H) :
    S.transfer (s + t) x = S.transfer s (S.transfer t x) := by
  rw [S.transfer_add]
  rfl

end OSStronglyContinuousSemigroup

/--
A concrete C₀ extension of one already-constructed discrete transfer family.
One lattice step is the nonnegative-real time `1`; physical units are attached
separately by the time-normalization source receipt.
-/
structure OSStronglyContinuousSemigroupExtension
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (discrete : ℕ → H →L[ℝ] H)
    extends OSStronglyContinuousSemigroup H where
  discreteAgreement : ∀ n : ℕ,
    toOSStronglyContinuousSemigroup.transfer (n : ℝ≥0) = discrete n

/--
Reflection-symmetric positive OS transfer semigroup.  These are the concrete
operator properties expected before applying the standard generator theorem.
-/
structure OSSymmetricPositiveStronglyContinuousSemigroup
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    extends OSStronglyContinuousSemigroup H where
  symmetric : ∀ t (x y : H),
    ⟪toOSStronglyContinuousSemigroup.transfer t x, y⟫_ℝ =
      ⟪x, toOSStronglyContinuousSemigroup.transfer t y⟫_ℝ
  positive : ∀ t (x : H),
    0 ≤ ⟪x, toOSStronglyContinuousSemigroup.transfer t x⟫_ℝ

/-- Symmetric/positive strongly-continuous extension of the discrete OS family. -/
structure OSSymmetricPositiveStronglyContinuousSemigroupExtension
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (discrete : ℕ → H →L[ℝ] H)
    extends OSSymmetricPositiveStronglyContinuousSemigroup H where
  discreteAgreement : ∀ n : ℕ,
    toOSSymmetricPositiveStronglyContinuousSemigroup.toOSStronglyContinuousSemigroup.transfer
      (n : ℝ≥0) = discrete n

/-- Exact remaining continuous-time source proposition once the discrete family is fixed. -/
def OSContinuousSemigroupExtensionExists
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (discrete : ℕ → H →L[ℝ] H) : Prop :=
  Nonempty (OSSymmetricPositiveStronglyContinuousSemigroupExtension discrete)

end RequestProject.YangMills

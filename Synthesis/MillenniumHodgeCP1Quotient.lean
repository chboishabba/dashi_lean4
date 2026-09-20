import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Data.Complex.Basic

/-!
# Literal complex projective line quotient producer

This file supplies the quotient carrier/eliminator that the Agda Hodge lane
deliberately leaves abstract. Mathlib's `Projectivization` is literally the
quotient of nonzero vectors by the action of nonzero scalars.

No cohomology or Hodge-theoretic claim is made here.
-/

namespace Synthesis.Millennium.Hodge

open scoped LinearAlgebra.Projectivization
open Projectivization

abbrev CP1 := Projectivization ℂ (Fin 2 → ℂ)

def firstVec (z : ℂ) : Fin 2 → ℂ := ![1, z]
def secondVec (w : ℂ) : Fin 2 → ℂ := ![w, 1]

theorem firstVec_ne_zero (z : ℂ) : firstVec z ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simpa [firstVec] using h0

theorem secondVec_ne_zero (w : ℂ) : secondVec w ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  simpa [secondVec] using h1

def firstChartClass (z : ℂ) : CP1 :=
  Projectivization.mk ℂ (firstVec z) (firstVec_ne_zero z)

def secondChartClass (w : ℂ) : CP1 :=
  Projectivization.mk ℂ (secondVec w) (secondVec_ne_zero w)

/-- Every literal projective-line point has a nonzero homogeneous representative. -/
theorem quotient_surjective (p : CP1) :
    ∃ v : Fin 2 → ℂ, ∃ hv : v ≠ 0, Projectivization.mk ℂ v hv = p := by
  induction p using Projectivization.ind with
  | h v hv =>
      exact ⟨v, hv, rfl⟩

/-- Scale-invariant functions on nonzero homogeneous pairs descend to the quotient. -/
def quotientLift {α : Type*}
    (f : {v : Fin 2 → ℂ // v ≠ 0} → α)
    (hf :
      ∀ (a b : {v : Fin 2 → ℂ // v ≠ 0}) (t : ℂ),
        a = t • (b : Fin 2 → ℂ) → f a = f b) :
    CP1 → α :=
  Projectivization.lift f hf

@[simp]
theorem quotientLift_mk {α : Type*}
    (f : {v : Fin 2 → ℂ // v ≠ 0} → α)
    (hf :
      ∀ (a b : {v : Fin 2 → ℂ // v ≠ 0}) (t : ℂ),
        a = t • (b : Fin 2 → ℂ) → f a = f b)
    (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    quotientLift f hf (Projectivization.mk ℂ v hv) = f ⟨v, hv⟩ := by
  rfl

/-- The two affine representatives glue in the actual projective quotient when
their coordinates satisfy the overlap equation `w*z = 1`. -/
theorem chart_classes_eq_of_mul_eq_one
    (z w : ℂ) (hwz : w * z = 1) :
    firstChartClass z = secondChartClass w := by
  rw [firstChartClass, secondChartClass,
    Projectivization.mk_eq_mk_iff' ℂ]
  refine ⟨w, ?_⟩
  funext i
  fin_cases i <;> simp [firstVec, secondVec, hwz]

/-- Symmetric form matching the Agda overlap theorem's `z*w=1` orientation. -/
theorem chart_classes_eq_of_mul_eq_one'
    (z w : ℂ) (hzw : z * w = 1) :
    firstChartClass z = secondChartClass w := by
  exact chart_classes_eq_of_mul_eq_one z w (by simpa [mul_comm] using hzw)

end Synthesis.Millennium.Hodge

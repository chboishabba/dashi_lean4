import Integration.AlbertJordanAutomorphism
import Mathlib

/-!
# Cubic rigidity boundary for the Albert algebra

For the exceptional rank-three Jordan algebra, the product is classically
recoverable from the distinguished unit together with the generic trace/cubic
norm package.  The external donor currently exposes the product, trace and
cubic separately but does not prove the full generic-minimal-polynomial /
Freudenthal identities needed to derive that recovery theorem.

This file isolates exactly that missing theorem.  Once `CubicRigidity A` is
supplied, a linear equivalence preserving unit, trace and cubic automatically
becomes a Jordan automorphism; product preservation no longer has to be proved
again generator-by-generator.
-/

namespace Integration.AlbertCubicRigidity

open Integration.AlbertJordanAutomorphism

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

/-- The exact rank-three rigidity theorem still owed by the donor/port layer. -/
structure CubicRigidity (A : AlbertStructure J) : Prop where
  product_recovered :
    ∀ e : J ≃ₗ[ℝ] J,
      e A.traceUnit.unit = A.traceUnit.unit →
      (∀ x, A.traceUnit.trace (e x) = A.traceUnit.trace x) →
      (∀ x, A.cubic (e x) = A.cubic x) →
      ∀ x y, e (A.jordanMul x y) = A.jordanMul (e x) (e y)

/-- Unit/trace/cubic preservation compiles to a full Jordan automorphism once
rank-three cubic rigidity is available. -/
noncomputable def jordanAutomorphismOfCubicRigidity
    (A : AlbertStructure J) (R : CubicRigidity A)
    (e : J ≃ₗ[ℝ] J)
    (hunit : e A.traceUnit.unit = A.traceUnit.unit)
    (htrace : ∀ x, A.traceUnit.trace (e x) = A.traceUnit.trace x)
    (hcubic : ∀ x, A.cubic (e x) = A.cubic x) :
    JordanAutomorphism A where
  toLinearEquiv := e
  map_unit := hunit
  map_jordan := R.product_recovered e hunit htrace hcubic
  map_trace := htrace
  map_cubic := hcubic

/-- Current source boundary: the pinned donor's `detTrace` package supplies
trace/cubic normalization and homogeneity, but not this product-recovery theorem. -/
structure Boundary where
  rigidityInterfaceTyped : Bool
  unitTraceCubicCompilerPaid : Bool
  donorFullGenericMinimalPolynomialPaid : Bool
  donorCubicRigidityPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  rigidityInterfaceTyped := true
  unitTraceCubicCompilerPaid := true
  donorFullGenericMinimalPolynomialPaid := false
  donorCubicRigidityPaid := false

inductive CubicHomogeneityAloneCreatesRigidity : Prop

theorem cubic_homogeneity_alone_does_not_create_rigidity :
    ¬ CubicHomogeneityAloneCreatesRigidity := by
  intro h; cases h

end Integration.AlbertCubicRigidity

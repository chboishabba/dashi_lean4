import Mathlib
import YangMills.OSGramNullSpace

/-!
# Positive-definite inner product on the OS null quotient

Reflection positivity gives a positive semidefinite symmetric Gram form on the
positive-time test space.  Quotienting by its radical makes the induced pairing
positive definite.  This file packages that fact as an actual
`InnerProductSpace.Core` on the OS quotient.

This closes the algebraic/norm-form part of E2.  Completion and the analytic
extension/generator of the physical time semigroup remain separate.
-/

namespace RequestProject.YangMills

/--
The reflected Gram pairing on `V ⧸ ker B` is a positive-definite real inner
product core.  No extra null-space axiom is assumed: definiteness is exactly the
previous quotient theorem.
-/
noncomputable def osGramQuotientInnerProductCore
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V)
    (hPositive : ∀ v : V, 0 ≤ B v v)
    (hSymmetric : B.IsSymm) :
    InnerProductSpace.Core ℝ (V ⧸ B.ker) where
  inner := osGramQuotientPairing B hPositive hSymmetric
  conj_inner_symm := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro vx vy
    change B vy vx = B vx vy
    exact hSymmetric.eq _ _
  re_inner_nonneg := by
    intro x
    simpa using osGramQuotientPairing_nonnegative B hPositive hSymmetric x
  add_left := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro vx vy vz
    change B (vx + vy) vz = B vx vz + B vy vz
    simp
  smul_left := by
    intro x y r
    refine Quotient.inductionOn₂ x y ?_
    intro vx vy
    change B (r • vx) vy = r * B vx vy
    simp
  definite := by
    intro x hx
    exact (osGramQuotientPairing_self_eq_zero_iff
      B hPositive hSymmetric x).mp hx

end RequestProject.YangMills

import Mathlib
import YangMills.OSGramNullSpace

/-!
# OS translation descent to the algebraic null quotient

This is the next exact E2 seam after null-equivalence preservation.  A
reflected-Gram contraction sends the radical of the positive semidefinite OS
form into itself, hence induces an honest linear endomorphism of the quotient.
No completion, strong continuity, or Hamiltonian generator is asserted here.
-/

namespace RequestProject.YangMills

/-- A reflected-Gram contraction preserves the radical as a submodule. -/
theorem osGramContraction_ker_le_comap
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V)
    (hPositive : ∀ v : V, 0 ≤ B v v)
    (hSymmetric : B.IsSymm)
    (T : V →ₗ[ℝ] V)
    (hContract : ∀ v : V, B (T v) (T v) ≤ B v v) :
    B.ker ≤ B.ker.comap T := by
  intro v hv
  have hNull : B v v = 0 :=
    (B.apply_apply_same_eq_zero_iff hPositive hSymmetric).mpr hv
  have hNullT : B (T v) (T v) = 0 :=
    os_gram_contraction_preserves_null B hPositive T hContract hNull
  exact
    (B.apply_apply_same_eq_zero_iff hPositive hSymmetric).mp hNullT

/-- The positive-time contraction descends canonically to the genuine OS quotient. -/
def osGramQuotientTranslation
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V)
    (hPositive : ∀ v : V, 0 ≤ B v v)
    (hSymmetric : B.IsSymm)
    (T : V →ₗ[ℝ] V)
    (hContract : ∀ v : V, B (T v) (T v) ≤ B v v) :
    V ⧸ B.ker →ₗ[ℝ] V ⧸ B.ker :=
  Submodule.mapQ B.ker B.ker T
    (osGramContraction_ker_le_comap B hPositive hSymmetric T hContract)

/-- On quotient classes the descended operator is literally induced by `T`. -/
theorem osGramQuotientTranslation_mk
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V)
    (hPositive : ∀ v : V, 0 ≤ B v v)
    (hSymmetric : B.IsSymm)
    (T : V →ₗ[ℝ] V)
    (hContract : ∀ v : V, B (T v) (T v) ≤ B v v)
    (v : V) :
    osGramQuotientTranslation B hPositive hSymmetric T hContract
        (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (T v) := by
  rfl

end RequestProject.YangMills

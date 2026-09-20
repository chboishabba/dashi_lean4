import Synthesis.MillenniumBSDGlobalKummerHomomorphism
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic

/-!
# Global descent map E(Q)/2E(Q) -> Sel^2

The full global Kummer law is now available.  We package it as a homomorphism
to the explicit all-place Selmer subgroup, prove that doubles are killed, and
factor through the literal quotient by 2E(Q).

This constructs the forward map in the classical 2-descent exact sequence.
It does not claim yet that the kernel is exactly 2E(Q), nor identify the
cokernel with Sha[2].
-/

namespace Synthesis.Millennium.BSD

noncomputable def totalGlobalKummerMonoidHom :
    Multiplicative RationalProjectivePoint →*
      (RatSquareClass × RatSquareClass) where
  toFun P := totalGlobalKummer P.toAdd
  map_one' := by
    simpa using totalGlobalKummer_zero
  map_mul' := by
    intro P Q
    change totalGlobalKummer (P.toAdd + Q.toAdd)
      = totalGlobalKummer P.toAdd * totalGlobalKummer Q.toAdd
    exact totalGlobalKummer_homomorphism P.toAdd Q.toAdd

noncomputable def globalKummerSelmerHom :
    Multiplicative RationalProjectivePoint →*
      explicitTwoSelmerSubgroup :=
  totalGlobalKummerMonoidHom.codRestrict
    explicitTwoSelmerSubgroup
    (fun P => totalGlobalKummer_mem_explicitTwoSelmer P.toAdd)

@[simp] theorem globalKummerSelmerHom_apply
    (P : RationalProjectivePoint) :
    ((globalKummerSelmerHom (Multiplicative.ofAdd P) :
      explicitTwoSelmerSubgroup) : RatSquareClass × RatSquareClass)
      = totalGlobalKummer P :=
  rfl

theorem totalGlobalKummer_double_eq_one
    (P : RationalProjectivePoint) :
    totalGlobalKummer (P + P) = 1 := by
  rw [totalGlobalKummer_homomorphism]
  apply Prod.ext <;>
    exact ratSquareClass_sq_eq_one _

def globalDoubleSubgroup :
    Subgroup (Multiplicative RationalProjectivePoint) where
  carrier := {x | ∃ P : RationalProjectivePoint, x.toAdd = P + P}
  one_mem' := by
    refine ⟨0, ?_⟩
    simp
  mul_mem' := by
    intro x y hx hy
    rcases hx with ⟨P, hP⟩
    rcases hy with ⟨Q, hQ⟩
    refine ⟨P + Q, ?_⟩
    simp only [Multiplicative.toAdd_mul]
    rw [hP, hQ]
    abel
  inv_mem' := by
    intro x hx
    rcases hx with ⟨P, hP⟩
    refine ⟨-P, ?_⟩
    simp only [Multiplicative.toAdd_inv]
    rw [hP]
    abel

theorem globalDoubleSubgroup_le_kummerKernel :
    globalDoubleSubgroup ≤ totalGlobalKummerMonoidHom.ker := by
  intro x hx
  rcases hx with ⟨P, hP⟩
  change totalGlobalKummer x.toAdd = 1
  rw [hP]
  exact totalGlobalKummer_double_eq_one P

theorem globalDoubleSubgroup_le_selmerKernel :
    globalDoubleSubgroup ≤ globalKummerSelmerHom.ker := by
  intro x hx
  apply Subtype.ext
  exact globalDoubleSubgroup_le_kummerKernel hx

noncomputable def globalKummerQuotientToSelmer :
    (Multiplicative RationalProjectivePoint ⧸ globalDoubleSubgroup) →*
      explicitTwoSelmerSubgroup :=
  QuotientGroup.lift
    globalDoubleSubgroup
    globalKummerSelmerHom
    globalDoubleSubgroup_le_selmerKernel

@[simp] theorem globalKummerQuotientToSelmer_mk
    (P : RationalProjectivePoint) :
    globalKummerQuotientToSelmer
      (QuotientGroup.mk' globalDoubleSubgroup (Multiplicative.ofAdd P))
      = globalKummerSelmerHom (Multiplicative.ofAdd P) := by
  rfl

def globalKummerImageSubgroup : Subgroup explicitTwoSelmerSubgroup :=
  globalKummerQuotientToSelmer.range

theorem globalKummerImageSubgroup_mem_iff
    (s : explicitTwoSelmerSubgroup) :
    s ∈ globalKummerImageSubgroup
      ↔ ∃ q : Multiplicative RationalProjectivePoint ⧸ globalDoubleSubgroup,
          globalKummerQuotientToSelmer q = s := by
  rfl

end Synthesis.Millennium.BSD

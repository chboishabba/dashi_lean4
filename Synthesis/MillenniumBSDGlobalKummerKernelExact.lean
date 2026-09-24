import Synthesis.MillenniumBSDGlobalKummerKernelHalfPoint
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic

/-!
# Exact kernel of the global two-descent Kummer map

The explicit half-point theorem supplies the missing reverse inclusion
ker(delta_Q) <= 2E(Q).  Together with the already-proved double-kernel
inclusion this identifies the kernel exactly and makes the quotient-to-Selmer
map injective.
-/

namespace Synthesis.Millennium.BSD

theorem globalDoubleSubgroup_eq_kummerKernel :
    globalDoubleSubgroup = totalGlobalKummerMonoidHom.ker := by
  apply le_antisymm
  · exact globalDoubleSubgroup_le_kummerKernel
  · intro x hx
    change totalGlobalKummer x.toAdd =
      (1 : RatSquareClass × RatSquareClass) at hx
    obtain ⟨Q, hQ⟩ :=
      totalGlobalKummer_eq_one_implies_double x.toAdd hx
    exact ⟨Q, hQ⟩

theorem globalDoubleSubgroup_eq_selmerKernel :
    globalDoubleSubgroup = globalKummerSelmerHom.ker := by
  apply le_antisymm
  · exact globalDoubleSubgroup_le_selmerKernel
  · intro x hx
    change globalKummerSelmerHom x = 1 at hx
    have hval := congrArg
      (fun s : explicitTwoSelmerSubgroup =>
        (s : RatSquareClass × RatSquareClass)) hx
    change totalGlobalKummer x.toAdd =
      (1 : RatSquareClass × RatSquareClass) at hval
    rw [globalDoubleSubgroup_eq_kummerKernel]
    exact hval

theorem globalKummerQuotientToSelmer_injective :
    Function.Injective globalKummerQuotientToSelmer := by
  exact (QuotientGroup.injective_lift_iff
    globalKummerSelmerHom
    globalDoubleSubgroup_le_selmerKernel).2
      globalDoubleSubgroup_eq_selmerKernel

noncomputable def globalKummerQuotientEquivImage :
    (Multiplicative RationalProjectivePoint ⧸ globalDoubleSubgroup) ≃*
      globalKummerImageSubgroup := by
  let f := globalKummerQuotientToSelmer.rangeRestrict
  exact MulEquiv.ofBijective f
    ⟨
      Function.Injective.comp
        globalKummerQuotientToSelmer_injective
        (fun _ _ h => Subtype.ext h),
      f.rangeRestrict_surjective
    ⟩

theorem globalKummerQuotient_eq_one_iff
    (q : Multiplicative RationalProjectivePoint ⧸ globalDoubleSubgroup) :
    globalKummerQuotientToSelmer q = 1 ↔ q = 1 := by
  constructor
  · intro h
    exact globalKummerQuotientToSelmer_injective
      (h.trans (map_one globalKummerQuotientToSelmer).symm)
  · intro h
    subst q
    exact map_one globalKummerQuotientToSelmer

end Synthesis.Millennium.BSD

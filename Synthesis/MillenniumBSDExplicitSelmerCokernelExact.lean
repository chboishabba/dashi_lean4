import Synthesis.MillenniumBSDGlobalKummerKernelExact
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic

/-!
# Literal cokernel of the global Kummer injection

Once E(Q)/2E(Q) injects into the explicit 2-Selmer subgroup, the remaining
group-theoretic cokernel can be formed honestly.  This file proves the short
exact sequence with that literal cokernel.  The arithmetic identification of
this cokernel with Sha(E/Q)[2] remains a separate theorem.
-/

namespace Synthesis.Millennium.BSD

abbrev ExplicitTwoSelmerCokernel : Type :=
  explicitTwoSelmerSubgroup ⧸ globalKummerImageSubgroup

noncomputable def explicitTwoSelmerCokernelMap :
    explicitTwoSelmerSubgroup →* ExplicitTwoSelmerCokernel :=
  QuotientGroup.mk' globalKummerImageSubgroup

theorem explicitTwoSelmerCokernelMap_surjective :
    Function.Surjective explicitTwoSelmerCokernelMap :=
  QuotientGroup.mk'_surjective globalKummerImageSubgroup

theorem explicitTwoSelmerCokernelMap_kernel :
    explicitTwoSelmerCokernelMap.ker = globalKummerImageSubgroup := by
  exact QuotientGroup.ker_mk' globalKummerImageSubgroup

theorem globalKummer_range_eq_cokernel_kernel :
    globalKummerQuotientToSelmer.range
      = explicitTwoSelmerCokernelMap.ker := by
  rw [explicitTwoSelmerCokernelMap_kernel]
  rfl

theorem explicitTwoSelmerCokernelMap_after_globalKummer
    (q : Multiplicative RationalProjectivePoint ⧸ globalDoubleSubgroup) :
    explicitTwoSelmerCokernelMap (globalKummerQuotientToSelmer q) = 1 := by
  rw [← MonoidHom.mem_ker]
  rw [explicitTwoSelmerCokernelMap_kernel]
  exact ⟨q, rfl⟩

theorem explicitTwoSelmerCokernel_exact_middle :
    ∀ s : explicitTwoSelmerSubgroup,
      explicitTwoSelmerCokernelMap s = 1
        ↔ ∃ q : Multiplicative RationalProjectivePoint ⧸ globalDoubleSubgroup,
            globalKummerQuotientToSelmer q = s := by
  intro s
  constructor
  · intro hs
    have hmem : s ∈ explicitTwoSelmerCokernelMap.ker := by
      exact hs
    rw [← globalKummer_range_eq_cokernel_kernel] at hmem
    exact hmem
  · rintro ⟨q, rfl⟩
    exact explicitTwoSelmerCokernelMap_after_globalKummer q

theorem explicitTwoSelmer_short_exact_left :
    Function.Injective globalKummerQuotientToSelmer :=
  globalKummerQuotientToSelmer_injective

theorem explicitTwoSelmer_short_exact_right :
    Function.Surjective explicitTwoSelmerCokernelMap :=
  explicitTwoSelmerCokernelMap_surjective

end Synthesis.Millennium.BSD

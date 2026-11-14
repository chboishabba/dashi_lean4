import Synthesis.MillenniumBSDCMOriginalEbarDoublingTopRepExact
import Synthesis.MillenniumBSDLocalKummerCohomologyReduction
import Mathlib.Tactic

/-!
# K2: original continuous E[2] ↪ E(Qbar) →[2] E(Qbar) exact at E

Previous project owners already construct:
  localActualE2InclusionCLM : E[2](Qbar) →L[Z] E(Qbar)
  globalGenericE2ToEllipticPoint : TopRep(E[2]) ⟶ TopRep(E(Qbar))
  cmEbarDoublingCLM : E(Qbar) →L[Z] E(Qbar)
  cmEbarDoublingTopRepHom : TopRep(E(Qbar)) ⟶ TopRep(E(Qbar)).

The actual E(Qbar) subtype is exactly the doubling kernel.
This file proves the two continuous-linear maps form an
UNDERLYING-MODULE short exact sequence, on the SAME geometric point
carrier; the original global TopRep maps already intertwine G_Q.

It is NOT a continuous-cohomology long exact sequence.
Naturality with E(Qbar_v) and classical Sha(E)[2] remain open.
Source-written only; exact-head local Lean kernel verification pending.
-/

namespace Synthesis.Millennium.BSD

/-- The actual, existing E[2] inclusion is injective. -/
theorem cmActualE2InclusionCLM_injective :
    Function.Injective localActualE2InclusionCLM := by
  intro T U h
  apply Subtype.ext
  exact h

/-- Exactness at the middle actual E(Qbar): doubling kills every
literal geometric two-torsion point. -/
theorem cmEbarDoubling_comp_actualE2Inclusion_zero
    (T : cmAlgClosureTwoTorsionSubgroup) :
    cmEbarDoublingCLM (localActualE2InclusionCLM T) = 0 := by
  exact (cmEbarDoublingTopRepHom_kernel_iff_actualE2 T.1).mpr T.2

/-- Every actual geometric point in the doubled kernel comes
from an actual geometric E[2] point, with NO abstract carrier. -/
theorem cmEbarDoubling_kernel_iff_actualE2Inclusion_range
    (P : CMAlgClosureProjectivePoint) :
    cmEbarDoublingCLM P = 0 ↔
      ∃ T : cmAlgClosureTwoTorsionSubgroup,
        localActualE2InclusionCLM T = P := by
  constructor
  · intro h
    have hT : P ∈ cmAlgClosureTwoTorsionSubgroup :=
      (cmEbarDoublingTopRepHom_kernel_iff_actualE2 P).mp h
    exact ⟨⟨P, hT⟩, rfl⟩
  · rintro ⟨T, h⟩
    rw [← h]
    exact cmEbarDoubling_comp_actualE2Inclusion_zero T

/-- Underlying continuous ℤ-module short exactness on the
original selected geometric curve: injective inclusion,
middle exactness and surjective doubling. -/
theorem cmEbarActualKummerShortExact_CLM :
    Function.Injective localActualE2InclusionCLM
      ∧
      (∀ P : CMAlgClosureProjectivePoint,
        cmEbarDoublingCLM P = 0 ↔
          ∃ T : cmAlgClosureTwoTorsionSubgroup,
            localActualE2InclusionCLM T = P)
      ∧ Function.Surjective cmEbarDoublingCLM := by
  exact ⟨cmActualE2InclusionCLM_injective,
    cmEbarDoubling_kernel_iff_actualE2Inclusion_range,
    cmEbarDoublingTopRepHom_surjective⟩

end Synthesis.Millennium.BSD

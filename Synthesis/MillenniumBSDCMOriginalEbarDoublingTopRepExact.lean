import Synthesis.MillenniumBSDActualEllipticPointTopRep
import Synthesis.MillenniumBSDCMAlgClosureDoublingSurjectiveExact
import Synthesis.MillenniumBSDActualAlgClosureTwoTorsionExact
import Mathlib.RepresentationTheory.Continuous.TopRep
import Mathlib.Tactic

/-!
# K2: literal [2] morphism in the original continuous E(Qbar) Galois module

The selected original E:y²=x³-x already has:
* cmEllipticPointRepresentation, the full discrete G_Q TopRep on
  ACTUAL E(AlgebraicClosure Q) points;
* cmAlgClosureGaloisAddHom preserving the original group law;
* cmAlgClosure_doubling_surjective constructing geometric half-points;
* cmAlgClosureTwoTorsionSubgroup classifying the actual doubling kernel.

This module upgrades literal geometric doubling to a morphism
cmEllipticPointRepresentation ⟶ cmEllipticPointRepresentation.
It proves its underlying point function is surjective and its
kernel is the original geometric E[2], NOT an invented (C2)^2 carrier.

The continuous H¹ long exact connecting map and the local-coefficient
comparison E(Qbar)|G_Qv versus E(Qbar_v) remain open.
No E-valued Sha[2] identification is asserted here.
Source-written; local Lean 4 kernel check on the pinned mathlib required.
-/

namespace Synthesis.Millennium.BSD

/-- Doubling as a continuous integer-linear map on the actual
discrete geometric elliptic point group. -/
noncomputable def cmEbarDoublingCLM :
    CMAlgClosureProjectivePoint →L[ℤ] CMAlgClosureProjectivePoint where
  toLinearMap :=
    (nsmulAddMonoidHom (α := CMAlgClosureProjectivePoint) 2).toIntLinearMap
  cont := continuous_of_discreteTopology

@[simp] theorem cmEbarDoublingCLM_apply
    (P : CMAlgClosureProjectivePoint) :
    cmEbarDoublingCLM P = (2 : ℕ) • P := rfl

/-- Doubling is an actual morphism of the original continuous
G_Q representation E(Qbar), not merely an additive group map. -/
noncomputable def cmEbarDoublingTopRepHom :
    cmEllipticPointRepresentation ⟶
      cmEllipticPointRepresentation :=
  TopRep.ofHom
    { __ := cmEbarDoublingCLM
      isIntertwining' σ := by
        ext P
        change
          (2 : ℕ) • cmAlgClosureGaloisAction σ P =
            cmAlgClosureGaloisAction σ ((2 : ℕ) • P)
        exact (map_nsmul (cmAlgClosureGaloisAddHom σ) P 2).symm }

/-- The genuine TopRep doubling map is surjective on the underlying
selected geometric point group, using actual half-points. -/
theorem cmEbarDoublingTopRepHom_surjective :
    Function.Surjective cmEbarDoublingCLM := by
  intro P
  obtain ⟨Q, hQ⟩ := cmAlgClosure_doubling_surjective P
  exact ⟨Q, by simpa using hQ⟩

/-- The kernel of the continuous-module doubling map is the
original geometric E[2] subgroup, elementwise on the same carrier. -/
theorem cmEbarDoublingTopRepHom_kernel_iff_actualE2
    (P : CMAlgClosureProjectivePoint) :
    cmEbarDoublingCLM P = 0 ↔
      P ∈ cmAlgClosureTwoTorsionSubgroup := by
  rfl

/-- Conjunction needed for the genuinely equivariant
short exact Kummer sequence on this selected geometric curve. -/
theorem cmEbarDoublingTopRepHom_kernel_and_surjective :
    (∀ P : CMAlgClosureProjectivePoint,
      cmEbarDoublingCLM P = 0 ↔
        P ∈ cmAlgClosureTwoTorsionSubgroup)
      ∧ Function.Surjective cmEbarDoublingCLM := by
  exact ⟨cmEbarDoublingTopRepHom_kernel_iff_actualE2,
    cmEbarDoublingTopRepHom_surjective⟩

end Synthesis.Millennium.BSD

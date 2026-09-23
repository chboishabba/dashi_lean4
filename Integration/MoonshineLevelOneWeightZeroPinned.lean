import Mathlib.Analysis.Complex.AbsMax
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# Level-one weight-zero constancy at the pinned Mathlib v4.28.0 dependency

Mathlib's later LevelOne.Basic module packages this theorem, but that module is
not present at the repository's v4.28.0 pin.  All load-bearing ingredients,
however, already exist at the pin:

* the SL2Z fundamental-domain reduction;
* the q-parameter inverse estimates;
* cusp-function holomorphy;
* the maximum-modulus theorem.

This module ports only the weight-zero/nonpositive-weight result needed by the
Moonshine Delta same-object proof.  It does not import or reproduce the later
dimension-formula stack.
-/

namespace Integration.MoonshineLevelOneWeightZeroPinned

open UpperHalfPlane ModularGroup SlashInvariantForm ModularForm Complex
  Real Function SlashInvariantFormClass ModularFormClass Periodic Filter Metric

open scoped MatrixGroups Topology

noncomputable section

local notation "𝕢" => qParam

variable {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}

/-- Direct level-one norm reduction, avoiding the later Gamma-one coercion
alias unavailable at the current pin. -/
theorem exists_one_half_le_im_and_norm_le
    [SlashInvariantFormClass F 𝒮ℒ k]
    (hk : k ≤ 0)
    (f : F)
    (τ : ℍ) :
    ∃ ξ : ℍ, 1 / 2 ≤ ξ.im ∧ ‖f τ‖ ≤ ‖f ξ‖ := by
  obtain ⟨γ, hγ, hdenom⟩ :=
    ModularGroup.exists_one_half_le_im_smul_and_norm_denom_le τ
  refine ⟨γ • τ, hγ, ?_⟩
  have hmem : ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have hslash :=
    SlashInvariantForm.slash_action_eqn''
      f hmem τ
  rw [hslash, norm_mul, norm_zpow]
  exact
    le_mul_of_one_le_left (norm_nonneg _) <|
      one_le_zpow_of_nonpos₀
        (norm_pos_iff.mpr (ModularGroup.denom_ne_zero γ τ))
        hdenom hk

/-- The q-disc representative of a nonpositive-weight level-one modular form
is constant. -/
private theorem cuspFunction_eqOn_const_of_nonpos_wt
    [ModularFormClass F 𝒮ℒ k]
    (hk : k ≤ 0)
    (f : F) :
    Set.EqOn
      (SlashInvariantFormClass.cuspFunction 1 f)
      (Function.const ℂ
        (SlashInvariantFormClass.cuspFunction 1 f 0))
      (Metric.ball 0 1) := by
  have hperiod : (1 : ℝ) ∈ 𝒮ℒ.strictPeriods := by simp
  refine
    Complex.eq_const_of_exists_le
      (fun q hq =>
        (ModularFormClass.differentiableAt_cuspFunction
          f one_pos hperiod
          (Metric.mem_ball_zero_iff.mp hq)).differentiableWithinAt)
      (Real.exp_nonneg (-Real.pi))
      ?_
      (fun q hq => ?_)
  · simp [Real.pi_pos]
  · rcases eq_or_ne q 0 with rfl | hq'
    · refine ⟨0, ?_, le_rfl⟩
      simpa only [norm_zero] using Real.exp_nonneg (-Real.pi)
    · let τ : ℍ :=
        ⟨Periodic.invQParam 1 q,
          Periodic.im_invQParam_pos_of_norm_lt_one
            Real.zero_lt_one
            (Metric.mem_ball_zero_iff.mp hq)
            hq'⟩
      obtain ⟨ξ, hξ, hbound⟩ :=
        exists_one_half_le_im_and_norm_le hk f τ
      refine
        ⟨𝕢 1 ξ,
          Function.Periodic.norm_qParam_le_of_one_half_le_im hξ,
          ?_⟩
      have hξEq :
          SlashInvariantFormClass.cuspFunction 1 f (𝕢 1 ξ) = f ξ :=
        SlashInvariantFormClass.eq_cuspFunction f ξ hperiod one_ne_zero
      have hτEq :
          SlashInvariantFormClass.cuspFunction 1 f q = f τ := by
        rw [← SlashInvariantFormClass.eq_cuspFunction
          f τ hperiod one_ne_zero]
        congr 1
        exact Periodic.qParam_right_inv one_ne_zero hq'
      simpa [hξEq, hτEq] using hbound

/-- Every level-one modular form of nonpositive weight is constant. -/
theorem levelOne_nonpos_wt_const
    [ModularFormClass F 𝒮ℒ k]
    (hk : k ≤ 0)
    (f : F) :
    (f : ℍ → ℂ) =
      Function.const ℍ
        (SlashInvariantFormClass.cuspFunction 1 f 0) := by
  funext z
  have hperiod : (1 : ℝ) ∈ 𝒮ℒ.strictPeriods := by simp
  have hQ : 𝕢 1 z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using
      UpperHalfPlane.norm_qParam_lt_one 1 z
  have hconst :=
    cuspFunction_eqOn_const_of_nonpos_wt hk f hQ
  have hz :=
    SlashInvariantFormClass.eq_cuspFunction
      f z hperiod one_ne_zero
  simpa [hz] using hconst

/-- Pinned replacement for the later Mathlib level-one weight-zero theorem. -/
theorem levelOne_weight_zero_const
    [ModularFormClass F 𝒮ℒ 0]
    (f : F) :
    ∃ c : ℂ, (f : ℍ → ℂ) = Function.const ℍ c :=
  ⟨_, levelOne_nonpos_wt_const le_rfl f⟩

/-- Every negative-weight level-one modular form vanishes. -/
theorem levelOne_neg_weight_eq_zero
    [ModularFormClass F 𝒮ℒ k]
    (hk : k < 0)
    (f : F) :
    (f : ℍ → ℂ) = 0 := by
  have hf := levelOne_nonpos_wt_const hk.le f
  have hS :
      f (ModularGroup.S • UpperHalfPlane.I) =
        (ModularGroup.denom ModularGroup.S UpperHalfPlane.I) ^ k *
          f UpperHalfPlane.I :=
    SlashInvariantForm.slash_action_eqn''
      f
      (show ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ 𝒮ℒ from
        ⟨ModularGroup.S, rfl⟩)
      UpperHalfPlane.I
  by_cases hc :
      SlashInvariantFormClass.cuspFunction 1 f 0 = 0
  · simpa [hf, hc]
  · exfalso
    have hfix : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
      ext
      simp [UpperHalfPlane.modular_S_smul]
    rw [hfix, hf] at hS
    simp only [Function.const_apply] at hS
    have hden :
        ModularGroup.denom ModularGroup.S UpperHalfPlane.I =
          (Complex.I : ℂ) := by
      simp [ModularGroup.denom_S]
    rw [hden] at hS
    have hne :
        (Complex.I : ℂ) ^ k ≠ 1 := by
      intro hi
      have habs := congrArg Complex.abs hi
      simp at habs
    exact hc (by
      have := hS
      field_simp at this
      aesop)

structure WeightZeroPinnedBoundary where
  fundamentalDomainNormReductionOwned : Bool
  cuspMaximumModulusReductionOwned : Bool
  nonpositiveWeightConstancyOwned : Bool
  weightZeroConstancyOwned : Bool
  dependencyBumpUsed : Bool

def weightZeroPinnedBoundary : WeightZeroPinnedBoundary where
  fundamentalDomainNormReductionOwned := true
  cuspMaximumModulusReductionOwned := true
  nonpositiveWeightConstancyOwned := true
  weightZeroConstancyOwned := true
  dependencyBumpUsed := false

end

end Integration.MoonshineLevelOneWeightZeroPinned

/-
# Row A — the shell Gaussian coefficient, trapped on both sides by kernel data

Row A's displayed completion condition for the Gaussian sector is two-sided,

    b₋·(m − k) ≤ Σ_{j∈[k,m)} β_{Z,j} ≤ b₊·(m − k),

and until now only the floor `b₋` was available from the literal one-loop trace.
`UpperShellBound` supplied the missing ceiling in terms of the two majorant data
`(c_V, K_W)`.  This file feeds *both* sides from the **same** source data that
already drives the floor:

* the Lorentz-diagonal averaging / constrained-projection variation is
  controlled by a single regularity constant `K_D ≤ 1/2`, and the transverse
  conjugate of the resulting vertex then obeys `c_V = 4π + 64K_D`
  (`sourceVariation_conj_bound`);
* the seagull insertion is bounded by `K_W`.

Hence

    1/8388608 ≤ β_Z ≤ (4π + 64K_D)² + 128K_W² ,

with no new input at all — `b₊` is a function of the *same* two constants as
`b₋`.  Specialising to kernel data gives

* `cellGaussian_two_sided_from_kernels`, and
* `shellGaussian_cumulative_from_kernels`, the cumulative prefix statement in
  exactly the shape Row A asks for.

**Honest status — Row A is not closed.**  This closes the two-sidedness of the
Gaussian sector, not the identification of the kernels with Bałaban's printed
objects.
-/
import RequestProject.YangMills.UpperShellBound
import RequestProject.YangMills.ZeroMassKernelVanishing

namespace YangMills

open Real Matrix Finset MeasureTheory Set

/-! ## 1. Two-sided bound from one regularity constant -/

/-- The explicit ceiling produced by the regularity constant `K_D` and the
seagull size `K_W`. -/
noncomputable def shellGaussianCeiling (KD KW : ℝ) : ℝ := (4 * π + 64 * KD) ^ 2 + 128 * KW ^ 2

/-- **The shell Gaussian coefficient is trapped on both sides by the same two
source constants.** -/
theorem cellGaussian_two_sided_from_regularity
    {f KD KW : ℝ} {D W : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    (hKD : 0 ≤ KD) (hKD2 : KD ≤ 1 / 2) (hKW : 0 ≤ KW)
    (hDmeas : ∀ a b, Measurable fun x => D x a b)
    (hWmeas : ∀ a b, Measurable fun x => W x a b)
    (hDoff : ∀ x a b, a ≠ b → D x a b = 0)
    (hDlin : ∀ x a b, |D x a b| ≤ KD * ‖x‖)
    (hWbd : ∀ x ∈ puncturedCell, ∀ a b, |W x a b| ≤ KW) :
    1 / 8388608 ≤ cellGaussianCoefficient
        (literalOneLoopIntegrand (sourceVariationMatrix f 1 D) W)
      ∧ cellGaussianCoefficient (literalOneLoopIntegrand (sourceVariationMatrix f 1 D) W)
          ≤ shellGaussianCeiling KD KW := by
  have hcVnn : (0 : ℝ) ≤ 4 * π + 64 * KD := by positivity
  have hconj : ∀ x ∈ puncturedCell, ∀ a b,
      |(transverseProjector (phatVec x) * sourceVariationMatrix f 1 D x
        * transverseProjector (phatVec x)) a b| ≤ (4 * π + 64 * KD) * ‖x‖ := by
    intro x hx a b
    exact sourceVariation_conj_bound hKD hDlin (phatSq_ne_zero_of_mem_puncturedCell hx) a b
  have hVmeas := measurable_sourceVariationMatrix_entry f 1 hDmeas
  have hsym : ∀ x, (sourceVariationMatrix f 1 D x)ᵀ = sourceVariationMatrix f 1 D x :=
    fun x => sourceVariationMatrix_transpose hDoff x
  have hint : IntegrableOn (literalOneLoopIntegrand (sourceVariationMatrix f 1 D) W)
      puncturedCell :=
    literalOneLoopIntegrand_integrableOn_of_conjBound hcVnn hKW hVmeas hWmeas hsym hconj hWbd
  constructor
  · have hnonneg : ∀ q ∈ puncturedCell,
        0 ≤ literalOneLoopIntegrand (sourceVariationMatrix f 1 D) W q := fun q hq =>
      literalOneLoopIntegrand_nonneg (phatSq_ne_zero_of_mem_puncturedCell hq) (hsym q)
    have hpatch : ∀ q ∈ wardPatch,
        (1 : ℝ) / 32768 ≤ literalOneLoopIntegrand (sourceVariationMatrix f 1 D) W q := by
      intro q hq
      exact literalOneLoopIntegrand_wardPatch_floor_local (d := KD / 2) hDoff
        (fun y hy a => diagonal_bound_of_linearVanishing hKD hDlin hy a) (by linarith) hq
    have hfl := cellGaussianFloor_of_wardPatch hint hnonneg hpatch
    calc (1 : ℝ) / 8388608 = 1 / 256 * (1 / 32768) := by norm_num
      _ ≤ _ := hfl
  · exact le_trans (le_abs_self _)
      (abs_cellGaussianCoefficient_le hcVnn hKW hVmeas hWmeas hsym hconj hWbd)

/-! ## 2. Two-sided bound from kernel data -/

/-- **The two-sided shell Gaussian bound with both sides driven by kernel
data.**  The variation is the symbol of finite-range zero-total-mass kernels of
range `R` and mass `M`, and the seagull is the symbol of kernels of mass `MW`. -/
theorem cellGaussian_two_sided_from_kernels
    {ξ ζ : Type*} [Fintype ξ] [Fintype ζ] {f R M MW : ℝ}
    {Kk : Fin 4 → ξ → ℝ} {dd : Fin 4 → ξ → (Fin 4 → ℝ)}
    {KW : Fin 4 → Fin 4 → ζ → ℝ} {dW : Fin 4 → Fin 4 → ζ → (Fin 4 → ℝ)}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hMW : 0 ≤ MW)
    (hzero : ∀ a, ∑ i, Kk a i = 0)
    (hd : ∀ a i mu, |dd a i mu| ≤ R)
    (hmass : ∀ a, kernelMass (Kk a) ≤ M)
    (hsmallK : linearVanishingConstant R M ≤ 1 / 2)
    (hmassW : ∀ a b, kernelMass (KW a b) ≤ MW) :
    1 / 8388608 ≤ cellGaussianCoefficient
        (literalOneLoopIntegrand
          (sourceVariationMatrix f 1 (diagCosSymbolMatrix Kk dd)) (cosSymbolMatrix KW dW))
      ∧ cellGaussianCoefficient
          (literalOneLoopIntegrand
            (sourceVariationMatrix f 1 (diagCosSymbolMatrix Kk dd)) (cosSymbolMatrix KW dW))
          ≤ shellGaussianCeiling (linearVanishingConstant R M) MW :=
  cellGaussian_two_sided_from_regularity
    (linearVanishingConstant_nonneg hM) hsmallK hMW
    (measurable_diagCosSymbolMatrix_entry Kk dd)
    (measurable_cosSymbolMatrix_entry KW dW)
    (fun x _ _ hab => diagCosSymbolMatrix_offdiag Kk dd x hab)
    (fun x a b => abs_diagCosSymbolMatrix_le hR hzero hd hmass hM x a b)
    (fun x _ a b => abs_cosSymbolMatrix_le hmassW x a b)

/-! ## 3. The cumulative Row A statement -/

/-- **Row A's cumulative two-sided Gaussian statement, instantiated on kernel
data.**  Over any block of `m − k` shells, the cumulative Gaussian sector of the
literal one-loop trace grows linearly with rates `b₋ = 2⁻²³` and
`b₊ = (4π + 64·LVC(R,M))² + 128·MW²`, uniformly in the shell index and in the
admissible history. -/
theorem shellGaussian_cumulative_from_kernels
    {ξ ζ : Type*} [Fintype ξ] [Fintype ζ] {f R M MW : ℝ}
    {Kk : ℕ → (ℕ → ℝ) → Fin 4 → ξ → ℝ} {dd : ℕ → (ℕ → ℝ) → Fin 4 → ξ → (Fin 4 → ℝ)}
    {KW : ℕ → (ℕ → ℝ) → Fin 4 → Fin 4 → ζ → ℝ}
    {dW : ℕ → (ℕ → ℝ) → Fin 4 → Fin 4 → ζ → (Fin 4 → ℝ)}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hMW : 0 ≤ MW)
    (hzero : ∀ j h a, ∑ i, Kk j h a i = 0)
    (hd : ∀ j h a i mu, |dd j h a i mu| ≤ R)
    (hmass : ∀ j h a, kernelMass (Kk j h a) ≤ M)
    (hsmallK : linearVanishingConstant R M ≤ 1 / 2)
    (hmassW : ∀ j h a b, kernelMass (KW j h a b) ≤ MW)
    (h : ℕ → ℝ) (k m : ℕ) :
    (1 / 8388608 : ℝ) * (m - k : ℕ)
        ≤ ∑ j ∈ Finset.Ico k m, shellGaussianOfIntegrand
            (fun j' h' => literalOneLoopIntegrand
              (sourceVariationMatrix f 1 (diagCosSymbolMatrix (Kk j' h') (dd j' h')))
              (cosSymbolMatrix (KW j' h') (dW j' h'))) j h
      ∧ ∑ j ∈ Finset.Ico k m, shellGaussianOfIntegrand
            (fun j' h' => literalOneLoopIntegrand
              (sourceVariationMatrix f 1 (diagCosSymbolMatrix (Kk j' h') (dd j' h')))
              (cosSymbolMatrix (KW j' h') (dW j' h'))) j h
          ≤ shellGaussianCeiling (linearVanishingConstant R M) MW * (m - k : ℕ) := by
  refine shellGaussian_cumulative_two_sided (betaZ := fun j =>
    shellGaussianOfIntegrand
      (fun j' h' => literalOneLoopIntegrand
        (sourceVariationMatrix f 1 (diagCosSymbolMatrix (Kk j' h') (dd j' h')))
        (cosSymbolMatrix (KW j' h') (dW j' h'))) j h)
    (fun j _ => ?_) (fun j _ => ?_)
  · exact (cellGaussian_two_sided_from_kernels (f := f) hR hM hMW (hzero j h) (hd j h)
      (hmass j h) hsmallK (hmassW j h)).1
  · exact (cellGaussian_two_sided_from_kernels (f := f) hR hM hMW (hzero j h) (hd j h)
      (hmass j h) hsmallK (hmassW j h)).2

end YangMills

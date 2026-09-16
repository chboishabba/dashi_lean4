/-
# Row A1.1 — the averaging hypothesis package is inhabited by a background
family with a *nonzero* derivative

`CMP98BackgroundDerivative` reduces the Gaussian sector of the Row A shell bound
to a normalised background family of the source averaging transports together
with a mass bound on its derivative kernel.  A hypothesis package is only worth
anything if it can be satisfied non-trivially, so this file exhibits an explicit
family that satisfies it with a derivative kernel that is *not* zero:

    T_t(x, μ, k) = 1 + t·δ·ε(k) ,     ε(0) = 1, ε(k) = −1 for k ≠ 0 ,

at block size `L = 2`, colour space of dimension one.  Because `ε` sums to zero
along each axial path, the averaging map reproduces constants for *every* value
of the background parameter `t` — the normalisation of the source operator — and
the derivative kernel is the nonzero, zero-total-mass kernel `2⁻⁵·δ·ε`.

* `witnessTransport_normalized` — normalisation at every `t`;
* `hasDerivAt_witnessKernel` — the derivative kernel;
* `witnessDerivKernel_mass` — its mass is `|δ|`, so the small-field inequality
  holds for `δ = 1/20000`;
* `witnessDerivKernel_ne_zero` — it is not the zero kernel;
* `A1_beta_pos_from_cmp98_averaging_nonvacuous` — the Row A shell bound obtained
  from this family.

This is an inhabitation statement about the hypothesis package.  It is *not* a
claim that this family is the source background family.
-/
import RequestProject.YangMills.CMP98BackgroundDerivative

namespace YangMills

open Real Finset

/-! ## 1. The witness family -/

/-- The alternating step profile along an axial path of length `2`. -/
def witnessStep (k : ℕ) : ℝ := if k = 0 then 1 else -1

/-- The witness background family: a one-dimensional colour space, block size
`2`, and a background parameter that tilts the two links of each axial path
against each other. -/
noncomputable def witnessTransport (delta t : ℝ) : TransportData (Fin 1) :=
  fun _ _ k => Matrix.of fun _ _ => 1 + t * (delta * witnessStep k)

/-- **The witness family is normalised at every background parameter**: the
averaging map reproduces constants, because the tilt sums to zero along each
axial path. -/
theorem witnessTransport_normalized (delta t : ℝ) :
    CMP98Normalized 2 (witnessTransport delta t) := by
  intro c y mu a
  obtain rfl : a = 0 := Subsingleton.elim a 0
  rw [cmp98Q]
  have hconst : ∀ r : Fin 4 → Fin 2,
      ((((2 : ℕ) : ℝ)) ^ (4 + 1))⁻¹ *
          cmp98PathVariable 2 (witnessTransport delta t) (fun _ _ b => c b)
            (blockSite 2 y r) mu 0
        = (1 / 16 : ℝ) * c 0 := by
    intro r
    unfold cmp98PathVariable witnessTransport witnessStep
    simp [Fin.sum_univ_two]
    ring
  rw [Finset.sum_congr rfl fun r _ => hconst r, Finset.sum_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  norm_num
  ring

/-! ## 2. The derivative kernel -/

/-- The derivative of the witness kernel: weight `2⁻⁵·δ` with the alternating
sign of the step index. -/
noncomputable def witnessDerivKernel (delta : ℝ) : BlockKernelIndex 2 → ℝ :=
  fun i => ((((2 : ℕ) : ℝ)) ^ 5)⁻¹ * (delta * witnessStep i.2)

theorem hasDerivAt_witnessKernel (delta t₀ : ℝ) (y : Site) (mu : Fin 4)
    (a b : Fin 1) (i : BlockKernelIndex 2) :
    HasDerivAt (fun t => cmp98Kernel 2 (witnessTransport delta t) y mu a b i)
      (witnessDerivKernel delta i) t₀ := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + t * (delta * witnessStep i.2))
      (delta * witnessStep i.2) t₀ := by
    simpa using ((hasDerivAt_id t₀).mul_const (delta * witnessStep i.2)).const_add 1
  have h := h1.const_mul ((((2 : ℕ) : ℝ)) ^ 5)⁻¹
  simpa [cmp98Kernel, witnessTransport, witnessDerivKernel] using h

/-- **The witness derivative kernel has total mass `|δ|`.** -/
theorem witnessDerivKernel_mass (delta : ℝ) :
    kernelMass (witnessDerivKernel delta) = |delta| := by
  have hterm : ∀ i : BlockKernelIndex 2, |witnessDerivKernel delta i| = |delta| / 32 := by
    intro i
    have habs : |witnessStep i.2| = 1 := by
      unfold witnessStep
      by_cases h : (i.2 : ℕ) = 0 <;> simp [h]
    rw [witnessDerivKernel, abs_mul, abs_mul, habs]
    norm_num
    ring
  rw [kernelMass, Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_const,
    Finset.card_univ, card_blockKernelIndex]
  norm_num
  ring

/-- **The witness derivative kernel is not the zero kernel** when `δ ≠ 0`: the
averaging derivative that the Gaussian sector consumes is genuinely present. -/
theorem witnessDerivKernel_ne_zero {delta : ℝ} (hdelta : delta ≠ 0) :
    witnessDerivKernel delta ≠ 0 := by
  intro hzero
  have h := congrFun hzero (⟨fun _ => 0, 0⟩ : BlockKernelIndex 2)
  rw [witnessDerivKernel] at h
  simp [witnessStep] at h
  exact hdelta h

/-- The small-field inequality for the witness mass. -/
theorem witness_smallness : linearVanishingConstant (2 * (2 : ℕ)) (1 / 20000 : ℝ) ≤ 1 / 2 := by
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hpi0 : 0 < Real.pi := Real.pi_pos
  unfold linearVanishingConstant
  push_cast
  nlinarith

/-! ## 3. The shell bound from the witness family -/

/-- **The hypothesis package of `A1_beta_pos_from_cmp98_averaging` is inhabited
with a nonzero averaging derivative.**  The background family is normalised at
every parameter value, its derivative kernel has mass `1/20000` and is not zero,
and the resulting Row A shell bound holds. -/
theorem A1_beta_pos_from_cmp98_averaging_nonvacuous (f : ℝ) (y : Site) (j : ℕ) :
    (1 : ℝ) / 16777216 ≤ shellBetaOfSources
      (fun _ _ => literalOneLoopIntegrand
        (sourceVariationMatrix f 1
          (diagCosSymbolMatrix (fun _ => witnessDerivKernel (1 / 20000))
            (fun mu => blockAveragingDispl 2 mu)))
        (cosSymbolMatrix (fun _ _ (_ : Fin 0) => (0 : ℝ))
          (fun _ _ (_ : Fin 0) => (0 : Fin 4 → ℝ))))
      (fun _ _ (_ : Fin 0) => (0 : ℝ)) (fun _ _ (_ : Fin 0) => (0 : ℝ))
      (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) 0 j
      (fun _ => (0 : ℝ)) := by
  refine A1_beta_pos_from_cmp98_averaging (color := Fin 1)
    (Adm := fun h => ∀ j, h j = 0) (g := fun _ => 0)
    (T := fun _ _ t => witnessTransport (1 / 20000) t)
    (Kd := fun _ _ _ => witnessDerivKernel (1 / 20000))
    (y := y) (a := 0) (b := 0) (t₀ := 0)
    (M := 1 / 20000) (MW := 0)
    (AInt := fun _ => 0) (AChart := fun _ => 0) (ALoc := fun _ => 0)
    (LamDet := 0) (LamGauge := 0) (theta := 1 / 2)
    (by norm_num) (by norm_num)
    (fun _ _ t => witnessTransport_normalized _ t)
    (fun _ _ mu i => hasDerivAt_witnessKernel _ 0 y mu 0 0 i)
    (fun _ _ _ => le_of_eq (by rw [witnessDerivKernel_mass]; norm_num))
    witness_smallness
    (fun _ _ _ _ => le_of_eq (by simp [kernelMass]))
    (fun _ _ i => absurd i.isLt (by omega)) (fun _ _ i => absurd i.isLt (by omega))
    (fun _ _ _ => by norm_num) (fun _ _ _ => by norm_num) (fun _ _ _ => by norm_num)
    ?_ (by norm_num) (by norm_num) (fun _ => rfl) (fun _ => le_rfl) ?_ j
  · intro j' h hh
    refine ⟨le_of_eq (hh j').symm, ?_, ?_, ?_⟩ <;> rw [hh j'] <;> norm_num
  · intro j'
    have hC : 0 ≤ Cbeta (sourceChannelCoefficient (Fintype.card (Fin 0)) (Fintype.card (Fin 0))
        0 0 (1 / 2) (fun _ => 0) (fun _ => 0) (fun _ => 0) 0) := by
      rw [Cbeta]
      exact Finset.sum_nonneg fun k _ =>
        sourceChannelCoefficient_nonneg (by norm_num) (by norm_num) k
    exact (criticalCoupling_pos (by norm_num) hC).le

end YangMills

/-
# Row A1 (source lane) — zero total mass is *forced* by normalisation

`ZeroMassKernelVanishing` reduced the whole Gaussian sector of the Row A1a shell
bound to three structural facts about the position kernel of the Lorentz-diagonal
averaging / constrained-projection variation:

    Σ_i K_i = 0        (zero total mass),
    |d_i| ≤ R          (finite range),
    Σ_i |K_i| ≤ M      (small mass).

Of these, the *first* was still stated as an assumption.  It should not be: it is
a consequence of the one property the averaging map has by construction, namely
that it reproduces constants.  Bałaban's averaging operator satisfies

    Q(V)·(constant) = constant                                          (N)

for every admissible background `V`; in kernel language, the total mass of the
averaging kernel is `1` **for every background**.  Differentiating `(N)` along
any deformation of the background therefore gives total mass `0` for the
derivative kernel.  That is the content of

* `zeroMass_of_normalizedFamily`,

which needs nothing but uniqueness of derivatives.  It converts "the variation
has zero total mass" from a hypothesis into a theorem about normalisation-
preserving deformations.

The flat-background instance of `(N)` is already available
(`blockAverage_flatTransport_const`).  Here we also record the flat averaging
kernel itself — weight `L⁻⁵` on each of the `L⁵` block-path displacements — and
verify its normalisation and range directly:

* `blockAveragingWeight_sum` : total mass `1`;
* `blockAveragingKernel_mass` : `Σ_i |K_i| = 1`;
* `blockAveragingDispl_range` : all displacements bounded by `2L`.

Finally `A1_beta_pos_ward_from_normalizedAveraging` restates the Row A1a shell
bound with the zero-mass hypothesis replaced by normalisation of the averaging
family together with differentiability along the background deformation.

**Honest status — Row A1 is not closed.**  The range and mass bounds for the
derivative kernel are still hypotheses (they are quantitative source estimates),
and the five remainder-channel majorants are untouched.
-/
import RequestProject.YangMills.ZeroMassKernelVanishing
import RequestProject.YangMills.FlatBackgroundAveraging

namespace YangMills

open Real Matrix Finset

/-! ## 1. Normalisation forces zero total mass of the derivative kernel -/

/-- **Normalisation forces zero total mass.**  If a one-parameter family of
finite kernels has total mass `1` for every parameter value — the statement that
the averaging map reproduces constants along the whole deformation — then the
derivative kernel has total mass `0`.

This is the structural origin of the linear vanishing of the averaging /
constrained-projection variation at zero momentum. -/
theorem zeroMass_of_normalizedFamily {ι : Type*} [Fintype ι] {K : ℝ → ι → ℝ} {K' : ι → ℝ}
    {t₀ : ℝ} (hnorm : ∀ t, ∑ i, K t i = 1)
    (hd : ∀ i, HasDerivAt (fun t => K t i) (K' i) t₀) :
    ∑ i, K' i = 0 := by
  have hsum0 := HasDerivAt.sum (u := (Finset.univ : Finset ι))
    (A := fun i => fun t => K t i) (fun i _ => hd i)
  have hsum : HasDerivAt (fun t => ∑ i, K t i) (∑ i, K' i) t₀ := by
    have hfun : (∑ i ∈ (Finset.univ : Finset ι), fun t => K t i) = fun t => ∑ i, K t i := by
      funext t; simp [Finset.sum_apply]
    rwa [hfun] at hsum0
  have hconst : HasDerivAt (fun t : ℝ => ∑ i, K t i) 0 t₀ := by
    have hc : (fun t : ℝ => ∑ i, K t i) = fun _ => (1 : ℝ) := funext hnorm
    rw [hc]; exact hasDerivAt_const _ _
  exact hsum.unique hconst

/-- The same statement for a family whose total mass is any fixed constant. -/
theorem zeroMass_of_constantMassFamily {ι : Type*} [Fintype ι] {K : ℝ → ι → ℝ} {K' : ι → ℝ}
    {t₀ c : ℝ} (hnorm : ∀ t, ∑ i, K t i = c)
    (hd : ∀ i, HasDerivAt (fun t => K t i) (K' i) t₀) :
    ∑ i, K' i = 0 := by
  have hsum0 := HasDerivAt.sum (u := (Finset.univ : Finset ι))
    (A := fun i => fun t => K t i) (fun i _ => hd i)
  have hsum : HasDerivAt (fun t => ∑ i, K t i) (∑ i, K' i) t₀ := by
    have hfun : (∑ i ∈ (Finset.univ : Finset ι), fun t => K t i) = fun t => ∑ i, K t i := by
      funext t; simp [Finset.sum_apply]
    rwa [hfun] at hsum0
  have hconst : HasDerivAt (fun t : ℝ => ∑ i, K t i) 0 t₀ := by
    have hc : (fun t : ℝ => ∑ i, K t i) = fun _ => c := funext hnorm
    rw [hc]; exact hasDerivAt_const _ _
  exact hsum.unique hconst

/-! ## 2. The flat block-averaging kernel -/

/-- The index set of the block-averaging kernel: one index per axial path `r` of
the block and per link `k` along that path. -/
abbrev BlockKernelIndex (L : ℕ) : Type := (Fin 4 → Fin L) × Fin L

/-- The weight of the flat block-averaging kernel: `L⁻⁵` on each of the `L⁵`
fine links entering the coarse link. -/
noncomputable def blockAveragingWeight (L : ℕ) : BlockKernelIndex L → ℝ :=
  fun _ => ((L : ℝ) ^ 5)⁻¹

/-- The displacement attached to the index `(r, k)` in direction `μ`: the offset
`r` inside the block plus `k` steps along `μ`. -/
def blockAveragingDispl (L : ℕ) (mu : Fin 4) : BlockKernelIndex L → (Fin 4 → ℝ) :=
  fun i nu => (i.1 nu : ℝ) + (if nu = mu then (i.2 : ℝ) else 0)

theorem card_blockKernelIndex (L : ℕ) :
    Fintype.card (BlockKernelIndex L) = L ^ 5 := by
  simp [BlockKernelIndex, Fintype.card_prod]
  ring

/-- **The flat block-averaging kernel is normalised**: its total mass is `1`.
This is the kernel form of `blockAverage_flatTransport_const`. -/
theorem blockAveragingWeight_sum {L : ℕ} (hL : L ≠ 0) :
    ∑ i, blockAveragingWeight L i = 1 := by
  have hL' : ((L : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hL
  simp only [blockAveragingWeight]
  rw [Finset.sum_const, Finset.card_univ, card_blockKernelIndex, nsmul_eq_mul, Nat.cast_pow]
  field_simp

/-- The flat block-averaging kernel has mass exactly `1` (all weights are
positive). -/
theorem blockAveragingKernel_mass {L : ℕ} (hL : L ≠ 0) :
    kernelMass (blockAveragingWeight L) = 1 := by
  have hnn : ∀ i : BlockKernelIndex L, |blockAveragingWeight L i| = blockAveragingWeight L i := by
    intro i
    simp only [blockAveragingWeight]
    exact abs_of_nonneg (by positivity)
  rw [kernelMass, Finset.sum_congr rfl fun i _ => hnn i]
  exact blockAveragingWeight_sum hL

/-- **The block-averaging kernel has range `2L`**: every displacement of a fine
link inside a block, including the `k` steps along the coarse direction, is
bounded by `2L`. -/
theorem blockAveragingDispl_range {L : ℕ} (mu : Fin 4) (i : BlockKernelIndex L) (nu : Fin 4) :
    |blockAveragingDispl L mu i nu| ≤ 2 * L := by
  have h1 : (i.1 nu : ℝ) < L := by exact_mod_cast (i.1 nu).isLt
  have h2 : (i.2 : ℝ) < L := by exact_mod_cast i.2.isLt
  have h1' : (0 : ℝ) ≤ (i.1 nu : ℝ) := Nat.cast_nonneg _
  have h2' : (0 : ℝ) ≤ (i.2 : ℝ) := Nat.cast_nonneg _
  simp only [blockAveragingDispl]
  rw [abs_of_nonneg]
  · by_cases h : nu = mu
    · rw [if_pos h]; linarith
    · rw [if_neg h]; linarith
  · by_cases h : nu = mu
    · rw [if_pos h]; linarith
    · rw [if_neg h]; linarith

/-! ## 3. Row A1a with zero mass derived from normalisation -/

/-- **Row A1a with the zero-mass input replaced by normalisation.**  The
Lorentz-diagonal averaging / constrained-projection variation is the derivative,
along a deformation of the background, of a family of finite-range kernels each
of which reproduces constants.  Zero total mass — hence the linear vanishing of
the symbol at zero momentum — is then a theorem, not an assumption.

What remains in the Gaussian sector is quantitative only: the range bound `R`,
the derivative-mass bound `M`, and the smallness `16π²R²M + 2M ≤ 1/2`, which is
exactly the small-field condition. -/
theorem A1_beta_pos_ward_from_normalizedAveraging
    {ι κ ξ ζ : Type*} [Fintype ι] [Fintype κ] [Fintype ξ] [Fintype ζ]
    {Adm : (ℕ → ℝ) → Prop} {g : ℕ → ℝ} {f R M MW t₀ : ℝ}
    {Kfam : ℕ → (ℕ → ℝ) → Fin 4 → ℝ → ξ → ℝ}
    {Kk : ℕ → (ℕ → ℝ) → Fin 4 → ξ → ℝ} {dd : ℕ → (ℕ → ℝ) → Fin 4 → ξ → (Fin 4 → ℝ)}
    {KW : ℕ → (ℕ → ℝ) → Fin 4 → Fin 4 → ζ → ℝ}
    {dW : ℕ → (ℕ → ℝ) → Fin 4 → Fin 4 → ζ → (Fin 4 → ℝ)}
    {lamDet : ℕ → (ℕ → ℝ) → ι → ℝ} {lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ}
    {aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    {AInt AChart ALoc : ℕ → ℝ} {N : ℕ} {LamDet LamGauge theta : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hMW : 0 ≤ MW)
    (hnorm : ∀ j h a t, ∑ i, Kfam j h a t i = 1)
    (hderiv : ∀ j h a i, HasDerivAt (fun t => Kfam j h a t i) (Kk j h a i) t₀)
    (hd : ∀ j h a i mu, |dd j h a i mu| ≤ R)
    (hmass : ∀ j h a, kernelMass (Kk j h a) ≤ M)
    (hsmallK : linearVanishingConstant R M ≤ 1 / 2)
    (hmassW : ∀ j h a b, kernelMass (KW j h a b) ≤ MW)
    (hLd : ∀ j h i, |lamDet j h i| ≤ LamDet)
    (hLg : ∀ j h i, |lamGauge j h i| ≤ LamGauge)
    (hAInt : ∀ j h n, |aInt j h n| ≤ AInt n)
    (hAChart : ∀ j h n, |aChart j h n| ≤ AChart n)
    (hALoc : ∀ j h n, |aLoc j h n| ≤ ALoc n)
    (hsmall : ∀ j h, Adm h → 0 ≤ h j ∧ h j ≤ theta ∧
        h j * LamDet ≤ theta ∧ h j * LamGauge ≤ theta)
    (hth : theta < 1) (hth0 : 0 ≤ theta)
    (hadm : Adm g) (hg0 : ∀ j, 0 ≤ g j)
    (hgg : ∀ j, g j ≤ criticalCoupling (1 / 8388608 : ℝ)
      (Cbeta (sourceChannelCoefficient (Fintype.card ι) (Fintype.card κ)
        LamDet LamGauge theta AInt AChart ALoc N)))
    (j : ℕ) :
    (1 : ℝ) / 16777216 ≤ shellBetaOfSources
      (fun j' h => literalOneLoopIntegrand
        (sourceVariationMatrix f 1 (diagCosSymbolMatrix (Kk j' h) (dd j' h)))
        (cosSymbolMatrix (KW j' h) (dW j' h)))
      lamDet lamGauge aInt aChart aLoc N j g :=
  A1_beta_pos_ward_from_kernels (R := R) (M := M) (MW := MW)
    (Kk := Kk) (dd := dd) (KW := KW) (dW := dW)
    hR hM hMW
    (fun j' h a => zeroMass_of_normalizedFamily (hnorm j' h a) (hderiv j' h a))
    hd hmass hsmallK hmassW hLd hLg hAInt hAChart hALoc hsmall hth hth0 hadm hg0 hgg j

end YangMills

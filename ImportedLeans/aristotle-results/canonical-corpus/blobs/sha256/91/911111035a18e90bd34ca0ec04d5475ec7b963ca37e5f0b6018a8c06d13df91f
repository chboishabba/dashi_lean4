/-
# Row A1.1 / A1.3 — the background derivative `Q'` of the literal Eq. (125)
averaging operator, and the constants it produces

`CMP98AveragingEq125` identified the Row A averaging map with the source
operator

    (Q A)_c = Σ_{x ∈ B(c₋)} L^{-(d+1)} (R_{0,c₋} A)([x,x'])                (125)

whose only background dependence sits in the colour transport `R_{0,c₋}`.  The
object the shell bound actually consumes is the *derivative of that operator in
the background*, `Q'`, and the two properties of `Q'` that the Gaussian sector
needs:

* zero total mass, i.e. `Q'` annihilates constants — hence its momentum symbol
  vanishes at zero momentum;
* finite range `2L` and a mass bound `M`, giving the linear bound
  `|Q'(q)| ≤ (16π²(2L)²M + 2M)·‖q‖`.

## What is proved here

* `cmp98Q_eq_kernelSum` — the operator of Eq. (125) written as a kernel sum in
  the kernel data `cmp98Kernel` (weight `L^{-(d+1)}` times the transport entry)
  over the index set `BlockKernelIndex L`, on the sites `cmp98IndexSite`.
* `cmp98Kernel_totalMass_of_normalized` — the source normalisation "the
  averaging map reproduces constants at every background" says exactly that the
  total mass of the kernel in the colour pair `(a,b)` is `δ_{ab}`, for every
  background.
* `cmp98DerivKernel_zeroMass` — therefore *every* background derivative of the
  kernel has total mass `0`.  Zero mass is a theorem about Eq. (125), not an
  assumption about an abstract kernel.
* `cmp98DerivKernel_range` — the range of the derivative kernel is `2L`, from
  the displacements of Eq. (125) computed in `CMP98AveragingEq125`.
* `cmp98DerivSymbol_linear_bound`, `cmp98_KQ` — the derived linear-vanishing
  constant of `Q'`: `K_Q = 16π²(2L)²M + 2M`, with `M` the mass of the derivative
  kernel.  This is the concrete constant required by the `hQlin` slot of
  `PivotSolveShellBound`.
* `A1_beta_pos_from_cmp98_averaging` — the Row A shell bound `β_j ≥ 1/16777216`
  with the Gaussian-sector kernel data *supplied by* the background derivative
  of Eq. (125): the hypotheses about that sector are now the source
  normalisation, differentiability of the background family, and the mass bound
  `M` with the small-field inequality `16π²(2L)²M + 2M ≤ 1/2`.

**Honest status.**  What is *not* proved here, and is left explicit as a
hypothesis: the quantitative mass bound `M` on the derivative kernel (the source
supplies it through its analyticity estimates), and the interaction-channel
data.  Nothing in this file assumes the linear vanishing of `Q'`; that is now
derived.
-/
import RequestProject.YangMills.CMP98AveragingEq125

namespace YangMills

open Finset Real

variable {color : Type*} [Fintype color]

/-! ## 1. Eq. (125) as a kernel -/

/-- Reordering of a triple finite sum, used to move the colour sum outside. -/
theorem sum_comm_three {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (F : A → B → C → ℝ) :
    ∑ r, ∑ k, ∑ b, F r k b = ∑ b, ∑ r, ∑ k, F r k b := by
  rw [Finset.sum_comm (γ := C)]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- **The kernel of Eq. (125).**  For the coarse link `(y, μ)` and the colour
pair `(a,b)`, the weight carried by the fine link with index `i = (r,k)` is the
normalisation `L^{-(d+1)}` times the transport entry `R_{0,c₋}^{ab}`. -/
noncomputable def cmp98Kernel (L : ℕ) (T : TransportData color) (y : Site) (mu : Fin 4)
    (a b : color) : BlockKernelIndex L → ℝ :=
  fun i => ((L : ℝ) ^ 5)⁻¹ * T (blockSite L y i.1) mu i.2 a b

/-- **Eq. (125) is the kernel sum of `cmp98Kernel` over the sites
`cmp98IndexSite`** — for every background, not only the flat one. -/
theorem cmp98Q_eq_kernelSum (L : ℕ) (T : TransportData color) (A : LinkField color)
    (y : Site) (mu : Fin 4) (a : color) :
    cmp98Q L T A y mu a
      = ∑ b : color, ∑ i : BlockKernelIndex L,
          cmp98Kernel L T y mu a b i * A (cmp98IndexSite L y mu i) mu b := by
  rw [cmp98Q_eq_blockAverage]
  simp only [blockAverage, cmp98Kernel, cmp98IndexSite, Fintype.sum_prod_type,
    Finset.mul_sum, mul_assoc]
  exact sum_comm_three _

/-! ## 2. Normalisation of Eq. (125) fixes the total mass of the kernel -/

/-- **The normalisation property of the source averaging map**: at the
background `T` it reproduces constant fluctuation fields. -/
def CMP98Normalized (L : ℕ) (T : TransportData color) : Prop :=
  ∀ (c : color → ℝ) (y : Site) (mu : Fin 4) (a : color),
    cmp98Q L T (fun _ _ b => c b) y mu a = c a

/-- The flat background is normalised — the instance already available from the
weight `L^{-(d+1)}` of Eq. (125). -/
theorem cmp98Normalized_flat [DecidableEq color] {L : ℕ} (hL : L ≠ 0) :
    CMP98Normalized L (flatTransport color) :=
  fun c y mu a => cmp98Q_flat_const hL c y mu a

/-- **Normalisation is the statement that the kernel has total mass `δ_{ab}`.**
Testing the source normalisation on the colour basis vector `b` gives the total
mass of the kernel in the colour channel `(a,b)`. -/
theorem cmp98Kernel_totalMass_of_normalized [DecidableEq color] {L : ℕ}
    {T : TransportData color} (hnorm : CMP98Normalized L T)
    (y : Site) (mu : Fin 4) (a b : color) :
    ∑ i : BlockKernelIndex L, cmp98Kernel L T y mu a b i = if a = b then 1 else 0 := by
  have h := hnorm (fun b' => if b' = b then (1 : ℝ) else 0) y mu a
  rw [cmp98Q_eq_kernelSum] at h
  have hinner : ∀ b' : color,
      (∑ i : BlockKernelIndex L, cmp98Kernel L T y mu a b' i *
          (if b' = b then (1 : ℝ) else 0))
        = if b' = b then ∑ i : BlockKernelIndex L, cmp98Kernel L T y mu a b' i else 0 := by
    intro b'
    by_cases hb : b' = b
    · simp [hb]
    · simp [hb]
  rw [Finset.sum_congr rfl fun b' _ => hinner b'] at h
  rw [Finset.sum_ite_eq' Finset.univ b
      (fun b' => ∑ i : BlockKernelIndex L, cmp98Kernel L T y mu a b' i)] at h
  simpa using h

/-! ## 3. Zero total mass of the background derivative -/

/-- **The background derivative of the Eq. (125) kernel has zero total mass.**
The total mass is `δ_{ab}` for every background, so it is constant along any
deformation of the background, and its derivative vanishes.  This is the
structural origin of the linear vanishing of `Q'` at zero momentum. -/
theorem cmp98DerivKernel_zeroMass [DecidableEq color] {L : ℕ}
    {T : ℝ → TransportData color} {t₀ : ℝ} {y : Site} {mu : Fin 4} {a b : color}
    {K' : BlockKernelIndex L → ℝ}
    (hnorm : ∀ t, CMP98Normalized L (T t))
    (hd : ∀ i, HasDerivAt (fun t => cmp98Kernel L (T t) y mu a b i) (K' i) t₀) :
    ∑ i, K' i = 0 :=
  zeroMass_of_constantMassFamily
    (c := if a = b then 1 else 0)
    (fun t => cmp98Kernel_totalMass_of_normalized (hnorm t) y mu a b) hd

/-! ## 4. The range and the derived linear-vanishing constant -/

/-- **The range of the Eq. (125) kernel — hence of its background derivative —
is `2L`.** -/
theorem cmp98DerivKernel_range {L : ℕ} (mu : Fin 4) (i : BlockKernelIndex L) (nu : Fin 4) :
    |blockAveragingDispl L mu i nu| ≤ 2 * L :=
  blockAveragingDispl_range mu i nu

/-- **The derived linear bound on the momentum symbol of `Q'`.**  A background
derivative of the Eq. (125) kernel with mass at most `M` has symbol bounded by
`(16π²(2L)²M + 2M)‖q‖`; no linear-vanishing constant is assumed. -/
theorem cmp98DerivSymbol_linear_bound [DecidableEq color] {L : ℕ}
    {T : ℝ → TransportData color} {t₀ : ℝ} {y : Site} {mu : Fin 4} {a b : color}
    {K' : BlockKernelIndex L → ℝ} {M : ℝ}
    (hnorm : ∀ t, CMP98Normalized L (T t))
    (hd : ∀ i, HasDerivAt (fun t => cmp98Kernel L (T t) y mu a b i) (K' i) t₀)
    (hmass : kernelMass K' ≤ M) (q : Fin 4 → ℝ) :
    |cosSymbol K' (blockAveragingDispl L mu) q|
      ≤ linearVanishingConstant (2 * L) M * ‖q‖ := by
  have hzero := cmp98DerivKernel_zeroMass hnorm hd
  have hR : (0 : ℝ) ≤ 2 * L := by positivity
  refine le_trans
    (abs_cosSymbol_le_linear_of_zeroMass hzero hR
      (fun i nu => cmp98DerivKernel_range mu i nu) q) ?_
  have hmono : linearVanishingConstant (2 * L) (kernelMass K')
      ≤ linearVanishingConstant (2 * L) M := by
    have h1 : 16 * π ^ 2 * (2 * (L : ℝ)) ^ 2 * kernelMass K'
        ≤ 16 * π ^ 2 * (2 * (L : ℝ)) ^ 2 * M :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    have h2 : 2 * kernelMass K' ≤ 2 * M := by linarith
    unfold linearVanishingConstant
    linarith
  exact mul_le_mul_of_nonneg_right hmono (norm_nonneg q)

/-- **The derived pivot constant `K_Q`.**  This is the concrete number the
`hQlin` slot of `A1_beta_pos_from_pivotSolve` asks for, expressed in the two
data of the source averaging operator: the block size `L` and the mass `M` of
the background derivative of its kernel. -/
noncomputable def cmp98_KQ (L : ℕ) (M : ℝ) : ℝ := linearVanishingConstant (2 * L) M

theorem cmp98_KQ_nonneg {L : ℕ} {M : ℝ} (hM : 0 ≤ M) : 0 ≤ cmp98_KQ L M :=
  linearVanishingConstant_nonneg hM

/-! ## 5. The Row A shell bound with `Q'` supplied by Eq. (125) -/

/-- **Row A shell positivity with the Gaussian-sector kernel data supplied by
the background derivative of the literal Eq. (125) averaging operator.**

The Gaussian sector no longer takes an abstract zero-mass kernel: it takes a
background family of the source averaging operator, each member of which
reproduces constants (the source normalisation), and its derivative.  Zero total
mass and the range `2L` are then theorems; the only quantitative Gaussian input
left is the mass bound `M` of the derivative kernel together with the small-field
inequality `16π²(2L)²M + 2M ≤ 1/2`.

For every scale `j` and every admissible history, `β_j(g) ≥ 1/16777216 > 0`. -/
theorem A1_beta_pos_from_cmp98_averaging
    [DecidableEq color] {ι κ ζ : Type*} [Fintype ι] [Fintype κ] [Fintype ζ]
    {Adm : (ℕ → ℝ) → Prop} {g : ℕ → ℝ} {f M MW t₀ : ℝ} {L : ℕ}
    {T : ℕ → (ℕ → ℝ) → ℝ → TransportData color}
    {Kd : ℕ → (ℕ → ℝ) → Fin 4 → BlockKernelIndex L → ℝ}
    {y : Site} {a b : color}
    {KW : ℕ → (ℕ → ℝ) → Fin 4 → Fin 4 → ζ → ℝ}
    {dW : ℕ → (ℕ → ℝ) → Fin 4 → Fin 4 → ζ → (Fin 4 → ℝ)}
    {lamDet : ℕ → (ℕ → ℝ) → ι → ℝ} {lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ}
    {aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    {AInt AChart ALoc : ℕ → ℝ} {N : ℕ} {LamDet LamGauge theta : ℝ}
    (hM : 0 ≤ M) (hMW : 0 ≤ MW)
    (hnorm : ∀ j h t, CMP98Normalized L (T j h t))
    (hderiv : ∀ j h mu i,
      HasDerivAt (fun t => cmp98Kernel L (T j h t) y mu a b i) (Kd j h mu i) t₀)
    (hmass : ∀ j h mu, kernelMass (Kd j h mu) ≤ M)
    (hsmallK : linearVanishingConstant (2 * L) M ≤ 1 / 2)
    (hmassW : ∀ j h a' b', kernelMass (KW j h a' b') ≤ MW)
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
        (sourceVariationMatrix f 1
          (diagCosSymbolMatrix (Kd j' h) (fun mu => blockAveragingDispl L mu)))
        (cosSymbolMatrix (KW j' h) (dW j' h)))
      lamDet lamGauge aInt aChart aLoc N j g :=
  A1_beta_pos_ward_from_kernels
    (R := 2 * L) (M := M) (MW := MW)
    (Kk := Kd) (dd := fun _ _ mu => blockAveragingDispl L mu)
    (by positivity) hM hMW
    (fun j' h mu => cmp98DerivKernel_zeroMass (hnorm j' h) (hderiv j' h mu))
    (fun _ _ mu i nu => cmp98DerivKernel_range mu i nu)
    (fun j' h mu => hmass j' h mu)
    hsmallK hmassW hLd hLg hAInt hAChart hALoc hsmall hth hth0 hadm hg0 hgg j

end YangMills

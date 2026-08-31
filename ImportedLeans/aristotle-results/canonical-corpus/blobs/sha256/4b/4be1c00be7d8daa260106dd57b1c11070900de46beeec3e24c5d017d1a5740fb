/-
# Row A1 (source lane) — composition of averaging kernels, uniformly in the history

Bałaban's renormalisation-group step composes averaging operators: at scale `j`
the object that acts on the original field is the *product* of the one-step
averaging kernels of all previous scales.  The Row A1a Gaussian bound is required
to hold **uniformly over the admissible history**, so the structural facts it
uses — zero total mass, finite range, small mass — have to survive composition.

They do, and this file proves it with no analysis at all, only the algebra of
kernel convolution.  For kernels given by weights on displacements,

    (K₁ ∗ K₂)_{(i,j)} = K₁ᵢ·K₂ⱼ,      d_{(i,j)} = d₁ᵢ + d₂ⱼ ,

one has

* `kernelConv_sum` : total mass multiplies, so **normalised ∘ normalised is
  normalised** and **zero-mass ∘ anything is zero-mass**;
* `kernelMass_kernelConv` : the mass multiplies as well, so composing a
  derivative kernel of mass `M` with normalised nonnegative kernels leaves the
  mass at `M` — *uniformly in the number of RG steps*;
* `displConv_range` : only the range adds.

The `n`-fold version uses the index type `Fin n → ι`:

* `multiKernel_sum`, `multiKernel_mass`, `multiDispl_range`.

The payoff is `abs_cosSymbol_le_linear_of_composedKernel`: the symbol of the
`n`-times-composed averaging derivative still vanishes linearly at zero momentum,
with the constant `16π²(R₀ + nR)²M + 2M` — degrading only through the range, not
through the mass, and not through the number of composed steps.

**Honest status.**  These are the composition estimates for the kernel model of
the averaging operator.  They do not identify that model with Bałaban's printed
averaging map; Row A1 is not closed.
-/
import RequestProject.YangMills.ZeroMassKernelVanishing

namespace YangMills

open Real Finset

/-! ## 1. Convolution of two finite kernels -/

/-- The weights of the convolution of two finite kernels. -/
def kernelConv {ι κ : Type*} (K₁ : ι → ℝ) (K₂ : κ → ℝ) : ι × κ → ℝ :=
  fun p => K₁ p.1 * K₂ p.2

/-- The displacements of the convolution: displacements add. -/
def displConv {ι κ : Type*} (d₁ : ι → (Fin 4 → ℝ)) (d₂ : κ → (Fin 4 → ℝ)) :
    ι × κ → (Fin 4 → ℝ) :=
  fun p mu => d₁ p.1 mu + d₂ p.2 mu

/-- **Total mass multiplies under composition.** -/
theorem kernelConv_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (K₁ : ι → ℝ) (K₂ : κ → ℝ) :
    ∑ p, kernelConv K₁ K₂ p = (∑ i, K₁ i) * (∑ j, K₂ j) := by
  simp only [kernelConv]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]

/-- **Composing with a normalised kernel preserves zero total mass.**  This is
what makes the Row A1a Gaussian estimate uniform over the RG history: the
derivative of the averaging map at any scale, transported through all later
normalised averaging steps, still has zero total mass. -/
theorem kernelConv_zeroMass_left {ι κ : Type*} [Fintype ι] [Fintype κ]
    {K₁ : ι → ℝ} {K₂ : κ → ℝ} (h₁ : ∑ i, K₁ i = 0) :
    ∑ p, kernelConv K₁ K₂ p = 0 := by
  rw [kernelConv_sum, h₁, zero_mul]

/-- **The kernel mass multiplies under composition.** -/
theorem kernelMass_kernelConv {ι κ : Type*} [Fintype ι] [Fintype κ] (K₁ : ι → ℝ) (K₂ : κ → ℝ) :
    kernelMass (kernelConv K₁ K₂) = kernelMass K₁ * kernelMass K₂ := by
  simp only [kernelMass, kernelConv, abs_mul]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]

/-- **Only the range adds under composition.** -/
theorem displConv_range {ι κ : Type*} {d₁ : ι → (Fin 4 → ℝ)} {d₂ : κ → (Fin 4 → ℝ)}
    {R₁ R₂ : ℝ} (h₁ : ∀ i mu, |d₁ i mu| ≤ R₁) (h₂ : ∀ j mu, |d₂ j mu| ≤ R₂)
    (p : ι × κ) (mu : Fin 4) : |displConv d₁ d₂ p mu| ≤ R₁ + R₂ := by
  rw [displConv]
  exact le_trans (abs_add_le _ _) (add_le_add (h₁ p.1 mu) (h₂ p.2 mu))

/-! ## 2. The `n`-fold composition -/

/-- The `n`-fold convolution power of a kernel, indexed by `Fin n → ι`. -/
def multiKernel {ι : Type*} (K : ι → ℝ) (n : ℕ) : (Fin n → ι) → ℝ :=
  fun s => ∏ k, K (s k)

/-- The displacements of the `n`-fold convolution power. -/
def multiDispl {ι : Type*} (d : ι → (Fin 4 → ℝ)) (n : ℕ) : (Fin n → ι) → (Fin 4 → ℝ) :=
  fun s mu => ∑ k, d (s k) mu

/-- **`n` normalised steps compose to a normalised kernel.** -/
theorem multiKernel_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → ℝ) (n : ℕ) :
    ∑ s, multiKernel K n s = (∑ i, K i) ^ n :=
  (Fintype.sum_pow K n).symm

theorem multiKernel_sum_of_normalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ι → ℝ} (h : ∑ i, K i = 1) (n : ℕ) : ∑ s, multiKernel K n s = 1 := by
  rw [multiKernel_sum, h, one_pow]

/-- **The mass of the `n`-fold composition is the `n`-th power of the mass** — in
particular it stays `1` for a normalised nonnegative kernel, however many steps
are composed. -/
theorem multiKernel_mass {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → ℝ) (n : ℕ) :
    kernelMass (multiKernel K n) = (kernelMass K) ^ n := by
  have hstep : ∀ s : Fin n → ι, |multiKernel K n s| = ∏ k, |K (s k)| := by
    intro s
    rw [multiKernel, Finset.abs_prod]
  rw [kernelMass, Finset.sum_congr rfl fun s _ => hstep s, kernelMass]
  exact (Fintype.sum_pow (fun i => |K i|) n).symm

/-- **The range of the `n`-fold composition grows linearly.** -/
theorem multiDispl_range {ι : Type*} {d : ι → (Fin 4 → ℝ)} {R : ℝ}
    (h : ∀ i mu, |d i mu| ≤ R) (n : ℕ) (s : Fin n → ι) (mu : Fin 4) :
    |multiDispl d n s mu| ≤ n * R := by
  rw [multiDispl]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ k : Fin n, |d (s k) mu| ≤ ∑ _k : Fin n, R :=
        Finset.sum_le_sum fun k _ => h (s k) mu
    _ = n * R := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## 3. The composed averaging derivative still vanishes linearly -/

/-- **The transported averaging derivative.**  One zero-mass derivative kernel
followed by `n` normalised averaging steps. -/
noncomputable def transportedDerivativeKernel {ι κ : Type*} (K₀ : ι → ℝ) (K : κ → ℝ) (n : ℕ) :
    ι × (Fin n → κ) → ℝ :=
  kernelConv K₀ (multiKernel K n)

/-- Its displacements. -/
noncomputable def transportedDerivativeDispl {ι κ : Type*}
    (d₀ : ι → (Fin 4 → ℝ)) (d : κ → (Fin 4 → ℝ)) (n : ℕ) :
    ι × (Fin n → κ) → (Fin 4 → ℝ) :=
  displConv d₀ (multiDispl d n)

theorem transportedDerivativeKernel_zeroMass {ι κ : Type*} [Fintype ι] [Fintype κ]
    {K₀ : ι → ℝ} {K : κ → ℝ} (h₀ : ∑ i, K₀ i = 0) (n : ℕ) :
    ∑ p, transportedDerivativeKernel K₀ K n p = 0 :=
  kernelConv_zeroMass_left h₀

/-- **The mass of the transported derivative kernel is unchanged by the number
of composed averaging steps.** -/
theorem transportedDerivativeKernel_mass {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {K₀ : ι → ℝ} {K : κ → ℝ} (hK : kernelMass K = 1) (n : ℕ) :
    kernelMass (transportedDerivativeKernel K₀ K n) = kernelMass K₀ := by
  rw [transportedDerivativeKernel, kernelMass_kernelConv, multiKernel_mass, hK, one_pow, mul_one]

theorem transportedDerivativeDispl_range {ι κ : Type*}
    {d₀ : ι → (Fin 4 → ℝ)} {d : κ → (Fin 4 → ℝ)} {R₀ R : ℝ}
    (h₀ : ∀ i mu, |d₀ i mu| ≤ R₀) (h : ∀ i mu, |d i mu| ≤ R) (n : ℕ)
    (p : ι × (Fin n → κ)) (mu : Fin 4) :
    |transportedDerivativeDispl d₀ d n p mu| ≤ R₀ + n * R :=
  displConv_range h₀ (fun s nu => multiDispl_range h n s nu) p mu

/-- **The symbol of the transported averaging derivative still vanishes linearly
at zero momentum**, with a constant that degrades only through the range: the
mass, and hence the whole small-field smallness budget, is untouched by the
number of composed RG steps. -/
theorem abs_cosSymbol_le_linear_of_composedKernel {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] {K₀ : ι → ℝ} {K : κ → ℝ} {d₀ : ι → (Fin 4 → ℝ)} {d : κ → (Fin 4 → ℝ)}
    {R₀ R : ℝ} (hR₀ : 0 ≤ R₀) (hR : 0 ≤ R)
    (h₀ : ∑ i, K₀ i = 0) (hK : kernelMass K = 1)
    (hd₀ : ∀ i mu, |d₀ i mu| ≤ R₀) (hd : ∀ i mu, |d i mu| ≤ R)
    (n : ℕ) (q : Fin 4 → ℝ) :
    |cosSymbol (transportedDerivativeKernel K₀ K n)
        (transportedDerivativeDispl d₀ d n) q|
      ≤ linearVanishingConstant (R₀ + n * R) (kernelMass K₀) * ‖q‖ := by
  have hrange : (0 : ℝ) ≤ R₀ + n * R := by positivity
  have hbound := abs_cosSymbol_le_linear_of_zeroMass
    (K := transportedDerivativeKernel K₀ K n)
    (d := transportedDerivativeDispl d₀ d n) (R := R₀ + n * R)
    (transportedDerivativeKernel_zeroMass h₀ n) hrange
    (fun p mu => transportedDerivativeDispl_range hd₀ hd n p mu) q
  rwa [transportedDerivativeKernel_mass hK n] at hbound

end YangMills

/-
# Row A1a — the linear-vanishing datum from the *structure* of the source kernel

`A1_beta_pos_ward_from_regularity` (`WardFloorFromRegularity`) reduced the whole
Gaussian sector of the Row A1a shell bound to one numerical datum: a constant
`K_D ≤ 1/2` with

    |D(q)_{ab}| ≤ K_D‖q‖                                              (†)

for the Lorentz-diagonal averaging / constrained-projection variation.  This file
removes `(†)` as a free numerical assumption and derives it from a *structural*
property of the position-space kernel it comes from.

The momentum symbol of a finite-range position kernel is the cosine transform

    S(q) = Σ_i K_i cos(2π q·d_i)                                    (`cosSymbol`)

where `d_i` runs over the finitely many displacement vectors of the kernel and
`K_i` over its weights.  Two facts, both proved here:

* `abs_cosSymbol_le_mass` : `|S(q)| ≤ Σ_i |K_i|` — the symbol is bounded by the
  kernel mass, everywhere;
* `abs_cosSymbol_le_quadratic_of_zeroMass` : if the kernel has **zero total
  mass**, `Σ_i K_i = 0`, then `|S(q)| ≤ 32π²R²·M·‖q‖²` with `R` the range and
  `M` the mass — the symbol vanishes *quadratically* at zero momentum.

Together they give the global linear bound `abs_cosSymbol_le_linear_of_zeroMass`
with the computed constant `K_D = 16π²R²M + 2M`, and hence

* `A1_beta_pos_ward_from_kernelMass` : the Row A1a shell bound for a
  Lorentz-diagonal variation whose entries are the symbols of zero-mass kernels,
  with **no** free linear-vanishing constant and no diagonal-size assumption.
  The only surviving inputs in the Gaussian sector are: the kernel is
  Lorentz-diagonal, has zero total mass, and its mass and range obey
  `16π²R²M + 2M ≤ 1/2`.

**Honest status — Row A1 is not closed.**  Whether Bałaban's background
derivative of the averaging / constrained-projection kernel actually has zero
total mass with a mass–range product this small is a source estimate, not
something proved here; and the five remainder-channel majorants are untouched.
-/
import RequestProject.YangMills.WardFloorFromRegularity

namespace YangMills

open Real Matrix Finset MeasureTheory Set

/-! ## 1. The cosine symbol of a finite-range position kernel -/

/-- The momentum symbol of a finite-range position kernel: weights `K i` sitting
at displacements `d i`, transformed with the lattice plane wave. -/
noncomputable def cosSymbol {ι : Type*} [Fintype ι] (K : ι → ℝ) (d : ι → (Fin 4 → ℝ))
    (q : Fin 4 → ℝ) : ℝ :=
  ∑ i, K i * Real.cos (2 * π * ∑ mu : Fin 4, q mu * d i mu)

/-- The kernel mass. -/
noncomputable def kernelMass {ι : Type*} [Fintype ι] (K : ι → ℝ) : ℝ := ∑ i, |K i|

theorem kernelMass_nonneg {ι : Type*} [Fintype ι] (K : ι → ℝ) : 0 ≤ kernelMass K :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **The symbol is bounded by the kernel mass.** -/
theorem abs_cosSymbol_le_mass {ι : Type*} [Fintype ι] (K : ι → ℝ) (d : ι → (Fin 4 → ℝ))
    (q : Fin 4 → ℝ) : |cosSymbol K d q| ≤ kernelMass K := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-- `|cos θ − 1| ≤ θ²/2`. -/
theorem abs_cos_sub_one_le_half_sq (t : ℝ) : |Real.cos t - 1| ≤ t ^ 2 / 2 := by
  have h1 : Real.cos t ≤ 1 := Real.cos_le_one t
  have h2 : 1 - t ^ 2 / 2 ≤ Real.cos t := Real.one_sub_sq_div_two_le_cos
  rw [abs_le]
  constructor <;> linarith

/-- The phase of a displacement of range `R` at momentum `q` is at most
`8π R‖q‖`. -/
theorem abs_phase_le {d : Fin 4 → ℝ} {R : ℝ} (hd : ∀ mu, |d mu| ≤ R) (q : Fin 4 → ℝ) :
    |2 * π * ∑ mu : Fin 4, q mu * d mu| ≤ 8 * π * R * ‖q‖ := by
  have hq : ∀ mu : Fin 4, |q mu| ≤ ‖q‖ := fun mu => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm q mu
  have hR : 0 ≤ R := le_trans (abs_nonneg _) (hd 0)
  have hterm : ∀ mu : Fin 4, |q mu * d mu| ≤ ‖q‖ * R := by
    intro mu
    rw [abs_mul]
    exact mul_le_mul (hq mu) (hd mu) (abs_nonneg _) (norm_nonneg q)
  have hsum : |∑ mu : Fin 4, q mu * d mu| ≤ 4 * (‖q‖ * R) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ mu : Fin 4, |q mu * d mu| ≤ ∑ _mu : Fin 4, ‖q‖ * R :=
          Finset.sum_le_sum fun mu _ => hterm mu
      _ = 4 * (‖q‖ * R) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
  have hpi := Real.pi_pos
  calc |2 * π * ∑ mu : Fin 4, q mu * d mu|
      = 2 * π * |∑ mu : Fin 4, q mu * d mu| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * π)]
    _ ≤ 2 * π * (4 * (‖q‖ * R)) := by
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 8 * π * R * ‖q‖ := by ring

/-- **A zero-mass kernel has a symbol that vanishes quadratically at zero
momentum.**  This is the structural reason the averaging / constrained-projection
variation is allowed to enter the one-loop integrand at all. -/
theorem abs_cosSymbol_le_quadratic_of_zeroMass {ι : Type*} [Fintype ι] {K : ι → ℝ}
    {d : ι → (Fin 4 → ℝ)} {R : ℝ} (hzero : ∑ i, K i = 0) (hR : 0 ≤ R)
    (hd : ∀ i mu, |d i mu| ≤ R) (q : Fin 4 → ℝ) :
    |cosSymbol K d q| ≤ 32 * π ^ 2 * R ^ 2 * kernelMass K * ‖q‖ ^ 2 := by
  have hrw : cosSymbol K d q
      = ∑ i, K i * (Real.cos (2 * π * ∑ mu : Fin 4, q mu * d i mu) - 1) := by
    have hsplit : ∀ i : ι, K i * (Real.cos (2 * π * ∑ mu : Fin 4, q mu * d i mu) - 1)
        = K i * Real.cos (2 * π * ∑ mu : Fin 4, q mu * d i mu) - K i := by
      intro i; ring
    rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_sub_distrib, hzero, sub_zero,
      cosSymbol]
  have hterm : ∀ i : ι,
      |K i * (Real.cos (2 * π * ∑ mu : Fin 4, q mu * d i mu) - 1)|
        ≤ |K i| * (32 * π ^ 2 * R ^ 2 * ‖q‖ ^ 2) := by
    intro i
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine le_trans (abs_cos_sub_one_le_half_sq _) ?_
    have hph := abs_phase_le (hd i) q
    have hnn : (0 : ℝ) ≤ 8 * π * R * ‖q‖ := by positivity
    have hsq : (2 * π * ∑ mu : Fin 4, q mu * d i mu) ^ 2 ≤ (8 * π * R * ‖q‖) ^ 2 := by
      have habs := sq_abs (2 * π * ∑ mu : Fin 4, q mu * d i mu)
      nlinarith [abs_nonneg (2 * π * ∑ mu : Fin 4, q mu * d i mu)]
    nlinarith
  rw [hrw]
  calc |∑ i, K i * (Real.cos (2 * π * ∑ mu : Fin 4, q mu * d i mu) - 1)|
      ≤ ∑ i, |K i * (Real.cos (2 * π * ∑ mu : Fin 4, q mu * d i mu) - 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |K i| * (32 * π ^ 2 * R ^ 2 * ‖q‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = 32 * π ^ 2 * R ^ 2 * kernelMass K * ‖q‖ ^ 2 := by
        rw [← Finset.sum_mul, kernelMass]; ring

/-- The computed linear-vanishing constant of a zero-mass kernel of range `R`
and mass `M`. -/
noncomputable def linearVanishingConstant (R M : ℝ) : ℝ := 16 * π ^ 2 * R ^ 2 * M + 2 * M

theorem linearVanishingConstant_nonneg {R M : ℝ} (hM : 0 ≤ M) :
    0 ≤ linearVanishingConstant R M := by
  unfold linearVanishingConstant
  positivity

/-- **The global linear bound.**  A zero-mass kernel of range `R` and mass `M`
has a symbol obeying `|S(q)| ≤ (16π²R²M + 2M)‖q‖` for every momentum: the
quadratic bound does the work near the origin, the mass bound away from it. -/
theorem abs_cosSymbol_le_linear_of_zeroMass {ι : Type*} [Fintype ι] {K : ι → ℝ}
    {d : ι → (Fin 4 → ℝ)} {R : ℝ} (hzero : ∑ i, K i = 0) (hR : 0 ≤ R)
    (hd : ∀ i mu, |d i mu| ≤ R) (q : Fin 4 → ℝ) :
    |cosSymbol K d q| ≤ linearVanishingConstant R (kernelMass K) * ‖q‖ := by
  have hM := kernelMass_nonneg K
  have hn := norm_nonneg q
  have hpi := Real.pi_pos
  rcases le_or_gt ‖q‖ (1 / 2) with hsmall | hlarge
  · have hquad := abs_cosSymbol_le_quadratic_of_zeroMass hzero hR hd q
    have hstep : 32 * π ^ 2 * R ^ 2 * kernelMass K * ‖q‖ ^ 2
        ≤ 16 * π ^ 2 * R ^ 2 * kernelMass K * ‖q‖ := by
      have hfac : (0 : ℝ) ≤ 32 * π ^ 2 * R ^ 2 * kernelMass K * ‖q‖ := by positivity
      nlinarith
    have hrest : (0 : ℝ) ≤ 2 * kernelMass K * ‖q‖ := by positivity
    unfold linearVanishingConstant
    nlinarith
  · have hmass := abs_cosSymbol_le_mass K d q
    have hstep : kernelMass K ≤ 2 * kernelMass K * ‖q‖ := by nlinarith
    have hrest : (0 : ℝ) ≤ 16 * π ^ 2 * R ^ 2 * kernelMass K * ‖q‖ := by positivity
    unfold linearVanishingConstant
    nlinarith

theorem measurable_cosSymbol {ι : Type*} [Fintype ι] (K : ι → ℝ) (d : ι → (Fin 4 → ℝ)) :
    Measurable (cosSymbol K d) := by
  have : Continuous (cosSymbol K d) := by
    unfold cosSymbol
    fun_prop
  exact this.measurable

/-! ## 2. The Lorentz-diagonal variation built from zero-mass kernels -/

/-- The Lorentz-diagonal averaging / constrained-projection variation assembled
from one zero-mass position kernel per Lorentz direction. -/
noncomputable def diagCosSymbolMatrix {ι : Type*} [Fintype ι] (K : Fin 4 → ι → ℝ)
    (d : Fin 4 → ι → (Fin 4 → ℝ)) (q : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal fun a => cosSymbol (K a) (d a) q

theorem diagCosSymbolMatrix_offdiag {ι : Type*} [Fintype ι] (K : Fin 4 → ι → ℝ)
    (d : Fin 4 → ι → (Fin 4 → ℝ)) (q : Fin 4 → ℝ) {a b : Fin 4} (hab : a ≠ b) :
    diagCosSymbolMatrix K d q a b = 0 :=
  Matrix.diagonal_apply_ne _ hab

theorem measurable_diagCosSymbolMatrix_entry {ι : Type*} [Fintype ι] (K : Fin 4 → ι → ℝ)
    (d : Fin 4 → ι → (Fin 4 → ℝ)) (a b : Fin 4) :
    Measurable fun q => diagCosSymbolMatrix K d q a b := by
  by_cases hab : a = b
  · subst hab
    simpa [diagCosSymbolMatrix, Matrix.diagonal_apply_eq] using measurable_cosSymbol (K a) (d a)
  · simp [diagCosSymbolMatrix, Matrix.diagonal_apply_ne _ hab]

/-- **Every entry of the diagonal variation vanishes linearly**, with the
constant computed from the kernel mass and range. -/
theorem abs_diagCosSymbolMatrix_le {ι : Type*} [Fintype ι] {K : Fin 4 → ι → ℝ}
    {d : Fin 4 → ι → (Fin 4 → ℝ)} {R M : ℝ} (hR : 0 ≤ R)
    (hzero : ∀ a, ∑ i, K a i = 0) (hd : ∀ a i mu, |d a i mu| ≤ R)
    (hmass : ∀ a, kernelMass (K a) ≤ M) (hM : 0 ≤ M) (q : Fin 4 → ℝ) (a b : Fin 4) :
    |diagCosSymbolMatrix K d q a b| ≤ linearVanishingConstant R M * ‖q‖ := by
  have hn := norm_nonneg q
  have hpi := Real.pi_pos
  by_cases hab : a = b
  · subst hab
    have hentry : diagCosSymbolMatrix K d q a a = cosSymbol (K a) (d a) q := by
      simp [diagCosSymbolMatrix, Matrix.diagonal_apply_eq]
    rw [hentry]
    refine le_trans (abs_cosSymbol_le_linear_of_zeroMass (hzero a) hR (hd a) q) ?_
    have hmono : linearVanishingConstant R (kernelMass (K a)) ≤ linearVanishingConstant R M := by
      have h1 : 16 * π ^ 2 * R ^ 2 * kernelMass (K a) ≤ 16 * π ^ 2 * R ^ 2 * M :=
        mul_le_mul_of_nonneg_left (hmass a) (by positivity)
      have h2 : 2 * kernelMass (K a) ≤ 2 * M := by linarith [hmass a]
      unfold linearVanishingConstant
      linarith
    exact mul_le_mul_of_nonneg_right hmono hn
  · rw [diagCosSymbolMatrix_offdiag K d q hab, abs_zero]
    have : 0 ≤ linearVanishingConstant R M := linearVanishingConstant_nonneg hM
    positivity

/-! ## 3. Row A1a with the linear-vanishing constant computed from the kernel -/

/-- **Row A1a from the literal one-loop trace, with the Gaussian sector reduced
to kernel structure.**  The Lorentz-diagonal averaging / constrained-projection
variation is the momentum symbol of a family of finite-range, zero-total-mass
position kernels; its linear vanishing is a theorem, and the diagonal-size datum
is gone.  The only surviving Gaussian-sector inputs are `Σ_i K_i = 0`, the range
bound, the mass bound and the smallness `16π²R²M + 2M ≤ 1/2`. -/
theorem A1_beta_pos_ward_from_kernelMass
    {ι κ ξ : Type*} [Fintype ι] [Fintype κ] [Fintype ξ]
    {Adm : (ℕ → ℝ) → Prop} {g : ℕ → ℝ} {f KW R M : ℝ}
    {Kk : ℕ → (ℕ → ℝ) → Fin 4 → ξ → ℝ} {dd : ℕ → (ℕ → ℝ) → Fin 4 → ξ → (Fin 4 → ℝ)}
    {Wm : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {lamDet : ℕ → (ℕ → ℝ) → ι → ℝ} {lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ}
    {aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    {AInt AChart ALoc : ℕ → ℝ} {N : ℕ} {LamDet LamGauge theta : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hzero : ∀ j h a, ∑ i, Kk j h a i = 0)
    (hd : ∀ j h a i mu, |dd j h a i mu| ≤ R)
    (hmass : ∀ j h a, kernelMass (Kk j h a) ≤ M)
    (hsmallK : linearVanishingConstant R M ≤ 1 / 2)
    (hKW : 0 ≤ KW)
    (hWmeas : ∀ j h a b, Measurable fun x => Wm j h x a b)
    (hWbd : ∀ j h, ∀ x ∈ puncturedCell, ∀ a b, |Wm j h x a b| ≤ KW)
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
        (sourceVariationMatrix f 1 (diagCosSymbolMatrix (Kk j' h) (dd j' h))) (Wm j' h))
      lamDet lamGauge aInt aChart aLoc N j g :=
  A1_beta_pos_ward_from_regularity (KD := linearVanishingConstant R M)
    (Dm := fun j' h => diagCosSymbolMatrix (Kk j' h) (dd j' h))
    (linearVanishingConstant_nonneg hM) hsmallK hKW
    (fun j' h a b => measurable_diagCosSymbolMatrix_entry (Kk j' h) (dd j' h) a b)
    hWmeas
    (fun j' h x _ _ hab => diagCosSymbolMatrix_offdiag (Kk j' h) (dd j' h) x hab)
    (fun j' h x a b =>
      abs_diagCosSymbolMatrix_le hR (hzero j' h) (hd j' h) (hmass j' h) hM x a b)
    hWbd hLd hLg hAInt hAChart hALoc hsmall hth hth0 hadm hg0 hgg j

/-! ## 3b. The seagull insertion from a finite-mass kernel -/

/-- A general (not necessarily Lorentz-diagonal) variation assembled from one
finite-range position kernel per matrix entry. -/
noncomputable def cosSymbolMatrix {ι : Type*} [Fintype ι] (K : Fin 4 → Fin 4 → ι → ℝ)
    (d : Fin 4 → Fin 4 → ι → (Fin 4 → ℝ)) (q : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun a b => cosSymbol (K a b) (d a b) q

theorem measurable_cosSymbolMatrix_entry {ι : Type*} [Fintype ι] (K : Fin 4 → Fin 4 → ι → ℝ)
    (d : Fin 4 → Fin 4 → ι → (Fin 4 → ℝ)) (a b : Fin 4) :
    Measurable fun q => cosSymbolMatrix K d q a b :=
  measurable_cosSymbol (K a b) (d a b)

/-- **The seagull built from kernels is bounded by their mass**, everywhere. -/
theorem abs_cosSymbolMatrix_le {ι : Type*} [Fintype ι] {K : Fin 4 → Fin 4 → ι → ℝ}
    {d : Fin 4 → Fin 4 → ι → (Fin 4 → ℝ)} {MW : ℝ}
    (hmass : ∀ a b, kernelMass (K a b) ≤ MW) (q : Fin 4 → ℝ) (a b : Fin 4) :
    |cosSymbolMatrix K d q a b| ≤ MW :=
  le_trans (abs_cosSymbol_le_mass (K a b) (d a b) q) (hmass a b)

/-- **Row A1a with the whole Gaussian sector reduced to kernel data.**  Both the
Lorentz-diagonal averaging / constrained-projection variation and the seagull
insertion are momentum symbols of finite-range position kernels: the former with
zero total mass and small mass–range product, the latter with any finite mass.
No linear-vanishing constant, no diagonal-size constant and no seagull bound is
assumed as a bare number. -/
theorem A1_beta_pos_ward_from_kernels
    {ι κ ξ ζ : Type*} [Fintype ι] [Fintype κ] [Fintype ξ] [Fintype ζ]
    {Adm : (ℕ → ℝ) → Prop} {g : ℕ → ℝ} {f R M MW : ℝ}
    {Kk : ℕ → (ℕ → ℝ) → Fin 4 → ξ → ℝ} {dd : ℕ → (ℕ → ℝ) → Fin 4 → ξ → (Fin 4 → ℝ)}
    {KW : ℕ → (ℕ → ℝ) → Fin 4 → Fin 4 → ζ → ℝ}
    {dW : ℕ → (ℕ → ℝ) → Fin 4 → Fin 4 → ζ → (Fin 4 → ℝ)}
    {lamDet : ℕ → (ℕ → ℝ) → ι → ℝ} {lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ}
    {aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    {AInt AChart ALoc : ℕ → ℝ} {N : ℕ} {LamDet LamGauge theta : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hMW : 0 ≤ MW)
    (hzero : ∀ j h a, ∑ i, Kk j h a i = 0)
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
  A1_beta_pos_ward_from_kernelMass (R := R) (M := M) (KW := MW)
    (Kk := Kk) (dd := dd) (Wm := fun j' h => cosSymbolMatrix (KW j' h) (dW j' h))
    hR hM hzero hd hmass hsmallK hMW
    (fun j' h a b => measurable_cosSymbolMatrix_entry (KW j' h) (dW j' h) a b)
    (fun j' h x _ a b => abs_cosSymbolMatrix_le (hmassW j' h) x a b)
    hLd hLg hAInt hAChart hALoc hsmall hth hth0 hadm hg0 hgg j

/-! ## 4. A non-vacuity witness with an *interacting* diagonal variation -/

/-- A zero-mass kernel: weight `1/1000` at the origin and `-1/1000` one lattice
step away. -/
noncomputable def zeroMassWitnessKernel (_a : Fin 4) : Fin 2 → ℝ :=
  fun i => if i = 0 then 1 / 1000 else -(1 / 1000)

/-- The two displacements of the witness kernel: the origin and the unit step in
direction `0`. -/
noncomputable def zeroMassWitnessDispl (_a : Fin 4) : Fin 2 → (Fin 4 → ℝ) :=
  fun i mu => if i = 1 ∧ mu = 0 then 1 else 0

theorem zeroMassWitnessKernel_zeroMass (a : Fin 4) : ∑ i, zeroMassWitnessKernel a i = 0 := by
  simp [zeroMassWitnessKernel, Fin.sum_univ_two]

theorem zeroMassWitnessKernel_mass (a : Fin 4) :
    kernelMass (zeroMassWitnessKernel a) ≤ 1 / 500 := by
  simp [kernelMass, zeroMassWitnessKernel, Fin.sum_univ_two]
  norm_num

theorem zeroMassWitnessDispl_range (a : Fin 4) (i : Fin 2) (mu : Fin 4) :
    |zeroMassWitnessDispl a i mu| ≤ 1 := by
  simp only [zeroMassWitnessDispl]
  split <;> norm_num

/-- The witness variation is **not** the zero matrix: at the momentum
`(1/2,0,0,0)` its diagonal entry is `1/500`. -/
theorem zeroMassWitness_diag_value :
    diagCosSymbolMatrix zeroMassWitnessKernel zeroMassWitnessDispl
        (fun mu => if mu = 0 then 1 / 2 else 0) 0 0
      = 1 / 500 := by
  have h : (2 : ℝ) * π * ∑ mu : Fin 4,
      (if mu = 0 then (1 : ℝ) / 2 else 0) * zeroMassWitnessDispl 0 1 mu = π := by
    simp [zeroMassWitnessDispl]
    ring
  simp only [diagCosSymbolMatrix, Matrix.diagonal_apply_eq, cosSymbol, Fin.sum_univ_two]
  rw [h]
  norm_num [zeroMassWitnessKernel, zeroMassWitnessDispl, Fin.sum_univ_four]

theorem zeroMassWitness_smallness : linearVanishingConstant 1 (1 / 500) ≤ 1 / 2 := by
  have hpi : π < 3.15 := by
    exact Real.pi_lt_d2
  have hpi0 : 0 < π := Real.pi_pos
  unfold linearVanishingConstant
  nlinarith

/-- **The hypothesis package of `A1_beta_pos_ward_from_kernelMass` is inhabited,
with a nonzero Lorentz-diagonal variation.**  Every hypothesis is discharged:
the kernel structure conditions by computation, the remainder channels by the
empty channel families.  This is an inhabitation statement about the compiler
inputs, not an identification of Bałaban's objects. -/
theorem A1_beta_pos_ward_from_kernelMass_nonvacuous (f : ℝ) (j : ℕ) :
    (1 : ℝ) / 16777216 ≤ shellBetaOfSources
      (fun _ _ => literalOneLoopIntegrand
        (sourceVariationMatrix f 1 (diagCosSymbolMatrix zeroMassWitnessKernel zeroMassWitnessDispl))
        (fun _ => 0))
      (fun _ _ (_ : Fin 0) => (0 : ℝ)) (fun _ _ (_ : Fin 0) => (0 : ℝ))
      (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) 0 j
      (fun _ => (0 : ℝ)) := by
  refine A1_beta_pos_ward_from_kernelMass (Adm := fun h => ∀ j, h j = 0)
    (Kk := fun _ _ => zeroMassWitnessKernel) (dd := fun _ _ => zeroMassWitnessDispl)
    (Wm := fun _ _ _ => 0) (R := 1) (M := 1 / 500) (KW := 0)
    (AInt := fun _ => 0) (AChart := fun _ => 0) (ALoc := fun _ => 0)
    (LamDet := 0) (LamGauge := 0) (theta := 1 / 2)
    (by norm_num) (by norm_num)
    (fun _ _ a => zeroMassWitnessKernel_zeroMass a)
    (fun _ _ a i mu => zeroMassWitnessDispl_range a i mu)
    (fun _ _ a => zeroMassWitnessKernel_mass a) zeroMassWitness_smallness le_rfl
    (fun _ _ _ _ => measurable_const)
    (fun _ _ _ _ _ _ => by norm_num)
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

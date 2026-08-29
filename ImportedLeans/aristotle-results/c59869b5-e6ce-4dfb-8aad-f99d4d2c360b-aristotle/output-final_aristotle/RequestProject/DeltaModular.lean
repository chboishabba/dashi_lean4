import Mathlib

/-!
# The circular symmetry: `Δ(−1/z) = z¹² Δ(z)`

The vertical structure of the portrait of `Δ` (`RequestProject/VerticalWalls.lean`) came for
free: real coefficients and period one. The *other* symmetry visible in the picture — the
reflection across the arcs `|z| = 1` — is genuine modularity, and it is proved here.

We take `Δ` in its honest form, the twenty-fourth power of the Dedekind eta function,

`Δ(z) = η(z)²⁴ = q ∏_{n≥1} (1 − qⁿ)²⁴`,  `q = e^{2πiz}`,

which is exactly the eta product whose coefficients `RequestProject/DeltaGraph.lean` expands.

The proof is the classical logarithmic-derivative argument:

* `logDeriv Δ = 24 · logDeriv η = 2πi E₂` (`logDeriv_Delta`, on top of Mathlib's
  `logDeriv_eta_eq_E2`);
* `E₂` transforms with a defect: `E₂(−1/z) = z²E₂(z) − 6iz/π` (`E2_S_transform`, from
  Mathlib's `G2_S_transform`);
* that defect is exactly the logarithmic derivative of `z¹²`, so `z ↦ Δ(−1/z)` and
  `z ↦ z¹²Δ(z)` have the same logarithmic derivative on the upper half plane
  (`logDeriv_Delta_comp`, `logDeriv_weight`);
* both are nonvanishing and holomorphic there and the upper half plane is open and connected,
  so the two differ by a constant, which is `1` because `−1/i = i` and `i¹² = 1`.

The consequences drawn afterwards are the ones the picture shows: the periodicity
`Δ(z+1) = Δ(z)`, the conjugation symmetry `Δ(−z̄) = conj Δ(z)`, and the reflection in the unit
circle `Δ(1/z̄) = conj (z¹² Δ(z))`, whence `‖Δ(1/z̄)‖ = ‖z‖¹² ‖Δ(z)‖` — a genuine mirror of
`‖Δ‖` exactly on the arc `|z| = 1`.
-/

noncomputable section

open Complex ModularForm EisensteinSeries
open UpperHalfPlane hiding I
open scoped Real Topology MatrixGroups

local notation "ℍₒ" => UpperHalfPlane.upperHalfPlaneSet

namespace DeltaModular

/-- The modular discriminant, as the twenty-fourth power of the Dedekind eta function:
`Δ(z) = η(z)²⁴`. -/
def Delta (z : ℂ) : ℂ := ModularForm.eta z ^ 24

@[simp] lemma Delta_apply (z : ℂ) : Delta z = ModularForm.eta z ^ 24 := rfl

/-! ### Elementary facts about the upper half plane -/

lemma ne_zero_of_mem {z : ℂ} (hz : z ∈ ℍₒ) : z ≠ 0 := by
  have hz' : 0 < z.im := hz
  exact fun h => by simp [h] at hz'

/-- The upper half plane is stable under `z ↦ −1/z`. -/
lemma neg_inv_mem {z : ℂ} (hz : z ∈ ℍₒ) : -z⁻¹ ∈ ℍₒ := by
  have hz' : 0 < z.im := hz
  have hn : 0 < Complex.normSq z := Complex.normSq_pos.mpr (ne_zero_of_mem hz)
  show 0 < (-z⁻¹).im
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  exact div_pos hz' hn

lemma isPreconnected_upperHalfPlaneSet : IsPreconnected ℍₒ :=
  (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected

lemma coe_S_smul (z : ℍ) : ((ModularGroup.S • z : ℍ) : ℂ) = -(z : ℂ)⁻¹ := by
  rw [UpperHalfPlane.modular_S_smul]; simp

/-! ### Basic analytic facts about `Δ` -/

lemma Delta_ne_zero {z : ℂ} (hz : z ∈ ℍₒ) : Delta z ≠ 0 :=
  pow_ne_zero _ (eta_ne_zero hz)

lemma differentiableAt_Delta {z : ℂ} (hz : z ∈ ℍₒ) : DifferentiableAt ℂ Delta z :=
  (differentiableAt_eta_of_mem_upperHalfPlaneSet hz).pow 24

lemma differentiableOn_Delta : DifferentiableOn ℂ Delta ℍₒ := fun _ hz =>
  (differentiableAt_Delta hz).differentiableWithinAt

/-- The logarithmic derivative of `Δ` is `2πi E₂`. -/
lemma logDeriv_Delta (z : ℍ) : logDeriv Delta (z : ℂ) = 2 * π * I * E2 z := by
  have h : logDeriv Delta (z : ℂ) = 24 * logDeriv ModularForm.eta (z : ℂ) :=
    logDeriv_fun_pow (differentiableAt_eta_of_mem_upperHalfPlaneSet z.2) 24
  rw [h, logDeriv_eta_eq_E2]
  ring

/-! ### The defect in the transformation of `E₂` -/

/-- The weight-two Eisenstein series `G₂` under `z ↦ −1/z`. -/
lemma G2_S (z : ℍ) : G2 (ModularGroup.S • z) = (z : ℂ) ^ 2 * G2 z - 2 * π * I * z := by
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  have hG := G2_S_transform z
  field_simp at hG
  linear_combination -hG

lemma E2_eq_G2 (w : ℍ) : E2 w = (3 / (π : ℂ) ^ 2) * G2 w := by
  have hpi : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [E2]
  simp only [Pi.smul_apply, smul_eq_mul, riemannZeta_two]
  field_simp
  ring

/-- `E₂` is not modular: `E₂(−1/z) = z² E₂(z) − 6iz/π`. -/
lemma E2_S_transform (z : ℍ) :
    E2 (ModularGroup.S • z) = (z : ℂ) ^ 2 * E2 z - 6 * I * z / π := by
  have hpi : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [E2_eq_G2, E2_eq_G2, G2_S]
  field_simp
  ring

/-! ### The two logarithmic derivatives agree -/

lemma logDeriv_Delta_comp (z : ℍ) :
    logDeriv (fun w : ℂ => Delta (-w⁻¹)) (z : ℂ) = 2 * π * I * E2 z + 12 / z := by
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  have hpi : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hdg : DifferentiableAt ℂ (fun w : ℂ => -w⁻¹) (z : ℂ) := by
    fun_prop (disch := assumption)
  have hderiv : deriv (fun w : ℂ => -w⁻¹) (z : ℂ) = ((z : ℂ) ^ 2)⁻¹ := by simp
  have h2 := logDeriv_comp (f := Delta) (g := fun w : ℂ => -w⁻¹) (x := (z : ℂ))
    (differentiableAt_Delta (neg_inv_mem z.2)) hdg
  simp only [Function.comp_def] at h2
  rw [h2, hderiv, ← coe_S_smul z, logDeriv_Delta, E2_S_transform]
  field_simp
  linear_combination (-12 : ℂ) * Complex.I_sq

lemma logDeriv_weight (z : ℍ) :
    logDeriv (fun w : ℂ => w ^ 12 * Delta w) (z : ℂ) = 2 * π * I * E2 z + 12 / z := by
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  have h := logDeriv_mul (f := fun w : ℂ => w ^ 12) (g := Delta) (x := (z : ℂ))
    (pow_ne_zero 12 hz) (Delta_ne_zero z.2) (by fun_prop) (differentiableAt_Delta z.2)
  rw [h, logDeriv_pow, logDeriv_Delta]
  push_cast
  ring

/-! ### The main theorem -/

/-- **The circular symmetry.** `Δ(−1/z) = z¹² Δ(z)` on the upper half plane. -/
theorem Delta_neg_inv (z : ℍ) : Delta (-(z : ℂ)⁻¹) = (z : ℂ) ^ 12 * Delta z := by
  have hfd : DifferentiableOn ℂ (fun w : ℂ => Delta (-w⁻¹)) ℍₒ := by
    intro x hx
    have hx0 : x ≠ 0 := ne_zero_of_mem hx
    have hdg : DifferentiableAt ℂ (fun w : ℂ => -w⁻¹) x := by
      fun_prop (disch := assumption)
    exact (((differentiableAt_Delta (neg_inv_mem hx)).comp x hdg)).differentiableWithinAt
  have hgd : DifferentiableOn ℂ (fun w : ℂ => w ^ 12 * Delta w) ℍₒ := fun x hx =>
    (((differentiableAt_id.pow 12).mul (differentiableAt_Delta hx))).differentiableWithinAt
  have hfn : ∀ x ∈ ℍₒ, (fun w : ℂ => Delta (-w⁻¹)) x ≠ 0 := fun x hx =>
    Delta_ne_zero (neg_inv_mem hx)
  have hgn : ∀ x ∈ ℍₒ, (fun w : ℂ => w ^ 12 * Delta w) x ≠ 0 := fun x hx =>
    mul_ne_zero (pow_ne_zero 12 (ne_zero_of_mem hx)) (Delta_ne_zero hx)
  have heq : Set.EqOn (logDeriv fun w : ℂ => Delta (-w⁻¹))
      (logDeriv fun w : ℂ => w ^ 12 * Delta w) ℍₒ := by
    intro x hx
    have h1 := logDeriv_Delta_comp ⟨x, hx⟩
    have h2 := logDeriv_weight ⟨x, hx⟩
    simpa [UpperHalfPlane.coe] using h1.trans h2.symm
  obtain ⟨c, hc0, hc⟩ := (logDeriv_eqOn_iff hfd hgd isOpen_upperHalfPlaneSet
    isPreconnected_upperHalfPlaneSet hgn hfn).mp heq
  have hImem : (I : ℂ) ∈ ℍₒ := by simp [UpperHalfPlane.upperHalfPlaneSet]
  have hIpow : (I : ℂ) ^ 12 = 1 := by
    rw [show (12 : ℕ) = 4 * 3 from rfl, pow_mul, Complex.I_pow_four, one_pow]
  have hc1 : c = 1 := by
    have h := hc hImem
    simp only [Complex.inv_I, neg_neg, Pi.smul_apply, smul_eq_mul, hIpow, one_mul] at h
    have hz : (1 - c) * Delta I = 0 := by linear_combination h
    rcases mul_eq_zero.mp hz with h' | h'
    · exact (sub_eq_zero.mp h').symm
    · exact absurd h' (Delta_ne_zero hImem)
  have := hc z.2
  simpa [hc1] using this

/-- `Δ(−1/z) = z¹² Δ(z)`, stated for a complex number in the upper half plane. -/
theorem Delta_neg_inv' {z : ℂ} (hz : 0 < z.im) : Delta (-z⁻¹) = z ^ 12 * Delta z :=
  Delta_neg_inv ⟨z, hz⟩

/-! ### Periodicity, and hence full modularity -/

lemma qParam_one_add_one (z : ℂ) :
    Function.Periodic.qParam 1 (z + 1) = Function.Periodic.qParam 1 z := by
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  rw [mul_add, mul_one, Complex.exp_add, Complex.exp_two_pi_mul_I]
  ring

/-- The eta function picks up a twenty-fourth root of unity under `z ↦ z+1`. -/
lemma eta_add_one (z : ℂ) :
    ModularForm.eta (z + 1) = Complex.exp (2 * π * I / 24) * ModularForm.eta z := by
  unfold ModularForm.eta
  have h1 : Function.Periodic.qParam 24 (z + 1)
      = Complex.exp (2 * π * I / 24) * Function.Periodic.qParam 24 z := by
    simp only [Function.Periodic.qParam]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : ∀ n : ℕ, ModularForm.eta_q n (z + 1) = ModularForm.eta_q n z := fun n => by
    simp only [ModularForm.eta_q, qParam_one_add_one]
  rw [h1]
  simp only [h2]
  ring

/-- `Δ` has period one: the twenty-fourth power kills the root of unity. -/
theorem Delta_add_one (z : ℂ) : Delta (z + 1) = Delta z := by
  unfold Delta
  rw [eta_add_one, mul_pow, ← Complex.exp_nat_mul,
    show (24 : ℕ) * (2 * π * I / 24) = 2 * π * I by push_cast; ring,
    Complex.exp_two_pi_mul_I, one_mul]

/-- `Δ` as a function on the upper half plane. -/
def DeltaH : ℍ → ℂ := fun z => Delta (z : ℂ)

@[simp] lemma DeltaH_apply (z : ℍ) : DeltaH z = Delta (z : ℂ) := rfl

lemma DeltaH_S : DeltaH ∣[(12 : ℤ)] ModularGroup.S = DeltaH := by
  ext z
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  rw [SlashInvariantForm.slash_S_apply]
  show Delta ((-(z : ℂ))⁻¹) * (z : ℂ) ^ (-(12 : ℤ)) = Delta (z : ℂ)
  rw [inv_neg, Delta_neg_inv z, zpow_neg]
  field_simp

lemma DeltaH_T : DeltaH ∣[(12 : ℤ)] ModularGroup.T = DeltaH := by
  ext z
  simp_rw [ModularForm.SL_slash_def, UpperHalfPlane.modular_T_smul]
  simp only [ModularGroup.denom_apply, ModularGroup.T]
  norm_num
  show Delta (((1 : ℝ) +ᵥ z : ℍ) : ℂ) = Delta (z : ℂ)
  rw [UpperHalfPlane.coe_vadd]
  push_cast
  rw [add_comm, Delta_add_one]

/-- **Full modularity.** `Δ` is invariant of weight 12 under the whole of `SL₂(ℤ)`:
`Δ((az+b)/(cz+d)) = (cz+d)¹² Δ(z)`. -/
theorem DeltaH_slash (γ : SL(2, ℤ)) : DeltaH ∣[(12 : ℤ)] γ = DeltaH := by
  have hmem : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hmem using Subgroup.closure_induction with
  | one => simp
  | mem g hg =>
      rcases hg with h | h
      · rw [h]; exact DeltaH_S
      · rw [Set.mem_singleton_iff] at h; rw [h]; exact DeltaH_T
  | mul g h _ _ ig ih => rw [SlashAction.slash_mul, ig, ih]
  | inv g _ ig =>
      have h2 : (DeltaH ∣[(12 : ℤ)] g) ∣[(12 : ℤ)] g⁻¹ = DeltaH ∣[(12 : ℤ)] g⁻¹ := by rw [ig]
      rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] at h2
      exact h2.symm

/-! ### The reflection in the unit circle -/

lemma multipliable_eta {z : ℂ} (hz : z ∈ ℍₒ) :
    Multipliable (fun n : ℕ => 1 - ModularForm.eta_q n z) := by
  simpa [sub_eq_add_neg] using
    multipliable_one_add_of_summable (ModularForm.summable_eta_q ⟨z, hz⟩)

lemma qParam_conj (h : ℝ) (z : ℂ) :
    (starRingEnd ℂ) (Function.Periodic.qParam h z)
      = Function.Periodic.qParam h (-(starRingEnd ℂ) z) := by
  simp only [Function.Periodic.qParam, ← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

/-- The eta function has real `q`-coefficients: `η(−z̄) = conj η(z)`. -/
lemma eta_neg_conj {z : ℂ} (hz : z ∈ ℍₒ) :
    ModularForm.eta (-(starRingEnd ℂ) z) = (starRingEnd ℂ) (ModularForm.eta z) := by
  unfold ModularForm.eta
  rw [map_mul, ← qParam_conj,
    (multipliable_eta hz).map_tprod (starRingEnd ℂ) Complex.continuous_conj]
  congr 1
  refine tprod_congr (fun n => ?_)
  simp only [ModularForm.eta_q, map_sub, map_one, map_pow, ← qParam_conj]

/-- The vertical mirror for the true `Δ`: `Δ(−z̄) = conj Δ(z)`. -/
theorem Delta_neg_conj {z : ℂ} (hz : 0 < z.im) :
    Delta (-(starRingEnd ℂ) z) = (starRingEnd ℂ) (Delta z) := by
  unfold Delta
  rw [eta_neg_conj hz, map_pow]

/-- **The reflection in the unit circle.** `Δ(1/z̄) = conj (z¹² Δ(z))`; the map `z ↦ 1/z̄` is
the mirror across the arcs `|z| = 1`. -/
theorem Delta_inv_conj {z : ℂ} (hz : 0 < z.im) :
    Delta (((starRingEnd ℂ) z)⁻¹) = (starRingEnd ℂ) (z ^ 12 * Delta z) := by
  have hw : 0 < (-(starRingEnd ℂ) z).im := by simpa using hz
  have h := Delta_neg_inv' hw
  rw [show -(-(starRingEnd ℂ) z)⁻¹ = ((starRingEnd ℂ) z)⁻¹ by rw [inv_neg, neg_neg]] at h
  rw [h, Delta_neg_conj hz, map_mul, map_pow]
  ring

/-- `‖Δ‖` is mirrored by the reflection in the unit circle, up to the weight factor `‖z‖¹²`. -/
theorem norm_Delta_inv_conj {z : ℂ} (hz : 0 < z.im) :
    ‖Delta (((starRingEnd ℂ) z)⁻¹)‖ = ‖z‖ ^ 12 * ‖Delta z‖ := by
  rw [Delta_inv_conj hz, RCLike.norm_conj, norm_mul, norm_pow]

/-- On the arc `|z| = 1` the reflection is the identity, and the transformation law becomes a
phase lock: `conj Δ(z) = z¹² Δ(z)`. This is the circular counterpart of the vertical walls. -/
theorem Delta_arc {z : ℂ} (hz : 0 < z.im) (h1 : ‖z‖ = 1) :
    (starRingEnd ℂ) (Delta z) = z ^ 12 * Delta z := by
  have hinv : z⁻¹ = (starRingEnd ℂ) z := by
    have : z * (starRingEnd ℂ) z = 1 := by
      rw [Complex.mul_conj]
      norm_cast
      simp [Complex.normSq_eq_norm_sq, h1]
    exact inv_eq_of_mul_eq_one_right this
  have h := Delta_neg_inv' hz
  rw [hinv, Delta_neg_conj hz] at h
  exact h

/-- Consequently `z¹²Δ(z)²` is the *real* number `‖Δ(z)‖²` on the arc `|z| = 1`: the argument of
`Δ` is locked to `−6 arg z` up to half turns, exactly as it is locked to `0` or `π` on the
vertical walls. -/
theorem Delta_arc_phase {z : ℂ} (hz : 0 < z.im) (h1 : ‖z‖ = 1) :
    z ^ 12 * Delta z ^ 2 = ((‖Delta z‖ : ℝ) : ℂ) ^ 2 := by
  have h := Delta_arc hz h1
  have h2 : Delta z * (starRingEnd ℂ) (Delta z) = ((‖Delta z‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj]
    norm_cast
    simp [Complex.normSq_eq_norm_sq]
  rw [← h2, h]
  ring

end DeltaModular

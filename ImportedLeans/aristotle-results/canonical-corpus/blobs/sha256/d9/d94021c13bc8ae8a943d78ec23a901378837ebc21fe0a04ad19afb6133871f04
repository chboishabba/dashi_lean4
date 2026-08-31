/-
# Row A1a — integrability of the literal one-loop integrand

`A1WardAssembly` computes a positive floor for the literal one-loop trace on the
Ward momentum box, but it still *assumes* that the integrand is integrable on
the punctured cell (`hintg`).  That is a genuine analytic obligation, not an
identification receipt, and this file discharges it for the free case: no
Lorentz-diagonal averaging contribution and no seagull insertion.

The route is a closed form.  The lattice Ward identity of `WardTransverseVertex`
says that the transverse conjugate of the literal first variation is the scalar
`sin(2πx_ρ)` times the transverse projector.  Since the reduced bubble kernel is
`C V Cᵀ = (q̂²)⁻¹ P V P` and the bubble trace is the Frobenius norm of that
kernel, and since `Tr P = 3`, the whole integrand collapses to

    I(x) = (3/2)·sin(2πx_ρ)² / (q̂²)²                              (`freeWardIntegrand`)

with no matrices left.  Two elementary inequalities then finish the job on the
cell `[0,1/2]⁴`:

* `|sin(2πt)| = |2 sin(πt) cos(πt)| ≤ 2 sin(πt) = p̂(t)` for `t ∈ [0,1/2]`, so
  `sin(2πx_ρ)² ≤ q̂²` and hence `I(x) ≤ (3/2)/q̂²`;
* `p̂(t) ≥ 4t` on `[0,1/2]`, so `q̂² ≥ 16∑x_μ² ≥ 16‖x‖²`.

Therefore `I(x) ≤ (3/32)‖x‖⁻²`, and `‖x‖⁻²` is integrable in four dimensions
(`integrable_radialCutoff_norm`, via the polar-coordinates criterion).  This
gives `literalOneLoopIntegrand_free_integrableOn`, and hence a version of
`A1_beta_pos_ward` with the integrability hypothesis removed
(`A1_beta_pos_ward_free`), together with a fully instantiated witness showing
the whole hypothesis package is inhabited (`A1_beta_pos_ward_nonvacuous`).

**This does not close Row A1.**  The witness is an inhabitation statement about
the compiler inputs, *not* an identification of Bałaban's objects; the residual
obligations of `A1_beta_pos_ward` — the diagonal bound on the averaging and
constrained-projection variations, the integrability of the *interacting*
integrand, and the five remainder-channel majorants — are untouched here except
for integrability in the free case.  Scoreboard unchanged: `A, B, C, D` open,
frozen research count 4.
-/
import RequestProject.YangMills.A1WardAssembly

namespace YangMills

open Real Matrix Finset MeasureTheory Set

/-! ## 1. A radial majorant that is integrable in four dimensions -/

/-- The cut-off radial profile `y ↦ y⁻²·1_{y ≤ 1}`. -/
noncomputable def radialCutoff : ℝ → ℝ := fun y => if y ≤ 1 then (y ^ 2)⁻¹ else 0

theorem radialCutoff_nonneg (y : ℝ) : 0 ≤ radialCutoff y := by
  unfold radialCutoff
  split <;> positivity

/-- The polar-coordinates integrand of `radialCutoff` in four dimensions is
integrable on `(0, ∞)`. -/
theorem integrableOn_radialCutoff_polar :
    IntegrableOn (fun y : ℝ => y ^ (4 - 1) • radialCutoff y) (Ioi 0) volume := by
  have hEq : ∀ y ∈ Ioi (0 : ℝ), y ^ (4 - 1) • radialCutoff y = (if y ≤ 1 then y else 0) := by
    intro y hy
    have hy0 : y ≠ 0 := ne_of_gt hy
    simp only [radialCutoff, smul_eq_mul]
    by_cases h : y ≤ 1
    · simp only [if_pos h]; field_simp
    · simp [h]
  refine IntegrableOn.congr_fun ?_ (fun y hy => (hEq y hy).symm) measurableSet_Ioi
  have hsplit : Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
    rw [Set.Ioc_union_Ioi_eq_Ioi (by norm_num)]
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · refine IntegrableOn.congr_fun (f := fun y : ℝ => y) continuous_id.integrableOn_Ioc ?_
      measurableSet_Ioc
    intro y hy; simp [hy.2]
  · refine IntegrableOn.congr_fun (f := fun _ : ℝ => (0 : ℝ)) integrableOn_zero ?_
      measurableSet_Ioi
    intro y hy
    simp [not_le.mpr (mem_Ioi.mp hy)]

/-- **`‖x‖⁻²` is integrable in four dimensions** (with the cut-off at radius
one). -/
theorem integrable_radialCutoff_norm :
    Integrable (fun x : Fin 4 → ℝ => radialCutoff ‖x‖) volume := by
  rw [MeasureTheory.integrable_fun_norm_addHaar]
  simpa using integrableOn_radialCutoff_polar

/-! ## 2. The trace of the transverse projector -/

/-- The transverse projector of a nonzero vector in four dimensions has trace
`3`: it projects onto the orthogonal complement of a line. -/
theorem trace_transverseProjector {u : Fin 4 → ℝ} (hu : normSqVec u ≠ 0) :
    (transverseProjector u).trace = 3 := by
  rw [transverseProjector, Matrix.trace_sub, Matrix.trace_one, Matrix.trace_smul]
  have hvm : (Matrix.vecMulVec u u).trace = normSqVec u := by
    simp [Matrix.trace, Matrix.diag_apply, Matrix.vecMulVec_apply, normSqVec]
  rw [hvm, smul_eq_mul, inv_mul_cancel₀ hu]
  norm_num

/-- The Frobenius norm square of a multiple of the transverse projector. -/
theorem sum_sq_smul_transverseProjector {u : Fin 4 → ℝ} (hu : normSqVec u ≠ 0) (c : ℝ) :
    ∑ a, ∑ b, ((c • transverseProjector u) a b) ^ 2 = 3 * c ^ 2 := by
  have hsymm : ((c • transverseProjector u))ᵀ = c • transverseProjector u := by
    rw [Matrix.transpose_smul, transverseProjector_transpose]
  have h := trace_symm_mul_self_eq_sum_sq (c • transverseProjector u) hsymm
  rw [← h, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    transverseProjector_idem u hu, Matrix.trace_smul, trace_transverseProjector hu,
    smul_eq_mul]
  ring

/-! ## 3. The closed form of the free literal integrand -/

/-- **The literal one-loop integrand in the free case, in closed form.**  No
matrices survive: the transverse conjugation of the Wilson vertex is a scalar
multiple of the projector, and the projector has trace `3`. -/
noncomputable def freeWardIntegrand (rho : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  3 / 2 * (sinAtom (2 * x rho)) ^ 2 / (phatSq x) ^ 2

theorem freeWardIntegrand_nonneg (rho : Fin 4) (x : Fin 4 → ℝ) : 0 ≤ freeWardIntegrand rho x := by
  unfold freeWardIntegrand
  positivity

theorem literalOneLoopIntegrand_free_eq (f : ℝ) (rho : Fin 4) {x : Fin 4 → ℝ}
    (hne : phatSq x ≠ 0) :
    literalOneLoopIntegrand (sourceVariationMatrix f rho (fun _ => 0)) (fun _ => 0) x
      = freeWardIntegrand rho x := by
  have hnorm : normSqVec (phatVec x) ≠ 0 := by rwa [normSqVec_phatVec]
  have hV : (sourceVariationMatrix f rho (fun _ => 0) x)ᵀ
      = sourceVariationMatrix f rho (fun _ => 0) x :=
    sourceVariationMatrix_transpose (fun _ a b _ => rfl) x
  have hconj : transverseProjector (phatVec x) * sourceVariationMatrix f rho (fun _ => 0) x
      * transverseProjector (phatVec x)
      = sinAtom (2 * x rho) • transverseProjector (phatVec x) := by
    have hsplit : transverseProjector (phatVec x) * sourceVariationMatrix f rho (fun _ => 0) x
        * transverseProjector (phatVec x)
        = transverseProjector (phatVec x) * wilsonBgZeroMatrix x rho
            * transverseProjector (phatVec x)
          + transverseProjector (phatVec x) * gaugeVariationMatrix f (phatVec x) rho
              * transverseProjector (phatVec x)
          + transverseProjector (phatVec x) * (0 : Matrix (Fin 4) (Fin 4) ℝ)
              * transverseProjector (phatVec x) := by
      simp only [sourceVariationMatrix, Matrix.mul_add, Matrix.add_mul]
    rw [hsplit, transverseProjector_conj_wilsonBgZeroMatrix x rho hne,
      transverseProjector_conj_gaugeVariationMatrix f x rho hne]
    simp
  have hred : latticeGramFactor x * sourceVariationMatrix f rho (fun _ => 0) x
      * (latticeGramFactor x)ᵀ
      = ((phatSq x)⁻¹ * sinAtom (2 * x rho)) • transverseProjector (phatVec x) := by
    have hnn : (0 : ℝ) ≤ phatSq x := by rw [phatSq]; positivity
    rw [latticeReducedBubble_eq x hnn, hconj, smul_smul]
  have hG : latticeSymbolOf x = (latticeGramFactor x)ᵀ * latticeGramFactor x :=
    latticeSymbol_eq_gram x hne
  have hbub := bubble_eq_frobenius (G := latticeSymbolOf x)
    (V := sourceVariationMatrix f rho (fun _ => 0) x) (C := latticeGramFactor x) hG hV
  rw [literalOneLoopIntegrand, betaTrace, hbub, hred,
    sum_sq_smul_transverseProjector hnorm]
  simp only [Matrix.mul_zero, Matrix.transpose_zero, neg_zero,
    Matrix.trace_zero]
  rw [freeWardIntegrand]
  field_simp
  ring

/-! ## 4. The radial majorant on the cell -/

/-- On the cell the doubled sine atom is dominated by the lattice momentum
component: `|sin(2πt)| ≤ p̂(t)` for `t ∈ [0,1/2]`. -/
theorem abs_sinAtom_two_mul_le_phat {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    |sinAtom (2 * t)| ≤ phat t := by
  have hd : sinAtom (2 * t) = 2 * Real.sin (π * t) * Real.cos (π * t) := by
    rw [sinAtom, show π * (2 * t) = 2 * (π * t) by ring, Real.sin_two_mul]
  have hs : 0 ≤ Real.sin (π * t) := by
    have := sinAtom_nonneg h0 h1
    rwa [sinAtom] at this
  have hc : |Real.cos (π * t)| ≤ 1 := Real.abs_cos_le_one _
  rw [hd, phat, sinAtom, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.sin (π * t))]
  calc 2 * Real.sin (π * t) * |Real.cos (π * t)|
      ≤ 2 * Real.sin (π * t) * 1 := by
        exact mul_le_mul_of_nonneg_left hc (by positivity)
    _ = 2 * Real.sin (π * t) := by ring

/-- On the cell, `p̂(t)² ≥ 16t²`. -/
theorem sixteen_mul_sq_le_phat_sq {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    16 * t ^ 2 ≤ (phat t) ^ 2 := by
  have h := two_mul_le_sinAtom h0 h1
  have hph : 4 * t ≤ phat t := by rw [phat]; linarith
  nlinarith [mul_nonneg h0 h0]

/-- On the cell, `q̂² ≥ 16‖x‖²` for the supremum norm. -/
theorem sixteen_mul_normSq_le_phatSq {x : Fin 4 → ℝ} (hx : x ∈ momentumCell) :
    16 * ‖x‖ ^ 2 ≤ phatSq x := by
  have hb : ∀ mu : Fin 4, 0 ≤ x mu ∧ x mu ≤ 1 / 2 := by
    intro mu
    have := hx mu (mem_univ mu)
    simpa [momentumCell] using this
  have hsum : ∑ mu : Fin 4, 16 * (x mu) ^ 2 ≤ phatSq x := by
    rw [phatSq]
    exact Finset.sum_le_sum fun mu _ => sixteen_mul_sq_le_phat_sq (hb mu).1 (hb mu).2
  have hnorm : ‖x‖ ^ 2 ≤ ∑ mu : Fin 4, (x mu) ^ 2 := by
    have hnn : (0 : ℝ) ≤ ∑ mu : Fin 4, (x mu) ^ 2 :=
      Finset.sum_nonneg fun mu _ => sq_nonneg _
    have hle : ‖x‖ ≤ Real.sqrt (∑ mu : Fin 4, (x mu) ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun mu => ?_
      have hmem : (x mu) ^ 2 ≤ ∑ nu : Fin 4, (x nu) ^ 2 :=
        Finset.single_le_sum (f := fun nu : Fin 4 => (x nu) ^ 2)
          (fun nu _ => sq_nonneg _) (mem_univ mu)
      have hs := Real.sqrt_le_sqrt hmem
      rw [Real.sqrt_sq_eq_abs] at hs
      simpa [Real.norm_eq_abs] using hs
    have hsq := mul_self_le_mul_self (norm_nonneg x) hle
    rw [Real.mul_self_sqrt hnn] at hsq
    nlinarith [hsq]
  calc 16 * ‖x‖ ^ 2 ≤ 16 * ∑ mu : Fin 4, (x mu) ^ 2 := by linarith
    _ = ∑ mu : Fin 4, 16 * (x mu) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ phatSq x := hsum

/-- On the cell, `‖x‖ ≤ 1/2`. -/
theorem norm_le_half_of_mem_momentumCell {x : Fin 4 → ℝ} (hx : x ∈ momentumCell) :
    ‖x‖ ≤ 1 / 2 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun mu => ?_
  have hmu : x mu ∈ Set.Icc (0 : ℝ) (1 / 2) := by
    simpa [momentumCell] using hx mu (mem_univ mu)
  rw [Real.norm_eq_abs, abs_of_nonneg hmu.1]
  exact hmu.2

/-- **The radial majorant.**  On the momentum cell the free literal integrand is
dominated by `(3/32)‖x‖⁻²`. -/
theorem freeWardIntegrand_le_radial {rho : Fin 4} {x : Fin 4 → ℝ} (hx : x ∈ momentumCell) :
    freeWardIntegrand rho x ≤ 3 / 32 * radialCutoff ‖x‖ := by
  have hb : 0 ≤ x rho ∧ x rho ≤ 1 / 2 := by
    have := hx rho (mem_univ rho)
    simpa [momentumCell] using this
  have hhalf := norm_le_half_of_mem_momentumCell hx
  have hcut : radialCutoff ‖x‖ = (‖x‖ ^ 2)⁻¹ := by
    rw [radialCutoff, if_pos (by linarith)]
  rw [hcut]
  rcases eq_or_lt_of_le (norm_nonneg x) with hz | hpos
  · -- `x = 0`: both sides vanish
    have hx0 : x = 0 := by
      have : ‖x‖ = 0 := hz.symm
      exact norm_eq_zero.mp this
    have hr : x rho = 0 := by rw [hx0]; rfl
    rw [freeWardIntegrand, hr]
    simp [sinAtom]
  · have hnormsq : 0 < ‖x‖ ^ 2 := by positivity
    have h16 := sixteen_mul_normSq_le_phatSq hx
    have hq : 0 < phatSq x := lt_of_lt_of_le (by linarith) h16
    -- `sin(2πx_ρ)² ≤ p̂(x_ρ)² ≤ q̂²`
    have hsin : (sinAtom (2 * x rho)) ^ 2 ≤ phatSq x := by
      have habs := abs_sinAtom_two_mul_le_phat hb.1 hb.2
      have hph : (phat (x rho)) ^ 2 ≤ phatSq x := by
        rw [phatSq]
        exact Finset.single_le_sum (f := fun mu : Fin 4 => (phat (x mu)) ^ 2)
          (fun mu _ => sq_nonneg _) (mem_univ rho)
      have hnn : 0 ≤ phat (x rho) := le_trans (abs_nonneg _) habs
      nlinarith [sq_abs (sinAtom (2 * x rho)), abs_nonneg (sinAtom (2 * x rho))]
    rw [freeWardIntegrand, div_le_iff₀ (by positivity)]
    have hstep : 3 / 2 * (sinAtom (2 * x rho)) ^ 2 ≤ 3 / 2 * phatSq x := by linarith
    have hmain : 3 / 2 * phatSq x ≤ 3 / 32 * (‖x‖ ^ 2)⁻¹ * phatSq x ^ 2 := by
      have hkey : 3 / 2 * phatSq x * ‖x‖ ^ 2 ≤ 3 / 32 * phatSq x ^ 2 := by
        nlinarith [mul_nonneg hq.le (sub_nonneg.mpr h16)]
      calc 3 / 2 * phatSq x = (3 / 2 * phatSq x * ‖x‖ ^ 2) * (‖x‖ ^ 2)⁻¹ := by
            field_simp
        _ ≤ (3 / 32 * phatSq x ^ 2) * (‖x‖ ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hkey (by positivity)
        _ = 3 / 32 * (‖x‖ ^ 2)⁻¹ * phatSq x ^ 2 := by ring
    linarith

/-! ## 5. Integrability of the free literal integrand -/

theorem measurable_freeWardIntegrand (rho : Fin 4) : Measurable (freeWardIntegrand rho) := by
  have hnum : Measurable fun x : Fin 4 → ℝ => 3 / 2 * (sinAtom (2 * x rho)) ^ 2 := by
    have : Continuous fun x : Fin 4 → ℝ => 3 / 2 * (sinAtom (2 * x rho)) ^ 2 := by
      unfold sinAtom
      fun_prop
    exact this.measurable
  have hden : Measurable fun x : Fin 4 → ℝ => (phatSq x) ^ 2 := by
    have : Continuous fun x : Fin 4 → ℝ => (phatSq x) ^ 2 := by
      unfold phatSq phat sinAtom
      fun_prop
    exact this.measurable
  exact hnum.div hden

theorem freeWardIntegrand_integrableOn (rho : Fin 4) :
    IntegrableOn (freeWardIntegrand rho) momentumCell := by
  have hg : IntegrableOn (fun x : Fin 4 → ℝ => 3 / 32 * radialCutoff ‖x‖) momentumCell :=
    (integrable_radialCutoff_norm.const_mul (3 / 32)).integrableOn
  refine hg.mono' ((measurable_freeWardIntegrand rho).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_momentumCell).mpr ?_
  filter_upwards with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (freeWardIntegrand_nonneg rho x)]
  exact freeWardIntegrand_le_radial hx

/-- **The literal one-loop integrand is integrable on the punctured cell** in the
free case.  This discharges the `hintg` obligation of `A1_beta_pos_ward` when the
Lorentz-diagonal contribution and the seagull insertion are absent. -/
theorem literalOneLoopIntegrand_free_integrableOn (f : ℝ) (rho : Fin 4) :
    IntegrableOn (literalOneLoopIntegrand (sourceVariationMatrix f rho (fun _ => 0))
      (fun _ => 0)) puncturedCell := by
  have hsub : IntegrableOn (freeWardIntegrand rho) puncturedCell :=
    (freeWardIntegrand_integrableOn rho).mono_set (Set.diff_subset)
  refine hsub.congr_fun ?_ measurableSet_puncturedCell
  intro x hx
  exact (literalOneLoopIntegrand_free_eq f rho (phatSq_ne_zero_of_mem_puncturedCell hx)).symm

/-! ## 6. Row A1a in the free case, and a non-vacuity witness -/

/-- **Row A1a from the literal one-loop trace, with integrability proved.**  The
free case of `A1_beta_pos_ward`: no Lorentz-diagonal averaging contribution, no
seagull insertion, and no integrability hypothesis. -/
theorem A1_beta_pos_ward_free
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {Adm : (ℕ → ℝ) → Prop} {g : ℕ → ℝ} {f : ℝ}
    {lamDet : ℕ → (ℕ → ℝ) → ι → ℝ} {lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ}
    {aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    {AInt AChart ALoc : ℕ → ℝ} {N : ℕ} {LamDet LamGauge theta : ℝ}
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
      (fun _ _ => literalOneLoopIntegrand (sourceVariationMatrix f 1 (fun _ => 0)) (fun _ => 0))
      lamDet lamGauge aInt aChart aLoc N j g :=
  A1_beta_pos_ward (d := 0) (Dm := fun _ _ _ => 0) (Wm := fun _ _ _ => 0)
    (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ => by simp) (by norm_num)
    (fun _ _ => literalOneLoopIntegrand_free_integrableOn f 1)
    hLd hLg hAInt hAChart hALoc hsmall hth hth0 hadm hg0 hgg j

/-- **The hypothesis package is inhabited.**  A completely instantiated instance
of `A1_beta_pos_ward_free` with no hypotheses left at all.

This is an *inhabitation* statement about the compiler inputs.  It is emphatically
**not** an identification of Bałaban's literal objects with those inputs, and it
does not close Row A1. -/
theorem A1_beta_pos_ward_nonvacuous (f : ℝ) (j : ℕ) :
    (1 : ℝ) / 16777216 ≤ shellBetaOfSources
      (fun _ _ => literalOneLoopIntegrand (sourceVariationMatrix f 1 (fun _ => 0)) (fun _ => 0))
      (fun _ _ (_ : Fin 0) => (0 : ℝ)) (fun _ _ (_ : Fin 0) => (0 : ℝ))
      (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) 0 j
      (fun _ => (0 : ℝ)) := by
  refine A1_beta_pos_ward_free (Adm := fun h => ∀ j, h j = 0)
    (AInt := fun _ => 0) (AChart := fun _ => 0) (ALoc := fun _ => 0)
    (LamDet := 0) (LamGauge := 0) (theta := 1 / 2)
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

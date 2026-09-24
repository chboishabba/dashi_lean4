/-
# `C55`: the continuous level-annulus pigeonhole

`IncrementModulusCancellation.lean` shows that for the profile entropy
`β(q) = ζ(r_ε)` the radial channel cancels except on the set where `ζ″ ≠ 0`.
For a *smoothed* truncation `ζ_{λ,δ}` that set is the level annulus
`λ < r < λ+δ`, on which `|ζ″_{λ,δ}| ≲ δ^{-1}`.  Estimating that residual level by
level costs a factor `δ^{-1}`.

It need not be paid.  Averaging over the level `λ` instead of controlling every
level, for a fixed `r`,

  `∫_{λ₀}^{λ₁} δ^{-1}·1_{λ<r<λ+δ} dλ ≤ 1`,

with **no** `δ^{-1}` left over: the annuli at different levels are essentially
disjoint.  By Fubini, for any nonnegative density `G`,

  `∫_{λ₀}^{λ₁} ∫ G·|ζ″_{λ,δ}(r)| dλ ≤ ∫ G`,

so *some* level `λ_* ∈ [λ₀,λ₁]` satisfies

  `∫ G·|ζ″_{λ_*,δ}(r)| ≤ (λ₁−λ₀)^{-1}∫ G`.                              (C55)

De Giorgi only ever needs *one* level in a prescribed range, so this is enough.

Contents:

* `ClayNS.annulusKernel` and `ClayNS.integral_annulusKernel_le_one` — the exact
  one-dimensional level integral, for an arbitrary nonnegative profile of unit
  mass rescaled to width `δ` (the sharp `δ`-free bound);
* `ClayNS.levelAnnulusFubini` — the Fubini step on the periodic cell;
* `ClayNS.smoothedModulusLevelAnnulusPigeonhole` — (C55) for a general
  nonnegative kernel of unit level mass;
* `ClayNS.exists_level_smoothing_annulus_bound` — the form the modulus residual
  consumes: any residual profile dominated by the annulus kernel has a level at
  which its weighted cell integral is at most the average of the density.

Nothing here is specific to the Gaussian weight or to Navier–Stokes; the
statement is exactly the pigeonhole the smoothing annulus needs.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.PeriodicIntegral

open Real MeasureTheory Set

noncomputable section

namespace ClayNS

/-! ## The level-annulus kernel and its exact level integral -/

/-- The smoothing-annulus kernel of width `δ` at level `λ`, built from a fixed
profile `w`: `K_λ(s) = δ^{-1}w((s−λ)/δ)`.  For `w = 1_{(0,1)}` this is exactly
`δ^{-1}1_{λ<s<λ+δ}`, the bound available for `|ζ″_{λ,δ}|`. -/
def annulusKernel (delta : ℝ) (w : ℝ → ℝ) (lam s : ℝ) : ℝ := w ((s - lam) / delta) / delta

lemma annulusKernel_nonneg {delta : ℝ} (hd : 0 < delta) {w : ℝ → ℝ} (hw0 : ∀ u, 0 ≤ w u)
    (lam s : ℝ) : 0 ≤ annulusKernel delta w lam s :=
  div_nonneg (hw0 _) hd.le

lemma continuous_annulusKernel (delta : ℝ) {w : ℝ → ℝ} (hw : Continuous w) :
    Continuous fun p : ℝ × ℝ => annulusKernel delta w p.1 p.2 := by
  unfold annulusKernel
  fun_prop

/-- **The exact level integral, with no `δ^{-1}` loss.**  Integrating the
annulus kernel over the *level* `λ` — rather than over space — returns the mass
of the profile, independently of `δ`. -/
theorem integral_annulusKernel_le_one {delta : ℝ} (hd : 0 < delta) {w : ℝ → ℝ}
    (hw0 : ∀ u, 0 ≤ w u) (hwi : Integrable w) (hw1 : ∫ u, w u ≤ 1)
    {lam0 lam1 : ℝ} (hlam : lam0 ≤ lam1) (s : ℝ) :
    ∫ lam in Set.Icc lam0 lam1, annulusKernel delta w lam s ≤ 1 := by
  have hab : (s - lam1) / delta ≤ (s - lam0) / delta := by gcongr
  have h1 : ∫ lam in Set.Icc lam0 lam1, annulusKernel delta w lam s
      = ∫ lam in lam0..lam1, w ((s - lam) / delta) / delta := by
    rw [intervalIntegral.integral_of_le hlam, integral_Icc_eq_integral_Ioc]
    rfl
  have h2 : ∫ lam in lam0..lam1, w ((s - lam) / delta) / delta
      = ∫ y in (s - lam1)..(s - lam0), w (y / delta) / delta :=
    intervalIntegral.integral_comp_sub_left (fun y => w (y / delta) / delta) s
  have h3 : ∫ y in (s - lam1)..(s - lam0), w (y / delta) / delta
      = delta • ∫ u in ((s - lam1) / delta)..((s - lam0) / delta), w u / delta :=
    intervalIntegral.integral_comp_div (fun y => w y / delta) (ne_of_gt hd)
  have h4 : ∫ u in ((s - lam1) / delta)..((s - lam0) / delta), w u / delta
      = (∫ u in ((s - lam1) / delta)..((s - lam0) / delta), w u) / delta :=
    intervalIntegral.integral_div delta w
  have h5 : ∫ u in ((s - lam1) / delta)..((s - lam0) / delta), w u ≤ 1 := by
    rw [intervalIntegral.integral_of_le hab]
    exact le_trans (setIntegral_le_integral hwi (Filter.Eventually.of_forall hw0)) hw1
  rw [h1, h2, h3, h4, smul_eq_mul, mul_div_cancel₀ _ (ne_of_gt hd)]
  exact h5

/-! ## The Fubini step -/

section Fubini

variable {G r : E3 → ℝ} {K : ℝ → ℝ → ℝ}

/-- The joint continuity of the density-kernel product. -/
private lemma continuous_levelDens (hG : Continuous G) (hr : Continuous r)
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) :
    Continuous fun p : ℝ × (Fin 3 → ℝ) => G (coord p.2) * K p.1 (r (coord p.2)) := by
  have hc : Continuous fun p : ℝ × (Fin 3 → ℝ) => coord p.2 :=
    coord.continuous.comp continuous_snd
  exact (hG.comp hc).mul (hK.comp (continuous_fst.prodMk ((hr.comp hc))))

/-- **The Fubini step.**  The level average of the weighted cell integrals is
bounded by the cell integral of the density alone, provided every level integral
of the kernel is at most `1`. -/
theorem levelAnnulusFubini (hG : Continuous G) (hG0 : ∀ x, 0 ≤ G x) (hr : Continuous r)
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    {lam0 lam1 : ℝ}
    (hKint : ∀ s, ∫ l in Set.Icc lam0 lam1, K l s ≤ 1) :
    (∫ l in Set.Icc lam0 lam1, cellInt (fun x => G x * K l (r x))) ≤ cellInt G := by
  set Psi : ℝ → (Fin 3 → ℝ) → ℝ := fun l y => G (coord y) * K l (r (coord y)) with hPsi
  have hc : Continuous fun p : ℝ × (Fin 3 → ℝ) => Psi p.1 p.2 :=
    continuous_levelDens hG hr hK
  have hint : Integrable (fun p : ℝ × (Fin 3 → ℝ) => Psi p.1 p.2)
      ((volume.restrict (Set.Icc lam0 lam1)).prod (volume.restrict cell)) := by
    have h : IntegrableOn (fun p : ℝ × (Fin 3 → ℝ) => Psi p.1 p.2)
        (Set.Icc lam0 lam1 ×ˢ cell) :=
      hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_cell)
    rwa [IntegrableOn, MeasureTheory.Measure.volume_eq_prod, ← Measure.prod_restrict] at h
  have hswap : (∫ l in Set.Icc lam0 lam1, ∫ y in cell, Psi l y)
      = ∫ y in cell, ∫ l in Set.Icc lam0 lam1, Psi l y := integral_integral_swap hint
  -- the inner level integral is at most the density
  have hinner : ∀ y : Fin 3 → ℝ,
      (∫ l in Set.Icc lam0 lam1, Psi l y) ≤ G (coord y) := by
    intro y
    have hmul : (∫ l in Set.Icc lam0 lam1, Psi l y)
        = G (coord y) * ∫ l in Set.Icc lam0 lam1, K l (r (coord y)) :=
      integral_const_mul _ _
    have := mul_le_mul_of_nonneg_left (hKint (r (coord y))) (hG0 (coord y))
    rw [hmul]
    linarith [this]
  have hIint : IntegrableOn (fun y => ∫ l in Set.Icc lam0 lam1, Psi l y) cell :=
    MeasureTheory.Integrable.integral_prod_right hint
  have hmono : (∫ y in cell, ∫ l in Set.Icc lam0 lam1, Psi l y) ≤ ∫ y in cell, G (coord y) :=
    setIntegral_mono_on hIint (integrableOn_cell_of_continuous hG) measurableSet_cell
      fun y _ => hinner y
  calc (∫ l in Set.Icc lam0 lam1, cellInt (fun x => G x * K l (r x)))
      = ∫ l in Set.Icc lam0 lam1, ∫ y in cell, Psi l y := rfl
    _ = ∫ y in cell, ∫ l in Set.Icc lam0 lam1, Psi l y := hswap
    _ ≤ ∫ y in cell, G (coord y) := hmono
    _ = cellInt G := rfl

/-- **`C55`.  The continuous level-annulus pigeonhole.**  For a nonnegative
kernel whose *level* integral is at most `1` at every point — the smoothing
annulus is such a kernel, by `ClayNS.integral_annulusKernel_le_one` — there is a
level `λ_*` in the prescribed range at which the weighted cell integral is at
most the level average of the density.  No power of the smoothing width `δ` is
lost. -/
theorem smoothedModulusLevelAnnulusPigeonhole (hG : Continuous G) (hG0 : ∀ x, 0 ≤ G x)
    (hr : Continuous r) (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    {lam0 lam1 : ℝ} (hlt : lam0 < lam1)
    (hKint : ∀ s, ∫ l in Set.Icc lam0 lam1, K l s ≤ 1) :
    ∃ lams ∈ Set.Icc lam0 lam1,
      cellInt (fun x => G x * K lams (r x)) ≤ cellInt G / (lam1 - lam0) := by
  set F : ℝ → ℝ := fun l => cellInt (fun x => G x * K l (r x)) with hF
  set Psi : ℝ → (Fin 3 → ℝ) → ℝ := fun l y => G (coord y) * K l (r (coord y)) with hPsi
  have hc : Continuous fun p : ℝ × (Fin 3 → ℝ) => Psi p.1 p.2 :=
    continuous_levelDens hG hr hK
  have hint : Integrable (fun p : ℝ × (Fin 3 → ℝ) => Psi p.1 p.2)
      ((volume.restrict (Set.Icc lam0 lam1)).prod (volume.restrict cell)) := by
    have h : IntegrableOn (fun p : ℝ × (Fin 3 → ℝ) => Psi p.1 p.2)
        (Set.Icc lam0 lam1 ×ˢ cell) :=
      hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_cell)
    rwa [IntegrableOn, MeasureTheory.Measure.volume_eq_prod, ← Measure.prod_restrict] at h
  have hFint : IntegrableOn F (Set.Icc lam0 lam1) := hint.integral_prod_left
  have hmeas0 : volume (Set.Icc lam0 lam1) ≠ 0 := by
    rw [Real.volume_Icc]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  have hmeastop : volume (Set.Icc lam0 lam1) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  obtain ⟨lams, hmem, hle⟩ :=
    MeasureTheory.exists_le_setAverage (μ := volume) (s := Set.Icc lam0 lam1) (f := F)
      hmeas0 hmeastop hFint
  refine ⟨lams, hmem, ?_⟩
  have hreal : (volume.real (Set.Icc lam0 lam1)) = lam1 - lam0 := by
    rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  have havg : (⨍ l in Set.Icc lam0 lam1, F l)
      = (lam1 - lam0)⁻¹ * ∫ l in Set.Icc lam0 lam1, F l := by
    rw [setAverage_eq, hreal, smul_eq_mul]
  have hfub := levelAnnulusFubini hG hG0 hr hK hKint
  have hpos : (0:ℝ) < lam1 - lam0 := by linarith
  have hstep : (lam1 - lam0)⁻¹ * ∫ l in Set.Icc lam0 lam1, F l
      ≤ (lam1 - lam0)⁻¹ * cellInt G :=
    mul_le_mul_of_nonneg_left hfub (by positivity)
  have hfin : F lams ≤ (lam1 - lam0)⁻¹ * cellInt G := by
    rw [havg] at hle
    linarith
  rw [div_eq_inv_mul]
  exact hfin

end Fubini

/-! ## The form the modulus residual consumes -/

/-- **`C55` for the smoothing annulus.**  If the residual profile `Z` (in
practice `ζ″_{λ,δ}`) is dominated by the annulus kernel of width `δ`, then some
level `λ_*` in the prescribed range pays no more than the average of the
density.  The estimate is uniform in `δ`: the `δ^{-1}` of the pointwise bound has
been absorbed by the level average. -/
theorem exists_level_smoothing_annulus_bound {G r : E3 → ℝ} {Z : ℝ → ℝ → ℝ} {delta : ℝ}
    (hd : 0 < delta) {w : ℝ → ℝ} (hw : Continuous w) (hw0 : ∀ u, 0 ≤ w u)
    (hwi : Integrable w) (hw1 : ∫ u, w u ≤ 1)
    (hG : Continuous G) (hG0 : ∀ x, 0 ≤ G x) (hr : Continuous r)
    (hZ : ∀ l, Continuous fun x : E3 => Z l (r x))
    (hdom : ∀ l s, |Z l s| ≤ annulusKernel delta w l s)
    {lam0 lam1 : ℝ} (hlt : lam0 < lam1) :
    ∃ lams ∈ Set.Icc lam0 lam1,
      cellInt (fun x => G x * |Z lams (r x)|) ≤ cellInt G / (lam1 - lam0) := by
  obtain ⟨lams, hmem, hle⟩ := smoothedModulusLevelAnnulusPigeonhole (G := G) (r := r)
    (K := annulusKernel delta w) hG hG0 hr (continuous_annulusKernel delta hw) hlt
    (fun s => integral_annulusKernel_le_one hd hw0 hwi hw1 hlt.le s)
  refine ⟨lams, hmem, le_trans (cellInt_mono ?_ ?_ ?_) hle⟩
  · exact hG.mul (hZ lams).abs
  · exact hG.mul ((continuous_annulusKernel delta hw).comp
      (continuous_const.prodMk hr))
  · exact fun x => mul_le_mul_of_nonneg_left (hdom lams (r x)) (hG0 x)

end ClayNS

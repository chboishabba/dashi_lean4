/-
# Row A1a — the Ward-patch floor from *one* source-regularity constant

`A1_beta_pos_ward_of_linearVanishing` (`LiteralIntegrability`) still carries two
independent numerical inputs on the Lorentz-diagonal averaging /
constrained-projection variation `D`:

* a **linear-vanishing** bound `|D(x)_{ab}| ≤ K_D‖x‖`, used to make the one-loop
  integrand integrable at zero momentum, and
* a **diagonal-size** bound `|D(x)_{aa}| ≤ d ≤ 1/4`, used to keep the Ward
  factor `sin(2πx_ρ) − d` positive on the Ward patch.

The second one is redundant.  The Ward patch lies inside the momentum cell,
where the supremum norm is at most `1/2`; so the *same* linear-vanishing
constant already bounds the diagonal entries there by `K_D/2`, and
`K_D ≤ 1/2` is exactly what the Ward floor needs.  This file

* localises the Ward-patch floor, so that the diagonal bound is only ever
  required on the patch (`literalOneLoopIntegrand_wardPatch_floor_local`), and
* re-runs the shell assembly with the diagonal-size datum deleted
  (`A1_beta_pos_ward_from_regularity`).

The result is that the whole Gaussian sector of the Row A1a shell bound is now
driven by a single regularity constant of the source data: a local derivative
bound on Bałaban's averaging / constrained-projection operators of size
`K_D ≤ 1/2`, together with boundedness of the seagull insertion.

**Honest status — Row A1 is not closed.**  What remains is the identification of
`K_D` with a published derivative estimate for the averaging operator, and the
five remainder-channel majorants.  Scoreboard unchanged: `A, B, C, D` open.
-/
import RequestProject.YangMills.LiteralIntegrability

namespace YangMills

open Real Matrix Finset MeasureTheory Set

/-! ## 1. The Ward patch sits inside the cell, where `‖x‖ ≤ 1/2` -/

theorem wardPatch_norm_le_half {x : Fin 4 → ℝ} (hx : x ∈ wardPatch) : ‖x‖ ≤ 1 / 2 :=
  norm_le_half_of_mem_momentumCell (wardPatch_subset_momentumCell hx)

/-- **The diagonal-size datum is implied by the linear-vanishing datum.**  On the
Ward patch a linear bound `|D(x)_{aa}| ≤ K_D‖x‖` gives the constant bound
`K_D/2`. -/
theorem diagonal_bound_of_linearVanishing {D : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {KD : ℝ} (hKD : 0 ≤ KD) (hDlin : ∀ x a b, |D x a b| ≤ KD * ‖x‖)
    {x : Fin 4 → ℝ} (hx : x ∈ wardPatch) (a : Fin 4) : |D x a a| ≤ KD / 2 := by
  have h := hDlin x a a
  have hn := wardPatch_norm_le_half hx
  nlinarith [norm_nonneg x]

/-! ## 2. The Ward-patch floor with the diagonal bound required only on the patch -/

/-- The reduced bubble entry of the literal source variation, with the diagonal
bound needed only at the momentum in question. -/
theorem sourceVariation_bubble_entry_ge_local {f d : ℝ} {rho : Fin 4}
    {D : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    (hD : ∀ x a b, a ≠ b → D x a b = 0) {x : Fin 4 → ℝ} (hd : ∀ a, |D x a a| ≤ d)
    (hx : phatSq x ≠ 0) (hx0 : 0 < phatSq x) (i : Fin 4) :
    (phatSq x)⁻¹ * ((transverseProjector (phatVec x)) i i * (sinAtom (2 * x rho) - d))
      ≤ (latticeGramFactor x * sourceVariationMatrix f rho D x
          * (latticeGramFactor x)ᵀ) i i := by
  rw [latticeReducedBubble_eq x hx0.le]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hmain := transverseConjugate_diag_ge (x := x) hx rho (f := f) (d := d) (D := D x)
    (hD x) hd i
  exact mul_le_mul_of_nonneg_left hmain (inv_pos.mpr hx0).le

/-- **The Ward-patch floor, localised.**  Identical to
`literalOneLoopIntegrand_wardPatch_floor` except that the diagonal bound on the
averaging / constrained-projection variation is only assumed on the patch. -/
theorem literalOneLoopIntegrand_wardPatch_floor_local {f d : ℝ}
    {D : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {Wm : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    (hD : ∀ x a b, a ≠ b → D x a b = 0)
    (hd : ∀ x ∈ wardPatch, ∀ a, |D x a a| ≤ d) (hd4 : d ≤ 1 / 4)
    {x : Fin 4 → ℝ} (hx : x ∈ wardPatch) :
    (1 : ℝ) / 32768 ≤ literalOneLoopIntegrand (sourceVariationMatrix f 1 D) Wm x := by
  have hpos := wardPatch_phatSq_pos hx
  have hne : phatSq x ≠ 0 := ne_of_gt hpos
  have hle16 := wardPatch_phatSq_le x
  have hP := wardPatch_projector_diag_ge hx
  have hsin := wardPatch_sinAtom_ge hx
  have hentry := sourceVariation_bubble_entry_ge_local (f := f) (d := d) (rho := 1)
    hD (hd x hx) hne hpos 0
  have hbig : (1 : ℝ) / 8
      ≤ (transverseProjector (phatVec x)) 0 0 * (sinAtom (2 * x 1) - d) := by
    nlinarith
  have hinv : (1 : ℝ) / 16 ≤ (phatSq x)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hpos]
    linarith
  have hprod : (1 : ℝ) / 128
      ≤ (phatSq x)⁻¹ * ((transverseProjector (phatVec x)) 0 0 * (sinAtom (2 * x 1) - d)) := by
    have hnn : (0 : ℝ) ≤ (transverseProjector (phatVec x)) 0 0 * (sinAtom (2 * x 1) - d) := by
      linarith
    nlinarith
  have hE : (1 : ℝ) / 128
      ≤ (latticeGramFactor x * sourceVariationMatrix f 1 D x * (latticeGramFactor x)ᵀ) 0 0 :=
    le_trans hprod hentry
  have hmain := literalOneLoopIntegrand_ge_entry_sq (Vm := sourceVariationMatrix f 1 D)
    (Wm := Wm) hne (sourceVariationMatrix_transpose hD x) 0 0
  nlinarith

/-! ## 3. Row A1a with the diagonal-size assumption deleted -/

/-- **Row A1a from the literal one-loop trace, driven by one regularity
constant.**  The Lorentz-diagonal averaging / constrained-projection variation
enters only through the single bound `|D(x)_{ab}| ≤ K_D‖x‖` with `K_D ≤ 1/2`:
that one datum supplies both the integrability of the one-loop integrand at zero
momentum and the positivity of the Ward factor on the patch.  No separate
diagonal-size assumption survives. -/
theorem A1_beta_pos_ward_from_regularity
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {Adm : (ℕ → ℝ) → Prop} {g : ℕ → ℝ} {f KD KW : ℝ}
    {Dm Wm : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {lamDet : ℕ → (ℕ → ℝ) → ι → ℝ} {lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ}
    {aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    {AInt AChart ALoc : ℕ → ℝ} {N : ℕ} {LamDet LamGauge theta : ℝ}
    (hKD : 0 ≤ KD) (hKD2 : KD ≤ 1 / 2) (hKW : 0 ≤ KW)
    (hDmeas : ∀ j h a b, Measurable fun x => Dm j h x a b)
    (hWmeas : ∀ j h a b, Measurable fun x => Wm j h x a b)
    (hD : ∀ j h x a b, a ≠ b → Dm j h x a b = 0)
    (hDlin : ∀ j h x a b, |Dm j h x a b| ≤ KD * ‖x‖)
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
      (fun j' h => literalOneLoopIntegrand (sourceVariationMatrix f 1 (Dm j' h)) (Wm j' h))
      lamDet lamGauge aInt aChart aLoc N j g := by
  -- integrability, from the linear-vanishing datum alone
  have hintg : ∀ j' h, IntegrableOn
      (literalOneLoopIntegrand (sourceVariationMatrix f 1 (Dm j' h)) (Wm j' h))
      puncturedCell := by
    intro j' h
    refine literalOneLoopIntegrand_integrableOn_of_conjBound
      (cV := 4 * π + 64 * KD) (KW := KW) (by positivity) hKW
      (measurable_sourceVariationMatrix_entry f 1 (hDmeas j' h))
      (hWmeas j' h)
      (fun x => sourceVariationMatrix_transpose (hD j' h) x) ?_ (hWbd j' h)
    intro x hx a b
    exact sourceVariation_conj_bound hKD (hDlin j' h)
      (phatSq_ne_zero_of_mem_puncturedCell hx) a b
  -- the Gaussian floor, from the same datum
  have hfloor : HistoryUniformFloor (shellGaussianOfIntegrand
      (fun j' h => literalOneLoopIntegrand (sourceVariationMatrix f 1 (Dm j' h)) (Wm j' h)))
      Adm (1 / 8388608 : ℝ) := by
    intro j' h _
    have hnonneg : ∀ q ∈ puncturedCell,
        0 ≤ literalOneLoopIntegrand (sourceVariationMatrix f 1 (Dm j' h)) (Wm j' h) q := by
      intro q hq
      exact literalOneLoopIntegrand_nonneg (phatSq_ne_zero_of_mem_puncturedCell hq)
        (sourceVariationMatrix_transpose (hD j' h) q)
    have hpatch : ∀ q ∈ wardPatch,
        (1 : ℝ) / 32768
          ≤ literalOneLoopIntegrand (sourceVariationMatrix f 1 (Dm j' h)) (Wm j' h) q := by
      intro q hq
      exact literalOneLoopIntegrand_wardPatch_floor_local (d := KD / 2) (hD j' h)
        (fun y hy a => diagonal_bound_of_linearVanishing hKD (hDlin j' h) hy a)
        (by linarith) hq
    have := cellGaussianFloor_of_wardPatch (hintg j' h) hnonneg hpatch
    rw [shellGaussianOfIntegrand]
    calc (1 : ℝ) / 8388608 = 1 / 256 * (1 / 32768) := by norm_num
      _ ≤ _ := this
  have hmain := A1_historyUniform_half_floor (bpatch := 1 / 8388608)
    (beta := shellBetaOfSources
      (fun j' h => literalOneLoopIntegrand (sourceVariationMatrix f 1 (Dm j' h)) (Wm j' h))
      lamDet lamGauge aInt aChart aLoc N)
    (betaZ := shellGaussianOfIntegrand
      (fun j' h => literalOneLoopIntegrand (sourceVariationMatrix f 1 (Dm j' h)) (Wm j' h)))
    (betaInt := shellInteractionOfChannels lamDet lamGauge aInt aChart aLoc N)
    (by norm_num) (fun _ _ => rfl) hfloor
    (historyUniformQuartic_of_sourceChannels (fun _ _ _ => rfl)
      hLd hLg hAInt hAChart hALoc hsmall hth)
    (fun k => sourceChannelCoefficient_nonneg hth hth0 k) hadm hg0 hgg j
  have hval : (1 / 8388608 : ℝ) / 2 = 1 / 16777216 := by norm_num
  rw [hval] at hmain
  exact hmain

end YangMills

/-
# Row A1a — the Gaussian floor produced by one positive-volume patch

This file closes the corrected A1a route at the level of the *cell integral*:

    one positive-volume momentum patch with a strict lower bound
      + a sign on the complement
      ⟹ a uniform Gaussian floor `b_patch`
      ⟹ the corrected Row A1 margin.

The chain is:

* `cellGaussianFloor_of_patch` : an integrand nonnegative on the (punctured)
  momentum cell and at least `c` on the slab of half-width `δ` around normalised
  momentum `1/4` has cell integral at least `(δ/4)·c`, uniformly in the scale.
* `latticeCellFloor_of_patchEntry` : the literal bubble version.  For the
  project's lattice constrained symbol, the paramagnetic sign datum
  (`S = −WᵀW`, `Vᵀ = V`) gives nonnegativity of the one-loop integrand
  everywhere on the punctured cell — no near/far analysis — and a single entry
  bound `|M_j(q)_{00}| ≥ c` on the patch gives the floor `(δ/4)·(c²/2)`.
* `A1_from_patchFloor` : feeding that floor into `A1_corrected_lower_bound`
  gives the corrected margin end to end.

The point of the puncture: `p̂²` vanishes exactly at the single momentum `q = 0`
of the cell (`phatSq_ne_zero_of_mem_puncturedCell`), a Lebesgue-null set which
does not affect the integral (`setIntegral_puncturedCell`).

**Honest status.**  The entry bound `|M_j(q)_{00}| ≥ c` on the patch is the
remaining source datum — it is *not* proved here for Bałaban's construction.
-/
import RequestProject.YangMills.PositivePatchEnclosure
import RequestProject.YangMills.TransverseBubbleEntry
import RequestProject.YangMills.A1CorrectedMargin

namespace YangMills

open MeasureTheory Set Real Matrix

/-- The momentum cell with the single degenerate momentum `q = 0` removed. -/
def puncturedCell : Set (Fin 4 → ℝ) := momentumCell \ {(0 : Fin 4 → ℝ)}

theorem measurableSet_puncturedCell : MeasurableSet puncturedCell :=
  measurableSet_momentumCell.diff (measurableSet_singleton _)

/-- Removing the single momentum `q = 0` does not change any integral over the
cell. -/
theorem setIntegral_puncturedCell (f : (Fin 4 → ℝ) → ℝ) :
    ∫ q in puncturedCell, f q = ∫ q in momentumCell, f q := by
  have hnull : volume ({(0 : Fin 4 → ℝ)} : Set (Fin 4 → ℝ)) = 0 := by simp
  exact setIntegral_congr_set (MeasureTheory.diff_null_ae_eq_self hnull)

/-- On the cell, `p̂²` vanishes only at `q = 0`. -/
theorem phatSq_ne_zero_of_mem_puncturedCell {q : Fin 4 → ℝ} (hq : q ∈ puncturedCell) :
    phatSq q ≠ 0 := by
  obtain ⟨hcell, hne⟩ := hq
  intro hzero
  have hmem : ∀ mu : Fin 4, q mu ∈ Icc (0 : ℝ) (1 / 2) := fun mu => hcell mu (mem_univ mu)
  have hterm : ∀ mu : Fin 4, (phat (q mu)) ^ 2 = 0 := by
    intro mu
    have hnn : ∀ nu : Fin 4, nu ∈ Finset.univ → 0 ≤ (phat (q nu)) ^ 2 := fun nu _ => sq_nonneg _
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hzero mu (Finset.mem_univ mu)
  have hzero' : ∀ mu : Fin 4, q mu = 0 := by
    intro mu
    have hsin : Real.sin (π * q mu) = 0 := by
      have := hterm mu
      have h2 : phat (q mu) = 0 := by
        have := sq_eq_zero_iff.1 this
        exact this
      simpa [phat, sinAtom] using h2
    by_contra hne0
    have hpos : 0 < q mu := lt_of_le_of_ne (hmem mu).1 (Ne.symm hne0)
    have h1 : 0 < π * q mu := by positivity
    have h2 : π * q mu < π := by
      have : q mu ≤ 1 / 2 := (hmem mu).2
      nlinarith [Real.pi_pos]
    have := Real.sin_pos_of_pos_of_lt_pi h1 h2
    linarith
  exact hne (funext hzero')

/-- The Gaussian coefficient in continuum (cell-integral) form. -/
noncomputable def cellGaussianCoefficient (I : (Fin 4 → ℝ) → ℝ) : ℝ :=
  ∫ q in momentumCell, I q

/-- **The Gaussian floor from one positive-volume patch.** -/
theorem cellGaussianFloor_of_patch {I : (Fin 4 → ℝ) → ℝ} {c delta : ℝ}
    (rho : Fin 4) (hd0 : 0 < delta) (hd1 : delta < 1 / 4)
    (hint : IntegrableOn I puncturedCell)
    (hnonneg : ∀ q ∈ puncturedCell, 0 ≤ I q)
    (hpatch : ∀ q ∈ quarterSlab rho delta, c ≤ I q) :
    (delta / 4) * c ≤ cellGaussianCoefficient I := by
  have hsub : quarterSlab rho delta ⊆ puncturedCell := by
    intro q hq
    refine ⟨quarterSlab_subset (le_of_lt hd1) rho hq, ?_⟩
    intro h0
    have hrho : q rho ∈ Icc (1 / 4 - delta) (1 / 4 + delta) := by
      simpa [quarterSlab] using hq rho (mem_univ rho)
    have : q rho = 0 := by
      have : q = (0 : Fin 4 → ℝ) := h0
      rw [this]; rfl
    have := hrho.1
    rw [‹q rho = 0›] at this
    linarith
  have hmain := setIntegral_ge_patch (measurableSet_quarterSlab rho delta) hsub
    (quarterSlab_volume_ne_top rho delta) hint measurableSet_puncturedCell hpatch
    (fun q hq => hnonneg q hq.1)
  rw [Measure.real, quarterSlab_volume_real (le_of_lt hd0) rho] at hmain
  rw [cellGaussianCoefficient, ← setIntegral_puncturedCell]
  exact hmain

/-- **The literal one-loop integrand version.**  With the paramagnetic sign
datum the integrand is nonnegative on the whole punctured cell, and one entry
bound of the reduced bubble kernel on the patch produces the floor
`(δ/4)·(c²/2)`. -/
theorem latticeCellFloor_of_patchEntry
    {V S W : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {c delta : ℝ}
    (rho : Fin 4) (hd0 : 0 < delta) (hd1 : delta < 1 / 4) (hc : 0 ≤ c)
    (hV : ∀ q, (V q)ᵀ = V q) (hS : ∀ q, S q = -((W q)ᵀ * W q))
    (hint : IntegrableOn (fun q => betaTrace (latticeSymbolOf q) (V q) (V q) (S q))
      puncturedCell)
    (hentry : ∀ q ∈ quarterSlab rho delta,
      c ≤ |(latticeGramFactor q * V q * (latticeGramFactor q)ᵀ) 0 0|) :
    (delta / 4) * (c ^ 2 / 2)
      ≤ cellGaussianCoefficient
          (fun q => betaTrace (latticeSymbolOf q) (V q) (V q) (S q)) := by
  have hsub : quarterSlab rho delta ⊆ puncturedCell := by
    intro q hq
    refine ⟨quarterSlab_subset (le_of_lt hd1) rho hq, ?_⟩
    intro h0
    have hrho : q rho ∈ Icc (1 / 4 - delta) (1 / 4 + delta) := by
      simpa [quarterSlab] using hq rho (mem_univ rho)
    have hq0 : q rho = 0 := by
      have : q = (0 : Fin 4 → ℝ) := h0
      rw [this]; rfl
    have := hrho.1
    rw [hq0] at this
    linarith
  refine cellGaussianFloor_of_patch rho hd0 hd1 hint ?_ ?_
  · intro q hq
    have hne := phatSq_ne_zero_of_mem_puncturedCell hq
    exact betaTrace_nonneg_of_paramagnetic (latticeSymbol_eq_gram q hne) (hV q) (hS q)
  · intro q hq
    have hne := phatSq_ne_zero_of_mem_puncturedCell (hsub hq)
    have hmain := betaTrace_ge_entry_sq (latticeSymbol_eq_gram q hne) (hV q) (hS q) 0 0
    have hentry' := hentry q hq
    have hsq : c ^ 2
        ≤ ((latticeGramFactor q * V q * (latticeGramFactor q)ᵀ) 0 0) ^ 2 := by
      have habs := sq_abs ((latticeGramFactor q * V q * (latticeGramFactor q)ᵀ) 0 0)
      nlinarith [abs_nonneg ((latticeGramFactor q * V q * (latticeGramFactor q)ᵀ) 0 0)]
    rw [latticeSymbolOf]
    linarith

/-- **Row A1 end to end from a positive-volume patch.**  The Gaussian floor is
supplied by the patch, the interaction debt by the five channelwise quartic
majorants, the history debt by scale-local localization of the irrelevant
memory (plus an explicit marginal-memory bound). -/
theorem A1_from_patchFloor
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ}
    {R Rirr Rmarg : ℕ → ℕ → ℝ} {ch : ℕ → BetaChannel → ℝ}
    {c : BetaChannel → ℝ} {g gref : ℕ → ℝ}
    {I : ℕ → (Fin 4 → ℝ) → ℝ} {cpatch delta gamma theta Cloc Hmarg B : ℝ}
    (rho : Fin 4) (hd0 : 0 < delta) (hd1 : delta < 1 / 4)
    (hident : ∀ j, betaZ j gref = cellGaussianCoefficient (I j))
    (hint : ∀ j, IntegrableOn (I j) puncturedCell)
    (hnonneg : ∀ j, ∀ q ∈ puncturedCell, 0 ≤ I j q)
    (hpatch : ∀ j, ∀ q ∈ quarterSlab rho delta, cpatch ≤ I j q)
    (hsplit : ∀ j g, beta j g = betaZ j g + betaInt j g)
    (hchan : ∀ j, betaInt j g = ∑ k, ch j k)
    (hmaj : ∀ j k, |ch j k| ≤ c k * (g j) ^ 4)
    (hc : ∀ k, 0 ≤ c k) (hg0 : ∀ j, 0 ≤ g j) (hgg : ∀ j, g j ≤ gamma)
    (hresp : HasHistoryResponse betaZ R)
    (hRsplit : ∀ j k, R j k = Rirr j k + Rmarg j k)
    (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) (hCloc : 0 ≤ Cloc)
    (hgamma : 0 ≤ gamma)
    (hloc : ∀ j k, k < j → |Rirr j k| ≤ Cloc * gamma * theta ^ (j - k))
    (hmarg : ∀ j, ∑ k ∈ Finset.range j, |Rmarg j k| ≤ Hmarg)
    (hB : ∀ k, |g k - gref k| ≤ B)
    (j : ℕ) :
    correctedMargin ((delta / 4) * cpatch) (Cbeta c) (CH Cloc theta) gamma Hmarg B
      ≤ beta j g := by
  refine A1_corrected_lower_bound (fun j' => ?_) hsplit hchan hmaj hc hg0 hgg hresp
    hRsplit htheta0 htheta1 hCloc hgamma hloc hmarg hB j
  rw [hident j']
  exact cellGaussianFloor_of_patch rho hd0 hd1 (hint j') (hnonneg j') (hpatch j')

end YangMills

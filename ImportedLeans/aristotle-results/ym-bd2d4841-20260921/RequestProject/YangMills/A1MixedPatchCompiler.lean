/-
# Row A1a — the compiler fed by the mixed-component patch

`MixedComponentPatch` produces a *computed* floor for the mixed Lorentz
component of the constrained first variation on a positive-volume momentum box.
This file feeds that floor through the existing Row A1 chain:

    |V| ≥ v_*  on the box
      ⟹ one-loop integrand ≥ v_*²/2 there            (paramagnetic entry datum)
      ⟹ Gaussian coefficient ≥ 2δ⁴ · v_*²/2          (`cellGaussianFloor_of_mixedPatch`)
      ⟹ β_j ≥ b_patch/2 > 0                          (`A1_halfFloor_from_mixedPatch`)

with the interaction remainder controlled by the history-uniform five-channel
quartic bound and the coupling chosen by the root-free constructive rule
`γ_* = b/(2(C_β+b))`.

* `mixedPatch_subset_puncturedCell` : the box avoids the degenerate momentum
  `q = 0`, so it lies in the punctured cell.
* `cellGaussianFloor_of_mixedPatch` : the cell-integral floor `2δ⁴·c`.
* `A1_halfFloor_from_mixedPatch` : the shell floor `β_j ≥ (2δ⁴·c)/2`.
* `A1_halfFloor_from_literalMixedSymbol` : the same with `c` *computed* — at
  `δ = 1/16` and gauge amplitude `|f| ≤ 1` the mixed component is at least `1/5`
  on the box, so `β_j ≥ 1/3276800 > 0`, with no free error parameter left in the
  Gaussian sector.

**Honest status.**  Two source identifications are still hypotheses of the last
theorem, and are displayed as such: that the shell Gaussian coefficient is the
cell integral of the one-loop integrand of the *literal* mixed component, and
the history-uniform five-channel quartic remainder.  Row A1 is not closed.
-/
import RequestProject.YangMills.MixedComponentPatch
import RequestProject.YangMills.RestrictedSymbolPatch
import RequestProject.YangMills.PatchGaussianFloor

namespace YangMills

open MeasureTheory Set Real

variable {delta : ℝ}

/-- The mixed-component box avoids the single degenerate momentum `q = 0`: its
spectator coordinates are bounded below by `1/2 − δ > 0`. -/
theorem mixedPatch_subset_puncturedCell (hd0 : 0 < delta) (hd1 : delta ≤ 1 / 16) :
    mixedPatch delta ⊆ puncturedCell := by
  intro x hx
  refine ⟨mixedPatch_subset (by linarith) hx, ?_⟩
  intro hzero
  have hx2 : x 2 ∈ Icc (1 / 2 - delta) (1 / 2) :=
    mixedPatch_mem_spectator hx 2 (by decide) (by decide)
  have h0 : x 2 = 0 := by
    have : x = (0 : Fin 4 → ℝ) := hzero
    rw [this]; rfl
  have := hx2.1
  rw [h0] at this
  linarith

/-- **The Gaussian floor produced by the mixed-component box.** -/
theorem cellGaussianFloor_of_mixedPatch {I : (Fin 4 → ℝ) → ℝ} {c : ℝ}
    (hd0 : 0 < delta) (hd1 : delta ≤ 1 / 16)
    (hint : IntegrableOn I puncturedCell)
    (hnonneg : ∀ q ∈ puncturedCell, 0 ≤ I q)
    (hpatch : ∀ q ∈ mixedPatch delta, c ≤ I q) :
    2 * delta ^ 4 * c ≤ cellGaussianCoefficient I := by
  have hmain := setIntegral_ge_patch (measurableSet_mixedPatch delta)
    (mixedPatch_subset_puncturedCell hd0 hd1) (mixedPatch_volume_ne_top hd0.le) hint
    measurableSet_puncturedCell hpatch (fun q hq => hnonneg q hq.1)
  rw [Measure.real, mixedPatch_volume_real hd0.le] at hmain
  rw [cellGaussianCoefficient, ← setIntegral_puncturedCell]
  exact hmain

/-- **Row A1 from the mixed-component box.**  The Gaussian floor comes from the
box, the interaction remainder from the history-uniform five-channel quartic
control, and the coupling from the constructive rule. -/
theorem A1_halfFloor_from_mixedPatch
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {Adm : (ℕ → ℝ) → Prop}
    {cch : BetaChannel → ℝ} {g : ℕ → ℝ}
    {I : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → ℝ} {cpatch : ℝ}
    (hd0 : 0 < delta) (hd1 : delta ≤ 1 / 16)
    (hpos : 0 < 2 * delta ^ 4 * cpatch)
    (hident : ∀ j h, Adm h → betaZ j h = cellGaussianCoefficient (I j h))
    (hint : ∀ j h, IntegrableOn (I j h) puncturedCell)
    (hnonneg : ∀ j h, ∀ q ∈ puncturedCell, 0 ≤ I j h q)
    (hpatchI : ∀ j h, ∀ q ∈ mixedPatch delta, cpatch ≤ I j h q)
    (hsplit : ∀ j h, beta j h = betaZ j h + betaInt j h)
    (hquart : HistoryUniformQuartic betaInt Adm cch)
    (hc : ∀ k, 0 ≤ cch k) (hadm : Adm g) (hg0 : ∀ j, 0 ≤ g j)
    (hgg : ∀ j, g j ≤ criticalCoupling (2 * delta ^ 4 * cpatch) (Cbeta cch))
    (j : ℕ) :
    (2 * delta ^ 4 * cpatch) / 2 ≤ beta j g := by
  have hfloor : HistoryUniformFloor betaZ Adm (2 * delta ^ 4 * cpatch) := by
    intro j' h hh
    rw [hident j' h hh]
    exact cellGaussianFloor_of_mixedPatch hd0 hd1 (hint j' h) (hnonneg j' h) (hpatchI j' h)
  exact A1_historyUniform_half_floor hpos hsplit hfloor hquart hc hadm hg0 hgg j

/-- **The Gaussian sector with no free error parameter.**  With the literal
mixed component of the constrained first variation as the entry — Wilson cubic
vertex plus the computed gauge-projection variation, the averaging and
constrained-projection variations having been shown to vanish there — the
paramagnetic one-loop integrand is at least `(1/5)²/2 = 1/50` on the box of
half-width `1/16`, and the shell floor is

    β_j ≥ (2·(1/16)⁴·(1/50))/2 = 1/3276800 > 0.

The remaining hypotheses are the two source identifications, displayed
explicitly. -/
theorem A1_halfFloor_from_literalMixedSymbol
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {Adm : (ℕ → ℝ) → Prop}
    {cch : BetaChannel → ℝ} {g : ℕ → ℝ}
    {I : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → ℝ} {f : ℝ}
    (hf : |f| ≤ 1)
    (hident : ∀ j h, Adm h → betaZ j h = cellGaussianCoefficient (I j h))
    (hint : ∀ j h, IntegrableOn (I j h) puncturedCell)
    (hnonneg : ∀ j h, ∀ q ∈ puncturedCell, 0 ≤ I j h q)
    (hentry : ∀ j h, ∀ q ∈ mixedPatch (1 / 16),
      |mixedConstrainedSymbol f q 0 1| ^ 2 / 2 ≤ I j h q)
    (hsplit : ∀ j h, beta j h = betaZ j h + betaInt j h)
    (hquart : HistoryUniformQuartic betaInt Adm cch)
    (hc : ∀ k, 0 ≤ cch k) (hadm : Adm g) (hg0 : ∀ j, 0 ≤ g j)
    (hgg : ∀ j, g j ≤ criticalCoupling (2 * (1 / 16 : ℝ) ^ 4 * (1 / 50)) (Cbeta cch))
    (j : ℕ) :
    (1 : ℝ) / 3276800 ≤ beta j g := by
  have hpatchI : ∀ j' h, ∀ q ∈ mixedPatch (1 / 16 : ℝ), (1 : ℝ) / 50 ≤ I j' h q := by
    intro j' h q hq
    have hsym := mixedPatch_floor_concrete hf hq
    have habs : (0 : ℝ) ≤ |mixedConstrainedSymbol f q 0 1| := abs_nonneg _
    have hsq : (1 : ℝ) / 50 ≤ |mixedConstrainedSymbol f q 0 1| ^ 2 / 2 := by nlinarith
    exact le_trans hsq (hentry j' h q hq)
  have hmain := A1_halfFloor_from_mixedPatch (delta := 1 / 16) (cpatch := 1 / 50)
    (by norm_num) le_rfl (by norm_num) hident hint hnonneg hpatchI hsplit hquart hc hadm hg0
    hgg j
  have hval : (2 * (1 / 16 : ℝ) ^ 4 * (1 / 50)) / 2 = 1 / 3276800 := by norm_num
  rw [hval] at hmain
  exact hmain

end YangMills

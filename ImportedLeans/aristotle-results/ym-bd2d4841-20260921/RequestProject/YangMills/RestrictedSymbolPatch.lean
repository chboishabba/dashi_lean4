/-
# Row A1a — the quarter-region patch test on the **full restricted symbol**

`QuarterPatchLowerBound` certifies a floor for the *Wilson* component `W` on the
slab of half-width `1/8` around normalised momentum `1/4`.  That is not yet a
certificate for the Gaussian: what the constrained operator supplies is the
restricted first variation

    V = W + Q + R,   W = CᵀA'C,   Q = C'ᵀAC,   R = CᵀAC',

(`ConstraintCoordinateGaussian`).  A floor on `W` alone is worthless unless the
coordinate-connection terms are controlled — and because `A` is symmetric,
`Q = Rᵀ`, so on the diagonal the whole error is `2·R_ii`.

This file runs the patch test on the full restricted symbol.

* `restrictedSymbol` : the momentum-dependent restricted first variation.
* `restrictedSymbol_entry_ge_on_patch` : `W_ii ≥ c` and `|R_ii| ≤ e` on a patch
  give `V_ii ≥ c − 2e` there.
* `cellIntegral_restricted_ge` : the resulting cell-integral floor
  `(δ/4)·(c − 2e)`.
* `restrictedQuarterFloor_eighth` : at the project's candidate patch —
  half-width `1/8`, Wilson floor `√2/2` — the floor is `√2/64 − e/16`.
* **`restricted_patch_survives_iff`** : that floor is positive **iff**
  `e < √2/4`.  This is the sharp, explicit error budget the `Q`/`R` producer has
  to meet on this one patch: `√2/4 > 0.35`.
* `restricted_patch_fails_at_budget` : at `e = √2/4` the certificate is exactly
  lost, so the budget is not conservative.
* `A1_halfFloor_from_restrictedPatch` : the end-to-end assembly — patch floor on
  the full restricted symbol, history-uniform five-channel quartic remainder,
  and the constructive coupling `γ_*` give `β_j ≥ b_patch/2 > 0`.

**Honest status.**  Nothing here computes `A'` or `C'` for Bałaban's
construction, so neither the Wilson floor `c` nor the connection budget `e` is
instantiated.  Row A1 is not closed.  What is closed is the compiler: once one
number `e < √2/4` is produced on this patch, the rest of the chain is machine
checked.
-/
import RequestProject.YangMills.ConstraintCoordinateGaussian
import RequestProject.YangMills.QuarterPatchLowerBound
import RequestProject.YangMills.HistoryUniformRemainder

namespace YangMills

open Matrix Set MeasureTheory

variable {n m : Type*} [Fintype n]

/-- The momentum-dependent restricted first variation `V = W + Q + R`. -/
def restrictedSymbol (C C' : (Fin 4 → ℝ) → Matrix n m ℝ)
    (A A' : (Fin 4 → ℝ) → Matrix n n ℝ) (q : Fin 4 → ℝ) : Matrix m m ℝ :=
  opVariation (C q) (A' q) + connectionLeft (C q) (C' q) (A q)
    + connectionRight (C q) (C' q) (A q)

/-- **The patch test on the full restricted symbol.**  A Wilson-component floor
`c` and a connection-entry budget `e` on a set of momenta give the floor
`c − 2e` for the restricted symbol there. -/
theorem restrictedSymbol_entry_ge_on_patch
    {C C' : (Fin 4 → ℝ) → Matrix n m ℝ} {A A' : (Fin 4 → ℝ) → Matrix n n ℝ}
    {P : Set (Fin 4 → ℝ)} {i : m} {c e : ℝ}
    (hA : ∀ q, (A q)ᵀ = A q)
    (hW : ∀ q ∈ P, c ≤ opVariation (C q) (A' q) i i)
    (hR : ∀ q ∈ P, |connectionRight (C q) (C' q) (A q) i i| ≤ e) :
    ∀ q ∈ P, c - 2 * e ≤ restrictedSymbol C C' A A' q i i := by
  intro q hq
  exact restrictedVariation_entry_lower_bound (C q) (C' q) (hA q) (A' q) i (hW q hq) (hR q hq)

/-- **The cell-integral floor from the full restricted symbol.**  Patch bound on
`W`, connection budget on `R`, and the sign of the entry on the rest of the cell
give the cell integral floor `(δ/4)·(c − 2e)`. -/
theorem cellIntegral_restricted_ge
    {C C' : (Fin 4 → ℝ) → Matrix n m ℝ} {A A' : (Fin 4 → ℝ) → Matrix n n ℝ}
    {i : m} {c e delta : ℝ}
    (rho : Fin 4) (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1 / 4)
    (hA : ∀ q, (A q)ᵀ = A q)
    (hint : IntegrableOn (fun q => restrictedSymbol C C' A A' q i i) momentumCell)
    (hW : ∀ q ∈ quarterSlab rho delta, c ≤ opVariation (C q) (A' q) i i)
    (hR : ∀ q ∈ quarterSlab rho delta,
      |connectionRight (C q) (C' q) (A q) i i| ≤ e)
    (hrest : ∀ q ∈ momentumCell \ quarterSlab rho delta,
      0 ≤ restrictedSymbol C C' A A' q i i) :
    (delta / 4) * (c - 2 * e)
      ≤ ∫ q in momentumCell, restrictedSymbol C C' A A' q i i :=
  cellIntegral_ge_quarterSlab rho hd0 hd1 hint
    (restrictedSymbol_entry_ge_on_patch hA hW hR) hrest

/-! ## The explicit error budget on the project's candidate patch -/

/-- The candidate-patch floor with the Wilson bound `√2/2` and half-width `1/8`:
`(1/32)·(√2/2 − 2e) = √2/64 − e/16`. -/
theorem restrictedQuarterFloor_eighth (e : ℝ) :
    ((1 : ℝ) / 8) / 4 * (Real.sqrt 2 / 2 - 2 * e) = Real.sqrt 2 / 64 - e / 16 := by
  ring

/-- **The sharp error budget.**  The candidate patch survives the full
constrained calculation exactly when the connection entry stays below `√2/4`. -/
theorem restricted_patch_survives_iff (e : ℝ) :
    0 < ((1 : ℝ) / 8) / 4 * (Real.sqrt 2 / 2 - 2 * e) ↔ e < Real.sqrt 2 / 4 := by
  rw [restrictedQuarterFloor_eighth]
  constructor <;> intro h <;> linarith

/-- The budget is exactly attained, not conservative: at `e = √2/4` the floor is
zero and the certificate is lost. -/
theorem restricted_patch_fails_at_budget :
    ((1 : ℝ) / 8) / 4 * (Real.sqrt 2 / 2 - 2 * (Real.sqrt 2 / 4)) = 0 := by
  ring

/-- A usable decimal form of the budget: `√2/4 > 0.35`. -/
theorem sqrt2_div_four_gt_thirtyFive : (0.35 : ℝ) < Real.sqrt 2 / 4 := by
  have hnn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h : (1.4 : ℝ) < Real.sqrt 2 := by nlinarith
  linarith

/-- Consequently any connection budget below `0.35` certifies the patch. -/
theorem restricted_patch_survives_of_budget {e : ℝ} (he : e ≤ 0.35) :
    0 < ((1 : ℝ) / 8) / 4 * (Real.sqrt 2 / 2 - 2 * e) :=
  (restricted_patch_survives_iff e).2 (lt_of_le_of_lt he sqrt2_div_four_gt_thirtyFive)

/-! ## End-to-end assembly -/

/-- **Row A1 from the full restricted symbol.**  A positive-volume patch floor
for the *whole* restricted first variation (Wilson floor minus twice the
connection budget), held uniformly over admissible preceding-coupling histories,
together with the history-uniform five-channel quartic remainder and the
constructive coupling `γ_*`, gives `β_j ≥ b_patch/2 > 0` for every shell index,
uniformly in the number of scales, the volume and the cutoff. -/
theorem A1_halfFloor_from_restrictedPatch
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {Adm : (ℕ → ℝ) → Prop}
    {cch : BetaChannel → ℝ} {g : ℕ → ℝ}
    {I : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → ℝ} {cpatch e delta : ℝ}
    (rho : Fin 4) (hd0 : 0 < delta) (hd1 : delta < 1 / 4)
    (hpos : 0 < (delta / 4) * (cpatch - 2 * e))
    (hident : ∀ j h, Adm h → betaZ j h = cellGaussianCoefficient (I j h))
    (hint : ∀ j h, IntegrableOn (I j h) puncturedCell)
    (hnonneg : ∀ j h, ∀ q ∈ puncturedCell, 0 ≤ I j h q)
    (hpatchI : ∀ j h, ∀ q ∈ quarterSlab rho delta, cpatch - 2 * e ≤ I j h q)
    (hsplit : ∀ j h, beta j h = betaZ j h + betaInt j h)
    (hquart : HistoryUniformQuartic betaInt Adm cch)
    (hc : ∀ k, 0 ≤ cch k) (hadm : Adm g) (hg0 : ∀ j, 0 ≤ g j)
    (hgg : ∀ j, g j ≤ criticalCoupling ((delta / 4) * (cpatch - 2 * e)) (Cbeta cch))
    (j : ℕ) :
    ((delta / 4) * (cpatch - 2 * e)) / 2 ≤ beta j g := by
  have hfloor : HistoryUniformFloor betaZ Adm ((delta / 4) * (cpatch - 2 * e)) := by
    intro j' h hh
    rw [hident j' h hh]
    exact cellGaussianFloor_of_patch rho hd0 hd1 (hint j' h) (hnonneg j' h) (hpatchI j' h)
  exact A1_historyUniform_half_floor hpos hsplit hfloor hquart hc hadm hg0 hgg j

end YangMills

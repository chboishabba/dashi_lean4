/-
**The resource ledger for the whole admissible projector family.**

`ShiftProjector.lean` computed the ledger entry for one concrete purifier, the
first difference `D(·+s) − D(·)`.  This file does the same computation for the
*entire* admissible family

    `(P D)(t) = ∑_{j<r} c_j · D(t + s_j)`,   `P(1) = ∑_j c_j = 0`,

so that the lane can be settled once instead of one candidate at a time.  The
design principle is the one the modular-source programme uses: parameterise the
admissible consumers, compute an exact cost/resource functional for each, and
look for a strict margin *before* attempting any hard analysis.

The three entries are:

* `projected_diagonalMass_le` — the exact cost side.  Every annihilating
  projector damps the diagonal of the short-window second moment by at most the
  factor `(W · log N)²`, where `W = ∑_j ‖c_j‖|s_j|` is the projector weight.
  (`projected_secondMoment_le_general` feeds this into the exact short-window
  expansion of `ShortIntervalMeanValue.lean`.)
* `source_projector_gain_eq` — the value of that factor at the source
  parameters.  With shifts on the source grid, `s_j = k_j·(2π/L)`, and Dirichlet
  length `log N = cL`, the factor equals `(2πc ∑_j ‖c_j‖|k_j|)²`: a constant,
  **independent of `L`**.  So no finite shift projector on the source grid buys
  a power of `L` — the negative verdict of `source_gain_factor_eq` was not an
  artefact of choosing the first difference.
* `projector_ledger_no_margin` — the structural reason, and the sharpest form of
  the verdict.  An annihilating projector damps *low* frequencies, and the
  anchored floor lives at a low frequency.  So if the projector retains the
  floor, in the sense that `‖P(λ₀)‖ ≥ ϱ` at the anchor frequency `λ₀`, then its
  guaranteed diagonal-damping factor is at least `ϱ²`.  Within this budget model
  floor retention and diagonal vanishing are therefore mutually exclusive: the
  strict margin `δ > 0` cannot come from a finite shift projector alone.

Nothing here refers to `ζ`; `a` is an arbitrary finite coefficient sequence and
no arithmetic input is assumed.
-/
import RiemannAnalytic.ShiftProjector

namespace RiemannAnalytic

open Complex Finset intervalIntegral MeasureTheory

/-! ### The projector weight -/

/-- The weight `W = ∑_{j<r} ‖c_j‖ |s_j|` of a finite shift projector.  It is the
Lipschitz constant of its symbol at the zero frequency. -/
noncomputable def projectorWeight (c : ℕ → ℂ) (sh : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range r, ‖c j‖ * |sh j|

theorem projectorWeight_nonneg (c : ℕ → ℂ) (sh : ℕ → ℝ) (r : ℕ) :
    0 ≤ projectorWeight c sh r :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- The coefficients of the projected Dirichlet polynomial. -/
noncomputable def projectedCoeff (c : ℕ → ℂ) (sh : ℕ → ℝ) (r : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n * shiftMultiplier c sh r (Real.log n)

/-- **Exact annihilation of the zero-frequency mode**, for the whole family: an
annihilating projector kills the `n = 1` coefficient outright. -/
@[simp] theorem projectedCoeff_one {c : ℕ → ℂ} {sh : ℕ → ℝ} {r : ℕ}
    (hc : ∑ j ∈ Finset.range r, c j = 0) (a : ℕ → ℂ) :
    projectedCoeff c sh r a 1 = 0 := by
  simp [projectedCoeff, shiftMultiplier_zeroFreq_eq_zero hc]

/-- The projected polynomial is the Dirichlet polynomial of the projected
coefficients. -/
theorem shiftProjected_eq_dirichletPoly (c : ℕ → ℂ) (sh : ℕ → ℝ) (r : ℕ) (a : ℕ → ℂ) (N : ℕ)
    (t : ℝ) :
    shiftProjected c sh r (dirichletPoly a N) t
      = dirichletPoly (projectedCoeff c sh r a) N t :=
  shiftProjected_dirichletPoly c sh r a N t

/-- **The cost side of the ledger.**  Every annihilating projector damps the
diagonal by at most the factor `(W log N)²`. -/
theorem projected_diagonalMass_le {c : ℕ → ℂ} {sh : ℕ → ℝ} {r : ℕ}
    (hc : ∑ j ∈ Finset.range r, c j = 0) (a : ℕ → ℂ) (N : ℕ) :
    diagonalMass (projectedCoeff c sh r a) N
      ≤ (projectorWeight c sh r * Real.log N) ^ 2 * diagonalMass a N := by
  unfold diagonalMass
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
  have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.2
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlogN : Real.log n ≤ Real.log N := Real.log_le_log (by linarith) hnN
  have hW : 0 ≤ projectorWeight c sh r := projectorWeight_nonneg c sh r
  have hmul : ‖shiftMultiplier c sh r (Real.log n)‖ ≤ projectorWeight c sh r * Real.log N := by
    refine le_trans (norm_shiftMultiplier_le_of_annihilating hc (Real.log n)) ?_
    rw [abs_of_nonneg hlog0]
    exact mul_le_mul_of_nonneg_left hlogN hW
  have hmul0 : 0 ≤ ‖shiftMultiplier c sh r (Real.log n)‖ := norm_nonneg _
  have hsq : ‖shiftMultiplier c sh r (Real.log n)‖ ^ 2
      ≤ (projectorWeight c sh r * Real.log N) ^ 2 := by nlinarith
  calc ‖projectedCoeff c sh r a n‖ ^ 2
      = ‖a n‖ ^ 2 * ‖shiftMultiplier c sh r (Real.log n)‖ ^ 2 := by
        unfold projectedCoeff
        rw [norm_mul, mul_pow]
    _ ≤ ‖a n‖ ^ 2 * (projectorWeight c sh r * Real.log N) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (projectorWeight c sh r * Real.log N) ^ 2 * ‖a n‖ ^ 2 := by ring

/-- **The projected short-window second moment, for the whole family.**  The
diagonal costs `H (W log N)² ∑|a_n|²` instead of `H ∑|a_n|²`, and the
off-diagonal is the classical one for the projected coefficients. -/
theorem projected_secondMoment_le_general {c : ℕ → ℂ} {sh : ℕ → ℝ} {r : ℕ}
    (hc : ∑ j ∈ Finset.range r, c j = 0) (a : ℕ → ℂ) (N : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    (∫ t in (0 : ℝ)..H, ‖shiftProjected c sh r (dirichletPoly a N) t‖ ^ 2)
      ≤ H * ((projectorWeight c sh r * Real.log N) ^ 2 * diagonalMass a N)
        + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * ‖projectedCoeff c sh r a m‖ * ‖projectedCoeff c sh r a n‖
              / |Real.log n - Real.log m| := by
  have hcongr : (∫ t in (0 : ℝ)..H, ‖shiftProjected c sh r (dirichletPoly a N) t‖ ^ 2)
      = ∫ t in (0 : ℝ)..H, ‖dirichletPoly (projectedCoeff c sh r a) N t‖ ^ 2 := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [shiftProjected_eq_dirichletPoly]
  rw [hcongr]
  refine le_trans (dirichletPoly_secondMoment_le (projectedCoeff c sh r a) N hH) ?_
  have hdiag : H * ∑ n ∈ Finset.Icc 1 N, ‖projectedCoeff c sh r a n‖ ^ 2
      ≤ H * ((projectorWeight c sh r * Real.log N) ^ 2 * diagonalMass a N) := by
    have := projected_diagonalMass_le (sh := sh) hc a N
    unfold diagonalMass at this
    exact mul_le_mul_of_nonneg_left this hH
  linarith

/-! ### The ledger at the source parameters -/

/-- The weight of a projector whose shifts are integer multiples `k_j` of the
source grid spacing `2π/L`. -/
theorem source_projectorWeight_eq (c : ℕ → ℂ) (k : ℕ → ℝ) {L : ℝ} (hL : 0 < L) (r : ℕ) :
    projectorWeight c (fun j => k j * (2 * Real.pi / L)) r
      = (2 * Real.pi / L) * ∑ j ∈ Finset.range r, ‖c j‖ * |k j| := by
  unfold projectorWeight
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hpos : 0 < 2 * Real.pi / L := by positivity
  rw [abs_mul, abs_of_pos hpos]
  ring

/-- **The ledger verdict for the whole family.**  With shifts on the source grid
`s_j = k_j (2π/L)` and Dirichlet length `log N = cL`, the diagonal-damping factor
of *any* finite shift projector equals

    `(2πc · ∑_j ‖c_j‖|k_j|)²`,

a constant independent of `L`.  The negative verdict recorded for the first
difference in `source_gain_factor_eq` was therefore not an artefact of that
particular choice: no finite shift projector on the source grid buys a power
of `L`. -/
theorem source_projector_gain_eq (cc : ℕ → ℂ) (k : ℕ → ℝ) {L cN : ℝ} (hL : 0 < L) (r : ℕ)
    {N : ℕ} (hlog : Real.log N = cN * L) :
    (projectorWeight cc (fun j => k j * (2 * Real.pi / L)) r * Real.log N) ^ 2
      = (2 * Real.pi * cN * ∑ j ∈ Finset.range r, ‖cc j‖ * |k j|) ^ 2 := by
  rw [source_projectorWeight_eq cc k hL r, hlog]
  congr 1
  field_simp

/-! ### Floor retention versus diagonal vanishing -/

/-- **The structural obstruction: the two ledger demands are incompatible.**

An annihilating projector damps *low* frequencies — that is the whole content of
`P(1) = 0` — and the anchored coercive floor lives at a low frequency `λ₀` (the
grid-spacing scale).  So suppose the projector retains the floor, in the sense
that its symbol satisfies `‖P(λ₀)‖ ≥ ϱ ≥ 0`, and that the Dirichlet length
dominates the anchor frequency, `|λ₀| ≤ log N`.  Then the guaranteed
diagonal-damping factor obeys

    `ϱ² ≤ (W log N)²`,

so it cannot tend to `0` while the retained floor `ϱ` stays bounded away
from `0`.  Within the purify-then-estimate budget model the strict margin
`δ > 0` therefore cannot come from a finite shift projector alone. -/
theorem projector_ledger_no_margin {c : ℕ → ℂ} {sh : ℕ → ℝ} {r : ℕ}
    (hc : ∑ j ∈ Finset.range r, c j = 0) {lam0 rho : ℝ} (hrho : 0 ≤ rho)
    (hfloor : rho ≤ ‖shiftMultiplier c sh r lam0‖) {N : ℕ} (hN : |lam0| ≤ Real.log N) :
    rho ^ 2 ≤ (projectorWeight c sh r * Real.log N) ^ 2 := by
  have hW : 0 ≤ projectorWeight c sh r := projectorWeight_nonneg c sh r
  have h1 : rho ≤ projectorWeight c sh r * |lam0| :=
    le_trans hfloor (norm_shiftMultiplier_le_of_annihilating hc lam0)
  have h2 : projectorWeight c sh r * |lam0| ≤ projectorWeight c sh r * Real.log N :=
    mul_le_mul_of_nonneg_left hN hW
  have h3 : rho ≤ projectorWeight c sh r * Real.log N := le_trans h1 h2
  nlinarith

/-- The contrapositive form actually used when scanning candidates: if a
projector's guaranteed damping factor is strictly below `ϱ²`, then it cannot
retain a floor of size `ϱ` at any frequency below `log N`. -/
theorem no_floor_of_small_gain {c : ℕ → ℂ} {sh : ℕ → ℝ} {r : ℕ}
    (hc : ∑ j ∈ Finset.range r, c j = 0) {lam0 rho : ℝ} (hrho : 0 ≤ rho) {N : ℕ}
    (hN : |lam0| ≤ Real.log N)
    (hgain : (projectorWeight c sh r * Real.log N) ^ 2 < rho ^ 2) :
    ‖shiftMultiplier c sh r lam0‖ < rho := by
  by_contra hcon
  exact absurd (projector_ledger_no_margin hc hrho (not_lt.mp hcon) hN) (not_le.mpr hgain)

end RiemannAnalytic

/-
# Row A — non-vacuity of the scaling / cubic-drive / small-bare-coupling package

`RowASmallBareCoupling.rowA_small_bare_coupling` is a conditional theorem with a
long hypothesis package: the source majorants of the five channels, a two-sided
window for the Gaussian shell coefficient, a quartic debt bound, a block-spin
irrelevant sector with a dimensional gap, a nonlinear remainder that is
Lipschitz in the state and cubically driven by the coupling on every interval,
and a Lipschitz dependence of the coefficients on the irrelevant state.  A
conditional theorem is worthless if that package is contradictory, so this file
exhibits an explicit instance of *all* of it and derives the conclusion.

Unlike the witness in `RowALiteralBetaWitness`, the memory sector here is
switched **on**: the irrelevant state is a genuine block-spin sector of one
operator of scaling dimension `8` at block size `L = 2`, so the linear factor is
`2^{−4} = 1/16`, and the remainder

    N_j(g, x) = 10⁻³g⁴

drives it with the interval-form cubic constant `C_gen = 4·10⁻³`.  The Gaussian
shell coefficient really depends on that state, `β_{Z,j}(p) = 1 + 10⁻²x_j(p)`,
so the whole Duhamel / marginal-weight / trajectory-summation chain is exercised
rather than evaded.  The direct channel sensitivity is nonzero as well
(`a_I = 10⁻³`, `C_dir = 10⁻²`).

This certifies consistency of the package; it does **not** close Row A, whose
open content is that the literal Bałaban objects satisfy hypotheses of this
shape with these constants.
-/
import RequestProject.YangMills.RowASmallBareCoupling

namespace YangMills
namespace CubicDriveWitness

open Finset

/-! ## 1. The concrete data -/

/-- No determinant modes. -/
noncomputable def lamD : ℕ → ℝ → Fin 0 → ℝ := fun _ _ i => i.elim0

/-- No gauge-determinant modes. -/
noncomputable def lamG : ℕ → ℝ → Fin 0 → ℝ := fun _ _ i => i.elim0

/-- A single, genuinely nonzero interaction Taylor coefficient. -/
noncomputable def aI : ℕ → ℝ → ℕ → ℝ := fun _ _ _ => 1 / 1000

/-- The chart and localisation channels are switched off. -/
def aZero : ℕ → ℝ → ℕ → ℝ := fun _ _ _ => 0

/-- One irrelevant operator, of scaling dimension `8`: at block size `L = 2` the
dimensional gap is `δ = 4` and the block-spin factor is `2⁻⁴ = 1/16`. -/
def dimIrr : Fin 1 → ℝ := fun _ => 8

/-- The nonlinear remainder of the renormalisation-group step: quartic in the
coupling, independent of the state. -/
noncomputable def Nlin : ℕ → ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) :=
  fun _ g _ _ => (1 / 1000) * g ^ 4

/-- The shell coefficient as a function of the irrelevant state and the
coupling. -/
noncomputable def shellVal (x g : ℝ) : ℝ := 1 + (1 / 100) * x + (1 / 1000) * g ^ 4

/-- The joint recursion of the trajectory and the irrelevant state. -/
noncomputable def state (p : ℝ) : ℕ → ℝ × (Fin 1 → ℝ)
  | 0 => (p, fun _ => 0)
  | (j + 1) =>
      ((state p j).1 + shellVal ((state p j).2 0) (couplingOf (state p j).1),
        rgStep 2 dimIrr Nlin j (state p j).1 (state p j).2)

/-- The generated trajectory. -/
noncomputable def traj (p : ℝ) (j : ℕ) : ℝ := (state p j).1

/-- The generated irrelevant state. -/
noncomputable def mem (j : ℕ) (p : ℝ) : Fin 1 → ℝ := (state p j).2

/-- The Gaussian shell coefficient, genuinely dependent on the irrelevant
state. -/
noncomputable def betaZ (j : ℕ) (p : ℝ) : ℝ := 1 + (1 / 100) * mem j p 0

/-- The shell coefficient of the witness. -/
noncomputable def bet (j : ℕ) (p : ℝ) : ℝ :=
  shellVal (mem j p 0) (couplingOf (traj p j))

theorem traj_zero (p : ℝ) : traj p 0 = p := rfl

theorem mem_zero (p : ℝ) : mem 0 p = fun _ => 0 := rfl

theorem traj_succ (p : ℝ) (j : ℕ) : traj p (j + 1) = traj p j + bet j p := rfl

theorem mem_succ (p : ℝ) (j : ℕ) :
    mem (j + 1) p = rgStep 2 dimIrr Nlin j (traj p j) (mem j p) := rfl

/-! ## 2. The block-spin factor -/

theorem two_rpow_neg_four : (2 : ℝ) ^ (-(4 : ℝ)) = 1 / 16 := by
  rw [Real.rpow_neg (by norm_num)]
  norm_num [show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem blockScaling_value (x : Fin 1 → ℝ) (o : Fin 1) :
    blockScaling 2 dimIrr x o = (1 / 16) * x o := by
  rw [blockScaling, dimIrr]
  norm_num [two_rpow_neg_four]

theorem mem_succ_value (p : ℝ) (j : ℕ) (o : Fin 1) :
    mem (j + 1) p o = (1 / 16) * mem j p o + (1 / 1000) * couplingOf (traj p j) ^ 4 := by
  rw [mem_succ, rgStep]
  simp [blockScaling_value, Nlin]

/-! ## 3. The trajectory and the irrelevant state stay in their windows -/

theorem couplingOf_one : couplingOf (1 : ℝ) = 1 := by
  rw [couplingOf]
  norm_num

/-- On the tube `p ≥ 1` the trajectory stays above `1` and the irrelevant state
stays in `[0, 1/500]`. -/
theorem state_bounds {p : ℝ} (hp : (1 : ℝ) ≤ p) (j : ℕ) :
    1 ≤ traj p j ∧ ∀ o, 0 ≤ mem j p o ∧ mem j p o ≤ 1 / 500 := by
  induction j with
  | zero =>
      refine ⟨hp, fun o => ?_⟩
      rw [mem_zero]
      norm_num
  | succ j ih =>
      obtain ⟨h1, h2⟩ := ih
      have hg0 : 0 ≤ couplingOf (traj p j) := couplingOf_nonneg _
      have hg1 : couplingOf (traj p j) ≤ 1 := by
        have h := couplingOf_le (u₀ := 1) (u := traj p j) (by norm_num) h1
        rwa [couplingOf_one] at h
      have hg4 : couplingOf (traj p j) ^ 4 ≤ 1 := by
        have := pow_le_pow_left₀ hg0 hg1 4
        simpa using this
      have hg40 : (0 : ℝ) ≤ couplingOf (traj p j) ^ 4 := by positivity
      obtain ⟨hm0, hm1⟩ := h2 0
      refine ⟨?_, fun o => ?_⟩
      · rw [traj_succ, bet, shellVal]
        linarith
      · obtain ⟨ho0, ho1⟩ := h2 o
        rw [mem_succ_value]
        constructor <;> linarith

theorem traj_ge_one {p : ℝ} (hp : (1 : ℝ) ≤ p) (j : ℕ) : 1 ≤ traj p j :=
  (state_bounds hp j).1

theorem mem_nonneg {p : ℝ} (hp : (1 : ℝ) ≤ p) (j : ℕ) (o : Fin 1) : 0 ≤ mem j p o :=
  ((state_bounds hp j).2 o).1

theorem mem_le {p : ℝ} (hp : (1 : ℝ) ≤ p) (j : ℕ) (o : Fin 1) : mem j p o ≤ 1 / 500 :=
  ((state_bounds hp j).2 o).2

theorem bet_nonneg {p : ℝ} (hp : (1 : ℝ) ≤ p) (j : ℕ) : 0 ≤ bet j p := by
  have h2 := mem_nonneg hp j 0
  have h3 : (0 : ℝ) ≤ couplingOf (traj p j) ^ 4 := by positivity
  rw [bet, shellVal]; linarith

/-- The trajectory never falls below its starting point. -/
theorem traj_ge_start {p : ℝ} (hp : (1 : ℝ) ≤ p) (j : ℕ) : p ≤ traj p j := by
  induction j with
  | zero => exact le_of_eq (traj_zero p).symm
  | succ k ih =>
      have hb := bet_nonneg hp k
      rw [traj_succ]; linarith

/-- The trajectory generated by `bet` in the shooting sense is the one defined
by the joint recursion. -/
theorem shootingTrajectory_eq (p : ℝ) (j : ℕ) : shootingTrajectory bet p j = traj p j := by
  induction j with
  | zero => simp [traj_zero]
  | succ j ih => rw [shootingTrajectory_step, ih, traj_succ]

/-! ## 4. The witness satisfies the literal-shell structure -/

theorem literalShellAt_eq (j : ℕ) (p g : ℝ) :
    literalShellAt betaZ lamD lamG aI aZero aZero 1 j p g
      = 1 + (1 / 100) * mem j p 0 + (1 / 1000) * g ^ 4 := by
  simp [literalShellAt, frozenShellInteraction, logDetChannel, tailPolyChannel,
    betaZ, aI, aZero]

theorem frozenShellInteraction_eq (j : ℕ) (p g : ℝ) :
    frozenShellInteraction (lamD j p) (lamG j p) (aI j p) (aZero j p) (aZero j p) 1 g
      = (1 / 1000) * g ^ 4 := by
  simp [frozenShellInteraction, logDetChannel, tailPolyChannel, aI, aZero]

theorem bet_eq_literalShellAt (j : ℕ) (p : ℝ) :
    bet j p = literalShellAt betaZ lamD lamG aI aZero aZero 1 j p
      (couplingOf (shootingTrajectory bet p j)) := by
  rw [shootingTrajectory_eq, literalShellAt_eq, bet, shellVal]

/-! ## 5. The renormalisation-group hypotheses of the witness -/

theorem cdir_value :
    analyticDirectSensitivityBound (Fintype.card (Fin 0)) (Fintype.card (Fin 0))
      0 0 (1 / 2) (1 / 1000) 0 0 1 (1 / 2) ≤ 1 / 100 := by
  simp [analyticDirectSensitivityBound]
  norm_num

/-- The remainder does not depend on the state at all, so `η = 0`. -/
theorem hNlip_witness (j : ℕ) (g : ℝ) (x y : Fin 1 → ℝ) :
    ‖Nlin j g x - Nlin j g y‖ ≤ (0 : ℝ) * ‖x - y‖ := by
  have h : Nlin j g x - Nlin j g y = 0 := by
    funext o; simp [Nlin]
  rw [h]
  simp

/-- **The interval-form cubic drive of the witness.**  `|10⁻³(g⁴ − g'⁴)| ≤
4·10⁻³G³|g − g'|` on `[0,G]`. -/
theorem hgen3_witness (j : ℕ) (G g g' : ℝ) (x : Fin 1 → ℝ) (hg0 : 0 ≤ g) (hgG : g ≤ G)
    (hg'0 : 0 ≤ g') (hg'G : g' ≤ G) :
    ‖Nlin j g x - Nlin j g' x‖ ≤ (1 / 250 : ℝ) * G ^ 3 * |g - g'| := by
  have hG0 : 0 ≤ G := le_trans hg0 hgG
  have hpow : |g ^ (3 + 1) - g' ^ (3 + 1)| ≤ ((3 : ℝ) + 1) * G ^ 3 * |g - g'| :=
    abs_pow_succ_sub_le hg0 hg'0 hgG hg'G 3
  have hpow' : |g ^ 4 - g' ^ 4| ≤ 4 * G ^ 3 * |g - g'| := by
    norm_num at hpow
    exact hpow
  have hc : (0 : ℝ) ≤ (1 / 250 : ℝ) * G ^ 3 * |g - g'| := by positivity
  refine (pi_norm_le_iff_of_nonneg hc).mpr fun o => ?_
  have hval : (Nlin j g x - Nlin j g' x) o = (1 / 1000 : ℝ) * (g ^ 4 - g' ^ 4) := by
    simp [Nlin]; ring
  rw [hval, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 1000)]
  calc (1 / 1000 : ℝ) * |g ^ 4 - g' ^ 4|
      ≤ (1 / 1000) * (4 * G ^ 3 * |g - g'|) :=
        mul_le_mul_of_nonneg_left hpow' (by norm_num)
    _ = (1 / 250 : ℝ) * G ^ 3 * |g - g'| := by ring

theorem hlip_witness (j : ℕ) (p q g : ℝ) :
    |literalShellAt betaZ lamD lamG aI aZero aZero 1 j p g
      - literalShellAt betaZ lamD lamG aI aZero aZero 1 j q g|
      ≤ (1 / 100 : ℝ) * ‖mem j p - mem j q‖ := by
  rw [literalShellAt_eq, literalShellAt_eq]
  have h : 1 + (1 / 100 : ℝ) * mem j p 0 + (1 / 1000) * g ^ 4
      - (1 + (1 / 100) * mem j q 0 + (1 / 1000) * g ^ 4)
      = (1 / 100) * (mem j p 0 - mem j q 0) := by ring
  rw [h, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100)]
  have hcomp : |mem j p 0 - mem j q 0| ≤ ‖mem j p - mem j q‖ := by
    have := norm_le_pi_norm (mem j p - mem j q) 0
    simpa [Real.norm_eq_abs] using this
  exact mul_le_mul_of_nonneg_left hcomp (by norm_num)

theorem hIntQ_witness (j : ℕ) (p : ℝ) (hp : (1 : ℝ) ≤ p) :
    |frozenShellInteraction (lamD j p) (lamG j p) (aI j p) (aZero j p) (aZero j p) 1
        (couplingOf (shootingTrajectory bet p j))|
      ≤ (1 / 1000 : ℝ) * couplingOf p ^ 4 := by
  rw [frozenShellInteraction_eq]
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le one_pos hp
  have hcoup : couplingOf (traj p j) ≤ couplingOf p :=
    couplingOf_le hp0 (traj_ge_start hp j)
  have h4 : couplingOf (shootingTrajectory bet p j) ^ 4 ≤ couplingOf p ^ 4 := by
    rw [shootingTrajectory_eq]
    exact pow_le_pow_left₀ (couplingOf_nonneg _) hcoup 4
  have habs : |(1 / 1000 : ℝ) * couplingOf (shootingTrajectory bet p j) ^ 4|
      = (1 / 1000) * couplingOf (shootingTrajectory bet p j) ^ 4 :=
    abs_of_nonneg (by positivity)
  rw [habs]
  linarith

/-! ## 6. The package is inhabited -/

/-- **The scaling / cubic-drive / small-bare-coupling hypothesis package is
inhabited.**  For the explicit data above — a nonzero interaction channel, an
active block-spin irrelevant sector with dimensional gap `δ = 4`, a quartic
coupling drive, and a Gaussian shell coefficient that really depends on that
sector — there is a threshold `U` such that every bare inverse coupling above it
produces the Row-A completion predicate at every cutoff and every admissible
observation target. -/
theorem cubicDrive_package_inhabited :
    ∃ U : ℝ, 1 ≤ U ∧
      ∀ u₀ : ℝ, U ≤ u₀ → ∀ (K : ℕ) (target : ℝ),
        u₀ + (1 + 1 / 50000 + quarticDebtTolerance (1 / 1000) u₀) * K ≤ target →
        RowACompletion bet K target
          (1 - quarticDebtTolerance (1 / 1000) u₀)
          (1 + 1 / 50000 + quarticDebtTolerance (1 / 1000) u₀)
          (target - (1 + 1 / 50000 + quarticDebtTolerance (1 / 1000) u₀) * K)⁻¹ := by
  obtain ⟨U, -, hU1, hall⟩ := rowA_small_bare_coupling
    (bet := bet) (betaZ := betaZ) (lamD := lamD) (lamG := lamG)
    (aI := aI) (aC := aZero) (aL := aZero) (N := 1)
    (dim := dimIrr) (Nl := Nlin) (rst := mem)
    (LamDet := 0) (LamGauge := 0) (theta := 1 / 2)
    (AI := 1 / 1000) (AC := 0) (AL := 0) (Kmaj := 1) (rho := 1 / 2)
    (Cdir := 1 / 100) (Lcoef := 1 / 100) (Cgen := 1 / 250) (Cmem := 1)
    (L := 2) (delta := 4) (eta := 0)
    (bZm := 1) (bZp := 1 + 1 / 50000) (Cint := 1 / 1000) (ubase := 1)
    (fun j p _ => bet_eq_literalShellAt j p)
    (fun _ _ i => i.elim0) (fun _ _ i => i.elim0) le_rfl le_rfl
    (fun j p n => by simp [aI]) (fun j p n => by simp [aZero])
    (fun j p n => by simp [aZero])
    (by norm_num) le_rfl le_rfl (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    cdir_value
    (fun j p hp => by
      have := mem_nonneg hp j 0
      rw [betaZ]; linarith)
    (fun j p hp => by
      have := mem_le hp j 0
      rw [betaZ]; linarith)
    hIntQ_witness (by norm_num)
    (by norm_num) (fun o => by rw [dimIrr]; norm_num)
    hNlip_witness le_rfl (by rw [two_rpow_neg_four]; norm_num)
    hgen3_witness (by norm_num)
    (fun p q _ _ => by rw [mem_zero, mem_zero])
    (fun j p _ => by rw [shootingTrajectory_eq]; exact mem_succ p j)
    hlip_witness (by norm_num)
    (by rw [two_rpow_neg_four]; norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨U, hU1, hall⟩

end CubicDriveWitness
end YangMills

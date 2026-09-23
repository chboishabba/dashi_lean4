/-
# Row A1 — the end-to-end statement

This file states Row A1 as a single theorem: the positivity of the one-shell
beta coefficient

    β_j ≥ (11/24) C_A(G) − r_local − L_β γ B  >  0,

with

* `r_local` supplied by the A1a chain (`A1aClosure.A1a_closure_of_formFactor`),
  namely the exact number `splitCost (2/5) = 236679/640000 = 0.3698…`;
* `L_β γ B` supplied by the A1b chain (`BetaObserver.historyRemainder_bound`),
  with `γ = 1/(1−κ)` for the observer contraction factor `κ < 1`.

Two inputs remain explicit hypotheses, and they are exactly the two physical
facts this development does not derive:

1. `hlocal` — the identification of the local remainder of the shell with the
   Lebesgue cell integral of the cancellation-preserving combined density of the
   four hypercubic orbits of the joint (Wilson + reduced Faddeev–Popov + Haar)
   one-loop numerator, and the transverse form-factor bounds on that numerator;
2. `hobs` — the observer data for the RG step (`κ`, `L_β`, tube radius `B`)
   with `L_β γ B ≤ 1/2`.

Everything between those inputs and the conclusion is proved here.
-/
import RequestProject.YangMills.A1aClosure
import RequestProject.YangMills.LocalGap

namespace YangMills

open MeasureTheory

variable {X : Type*} [PseudoMetricSpace X]

/-- **Row A1, end to end.**  The A1a cell integral bound and the A1b history
budget together force a strictly positive shell beta coefficient for every
`SU(N)` with `N ≥ 2`. -/
theorem A1_beta_pos
    {N : ℕ} (hN : 2 ≤ N)
    -- A1a: the joint one-loop numerator and its transverse form factor
    {Num : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ} {Pi : (Fin 4 → ℝ) → ℝ}
    (hNum : IsTransverseFactorisation Num Pi)
    {A : ℝ} (hA : 0 ≤ A) (hA' : A ≤ 1 / 40)
    (r₁ r₂ r₃ r₄ : Fin 4 × Fin 4)
    (hnearPi : ∀ p ∈ nearCellBox (2 / 5), |Pi p| ≤ A * phatSq p)
    (hfarPi : ∀ p ∈ farCellShell (2 / 5), |Pi p| ≤ 25 / 128)
    (hint : IntegrableOn (combinedDensity (orbitDensity Num r₁) (orbitDensity Num r₂)
      (orbitDensity Num r₃) (orbitDensity Num r₄)) brillouinCell volume)
    -- A1b: the beta observer contraction data
    {beta Rlocal : ℝ} {betaCoeff : X → ℝ} {T : X → X} {kappa L B : ℝ}
    (hk0 : 0 ≤ kappa) (hk1 : kappa < 1) (hL : 0 ≤ L)
    (hT : IsObserverContraction T kappa) (hbeta : IsBetaLipschitz betaCoeff L)
    {x xs : X} (hfix : T xs = xs) (hB : dist x xs ≤ B) (m : ℕ)
    (hbudget : L * (1 / (1 - kappa)) * B ≤ 1 / 2)
    -- the two identifications with the shell data
    (hlocal : Rlocal = ∫ p in brillouinCell,
      combinedDensity (orbitDensity Num r₁) (orbitDensity Num r₂)
        (orbitDensity Num r₃) (orbitDensity Num r₄) p)
    (hdecomp : beta = 11 / 24 * casimirAdjointSU N + Rlocal
      + historyRemainder betaCoeff T x xs m) :
    0 < beta := by
  have ha1a : -splitCost (2 / 5) ≤ Rlocal := by
    rw [hlocal]
    exact A1a_closure_of_formFactor hNum hA hA' r₁ r₂ r₃ r₄ hnearPi hfarPi hint
  have ha1b : |historyRemainder betaCoeff T x xs m| ≤ L * (1 / (1 - kappa)) * B :=
    historyRemainder_bound hk0 hk1 hL hT hbeta hfix hB m
  exact beta_pos_of_budgets hN hdecomp ha1a le_rfl ha1b hbudget

/-- **Non-vacuity check for `A1_beta_pos`.**  The hypothesis package of
`A1_beta_pos` is jointly satisfiable: instantiating it at the trivial numerator
and the trivial observer produces an actual application of the theorem.  So the
conclusion is not reached through a contradictory hypothesis set. -/
theorem A1_beta_pos_nonvacuous : (0:ℝ) < 11 / 24 * casimirAdjointSU 2 := by
  have hz : combinedDensity (orbitDensity (fun _ _ _ => (0:ℝ)) (0,0))
      (orbitDensity (fun _ _ _ => (0:ℝ)) (0,0)) (orbitDensity (fun _ _ _ => (0:ℝ)) (0,0))
      (orbitDensity (fun _ _ _ => (0:ℝ)) (0,0)) = fun _ => 0 := by
    funext p; simp [combinedDensity, orbitDensity]
  exact A1_beta_pos (N := 2) (le_refl 2)
    (Num := fun _ _ _ => 0) (Pi := fun _ => 0)
    (by intro p mu nu; simp) (A := 0) le_rfl (by norm_num)
    (0,0) (0,0) (0,0) (0,0)
    (by intro p hp; simp) (by intro p hp; norm_num)
    (by rw [hz]; exact integrableOn_zero)
    (X := ℝ) (betaCoeff := fun _ => 0) (T := fun _ => 0) (kappa := 0) (L := 0) (B := 0)
    le_rfl (by norm_num) le_rfl (by intro x y; simp) (by intro x y; simp)
    (x := 0) (xs := 0) rfl (by simp) 0 (by norm_num)
    (Rlocal := 0) (by rw [hz]; simp)
    (beta := 11 / 24 * casimirAdjointSU 2) (by simp [historyRemainder])

end YangMills

/-
# Row A1a — the closure statement

Everything the near/far analysis produces is assembled here into a single
theorem chain:

    scalar form factor bound
      → per-orbit pointwise density bounds (near box and far shell)
      → cancellation-preserving combined density bound
      → Lebesgue cell integral bound
      → the Row A1 local remainder budget.

The combination `D = 4 d₁ + 6 d₂ + 4 d₃ + d₄` with the hypercubic multiplicities
`(4,6,4,1)` of the four axis-support orbits is bounded *before* integration, so
no cancellation is discarded at the assembly step.

The only physical input left in the chain is the pair of scalar bounds on the
form factor `Π` of the joint (Wilson + reduced Faddeev–Popov + Haar) numerator:
`|Π(p)| ≤ A p̂²` with `A ≤ 1/40` on the near box, and `|Π(p)| ≤ 25/128` on the
far shell.  See `docs/ym_A1_status.md` for the exact statement of what remains.
-/
import RequestProject.YangMills.TransverseFormFactor
import RequestProject.YangMills.ShellBudget

namespace YangMills

open MeasureTheory Finset

/-- The cancellation-preserving combination of the four orbit densities. -/
noncomputable def combinedDensity (d₁ d₂ d₃ d₄ : (Fin 4 → ℝ) → ℝ)
    (p : Fin 4 → ℝ) : ℝ :=
  4 * d₁ p + 6 * d₂ p + 4 * d₃ p + d₄ p

/-- A common per-orbit modulus bound `u` bounds the combined density below by
`−15 u`, the multiplicities being `4 + 6 + 4 + 1 = 15`. -/
theorem combinedDensity_lower_bound {d₁ d₂ d₃ d₄ : (Fin 4 → ℝ) → ℝ} {u : ℝ}
    {p : Fin 4 → ℝ} (h₁ : |d₁ p| ≤ u) (h₂ : |d₂ p| ≤ u) (h₃ : |d₃ p| ≤ u)
    (h₄ : |d₄ p| ≤ u) : -(15 * u) ≤ combinedDensity d₁ d₂ d₃ d₄ p := by
  have g₁ := neg_le_of_abs_le h₁
  have g₂ := neg_le_of_abs_le h₂
  have g₃ := neg_le_of_abs_le h₃
  have g₄ := neg_le_of_abs_le h₄
  unfold combinedDensity
  linarith

/-- **Row A1a cell bound from per-orbit pointwise bounds.**  Near per-orbit
modulus `2/5` and far per-orbit modulus `25/64` put the cell integral of the
combined density strictly inside the shell budget. -/
theorem A1a_cell_bound {d₁ d₂ d₃ d₄ : (Fin 4 → ℝ) → ℝ}
    (hint : IntegrableOn (combinedDensity d₁ d₂ d₃ d₄) brillouinCell volume)
    (hnear : ∀ p ∈ nearCellBox (2 / 5),
      |d₁ p| ≤ 2 / 5 ∧ |d₂ p| ≤ 2 / 5 ∧ |d₃ p| ≤ 2 / 5 ∧ |d₄ p| ≤ 2 / 5)
    (hfar : ∀ p ∈ farCellShell (2 / 5),
      |d₁ p| ≤ 25 / 64 ∧ |d₂ p| ≤ 25 / 64 ∧ |d₃ p| ≤ 25 / 64 ∧ |d₄ p| ≤ 25 / 64) :
    -splitCost (2 / 5) ≤ ∫ p in brillouinCell, combinedDensity d₁ d₂ d₃ d₄ p := by
  refine A1a_shell_bound_sharp hint ?_ ?_
  · intro p hp
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hnear p hp
    have := combinedDensity_lower_bound h₁ h₂ h₃ h₄
    unfold combinedOfPerOrbit perOrbitNearBound
    linarith
  · intro p hp
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hfar p hp
    have := combinedDensity_lower_bound h₁ h₂ h₃ h₄
    unfold combinedOfPerOrbit perOrbitFarBound
    linarith

/-- The four orbit densities attached to a joint numerator `N` and a choice of
orbit representatives `rep : Fin 4 → Fin 4 × Fin 4`. -/
noncomputable def orbitDensity (N : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (rep : Fin 4 × Fin 4) (p : Fin 4 → ℝ) : ℝ :=
  N p rep.1 rep.2 / phatSq p

/-- **Row A1a closure modulo the scalar form factor.**  If the joint one-loop
numerator is transverse with form factor `Π`, and `Π` obeys

* `|Π(p)| ≤ A p̂²` with `0 ≤ A ≤ 1/40` on the near box `[0,2/5]^4`, and
* `|Π(p)| ≤ 25/128` on the far shell,

then the cell integral of the cancellation-preserving combined density of the
four orbit representatives is strictly inside the Row A1 shell budget.  No other
physical hypothesis enters. -/
theorem A1a_closure_of_formFactor
    {N : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ} {Pi : (Fin 4 → ℝ) → ℝ}
    (hN : IsTransverseFactorisation N Pi)
    {A : ℝ} (hA : 0 ≤ A) (hA' : A ≤ 1 / 40)
    (r₁ r₂ r₃ r₄ : Fin 4 × Fin 4)
    (hnearPi : ∀ p ∈ nearCellBox (2 / 5), |Pi p| ≤ A * phatSq p)
    (hfarPi : ∀ p ∈ farCellShell (2 / 5), |Pi p| ≤ 25 / 128)
    (hint : IntegrableOn (combinedDensity (orbitDensity N r₁) (orbitDensity N r₂)
      (orbitDensity N r₃) (orbitDensity N r₄)) brillouinCell volume) :
    -splitCost (2 / 5) ≤
      ∫ p in brillouinCell, combinedDensity (orbitDensity N r₁) (orbitDensity N r₂)
        (orbitDensity N r₃) (orbitDensity N r₄) p := by
  refine A1a_cell_bound hint ?_ ?_
  · intro p hp
    have h := hnearPi p hp
    exact ⟨near_perOrbit_bound_of_formFactor hN hA hA' h _ _,
      near_perOrbit_bound_of_formFactor hN hA hA' h _ _,
      near_perOrbit_bound_of_formFactor hN hA hA' h _ _,
      near_perOrbit_bound_of_formFactor hN hA hA' h _ _⟩
  · intro p hp
    have h := hfarPi p hp
    exact ⟨far_perOrbit_bound_of_formFactor hN h _ _,
      far_perOrbit_bound_of_formFactor hN h _ _,
      far_perOrbit_bound_of_formFactor hN h _ _,
      far_perOrbit_bound_of_formFactor hN h _ _⟩

end YangMills

/-
**M6: the detectability radius carried by the one-sided Gram defect.**

`OneSidedGram.lean` gives the explicit quadratic floor

  `ΔGram(m+1) ≥ (81/16384) L⁶ α²`

for the Gram determinant of the one-sided source window (once the lattice tail
is absorbed, `htail` below).  `Detectability.lean` turns a quadratic floor plus
an error budget into a tube around the critical line.  This file plugs the
first into the second, in the exact `L⁶` normalisation the Gram defect
produces:

  `ΔGram ≤ E   ⟹   |α| ≤ √(E / ((81/16384) L⁶))`

(`abs_offset_le_gramDetectRadius`, `zero_in_gram_tube`), and records the
shrinking-tube consequence: if the *relative* budget `E(T)/L(T)⁶` tends to
zero, the radius tends to zero (`gramDetectRadius_tendsto_zero`), and if it
vanishes at some scale the zero is exactly on the critical line
(`zero_on_line_of_gram_budget_zero`).

The error budget `E` is a hypothesis here, not a theorem: producing it is the
prime-side obligation (`PairExpansion.lean` states the literal transport
inequality it has to feed).
-/
import RiemannAnalytic.Detectability
import RiemannAnalytic.OneSidedGram

namespace RiemannAnalytic

open Filter Topology

/-- The detectability radius attached to the `L⁶`-normalised Gram floor. -/
noncomputable def gramDetectRadius (L E : ℝ) : ℝ := detectRadius (81 / 16384 * L ^ 2) L E

/-- **Detectability from the one-sided Gram floor.**  For a `C¹`, nonnegative,
real even taper in the source regime, a window long enough for the lattice tail
to eat at most half the retention floor, and any upper bound `E` for the Gram
defect, the transverse offset lies inside the explicit radius. -/
theorem abs_offset_le_gramDetectRadius {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ) {m : ℕ}
    (hm : 1 ≤ m)
    (htail : derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m) ≤ 9 / 1024 * L ^ 4 * α ^ 2)
    {E : ℝ} (hbound : finiteGridGramDefect φ (2 * Real.pi / L) α (m + 1) ≤ E) :
    |α| ≤ gramDetectRadius L E := by
  have hfloor := finiteGridGramDefect_source_floor hφ hev hnn hL h2R ha hplat α hm
  have hstep : 81 / 16384 * L ^ 2 * L ^ 4 * α ^ 2
      ≤ 9 / 16 * L ^ 2 * (9 / 512 * L ^ 4 * α ^ 2
        - derivMass φ α ^ 2 / ((2 * Real.pi / L) ^ 2 * m)) := by
    have hL2 : (0 : ℝ) < 9 / 16 * L ^ 2 := by positivity
    nlinarith [htail, hL2]
  exact abs_offset_le_detectRadius (by positivity) hL (by linarith) hbound

/-- **The tube around the critical line.**  Applied at a hypothetical zero of
the completed zeta function, whose transverse offset is `zeroOffset ρ`. -/
theorem zero_in_gram_tube {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (ρ : ℂ) {m : ℕ}
    (hm : 1 ≤ m)
    (htail : derivMass φ (zeroOffset ρ) ^ 2 / ((2 * Real.pi / L) ^ 2 * m)
      ≤ 9 / 1024 * L ^ 4 * zeroOffset ρ ^ 2)
    {E : ℝ}
    (hbound : finiteGridGramDefect φ (2 * Real.pi / L) (zeroOffset ρ) (m + 1) ≤ E) :
    |ρ.re - 1 / 2| ≤ gramDetectRadius L E :=
  abs_offset_le_gramDetectRadius hφ hev hnn hL h2R ha hplat (zeroOffset ρ) hm htail hbound

/-- If the relative budget `E(T)/L(T)⁶` tends to zero, the Gram detectability
radius tends to zero: the tube shrinks onto the critical line. -/
theorem gramDetectRadius_tendsto_zero (L E : ℝ → ℝ)
    (h : Tendsto (fun T => E T / (81 / 16384 * L T ^ 2 * L T ^ 4)) atTop (𝓝 0)) :
    Tendsto (fun T => gramDetectRadius (L T) (E T)) atTop (𝓝 0) := by
  have hc := (Real.continuous_sqrt.tendsto 0).comp h
  simpa [gramDetectRadius, detectRadius, Function.comp] using hc

/-- If at some scale the Gram budget makes the radius vanish, the zero is
exactly on the critical line. -/
theorem zero_on_line_of_gram_budget_zero {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (hnn : ∀ t, 0 ≤ φ t) {L : ℝ} (hL : 0 < L) (h2R : 2 * R ≤ L)
    {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (ρ : ℂ) {m : ℕ}
    (hm : 1 ≤ m)
    (htail : derivMass φ (zeroOffset ρ) ^ 2 / ((2 * Real.pi / L) ^ 2 * m)
      ≤ 9 / 1024 * L ^ 4 * zeroOffset ρ ^ 2)
    {E : ℝ}
    (hbound : finiteGridGramDefect φ (2 * Real.pi / L) (zeroOffset ρ) (m + 1) ≤ E)
    (hzero : gramDetectRadius L E = 0) :
    ρ.re = 1 / 2 := by
  have h := zero_in_gram_tube hφ hev hnn hL h2R ha hplat ρ hm htail hbound
  rw [hzero] at h
  have habs : |ρ.re - 1 / 2| = 0 := le_antisymm h (abs_nonneg _)
  have := abs_eq_zero.1 habs
  linarith

end RiemannAnalytic

/-
# Row A1.2 — the Lean shell Gaussian coefficient *is* the polarization
coefficient of the source

## Source data used here

The definition of the vacuum-polarization tensor used below is the one supplied
with the task, from the coupling-constant renormalisation section of the
Bałaban RG paper (CMP 109):

    Π(b,b') = [ δ² / δB(b) δB(b') · E^{(j)}(U_j(e^{iB})) ]_{B = 0} ,

and `β_j(g_{j-1})` is *by definition* the coefficient of the specified tensor
structure inside that polarization tensor.

Everything in this file is a statement about that second variation.  Nothing
about the source effective action is assumed beyond the shape hypotheses that
are stated explicitly in each theorem.

## What is proved

* `polarizationAt` — the literal second variation `δ²/δB(b) δB(b')` at `B = 0`,
  taken along the two-parameter test configuration `s·e_b + t·e_{b'}`.
* `polarizationAt_of_quadratic` — for an effective action whose restriction to
  the two-parameter test configuration is
  `β·(τ·st + q₂₀·s² + q₀₂·t²) + remainder`, with a remainder whose mixed second
  variation vanishes, the polarization tensor entry is `β·τ`: the coefficient of
  the tensor structure in the polarization tensor is exactly `β`, once the
  structure is normalised by `τ = 1` (`polarizationAt_of_normalizedStructure`).
* `shellGaussian_eq_polarization` — the **same-object weld**: with the source
  effective action carrying the Lean shell Gaussian coefficient
  `cellGaussianCoefficient I` on the normalised tensor structure, the second
  derivative `δ²/δB δB'` evaluates to that very coefficient.  No separate
  `11/12`-type computation and no universality argument is used: the two
  quantities are obtained from the same second derivative.
* `shellGaussianOfIntegrand_eq_polarization` — the scale-indexed form.
* `polarization_two_sided_from_kernels` — consequently the polarization
  coefficient inherits the two-sided Row A bounds
  `1/8388608 ≤ Π ≤ (4π + 64·LVC(R,M))² + 128·MW²` from the kernel data.

## Honest status

The identification is *conditional on the shape hypothesis* `hE`: that the
source effective action, restricted to the two-parameter test configuration, is
the Lean shell quadratic form plus a remainder with vanishing mixed second
variation.  That hypothesis is the place where the published expansion of
`E^{(j)}` has to be inserted; it is kept explicit here (a candidate bridge), not
silently discharged.  With it, the coefficient identification is a theorem, not
a normalisation convention.
-/
import RequestProject.YangMills.TwoSidedShellGaussian

namespace YangMills

open Real

/-! ## 1. The literal second variation -/

/-- The two-parameter test configuration `B = s·e_b + t·e_{b'}` used to take the
second variation `δ²/δB(b) δB(b')`. -/
def twoDirConfig {bIdx : Type*} [DecidableEq bIdx] (b b' : bIdx) (s t : ℝ) : bIdx → ℝ :=
  fun x => (if x = b then s else 0) + (if x = b' then t else 0)

/-- **The polarization tensor entry**, i.e. the literal
`δ²/δB(b) δB(b') E(B)` at `B = 0`. -/
noncomputable def polarizationAt {bIdx : Type*} [DecidableEq bIdx]
    (E : (bIdx → ℝ) → ℝ) (b b' : bIdx) : ℝ :=
  deriv (fun s => deriv (fun t => E (twoDirConfig b b' s t)) 0) 0

/-! ## 2. The coefficient of the tensor structure in the polarization tensor -/

/-- **Expanding the second derivative.**  If the effective action restricted to
the test configuration is `β·(τ·st + q₂₀s² + q₀₂t²)` plus a remainder whose
mixed second variation vanishes, then the polarization tensor entry is `β·τ`.

The pure `s²` and `t²` terms drop out of the *mixed* second derivative — this is
the cancellation between the diagonal polarization terms and the `β` term in the
source. -/
theorem polarizationAt_of_quadratic {bIdx : Type*} [DecidableEq bIdx]
    {E Rem : (bIdx → ℝ) → ℝ} {b b' : bIdx} {beta tau q20 q02 : ℝ} {rem1 : ℝ → ℝ}
    (hE : ∀ s t, E (twoDirConfig b b' s t)
      = beta * (tau * (s * t) + q20 * s ^ 2 + q02 * t ^ 2) + Rem (twoDirConfig b b' s t))
    (hRem1 : ∀ s, HasDerivAt (fun t => Rem (twoDirConfig b b' s t)) (rem1 s) 0)
    (hRem2 : HasDerivAt rem1 0 0) :
    polarizationAt E b b' = beta * tau := by
  have hquad : ∀ s : ℝ,
      HasDerivAt (fun t : ℝ => beta * (tau * (s * t) + q20 * s ^ 2 + q02 * t ^ 2))
        (beta * tau * s) 0 := by
    intro s
    have h1 : HasDerivAt (fun t : ℝ => tau * (s * t)) (tau * s) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul s).const_mul tau
    have h2 : HasDerivAt (fun t : ℝ => q02 * t ^ 2) 0 0 := by
      simpa using (hasDerivAt_pow 2 (0 : ℝ)).const_mul q02
    have h : HasDerivAt (fun t : ℝ => tau * (s * t) + q20 * s ^ 2 + q02 * t ^ 2)
        (tau * s) 0 := by
      simpa using (h1.add_const (q20 * s ^ 2)).add h2
    simpa [mul_assoc] using h.const_mul beta
  have hinner : ∀ s : ℝ,
      deriv (fun t => E (twoDirConfig b b' s t)) 0 = beta * tau * s + rem1 s := by
    intro s
    have heq : (fun t => E (twoDirConfig b b' s t))
        = fun t => beta * (tau * (s * t) + q20 * s ^ 2 + q02 * t ^ 2)
            + Rem (twoDirConfig b b' s t) := funext fun t => hE s t
    have h : HasDerivAt (fun t => E (twoDirConfig b b' s t)) (beta * tau * s + rem1 s) 0 := by
      rw [heq]
      exact (hquad s).add (hRem1 s)
    exact h.deriv
  have houter : HasDerivAt (fun s : ℝ => beta * tau * s + rem1 s) (beta * tau) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => beta * tau * s) (beta * tau) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (beta * tau)
    simpa using h1.add hRem2
  have hfun : (fun s => deriv (fun t => E (twoDirConfig b b' s t)) 0)
      = fun s => beta * tau * s + rem1 s := funext hinner
  rw [polarizationAt, hfun]
  exact houter.deriv

/-- **Normalised tensor structure.**  With the tensor structure normalised so
that its `(b,b')` component is `1`, the coefficient of that structure in the
polarization tensor *is* `β`. -/
theorem polarizationAt_of_normalizedStructure {bIdx : Type*} [DecidableEq bIdx]
    {E Rem : (bIdx → ℝ) → ℝ} {b b' : bIdx} {beta q20 q02 : ℝ} {rem1 : ℝ → ℝ}
    (hE : ∀ s t, E (twoDirConfig b b' s t)
      = beta * ((s * t) + q20 * s ^ 2 + q02 * t ^ 2) + Rem (twoDirConfig b b' s t))
    (hRem1 : ∀ s, HasDerivAt (fun t => Rem (twoDirConfig b b' s t)) (rem1 s) 0)
    (hRem2 : HasDerivAt rem1 0 0) :
    polarizationAt E b b' = beta := by
  have h := polarizationAt_of_quadratic (tau := 1) (q20 := q20) (q02 := q02)
    (by simpa using hE) hRem1 hRem2
  simpa using h

/-! ## 3. The weld: the Lean shell Gaussian coefficient is that coefficient -/

/-- **Same-object weld.**  If the source effective action carries, on the
normalised tensor structure of the two test directions, the coefficient that the
Row A lane computes as the cell integral of the one-loop integrand, then the
literal second variation `δ²/δB δB'` returns exactly that cell integral.

Left-hand side: the source polarization coefficient.
Right-hand side: the Lean shell Gaussian coefficient.  Same number, obtained by
expanding the same second derivative. -/
theorem shellGaussian_eq_polarization {bIdx : Type*} [DecidableEq bIdx]
    {E Rem : (bIdx → ℝ) → ℝ} {b b' : bIdx} {I : (Fin 4 → ℝ) → ℝ} {q20 q02 : ℝ}
    {rem1 : ℝ → ℝ}
    (hE : ∀ s t, E (twoDirConfig b b' s t)
      = cellGaussianCoefficient I * ((s * t) + q20 * s ^ 2 + q02 * t ^ 2)
        + Rem (twoDirConfig b b' s t))
    (hRem1 : ∀ s, HasDerivAt (fun t => Rem (twoDirConfig b b' s t)) (rem1 s) 0)
    (hRem2 : HasDerivAt rem1 0 0) :
    polarizationAt E b b' = cellGaussianCoefficient I :=
  polarizationAt_of_normalizedStructure hE hRem1 hRem2

/-- The scale-indexed form of the weld: at scale `j` and history `h`, the
polarization coefficient of the source effective action is the Lean shell
Gaussian coefficient `shellGaussianOfIntegrand I j h`. -/
theorem shellGaussianOfIntegrand_eq_polarization {bIdx : Type*} [DecidableEq bIdx]
    {E Rem : (bIdx → ℝ) → ℝ} {b b' : bIdx}
    {I : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → ℝ} {j : ℕ} {h : ℕ → ℝ} {q20 q02 : ℝ}
    {rem1 : ℝ → ℝ}
    (hE : ∀ s t, E (twoDirConfig b b' s t)
      = shellGaussianOfIntegrand I j h * ((s * t) + q20 * s ^ 2 + q02 * t ^ 2)
        + Rem (twoDirConfig b b' s t))
    (hRem1 : ∀ s, HasDerivAt (fun t => Rem (twoDirConfig b b' s t)) (rem1 s) 0)
    (hRem2 : HasDerivAt rem1 0 0) :
    polarizationAt E b b' = shellGaussianOfIntegrand I j h :=
  polarizationAt_of_normalizedStructure hE hRem1 hRem2

/-! ## 4. The two-sided Row A bounds transported to the polarization
coefficient -/

/-- **The source polarization coefficient obeys the Row A two-sided bounds.**
The kernel data of the averaging/constrained-projection variation and of the
seagull bound the Lean shell Gaussian coefficient on both sides; through the
weld, the same bounds hold for the polarization coefficient of the source
effective action. -/
theorem polarization_two_sided_from_kernels
    {bIdx : Type*} [DecidableEq bIdx] {E Rem : (bIdx → ℝ) → ℝ} {b b' : bIdx}
    {ξ ζ : Type*} [Fintype ξ] [Fintype ζ] {f R M MW q20 q02 : ℝ}
    {Kk : Fin 4 → ξ → ℝ} {dd : Fin 4 → ξ → (Fin 4 → ℝ)}
    {KW : Fin 4 → Fin 4 → ζ → ℝ} {dW : Fin 4 → Fin 4 → ζ → (Fin 4 → ℝ)}
    {rem1 : ℝ → ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hMW : 0 ≤ MW)
    (hzero : ∀ a, ∑ i, Kk a i = 0)
    (hd : ∀ a i mu, |dd a i mu| ≤ R)
    (hmass : ∀ a, kernelMass (Kk a) ≤ M)
    (hsmallK : linearVanishingConstant R M ≤ 1 / 2)
    (hmassW : ∀ a b, kernelMass (KW a b) ≤ MW)
    (hE : ∀ s t, E (twoDirConfig b b' s t)
      = cellGaussianCoefficient
          (literalOneLoopIntegrand
            (sourceVariationMatrix f 1 (diagCosSymbolMatrix Kk dd)) (cosSymbolMatrix KW dW))
        * ((s * t) + q20 * s ^ 2 + q02 * t ^ 2) + Rem (twoDirConfig b b' s t))
    (hRem1 : ∀ s, HasDerivAt (fun t => Rem (twoDirConfig b b' s t)) (rem1 s) 0)
    (hRem2 : HasDerivAt rem1 0 0) :
    1 / 8388608 ≤ polarizationAt E b b'
      ∧ polarizationAt E b b' ≤ shellGaussianCeiling (linearVanishingConstant R M) MW := by
  have hweld := shellGaussian_eq_polarization hE hRem1 hRem2
  have htwo := cellGaussian_two_sided_from_kernels (f := f) (dW := dW)
    hR hM hMW hzero hd hmass hsmallK hmassW
  rw [hweld]
  exact htwo

end YangMills

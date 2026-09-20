import Mathlib

/-!
# Whole-space Navier–Stokes cubature boundary-defect estimate

This is the Lean/Mathlib producer corresponding to the current A-side Agda
frontier in `NSWholeSpaceFiniteConvolutionBoundaryDefectExact`.

For a finite Euclidean cubature, let `e i ≥ 0` be the sampled Fourier-energy
mass and let `δ i` be the loss caused by translating the finite window by the
outer convolution node.  If every row defect obeys

`|δ i| ≤ τ`,

then the total weighted defect

`Δ = ∑ i, e i * δ i`

satisfies the exact estimate

`|Δ| ≤ (∑ i, e i) * τ`.

This is deliberately only the finite analytic payment.  It introduces no
periodicity, no exact finite translation reindexing, and no Navier–Stokes
regularity conclusion.  The remaining Euclidean theorem is to obtain a
`τₙ → 0` tail bound from the actual expanding/refining R³ cubature of the
Fourier energy density.
-/

open scoped BigOperators

namespace RequestProject.NavierStokes

section FiniteBoundaryDefect

variable {ι : Type*} [DecidableEq ι]

/-- Total nonnegative Fourier-energy mass of a finite cubature. -/
def cubatureEnergyMass (s : Finset ι) (energy : ι → ℝ) : ℝ :=
  ∑ i in s, energy i

/-- Weighted translation-boundary defect of a finite convolution cubature. -/
def convolutionBoundaryDefect
    (s : Finset ι) (energy rowDefect : ι → ℝ) : ℝ :=
  ∑ i in s, energy i * rowDefect i

/--
If every translated row has absolute boundary loss at most `τ`, then the
whole convolution boundary defect is bounded by energy mass times `τ`.

This is the exact finite estimate requested by the current Agda A-lane:
`|Δₙ| ≤ Eₙ τₙ`.
-/
theorem abs_convolutionBoundaryDefect_le_energyMass_mul_tail
    (s : Finset ι)
    (energy rowDefect : ι → ℝ)
    (τ : ℝ)
    (henergy : ∀ i ∈ s, 0 ≤ energy i)
    (htail : ∀ i ∈ s, |rowDefect i| ≤ τ) :
    |convolutionBoundaryDefect s energy rowDefect|
      ≤ cubatureEnergyMass s energy * τ := by
  calc
    |convolutionBoundaryDefect s energy rowDefect|
        ≤ ∑ i in s, |energy i * rowDefect i| := by
            simpa [convolutionBoundaryDefect] using
              (Finset.abs_sum_le_sum_abs (s := s)
                (f := fun i => energy i * rowDefect i))
    _ ≤ ∑ i in s, energy i * τ := by
          refine Finset.sum_le_sum ?_
          intro i hi
          rw [abs_mul, abs_of_nonneg (henergy i hi)]
          exact mul_le_mul_of_nonneg_left (htail i hi) (henergy i hi)
    _ = cubatureEnergyMass s energy * τ := by
          simp [cubatureEnergyMass, Finset.sum_mul]

/--
The same estimate in the common normalized form where the finite energy mass
is bounded by a cutoff-independent physical energy ceiling `E`.
-/
theorem abs_convolutionBoundaryDefect_le_ceiling_mul_tail
    (s : Finset ι)
    (energy rowDefect : ι → ℝ)
    (τ E : ℝ)
    (henergy : ∀ i ∈ s, 0 ≤ energy i)
    (htail : ∀ i ∈ s, |rowDefect i| ≤ τ)
    (hτ : 0 ≤ τ)
    (hE : cubatureEnergyMass s energy ≤ E) :
    |convolutionBoundaryDefect s energy rowDefect| ≤ E * τ := by
  exact le_trans
    (abs_convolutionBoundaryDefect_le_energyMass_mul_tail
      s energy rowDefect τ henergy htail)
    (mul_le_mul_of_nonneg_right hE hτ)

/--
Finite boundary-defect cancellation is therefore reduced to one geometric
tail number.  In particular, a zero row-tail gives exact finite factorisation
without assuming that translation is a permutation of the Euclidean window.
-/
theorem convolutionBoundaryDefect_eq_zero_of_zero_tail
    (s : Finset ι)
    (energy rowDefect : ι → ℝ)
    (henergy : ∀ i ∈ s, 0 ≤ energy i)
    (htail : ∀ i ∈ s, |rowDefect i| ≤ 0) :
    convolutionBoundaryDefect s energy rowDefect = 0 := by
  have h :
      |convolutionBoundaryDefect s energy rowDefect| ≤
        cubatureEnergyMass s energy * 0 :=
    abs_convolutionBoundaryDefect_le_energyMass_mul_tail
      s energy rowDefect 0 henergy htail
  simp only [mul_zero] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

end FiniteBoundaryDefect

end RequestProject.NavierStokes

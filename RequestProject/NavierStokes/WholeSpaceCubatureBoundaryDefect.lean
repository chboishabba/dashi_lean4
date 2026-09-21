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


/--
Correct whole-space core/tail estimate.

Uniform translation control is required only on a fixed/core set of outer
frequencies.  The outer tail is paid by its own small energy mass.  This is the
finite statement appropriate to expanding Euclidean windows, where a uniform
row defect over every outer node is generally too strong.

If
* core row defect ≤ `τcore`,
* arbitrary tail row defect ≤ `M`,
* core energy mass ≤ `E`,
* tail energy mass ≤ `εtail`,

then

`|Δ(core ∪ tail)| ≤ E τcore + εtail M`.
-/
theorem abs_convolutionBoundaryDefect_union_le_core_tail
    (core tail : Finset ι)
    (hdisjoint : Disjoint core tail)
    (energy rowDefect : ι → ℝ)
    (τcore M E εtail : ℝ)
    (henergy_core : ∀ i ∈ core, 0 ≤ energy i)
    (henergy_tail : ∀ i ∈ tail, 0 ≤ energy i)
    (hcore : ∀ i ∈ core, |rowDefect i| ≤ τcore)
    (htail : ∀ i ∈ tail, |rowDefect i| ≤ M)
    (hτcore : 0 ≤ τcore)
    (hM : 0 ≤ M)
    (hE : cubatureEnergyMass core energy ≤ E)
    (hεtail : cubatureEnergyMass tail energy ≤ εtail) :
    |convolutionBoundaryDefect (core ∪ tail) energy rowDefect|
      ≤ E * τcore + εtail * M := by
  have hsplit :
      convolutionBoundaryDefect (core ∪ tail) energy rowDefect =
        convolutionBoundaryDefect core energy rowDefect +
        convolutionBoundaryDefect tail energy rowDefect := by
    simp [convolutionBoundaryDefect, Finset.sum_union hdisjoint]
  rw [hsplit]
  calc
    |convolutionBoundaryDefect core energy rowDefect +
        convolutionBoundaryDefect tail energy rowDefect|
        ≤ |convolutionBoundaryDefect core energy rowDefect| +
          |convolutionBoundaryDefect tail energy rowDefect| := abs_add _ _
    _ ≤ cubatureEnergyMass core energy * τcore +
          cubatureEnergyMass tail energy * M := by
      exact add_le_add
        (abs_convolutionBoundaryDefect_le_energyMass_mul_tail
          core energy rowDefect τcore henergy_core hcore)
        (abs_convolutionBoundaryDefect_le_energyMass_mul_tail
          tail energy rowDefect M henergy_tail htail)
    _ ≤ E * τcore + εtail * M := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hE hτcore)
        (mul_le_mul_of_nonneg_right hεtail hM)

/--
Asymptotic core/tail completion.

A fixed energy ceiling, vanishing core translation error, and vanishing outer
energy tail imply that the full weighted Euclidean boundary defect vanishes.
This is the correct replacement for a globally uniform row-tail assumption.
-/
theorem convolutionBoundaryDefect_union_tendsto_zero
    (core tail : ℕ → Finset ι)
    (energy rowDefect : ℕ → ι → ℝ)
    (τcore εtail : ℕ → ℝ)
    (E M : ℝ)
    (hdisjoint : ∀ n, Disjoint (core n) (tail n))
    (henergy_core : ∀ n i, i ∈ core n → 0 ≤ energy n i)
    (henergy_tail : ∀ n i, i ∈ tail n → 0 ≤ energy n i)
    (hcore : ∀ n i, i ∈ core n → |rowDefect n i| ≤ τcore n)
    (htail : ∀ n i, i ∈ tail n → |rowDefect n i| ≤ M)
    (hτcore_nonneg : ∀ n, 0 ≤ τcore n)
    (hεtail_nonneg : ∀ n, 0 ≤ εtail n)
    (hM : 0 ≤ M)
    (hcore_energy : ∀ n, cubatureEnergyMass (core n) (energy n) ≤ E)
    (htail_energy : ∀ n, cubatureEnergyMass (tail n) (energy n) ≤ εtail n)
    (hτcore_zero : Filter.Tendsto τcore Filter.atTop (nhds 0))
    (hεtail_zero : Filter.Tendsto εtail Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n =>
        convolutionBoundaryDefect
          (core n ∪ tail n) (energy n) (rowDefect n))
      Filter.atTop (nhds 0) := by
  have hbound :
      Filter.Tendsto
        (fun n => E * τcore n + εtail n * M)
        Filter.atTop (nhds 0) := by
    have hleft :
        Filter.Tendsto (fun n => E * τcore n) Filter.atTop (nhds 0) := by
      simpa using (Filter.tendsto_const_nhds.mul hτcore_zero)
    have hright :
        Filter.Tendsto (fun n => εtail n * M) Filter.atTop (nhds 0) := by
      simpa using (hεtail_zero.mul Filter.tendsto_const_nhds)
    simpa using hleft.add hright
  have habs :
      Filter.Tendsto
        (fun n =>
          |convolutionBoundaryDefect
            (core n ∪ tail n) (energy n) (rowDefect n)|)
        Filter.atTop (nhds 0) := by
    exact Filter.Tendsto.squeeze
      (by simpa using (Filter.tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0)))
      hbound
      (fun n => abs_nonneg _)
      (fun n =>
        abs_convolutionBoundaryDefect_union_le_core_tail
          (core n) (tail n) (hdisjoint n)
          (energy n) (rowDefect n)
          (τcore n) M E (εtail n)
          (henergy_core n) (henergy_tail n)
          (hcore n) (htail n)
          (hτcore_nonneg n) hM
          (hcore_energy n) (htail_energy n))
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [Real.norm_eq_abs] using habs

/--
Cutoff-independent energy control plus a vanishing nonnegative row-tail forces
the complete Euclidean translation-boundary defect to vanish.

This is the continuum compiler promised by the finite estimate:
`|Δₙ| ≤ E τₙ`, `τₙ → 0` implies `Δₙ → 0`.
-/
theorem convolutionBoundaryDefect_tendsto_zero
    (s : ℕ → Finset ι)
    (energy rowDefect : ℕ → ι → ℝ)
    (tail : ℕ → ℝ)
    (E : ℝ)
    (hE : 0 ≤ E)
    (henergy : ∀ n i, i ∈ s n → 0 ≤ energy n i)
    (htail_nonneg : ∀ n, 0 ≤ tail n)
    (htail : ∀ n i, i ∈ s n → |rowDefect n i| ≤ tail n)
    (hceiling : ∀ n, cubatureEnergyMass (s n) (energy n) ≤ E)
    (htail_zero : Filter.Tendsto tail Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => convolutionBoundaryDefect (s n) (energy n) (rowDefect n))
      Filter.atTop (nhds 0) := by
  have hprod :
      Filter.Tendsto (fun n => E * tail n) Filter.atTop (nhds 0) := by
    simpa using (Filter.tendsto_const_nhds.mul htail_zero)
  have habs :
      Filter.Tendsto
        (fun n => |convolutionBoundaryDefect (s n) (energy n) (rowDefect n)|)
        Filter.atTop (nhds 0) := by
    exact Filter.Tendsto.squeeze
      (by simpa using (Filter.tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0)))
      hprod
      (fun n => abs_nonneg _)
      (fun n =>
        abs_convolutionBoundaryDefect_le_ceiling_mul_tail
          (s n) (energy n) (rowDefect n) (tail n) E
          (henergy n) (htail n) (htail_nonneg n) (hceiling n))
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [Real.norm_eq_abs] using habs

end FiniteBoundaryDefect

end RequestProject.NavierStokes

/-
# From a vanishing cell integral to pointwise vanishing.

The energy method produces statements of the form `∫_cell q = 0` for a
continuous nonnegative density `q`.  On the torus this is exactly as strong as
`q ≡ 0`, and the present file supplies the (purely constructive-analytic)
bridge:

* `ClayNS.coord_decomp` — every point of `ℝ³` is a point of the closed unit cell
  translated by an integer vector;
* `ClayNS.periodic_zsmul` — a field periodic under the three unit shifts is
  periodic under the whole lattice `ℤ³`;
* `ClayNS.eq_zero_on_cell_of_cellInt_eq_zero` — a continuous nonnegative field
  with vanishing cell integral vanishes on the closed cell (the cell is the
  closure of its interior, and Lebesgue measure is positive on open sets);
* `ClayNS.eq_zero_of_cellInt_eq_zero` — combining the two, such a field vanishes
  at *every* point of space when it is periodic.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.PeriodicIntegral

open scoped BigOperators
open MeasureTheory Set

noncomputable section

namespace ClayNS

/-! ## Reduction of a point to the cell modulo `ℤ³` -/

/-- Every point of `ℝ³` is the sum of a point of the closed unit cell (its
componentwise fractional part) and an integer combination of the unit
vectors. -/
lemma coord_decomp (x : E3) :
    coord (fun i => Int.fract (coord.symm x i)) + ∑ i, ((⌊coord.symm x i⌋ : ℝ)) • ee i = x := by
  set u : Fin 3 → ℝ := coord.symm x with hu
  have h1 : ∀ i : Fin 3, ((⌊u i⌋ : ℝ)) • ee i
      = coord (((⌊u i⌋ : ℝ)) • (Pi.single i (1 : ℝ) : Fin 3 → ℝ)) := by
    intro i; rw [map_smul, coord_single]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h1 i), ← map_sum, ← map_add]
  have h2 : (fun i => Int.fract (u i))
      + ∑ i, ((⌊u i⌋ : ℝ)) • (Pi.single i (1 : ℝ) : Fin 3 → ℝ) = u := by
    funext i
    have h3 : (∑ j, ((⌊u j⌋ : ℝ)) • (Pi.single j (1 : ℝ) : Fin 3 → ℝ)) i = ((⌊u i⌋ : ℝ)) := by
      simp [Finset.sum_apply, Pi.single_apply]
    simp only [Pi.add_apply, h3]
    exact Int.fract_add_floor (u i)
  rw [h2, hu]
  simp

/-- A field invariant under the three unit shifts is invariant under the whole
period lattice `ℤ³`. -/
lemma periodic_zsmul {f : E3 → ℝ} (hper : ∀ (x : E3) (j : Fin 3), f (x + ee j) = f x)
    (j : Fin 3) : ∀ (m : ℤ) (x : E3), f (x + (m : ℝ) • ee j) = f x := by
  intro m
  induction m using Int.induction_on with
  | zero => intro x; simp
  | succ k ih =>
      intro x
      have h1 : ((((k : ℤ) + 1 : ℤ)) : ℝ) • ee j = ((k : ℤ) : ℝ) • ee j + ee j := by
        push_cast; module
      rw [h1, ← add_assoc, hper _ j, ih x]
  | pred k ih =>
      intro x
      have h1 : (x + (((-(k : ℤ) - 1 : ℤ)) : ℝ) • ee j) + ee j
          = x + (((-(k : ℤ) : ℤ)) : ℝ) • ee j := by
        push_cast; module
      calc f (x + (((-(k : ℤ) - 1 : ℤ)) : ℝ) • ee j)
          = f ((x + (((-(k : ℤ) - 1 : ℤ)) : ℝ) • ee j) + ee j) := (hper _ j).symm
        _ = f (x + (((-(k : ℤ) : ℤ)) : ℝ) • ee j) := by rw [h1]
        _ = f x := ih x

/-! ## Vanishing of a nonnegative density with vanishing cell integral -/

/-- The closed unit cell is the closure of its interior. -/
lemma cell_subset_closure_interior : cell ⊆ closure (interior cell) := by
  have h : cell = (univ.pi fun i : Fin 3 => Icc ((0 : Fin 3 → ℝ) i) ((1 : Fin 3 → ℝ) i)) :=
    (pi_univ_Icc _ _).symm
  rw [h, interior_pi_set finite_univ]
  simp only [interior_Icc]
  rw [closure_pi_set]
  refine pi_mono fun i _ => ?_
  have h01 : ((0 : Fin 3 → ℝ) i) ≠ ((1 : Fin 3 → ℝ) i) := by simp
  rw [closure_Ioo h01]

/-- A continuous nonnegative field whose cell integral vanishes is zero at every
point of the closed cell. -/
theorem eq_zero_on_cell_of_cellInt_eq_zero {f : E3 → ℝ} (hf : Continuous f)
    (hnn : ∀ x, 0 ≤ f x) (h : cellInt f = 0) : ∀ c ∈ cell, f (coord c) = 0 := by
  have hg : Continuous (fun c : Fin 3 → ℝ => f (coord c)) := hf.comp coord.continuous
  have hae : (fun c : Fin 3 → ℝ => f (coord c)) =ᵐ[volume.restrict cell] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall fun c => hnn _)
      (integrableOn_cell_of_continuous hf)).mp h
  intro c hc
  exact MeasureTheory.Measure.eqOn_of_ae_eq hae hg.continuousOn continuousOn_const
    cell_subset_closure_interior hc

/-- **A periodic continuous nonnegative field with vanishing cell integral
vanishes identically.** -/
theorem eq_zero_of_cellInt_eq_zero {f : E3 → ℝ} (hf : Continuous f) (hnn : ∀ x, 0 ≤ f x)
    (hper : ∀ (x : E3) (j : Fin 3), f (x + ee j) = f x) (h : cellInt f = 0) (x : E3) :
    f x = 0 := by
  set u : Fin 3 → ℝ := coord.symm x with hu
  set c : Fin 3 → ℝ := fun i => Int.fract (u i) with hc
  have hcell : c ∈ cell := ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩
  have hx : coord c + ∑ i, ((⌊u i⌋ : ℝ)) • ee i = x := coord_decomp x
  have hassoc : coord c + ∑ i, ((⌊u i⌋ : ℝ)) • ee i
      = ((coord c + ((⌊u 0⌋ : ℤ) : ℝ) • ee 0) + ((⌊u 1⌋ : ℤ) : ℝ) • ee 1)
        + ((⌊u 2⌋ : ℤ) : ℝ) • ee 2 := by
    rw [Fin.sum_univ_three]; abel
  have hstep : f x = f (coord c) := by
    rw [← hx, hassoc, periodic_zsmul hper 2 (⌊u 2⌋) _, periodic_zsmul hper 1 (⌊u 1⌋) _,
      periodic_zsmul hper 0 (⌊u 0⌋) _]
  rw [hstep]
  exact eq_zero_on_cell_of_cellInt_eq_zero hf hnn h c hcell

end ClayNS

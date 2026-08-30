/-
# Continuous periodic fields are bounded on time slabs

The Cauchy theory on a finite window needs one soft fact that the development
did not yet have: a continuous spatially `ℤ³`-periodic field is bounded on every
slab `[0,T] × ℝ³`, because it is determined there by its values on the compact
set `[0,T] × [0,1]³`.

* `ClayNS.spacePeriodic_add_zsmul` — invariance under `n·e_j` for every integer
  `n` (periodicity is stated only for `+e_j`);
* `ClayNS.spacePeriodic_add_intCombo` — invariance under an arbitrary lattice
  vector;
* `ClayNS.exists_cell_representative` — every point of space is a lattice
  translate of a point of the closed cell;
* `ClayNS.exists_slab_bound` — the boundedness statement itself;
* `ClayNS.exists_gradient_bound_on_slab` — its application: the velocity
  gradient of a smooth periodic field is bounded on every slab, with no extra
  hypothesis.  This is what makes the energy uniqueness argument work on a
  finite window.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GlobalEnergy

open scoped BigOperators
open MeasureTheory Set

noncomputable section

namespace ClayNS

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## Invariance under the full lattice -/

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- Periodicity under `+e_j` upgrades to invariance under `n·e_j`, `n : ℤ`. -/
lemma spacePeriodic_add_zsmul {f : STime → F} (hf : SpacePeriodic f) (t : ℝ) (x : E3)
    (j : Fin 3) (n : ℤ) : f (t, x + (n : ℝ) • ee j) = f (t, x) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have hstep : f (t, (x + (n : ℝ) • ee j) + ee j) = f (t, x + (n : ℝ) • ee j) :=
        hf (t, x + (n : ℝ) • ee j) j
      calc f (t, x + (((n : ℤ) + 1 : ℤ) : ℝ) • ee j)
          = f (t, (x + (n : ℝ) • ee j) + ee j) := by
            congr 2
            push_cast
            module
        _ = f (t, x + (n : ℝ) • ee j) := hstep
        _ = f (t, x) := ih
  | pred n ih =>
      have hstep : f (t, (x + (-(n : ℝ) - 1) • ee j) + ee j) = f (t, x + (-(n : ℝ) - 1) • ee j) :=
        hf (t, x + (-(n : ℝ) - 1) • ee j) j
      have hleft : (x + (-(n : ℝ) - 1) • ee j) + ee j = x + (-(n : ℝ)) • ee j := by
        module
      rw [hleft] at hstep
      calc f (t, x + ((-(n : ℤ) - 1 : ℤ) : ℝ) • ee j)
          = f (t, x + (-(n : ℝ) - 1) • ee j) := by
            congr 2
            push_cast
            module
        _ = f (t, x + (-(n : ℝ)) • ee j) := hstep.symm
        _ = f (t, x + ((-(n : ℤ) : ℤ) : ℝ) • ee j) := by
            congr 2
            push_cast
            module
        _ = f (t, x) := ih

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- Invariance under an arbitrary lattice vector `∑_j m_j e_j`, `m : Fin 3 → ℤ`. -/
lemma spacePeriodic_add_intCombo {f : STime → F} (hf : SpacePeriodic f) (t : ℝ)
    (m : Fin 3 → ℤ) : ∀ x : E3, f (t, x + ∑ j, ((m j : ℝ)) • ee j) = f (t, x) := by
  have key : ∀ s : Finset (Fin 3), ∀ x : E3,
      f (t, x + ∑ j ∈ s, ((m j : ℝ)) • ee j) = f (t, x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x; simp
    | insert a s ha ih =>
        intro x
        rw [Finset.sum_insert ha]
        have hassoc : x + (((m a : ℝ)) • ee a + ∑ j ∈ s, ((m j : ℝ)) • ee j)
            = (x + ((m a : ℝ)) • ee a) + ∑ j ∈ s, ((m j : ℝ)) • ee j := by
          rw [add_assoc]
        rw [hassoc, ih (x + ((m a : ℝ)) • ee a)]
        exact spacePeriodic_add_zsmul hf t x a (m a)
  exact key Finset.univ

/-! ## Reduction to the cell -/

lemma coord_apply (c : Fin 3 → ℝ) (j : Fin 3) : (coord c) j = c j := rfl

/-- Every point of space is a lattice translate of a point of the closed unit
cell. -/
lemma exists_cell_representative (x : E3) :
    ∃ (y : E3) (m : Fin 3 → ℤ), (∀ j, y j ∈ Icc (0 : ℝ) 1) ∧ x = y + ∑ j, ((m j : ℝ)) • ee j := by
  refine ⟨coord (fun j => Int.fract (x j)), fun j => ⌊x j⌋, ?_, ?_⟩
  · intro j
    exact ⟨(Int.fract_nonneg _), (Int.fract_lt_one _).le⟩
  · have hsum : (∑ j, ((⌊x j⌋ : ℝ)) • ee j) = coord (fun j => ((⌊x j⌋ : ℝ))) := by
      have := basis_expand (coord (fun j => ((⌊x j⌋ : ℝ))))
      rw [← this]
      rfl
    rw [hsum]
    ext j
    have h1 : (coord (fun j => Int.fract (x j)) + coord (fun j => ((⌊x j⌋ : ℝ)))) j
        = Int.fract (x j) + ((⌊x j⌋ : ℝ)) := rfl
    rw [h1, Int.fract]
    ring

/-! ## Boundedness on slabs -/

omit [NormedSpace ℝ F] in
/-- **A continuous periodic field is bounded on every time slab.** -/
theorem exists_slab_bound {f : STime → F} (hf : Continuous f) (hper : SpacePeriodic f)
    (T : ℝ) : ∃ C : ℝ, ∀ z : STime, z.1 ∈ Icc (0 : ℝ) T → ‖f z‖ ≤ C := by
  have hcompact : IsCompact ((Icc (0 : ℝ) T) ×ˢ (coord '' cell)) :=
    (isCompact_Icc).prod (isCompact_cell.image coord.continuous)
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨C, ?_⟩
  rintro ⟨t, x⟩ ht
  obtain ⟨y, m, hy, hxy⟩ := exists_cell_representative x
  have hfy : f (t, x) = f (t, y) := by
    rw [hxy]
    exact spacePeriodic_add_intCombo hper t m y
  have hmem : ((t, y) : STime) ∈ (Icc (0 : ℝ) T) ×ˢ (coord '' cell) := by
    refine ⟨ht, ?_⟩
    exact ⟨coord.symm y, ⟨fun j => (hy j).1, fun j => (hy j).2⟩, by simp⟩
  rw [hfy]
  exact hC _ hmem

/-- **The velocity gradient of a smooth periodic field is bounded on every
slab.**  No extra hypothesis is needed: this is pure compactness of the torus.
-/
theorem exists_gradient_bound_on_slab {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hVper : SpacePeriodic V) (T : ℝ) :
    ∃ M : ℝ, ∀ z : STime, z.1 ∈ Icc (0 : ℝ) T → ∀ j a : Fin 3,
      |dvec (0, ee j) (fun w => V w a) z| ≤ M := by
  classical
  have hVc : ∀ a : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w a) := fun a => contDiff_coord V hV a
  have hVd : ∀ a : Fin 3, Differentiable ℝ (fun w => V w a) := fun a =>
    differentiable_of_contDiffTop (hVc a)
  have hVper' : ∀ a : Fin 3, SpacePeriodic (fun w => V w a) := fun a =>
    spacePeriodic_coord hVper a
  set g : STime → ℝ := fun z => ∑ j, ∑ a, |dvec (0, ee j) (fun w => V w a) z| with hg
  have hgc : Continuous g :=
    continuous_finset_sum _ fun j _ => continuous_finset_sum _ fun a _ =>
      (continuous_dvec _ (hVc a) (0, ee j)).abs
  have hgper : SpacePeriodic g := by
    intro z j
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
    rw [spacePeriodic_dvec (hVd a) (hVper' a) (0, ee i) z j]
  obtain ⟨C, hC⟩ := exists_slab_bound hgc hgper T
  refine ⟨C, ?_⟩
  intro z hz j a
  have hterm : |dvec (0, ee j) (fun w => V w a) z| ≤ g z := by
    rw [hg]
    refine Finset.single_le_sum (f := fun i => ∑ b, |dvec (0, ee i) (fun w => V w b) z|)
      (fun i _ => Finset.sum_nonneg fun b _ => abs_nonneg _) (Finset.mem_univ j) |>.trans' ?_
    exact Finset.single_le_sum (f := fun b => |dvec (0, ee j) (fun w => V w b) z|)
      (fun b _ => abs_nonneg _) (Finset.mem_univ a)
  have hgz : g z ≤ C := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC z hz)
  exact hterm.trans hgz

end ClayNS

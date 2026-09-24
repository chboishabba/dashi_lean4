/-
# The divergence theorem on `ℝ³` for compactly supported `C¹` fluxes

`PeriodicIntegral.lean` proves the divergence theorem on the *torus*: the cell
integral of a divergence vanishes because the faces of `[0,1]³` cancel in pairs
by periodicity.  The scale-probe construction needs the other classical version:
on all of `ℝ³`, for a flux that vanishes outside a bounded set, the faces of a
large box carry nothing at all and

  `∫_{ℝ³} div F = 0`.

* `ClayNS.integral_divergence_eq_zero_of_vanishing_outside` — the statement, for
  a `C¹` family `F : Fin 3 → E3 → ℝ` with `F i x = 0` whenever `L ≤ ‖x‖`.

The proof transports the integral to coordinates (`PiLp.volume_preserving_toLp`),
notes that the divergence itself vanishes off the box `[-L,L]³` (on the *open*
set `‖x‖ > L` the flux is identically zero, hence so is its derivative), and
applies Mathlib's Bochner divergence theorem on that box, whose face integrals
are integrals of the zero function.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.PeriodicIntegral

open scoped BigOperators
open MeasureTheory Set

noncomputable section

namespace ClayNS

/-- A coordinate of a Euclidean vector is dominated by its norm. -/
lemma abs_coord_le_norm (x : E3) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq x,
    show |x i| = Real.sqrt (|x i| ^ 2) by rw [Real.sqrt_sq_eq_abs, abs_abs]]
  refine Real.sqrt_le_sqrt ?_
  refine (Finset.single_le_sum (f := fun j => ‖x.ofLp j‖ ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ i)).trans_eq' ?_
  simp [Real.norm_eq_abs]

/-- Integration over `E3` is integration over the coordinate space. -/
lemma integral_coord (g : E3 → ℝ) : ∫ y : (Fin 3 → ℝ), g (coord y) = ∫ x : E3, g x :=
  (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.measurableEmbedding (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))) g

/-- **Divergence theorem on `ℝ³` for a compactly supported flux.**  If each `F i`
is `C¹` and vanishes outside the ball of radius `L`, the integral of the
divergence `∑ᵢ ∂ᵢFᵢ` over all of `ℝ³` vanishes. -/
theorem integral_divergence_eq_zero_of_vanishing_outside
    (F : Fin 3 → E3 → ℝ) (hF : ∀ i, ContDiff ℝ (1 : ℕ) (F i)) {L : ℝ} (hL : 0 < L)
    (hsupp : ∀ (i : Fin 3) (x : E3), L ≤ ‖x‖ → F i x = 0) :
    ∫ x : E3, ∑ i, fderiv ℝ (F i) x (ee i) = 0 := by
  classical
  have hdiff : ∀ i, Differentiable ℝ (F i) := fun i => (hF i).differentiable (by simp)
  have hcontfd : ∀ i, Continuous (fun x : E3 => fderiv ℝ (F i) x) :=
    fun i => (hF i).continuous_fderiv (by simp)
  -- the flux vanishes on the open set `‖x‖ > L`, hence so does its derivative
  have hfd_zero : ∀ (i : Fin 3) (x : E3), L < ‖x‖ → fderiv ℝ (F i) x = 0 := by
    intro i x hx
    have hnb : {y : E3 | L < ‖y‖} ∈ nhds x :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hx
    have : F i =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
      filter_upwards [hnb] with y hy using hsupp i y (le_of_lt hy)
    rw [this.fderiv_eq]
    simp
  -- the divergence vanishes off the coordinate box `[-L,L]³`
  set a : Fin 3 → ℝ := fun _ => -L with ha
  set b : Fin 3 → ℝ := fun _ => L with hb
  have hle : a ≤ b := fun i => by simp [ha, hb]; linarith
  have houtside : ∀ y : (Fin 3 → ℝ), y ∉ Icc a b →
      (∑ i, fderiv ℝ (F i) (coord y) (ee i)) = 0 := by
    intro y hy
    have hex : ∃ i, L < |y i| := by
      by_contra hcon
      push_neg at hcon
      exact hy ⟨fun i => by have := hcon i; rw [abs_le] at this; simpa [ha] using this.1,
        fun i => by have := hcon i; rw [abs_le] at this; simpa [hb] using this.2⟩
    obtain ⟨i, hi⟩ := hex
    have hnorm : L < ‖coord y‖ := lt_of_lt_of_le hi (by
      have : (coord y) i = y i := rfl
      simpa [this] using abs_coord_le_norm (coord y) i)
    exact Finset.sum_eq_zero fun j _ => by rw [hfd_zero j _ hnorm]; simp
  -- move to coordinates and restrict to the box
  have hEq : (∫ x : E3, ∑ i, fderiv ℝ (F i) x (ee i))
      = ∫ y in Icc a b, ∑ i, fderiv ℝ (F i) (coord y) (ee i) := by
    rw [← integral_coord (fun x => ∑ i, fderiv ℝ (F i) x (ee i))]
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := volume) (s := Icc a b) (fun y hy => houtside y hy)).symm
  -- Mathlib's divergence theorem on the box
  set f : Fin 3 → (Fin 3 → ℝ) → ℝ := fun i x => F i (coord x) with hf
  set f' : Fin 3 → (Fin 3 → ℝ) → ((Fin 3 → ℝ) →L[ℝ] ℝ) :=
    fun i x => (fderiv ℝ (F i) (coord x)).comp (coord : (Fin 3 → ℝ) →L[ℝ] E3) with hf'
  have hHc : ∀ i, ContinuousOn (f i) (Icc a b) := fun i =>
    (((hF i).continuous).comp coord.continuous).continuousOn
  have hHd : ∀ x ∈ (Set.univ.pi fun i => Ioo (a i) (b i)) \ (∅ : Set (Fin 3 → ℝ)),
      ∀ i, HasFDerivAt (f i) (f' i x) x := fun x _ i =>
    ((hdiff i) (coord x)).hasFDerivAt.comp x (coord : (Fin 3 → ℝ) →L[ℝ] E3).hasFDerivAt
  have hHi : IntegrableOn (fun x => ∑ i, f' i x (Pi.single i 1)) (Icc a b) volume := by
    apply Continuous.continuousOn _ |>.integrableOn_compact isCompact_Icc
    refine continuous_finset_sum _ fun i _ => ?_
    exact ((hcontfd i).comp coord.continuous).clm_apply continuous_const
  have key := MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'
      a b hle f f' ∅ Set.countable_empty hHc hHd hHi
  have hfaces : ∀ i : Fin 3,
      ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), f i (i.insertNth (b i) y)) -
        ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), f i (i.insertNth (a i) y)) = 0 := by
    intro i
    have hzero : ∀ (c : ℝ) (y : Fin 2 → ℝ), L ≤ |c| → f i (i.insertNth c y) = 0 := by
      intro c y hc
      have hcoord : (coord (i.insertNth c y)) i = c := by
        simp [coord]
      refine hsupp i _ (le_trans hc ?_)
      simpa [hcoord] using abs_coord_le_norm (coord (i.insertNth c y)) i
    have h1 : ∀ y : Fin 2 → ℝ, f i (i.insertNth (b i) y) = 0 := fun y =>
      hzero _ y (by simp [hb, abs_of_pos hL])
    have h2 : ∀ y : Fin 2 → ℝ, f i (i.insertNth (a i) y) = 0 := fun y =>
      hzero _ y (by simp [ha, abs_of_pos hL])
    simp [h1, h2]
  rw [hEq, show (∫ y in Icc a b, ∑ i, fderiv ℝ (F i) (coord y) (ee i))
      = ∫ x in Icc a b, ∑ i, f' i x (Pi.single i 1) from rfl, key]
  exact Finset.sum_eq_zero fun i _ => hfaces i

end ClayNS

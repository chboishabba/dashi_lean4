/-
# The truncated Galerkin field is globally Lipschitz, and its flow exists

The literal Galerkin vector field of `GalerkinStateSpace.lean` is quadratic, so
it is only *locally* Lipschitz and Picard–Lindelöf alone gives no control on the
lifespan.  Here we cut it off smoothly outside a sublevel set of the energy.
The cut-off field

  `tvfield ν R = cut R · vfield ν`

is smooth with compact support, hence globally bounded and globally Lipschitz,
and therefore admits an integral curve through any state, on any prescribed
time window (`exists_solution_tvfield`).  The cutoff is removed in
`GalerkinExistence.lean` by an a-priori energy bound.
-/
import RequestProject.NavierStokes.GalerkinStateSpace
import Mathlib.Analysis.ODE.PicardLindelof

noncomputable section

open Set Metric

namespace ClayNS.GalerkinODE

open ClayNS.Waleffe

variable {modes : Finset Wave}

/-! ## Sublevel sets of the energy are compact -/

theorem norm_coord_sq_le_en (v : State modes) (k : ↥modes) (i : Fin 3) :
    ‖v k i‖ ^ 2 ≤ en modes v := by
  have h1 : ‖v k i‖ ^ 2 ≤ nsq (v k) := by
    have hle : Complex.normSq (v k i) ≤ ∑ j, Complex.normSq (v k j) :=
      Finset.single_le_sum (f := fun j => Complex.normSq (v k j))
        (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    simpa [nsq, Complex.sq_norm] using hle
  have h2 : nsq (v k) ≤ en modes v :=
    Finset.single_le_sum (f := fun m : ↥modes => nsq (v m))
      (fun m _ => nsq_nonneg (v m)) (Finset.mem_univ k)
  linarith

theorem norm_le_of_en_le {v : State modes} {c : ℝ} (h : en modes v ≤ c) :
    ‖v‖ ≤ Real.sqrt c := by
  refine pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg c) |>.2 fun k => ?_
  refine pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg c) |>.2 fun i => ?_
  have h1 : ‖v k i‖ ^ 2 ≤ c := le_trans (norm_coord_sq_le_en v k i) h
  have := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (norm_nonneg _)] at this

theorem isCompact_en_le (modes : Finset Wave) (c : ℝ) :
    IsCompact {v : State modes | en modes v ≤ c} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact isClosed_le (contDiff_en modes).continuous continuous_const
  · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨Real.sqrt c, fun v hv => ?_⟩
    simpa [mem_closedBall, dist_eq_norm] using norm_le_of_en_le (v := v) hv

/-! ## The cut-off field is compactly supported, bounded and Lipschitz -/

theorem hasCompactSupport_tvfield (modes : Finset Wave) (nu R : ℝ) :
    HasCompactSupport (tvfield modes nu R) := by
  have hsub : Function.support (tvfield modes nu R) ⊆ {v : State modes | en modes v ≤ R + 1} := by
    intro v hv
    by_contra hnot
    exact hv (tvfield_eq_zero (le_of_lt (lt_of_not_ge (by simpa using hnot))))
  refine IsCompact.of_isClosed_subset (isCompact_en_le modes (R + 1)) isClosed_closure ?_
  exact closure_minimal hsub (isClosed_le (contDiff_en modes).continuous continuous_const)

theorem exists_bound_tvfield (modes : Finset Wave) (nu R : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ v : State modes, ‖tvfield modes nu R v‖ ≤ L := by
  obtain ⟨L, hL⟩ := (hasCompactSupport_tvfield modes nu R).exists_bound_of_continuous
    (contDiff_tvfield modes nu R).continuous
  exact ⟨max L 0, le_max_right _ _, fun v => le_trans (hL v) (le_max_left _ _)⟩

theorem exists_lipschitzWith_tvfield (modes : Finset Wave) (nu R : ℝ) :
    ∃ K : NNReal, LipschitzWith K (tvfield modes nu R) := by
  refine ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ) (n := (⊤ : ℕ∞))
    (hasCompactSupport_tvfield modes nu R) ?_ (by simp)
  exact contDiff_tvfield modes nu R

/-! ## Existence of the truncated flow on an arbitrary window -/

/-- **The cut-off Galerkin flow exists on every time window.**  The truncated
field is globally bounded and globally Lipschitz, so Picard–Lindelöf applies on
any interval, with no smallness restriction on its length. -/
theorem exists_solution_tvfield (modes : Finset Wave) (nu R : ℝ) (v₀ : State modes)
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) :
    ∃ α : ℝ → State modes, α t₀ = v₀ ∧
      ∀ t ∈ Ioo a b, HasDerivAt α (tvfield modes nu R (α t)) t := by
  obtain ⟨L, hL0, hL⟩ := exists_bound_tvfield modes nu R
  obtain ⟨K, hK⟩ := exists_lipschitzWith_tvfield modes nu R
  set A : ℝ := L * max (b - t₀) (t₀ - a) with hA
  have hA0 : 0 ≤ A := by
    have : 0 ≤ max (b - t₀) (t₀ - a) := le_trans (by linarith [ht₀.1, ht₀.2]) (le_max_left _ _)
    exact mul_nonneg hL0 this
  have hpl : IsPicardLindelof (fun _ : ℝ => tvfield modes nu R) (tmin := a) (tmax := b)
      ⟨t₀, ht₀⟩ v₀ ⟨A, hA0⟩ 0 ⟨L, hL0⟩ K := by
    refine IsPicardLindelof.of_time_independent (fun x _ => hL x) hK.lipschitzOnWith ?_
    simp [hA]
  obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨α, hα0, fun t ht => ?_⟩
  exact (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end ClayNS.GalerkinODE

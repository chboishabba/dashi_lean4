import Mathlib
import Integration.Experiment.ParameterRegion

/-!
# Stage 4, lane 3 — continuous-time experiment dynamics

Stage 3's `Integration.Experiment.Protocol` had discrete-time maps over `ℚ`
only; frontier item 7 recorded the absence of differential dynamics.  This file
adds them, as its own lane, over `ℝ`:

```
ẋ = f(t, x, u(t)),      x(0) = x₀,      y = h(x)
```

with a protocol `u : [0,T] → U` and prediction consumers that a static
calculator cannot express.

## The objects

* `ContinuousSystem` — horizon, initial state, control and vector field; `field`
  folds the control in, giving `t ↦ x ↦ ẋ`.
* `IsTrajectory S x` — `x` starts at `x₀`, is continuous on `[0,T]` and solves
  the equation on `[0,T)` (a one-sided derivative, matching Mathlib's Grönwall
  API).
* Consumers: `endpoint`, `peak` (maximum over the run), `integrated`
  (`∫₀ᵀ x`), and `crossingTime` (first time a threshold is reached).

## What is proved

* `trajectory_unique` — **the prediction is well defined**: under a Lipschitz
  vector field, two trajectories of the same system coincide on `[0,T]`.  Every
  envelope statement downstream needs this, since a model that does not
  determine its own trajectory has no prediction to compare with data;
* `trajectory_exists` and `trajectory_exists_unique` — Picard–Lindelöf in the
  shape this file uses: a Lipschitz, time-continuous, bounded field has exactly
  one trajectory on the window, so the prediction is total and not merely
  well defined;
* `affine_isTrajectory` and `affineSolution_unique` — the constant-rate
  solution `x(t) = x₀ + k t`, the continuous-time analogue of the discrete
  coulomb count, together with its uniqueness;
* `peak_mem_image`, `endpoint_le_peak`, `integrated_affine`,
  `crossingTime_mem`, `crossingTime_is_first`, `crossing_exists` — the four
  consumers are total on the objects for which they are declared, and the
  threshold time really is the *first* crossing;
* `parameterisedFamily` and `parameterised_predictions_are_well_defined` — the
  bridge to lane 1: a θ-indexed system family whose solutions are trajectories
  induces a `ParamFamily`, and its predictions are the unique solutions, so the
  surviving-region machinery of `Integration.Experiment.ParameterRegion` applies
  to dynamical models unchanged.

**Claim boundary.** No discretisation-error bound, no existence theorem (a
trajectory is supplied, not constructed — Picard–Lindelöf is not invoked), and
no physical claim: `ContinuousSystem` is a record of real-valued functions.
-/

namespace Integration.Experiment.ContinuousDynamics

open Set

/-! ## §1 Systems and trajectories -/

/-- **A continuous-time experiment**: a horizon, an initial state, a control
protocol and a vector field `f(t, x, u)`. -/
structure ContinuousSystem (Control : Type*) where
  /-- The length of the run. -/
  horizon : ℝ
  /-- The horizon is nonnegative. -/
  horizon_nonneg : 0 ≤ horizon
  /-- The state at time `0`. -/
  init : ℝ
  /-- The protocol: the control applied at each time. -/
  control : ℝ → Control
  /-- The vector field `f(t, x, u)`. -/
  vf : ℝ → ℝ → Control → ℝ

namespace ContinuousSystem

variable {Control : Type*}

/-- The closed-loop field with the protocol substituted: `t ↦ x ↦ ẋ`. -/
def field (S : ContinuousSystem Control) (t x : ℝ) : ℝ := S.vf t x (S.control t)

/-- The run window. -/
def window (S : ContinuousSystem Control) : Set ℝ := Icc 0 S.horizon

/-- **A trajectory of the system**: right value at time zero, continuous on the
window, and solving the differential equation on it. -/
structure IsTrajectory (S : ContinuousSystem Control) (x : ℝ → ℝ) : Prop where
  /-- The initial condition. -/
  init : x 0 = S.init
  /-- Continuity on the window. -/
  cont : ContinuousOn x S.window
  /-- The differential equation, as a one-sided derivative. -/
  deriv : ∀ t ∈ Ico 0 S.horizon, HasDerivWithinAt x (S.field t (x t)) (Ici t) t

end ContinuousSystem

open ContinuousSystem

variable {Control : Type*}

/-- **The prediction of a continuous-time model is well defined.**  If the
closed-loop field is Lipschitz in the state, uniformly over the window, then two
trajectories of the same system agree throughout the run. -/
theorem trajectory_unique {S : ContinuousSystem Control} {K : NNReal}
    (hlip : ∀ t ∈ Ico 0 S.horizon, LipschitzWith K (S.field t))
    {x y : ℝ → ℝ} (hx : S.IsTrajectory x) (hy : S.IsTrajectory y) :
    EqOn x y S.window :=
  ODE_solution_unique_of_mem_Icc_right (K := K) (s := fun _ => univ)
    (fun t ht => (hlip t ht).lipschitzOnWith) hx.cont hx.deriv (fun _ _ => mem_univ _)
    hy.cont hy.deriv (fun _ _ => mem_univ _) (by rw [hx.init, hy.init])

/-- **A trajectory exists.**  Picard–Lindelöf, transported to the shape this
file uses: if the closed-loop field is Lipschitz in the state and continuous in
time on the window, and is bounded there, then the system *has* a trajectory.
With `trajectory_unique` this makes the prediction of a continuous-time model
total as well as well defined, rather than a hypothesis discharged only by an
explicit formula.

The three hypotheses are declared properties of the field, not of any solution;
the bound `‖f t x‖ ≤ L` is global in the state, which is what the constant-rate
and relaxation instances of this corpus satisfy. -/
theorem trajectory_exists {S : ContinuousSystem Control} {K L : NNReal}
    (hlip : ∀ t ∈ Icc 0 S.horizon, LipschitzWith K (S.field t))
    (hcont : ∀ x : ℝ, ContinuousOn (fun t => S.field t x) (Icc 0 S.horizon))
    (hbdd : ∀ t ∈ Icc 0 S.horizon, ∀ x : ℝ, ‖S.field t x‖ ≤ (L : ℝ)) :
    ∃ x : ℝ → ℝ, S.IsTrajectory x := by
  set T : ℝ := S.horizon with hT
  set t₀ : ↑(Icc (0:ℝ) T) := ⟨0, ⟨le_refl 0, S.horizon_nonneg⟩⟩ with ht₀
  set a : NNReal := L * ⟨T, S.horizon_nonneg⟩ with ha
  have hPL : IsPicardLindelof S.field t₀ S.init a 0 L K := by
    refine ⟨fun t ht => (hlip t ht).lipschitzOnWith, fun x _ => hcont x,
      fun t ht x _ => hbdd t ht x, ?_⟩
    have h0 : ((t₀ : ℝ)) = 0 := rfl
    simp only [ha, h0, NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_zero, sub_zero]
    rw [max_eq_left S.horizon_nonneg]
  obtain ⟨α, hα0, hαd⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt (x := S.init) (by simp)
  refine ⟨α, ⟨hα0, fun t ht => (hαd t ht).continuousWithinAt, fun t ht => ?_⟩⟩
  refine (hαd t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin ?_
  have hio : Iio T ∈ nhds t := Iio_mem_nhds ht.2
  exact Filter.mem_of_superset (inter_mem_nhdsWithin (Ici t) hio)
    (fun y hy => ⟨le_trans ht.1 hy.1, hy.2.le⟩)

/-- **Existence and uniqueness together**: under the hypotheses above the system
has exactly one trajectory on its window, up to agreement there. -/
theorem trajectory_exists_unique {S : ContinuousSystem Control} {K L : NNReal}
    (hlip : ∀ t ∈ Icc 0 S.horizon, LipschitzWith K (S.field t))
    (hcont : ∀ x : ℝ, ContinuousOn (fun t => S.field t x) (Icc 0 S.horizon))
    (hbdd : ∀ t ∈ Icc 0 S.horizon, ∀ x : ℝ, ‖S.field t x‖ ≤ (L : ℝ)) :
    ∃ x : ℝ → ℝ, S.IsTrajectory x ∧ ∀ y, S.IsTrajectory y → EqOn y x S.window := by
  obtain ⟨x, hx⟩ := trajectory_exists hlip hcont hbdd
  exact ⟨x, hx, fun y hy =>
    trajectory_unique (K := K) (fun t ht => hlip t ⟨ht.1, ht.2.le⟩) hy hx⟩

/-! ## §2 The constant-rate system -/

/-- The system with a constant rate `k`: `ẋ = k`, the continuous-time form of a
coulomb count. -/
def constantRate (T : ℝ) (hT : 0 ≤ T) (x₀ k : ℝ) : ContinuousSystem Unit where
  horizon := T
  horizon_nonneg := hT
  init := x₀
  control := fun _ => ()
  vf := fun _ _ _ => k

@[simp] theorem constantRate_field (T : ℝ) (hT : 0 ≤ T) (x₀ k t x : ℝ) :
    (constantRate T hT x₀ k).field t x = k := rfl

/-- Its solution. -/
def affineSolution (x₀ k : ℝ) : ℝ → ℝ := fun t => x₀ + k * t

/-- **The affine map is a trajectory of the constant-rate system.** -/
theorem affine_isTrajectory (T : ℝ) (hT : 0 ≤ T) (x₀ k : ℝ) :
    (constantRate T hT x₀ k).IsTrajectory (affineSolution x₀ k) where
  init := by simp [affineSolution, constantRate]
  cont := by
    apply Continuous.continuousOn
    unfold affineSolution
    fun_prop
  deriv := by
    intro t _
    have h : HasDerivAt (fun s : ℝ => x₀ + k * s) k t := by
      simpa using ((hasDerivAt_id t).const_mul k).const_add x₀
    exact h.hasDerivWithinAt

/-- **And it is the only one**: the constant field is Lipschitz, so
`trajectory_unique` applies. -/
theorem affineSolution_unique (T : ℝ) (hT : 0 ≤ T) (x₀ k : ℝ) {x : ℝ → ℝ}
    (hx : (constantRate T hT x₀ k).IsTrajectory x) :
    EqOn x (affineSolution x₀ k) (Icc 0 T) :=
  trajectory_unique (K := 0) (fun t _ => by
    have hfield : (constantRate T hT x₀ k).field t = fun _ : ℝ => k := rfl
    rw [hfield]
    exact LipschitzWith.const k) hx (affine_isTrajectory T hT x₀ k)

/-- **The existence hypotheses are satisfiable.**  The constant-rate system
meets the Lipschitz, continuity and boundedness conditions of
`trajectory_exists`, so that theorem is not vacuous: it produces a trajectory
here, which `affineSolution_unique` identifies with the affine solution. -/
theorem constantRate_trajectory_exists (T : ℝ) (hT : 0 ≤ T) (x₀ k : ℝ) :
    ∃ x : ℝ → ℝ, (constantRate T hT x₀ k).IsTrajectory x ∧ EqOn x (affineSolution x₀ k) (Icc 0 T) := by
  obtain ⟨x, hx⟩ := trajectory_exists (S := constantRate T hT x₀ k) (K := 0)
    (L := ⟨|k|, abs_nonneg k⟩)
    (fun t _ => by
      have hfield : (constantRate T hT x₀ k).field t = fun _ : ℝ => k := rfl
      rw [hfield]; exact LipschitzWith.const k)
    (fun x => continuousOn_const)
    (fun t _ x => by simp [Real.norm_eq_abs])
  exact ⟨x, hx, affineSolution_unique T hT x₀ k hx⟩

/-! ## §3 Prediction consumers of a trajectory -/

/-- **Endpoint consumer**: the state at the end of the run. -/
def endpoint (x : ℝ → ℝ) (T : ℝ) : ℝ := x T

/-- **Peak consumer**: the largest value reached during the run (e.g. a maximum
temperature). -/
noncomputable def peak (x : ℝ → ℝ) (T : ℝ) : ℝ := sSup (x '' Icc 0 T)

/-- **Integrated consumer**: e.g. total charge delivered. -/
noncomputable def integrated (x : ℝ → ℝ) (T : ℝ) : ℝ := ∫ t in (0:ℝ)..T, x t

/-- **Threshold-crossing consumer**: the first time in the run at which the
state reaches `c`. -/
noncomputable def crossingTime (x : ℝ → ℝ) (T c : ℝ) : ℝ :=
  sInf (Icc 0 T ∩ x ⁻¹' Ici c)

/-- The peak is attained: it is a value the trajectory actually takes. -/
theorem peak_mem_image {x : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hc : ContinuousOn x (Icc 0 T)) :
    peak x T ∈ x '' Icc 0 T := by
  have hcomp : IsCompact (x '' Icc 0 T) := isCompact_Icc.image_of_continuousOn hc
  have hne : (x '' Icc 0 T).Nonempty := ⟨x 0, ⟨0, ⟨le_refl 0, hT⟩, rfl⟩⟩
  exact hcomp.sSup_mem hne

/-- The endpoint never exceeds the peak. -/
theorem endpoint_le_peak {x : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hc : ContinuousOn x (Icc 0 T)) :
    endpoint x T ≤ peak x T := by
  have hcomp : IsCompact (x '' Icc 0 T) := isCompact_Icc.image_of_continuousOn hc
  exact le_csSup hcomp.bddAbove ⟨T, ⟨hT, le_refl T⟩, rfl⟩

/-- The integrated consumer of the constant-rate solution, in closed form. -/
theorem integrated_affine (x₀ k T : ℝ) :
    integrated (affineSolution x₀ k) T = x₀ * T + k * T ^ 2 / 2 := by
  unfold integrated affineSolution
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((intervalIntegral.intervalIntegrable_id).const_mul k)]
  rw [intervalIntegral.integral_const_mul, integral_id]
  simp
  ring

/-- **A threshold reached at the end is reached at some interior time**, by the
intermediate value theorem. -/
theorem crossing_exists {x : ℝ → ℝ} {T c : ℝ} (hT : 0 ≤ T) (hc : ContinuousOn x (Icc 0 T))
    (hlo : x 0 ≤ c) (hhi : c ≤ x T) : ∃ t ∈ Icc 0 T, x t = c :=
  intermediate_value_Icc hT hc ⟨hlo, hhi⟩

/-- **The crossing time is itself a crossing**: the infimum is attained. -/
theorem crossingTime_mem {x : ℝ → ℝ} {T c : ℝ} (hT : 0 ≤ T) (hc : ContinuousOn x (Icc 0 T))
    (hhi : c ≤ x T) : crossingTime x T c ∈ Icc 0 T ∩ x ⁻¹' Ici c := by
  apply IsClosed.csInf_mem (hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici)
  · exact ⟨T, ⟨hT, le_refl T⟩, hhi⟩
  · exact BddBelow.mono Set.inter_subset_left bddBelow_Icc

/-- **And it is the first one**: no earlier time in the run reaches the
threshold. -/
theorem crossingTime_is_first {x : ℝ → ℝ} {T c : ℝ} {t : ℝ} (ht : t ∈ Icc 0 T)
    (hreach : c ≤ x t) : crossingTime x T c ≤ t :=
  csInf_le (BddBelow.mono Set.inter_subset_left bddBelow_Icc) ⟨ht, hreach⟩

/-! ## §4 The bridge to continuous parameter regions -/

open Integration.Experiment.ParameterRegion

/-- A θ-indexed family of dynamical models, presented by its solutions and the
observation map, as a `ParamFamily`: this is what makes the lane-1 surviving
region, prediction envelope, risk envelope, discrimination and falsification
theorems apply to *dynamical* experiments. -/
def parameterisedFamily {Θ : Type*} (prior : Set Θ) (sol : Θ → ℝ → ℝ) (observe : ℝ → ℝ) :
    ParamFamily Θ where
  prior := prior
  predict := fun θ t => observe (sol θ t)

@[simp] theorem parameterisedFamily_predict {Θ : Type*} (prior : Set Θ) (sol : Θ → ℝ → ℝ)
    (observe : ℝ → ℝ) (θ : Θ) (t : ℝ) :
    (parameterisedFamily prior sol observe).predict θ t = observe (sol θ t) := rfl

/-- **The predictions of a parameterised dynamical family are the model's own
trajectories.**  If each declared solution is a trajectory of the corresponding
system and each closed-loop field is Lipschitz, then any other trajectory of the
same system produces the same predicted series on the run window: the family's
`predict` is a property of the dynamics, not a further declaration. -/
theorem parameterised_predictions_are_well_defined {Θ : Type*} (prior : Set Θ)
    (S : Θ → ContinuousSystem Control) (sol : Θ → ℝ → ℝ) (observe : ℝ → ℝ)
    (K : Θ → NNReal)
    (hlip : ∀ θ, ∀ t ∈ Ico 0 (S θ).horizon, LipschitzWith (K θ) ((S θ).field t))
    (hsol : ∀ θ, (S θ).IsTrajectory (sol θ))
    {θ : Θ} {x : ℝ → ℝ} (hx : (S θ).IsTrajectory x) :
    ∀ t ∈ (S θ).window, observe (x t) = (parameterisedFamily prior sol observe).predict θ t :=
  fun t ht => by
    rw [parameterisedFamily_predict, trajectory_unique (hlip θ) hx (hsol θ) ht]

end Integration.Experiment.ContinuousDynamics

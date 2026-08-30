import Mathlib
import Integration.Experiment.ContinuousDynamics
import Integration.Experiment.BestReading

/-!
# Stage 6, lane 5 — trajectory sensitivities

Stage 4 gave continuous dynamics (`Integration.Experiment.ContinuousDynamics`)
and certified static sensitivities (`Integration.Experiment.JacobianSensitivity`)
but nothing joining them: for a dynamical model the sensitivity of a prediction
to a parameter is itself the solution of a differential equation,

```
ẋ = f(t, x, θ),      s = ∂x/∂θ,      ṡ = f_x(t,x,θ) s + f_θ(t,x,θ),   s(0) = 0.
```

This file adds that variational equation as a first-class object, over a scalar
state and a scalar parameter.

## The trust boundary, kept where Stage 5 put it

A `ParamSystem` carries the partial derivatives `fx`, `fθ` **together with the
proofs that they are those partial derivatives** (`fx_cert`, `fθ_cert`), exactly
as `CertifiedLaw` does for a static edge.  A declared row that is not a
derivative cannot be used here.

## What is proved

* `sensitivity_unique` — the variational equation has at most one solution, so
  *the* trajectory sensitivity is well defined (the dynamical analogue of
  `trajectory_unique`; without it "the sensitivity" would name nothing);
* `sensitivity_bound` — a Grönwall bound: with `|f_x| ≤ K` and `|f_θ| ≤ B` the
  sensitivity obeys `|s(t)| ≤ gronwallBound 0 K B t`, i.e. `(B/K)(e^{Kt} − 1)`.
  This is a *certified* modulus for a dynamical measurement, computed from the
  field rather than declared;
* `constantRate_isParamTrajectory`, `constantRate_isSensitivity`,
  `constantRate_sensitivity_is_the_theta_derivative` — the worked instance
  `ẋ = −θ`, `x(0) = x₀`: the trajectory is `x₀ − θt`, the variational solution is
  `s(t) = −t`, and `s(t)` **is** `∂x/∂θ`, so in this instance the interchange of
  `d/dt` and `∂/∂θ` is verified rather than assumed;
* `locally_identifiable_of_nonzero_sensitivity` — the payoff: a nonzero
  trajectory sensitivity at a measurement time makes the parameter locally
  identifiable from that single reading;
* `zero_sensitivity_time_is_first_order_blind` — and a zero sensitivity makes the
  reading first-order useless, which is what an experiment designer needs to
  avoid;
* `most_sensitive_reading_is_maximal` — feeding the computed sensitivity to the
  existing measurement selector ranks candidate readings by *computed* dynamical
  response rather than by a declared modulus.

## The honest residual

`IsSensitivity` is a hypothesis about `s`, not a theorem about `∂x/∂θ`: nothing
here derives the variational equation from smooth dependence of the flow on the
parameter, because that derivation needs an interchange of `d/dt` and `∂/∂θ`
which is not available for an arbitrary field in this development.  The
instance above verifies the interchange in one case; the general statement
remains an obligation, and is recorded as such in `TOE_STAGE6_INFERENCE.md`.
-/

namespace Integration.Experiment.TrajectorySensitivity

open Set
open scoped NNReal ENNReal
open Integration.Experiment.ParameterRegion

/-! ## §1 A parameterised system with certified partials -/

/-- **A scalar dynamical model with a scalar parameter**, whose partial
derivatives are supplied with their certificates. -/
structure ParamSystem where
  /-- Length of the run. -/
  horizon : ℝ
  /-- The run has nonnegative length. -/
  hT : 0 ≤ horizon
  /-- The initial state, taken not to depend on the parameter. -/
  init : ℝ
  /-- The vector field `f t x θ`. -/
  f : ℝ → ℝ → ℝ → ℝ
  /-- The declared `∂f/∂x`. -/
  fx : ℝ → ℝ → ℝ → ℝ
  /-- The declared `∂f/∂θ`. -/
  fθ : ℝ → ℝ → ℝ → ℝ
  /-- The obligation, discharged: `fx` is `∂f/∂x`. -/
  fx_cert : ∀ t x θ, HasDerivAt (fun y => f t y θ) (fx t x θ) x
  /-- The obligation, discharged: `fθ` is `∂f/∂θ`. -/
  fθ_cert : ∀ t x θ, HasDerivAt (fun p => f t x p) (fθ t x θ) θ

namespace ParamSystem

variable (S : ParamSystem)

/-- The time window of a run. -/
def window : Set ℝ := Icc 0 S.horizon

/-- `x` is the trajectory of the system at parameter `θ`. -/
structure IsParamTrajectory (θ : ℝ) (x : ℝ → ℝ) : Prop where
  /-- The initial condition. -/
  init : x 0 = S.init
  /-- Continuity on the window. -/
  cont : ContinuousOn x S.window
  /-- The differential equation, as a one-sided derivative. -/
  deriv : ∀ t ∈ Ico 0 S.horizon, HasDerivWithinAt x (S.f t (x t) θ) (Ici t) t

/-- `s` is the trajectory sensitivity along `x`: the solution of the variational
equation `ṡ = f_x s + f_θ` with `s(0) = 0`. -/
structure IsSensitivity (θ : ℝ) (x s : ℝ → ℝ) : Prop where
  /-- The initial state does not depend on the parameter. -/
  init : s 0 = 0
  /-- Continuity on the window. -/
  cont : ContinuousOn s S.window
  /-- The variational equation. -/
  deriv : ∀ t ∈ Ico 0 S.horizon,
    HasDerivWithinAt s (S.fx t (x t) θ * s t + S.fθ t (x t) θ) (Ici t) t

end ParamSystem

open ParamSystem

/-! ## §2 The sensitivity is well defined -/

/-- **Uniqueness of the trajectory sensitivity.**  If `f_x` is bounded along the
trajectory then the variational equation has at most one solution, so "the
sensitivity of this prediction to this parameter" names a single function. -/
theorem sensitivity_unique {S : ParamSystem} {θ : ℝ} {x s₁ s₂ : ℝ → ℝ} {K : NNReal}
    (hK : ∀ t ∈ Ico 0 S.horizon, |S.fx t (x t) θ| ≤ K)
    (h₁ : S.IsSensitivity θ x s₁) (h₂ : S.IsSensitivity θ x s₂) :
    EqOn s₁ s₂ S.window := by
  refine ODE_solution_unique_of_mem_Icc_right (K := K)
    (v := fun t y => S.fx t (x t) θ * y + S.fθ t (x t) θ) (s := fun _ => univ)
    (fun t ht => ?_) h₁.cont h₁.deriv (fun _ _ => mem_univ _)
    h₂.cont h₂.deriv (fun _ _ => mem_univ _) (by rw [h₁.init, h₂.init])
  refine LipschitzWith.lipschitzOnWith ?_
  intro u v
  simp only [edist_dist, Real.dist_eq]
  have habs : |S.fx t (x t) θ * u + S.fθ t (x t) θ - (S.fx t (x t) θ * v + S.fθ t (x t) θ)|
      ≤ (K : ℝ) * |u - v| := by
    have : S.fx t (x t) θ * u + S.fθ t (x t) θ - (S.fx t (x t) θ * v + S.fθ t (x t) θ)
        = S.fx t (x t) θ * (u - v) := by ring
    rw [this, abs_mul]
    exact mul_le_mul_of_nonneg_right (hK t ht) (abs_nonneg _)
  calc ENNReal.ofReal |S.fx t (x t) θ * u + S.fθ t (x t) θ
          - (S.fx t (x t) θ * v + S.fθ t (x t) θ)|
      ≤ ENNReal.ofReal ((K : ℝ) * |u - v|) := ENNReal.ofReal_le_ofReal habs
    _ = (K : ℝ≥0∞) * ENNReal.ofReal |u - v| := by
        rw [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal]

/-- **A certified modulus for a dynamical measurement.**  With `|f_x| ≤ K` and
`|f_θ| ≤ B` along the trajectory, the sensitivity is bounded by Grönwall's
function — `(B/K)(e^{Kt} − 1)` when `K ≠ 0`.  Unlike the declared separation
modulus of `Integration.Experiment.NonlinearDiscrimination`, this bound is
computed from the model. -/
theorem sensitivity_bound {S : ParamSystem} {θ : ℝ} {x s : ℝ → ℝ} {K B : ℝ}
    (hs : S.IsSensitivity θ x s)
    (hK : ∀ t ∈ Ico 0 S.horizon, |S.fx t (x t) θ| ≤ K)
    (hB : ∀ t ∈ Ico 0 S.horizon, |S.fθ t (x t) θ| ≤ B) :
    ∀ t ∈ Icc 0 S.horizon, |s t| ≤ gronwallBound 0 K B t := by
  intro t ht
  have hmain := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := s) (f' := fun t => S.fx t (x t) θ * s t + S.fθ t (x t) θ)
    (δ := 0) (K := K) (ε := B) (a := 0) (b := S.horizon)
    hs.cont hs.deriv (by rw [hs.init]; simp)
    (fun u hu => by
      have h1 : |S.fx u (x u) θ * s u + S.fθ u (x u) θ|
          ≤ |S.fx u (x u) θ| * |s u| + |S.fθ u (x u) θ| := by
        calc |S.fx u (x u) θ * s u + S.fθ u (x u) θ|
            ≤ |S.fx u (x u) θ * s u| + |S.fθ u (x u) θ| := abs_add_le _ _
          _ = |S.fx u (x u) θ| * |s u| + |S.fθ u (x u) θ| := by rw [abs_mul]
      have h2 : |S.fx u (x u) θ| * |s u| ≤ K * |s u| :=
        mul_le_mul_of_nonneg_right (hK u hu) (abs_nonneg _)
      have h3 := hB u hu
      simpa [Real.norm_eq_abs] using h1.trans (by linarith))
    t ht
  simpa [Real.norm_eq_abs] using hmain

/-! ## §3 The worked instance: `ẋ = −θ` -/

/-- The galvanostatic-hold shape: `ẋ = −θ`, whose partials are constants. -/
noncomputable def constantRate (T : ℝ) (hT : 0 ≤ T) (x₀ : ℝ) : ParamSystem where
  horizon := T
  hT := hT
  init := x₀
  f := fun _ _ θ => -θ
  fx := fun _ _ _ => 0
  fθ := fun _ _ _ => -1
  fx_cert := fun _ _ _ => hasDerivAt_const _ _
  fθ_cert := fun _ _ θ => by simpa using (hasDerivAt_id θ).neg

/-- The trajectory of `ẋ = −θ` is `x₀ − θt`. -/
theorem constantRate_isParamTrajectory (T : ℝ) (hT : 0 ≤ T) (x₀ θ : ℝ) :
    (constantRate T hT x₀).IsParamTrajectory θ (fun t => x₀ - θ * t) where
  init := by simp [constantRate]
  cont := (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
  deriv := by
    intro t _
    have : HasDerivAt (fun t : ℝ => x₀ - θ * t) (-θ) t := by
      simpa using (((hasDerivAt_id t).const_mul θ).const_sub x₀)
    exact this.hasDerivWithinAt

/-- Its trajectory sensitivity is `s(t) = −t`. -/
theorem constantRate_isSensitivity (T : ℝ) (hT : 0 ≤ T) (x₀ θ : ℝ) :
    (constantRate T hT x₀).IsSensitivity θ (fun t => x₀ - θ * t) (fun t => -t) where
  init := by simp
  cont := (continuous_neg).continuousOn
  deriv := by
    intro t _
    have : HasDerivAt (fun t : ℝ => -t) (-1) t := by simpa using (hasDerivAt_id t).neg
    simpa [constantRate] using this.hasDerivWithinAt

/-- **And in this instance the sensitivity really is `∂x/∂θ`**: the interchange
of `d/dt` and `∂/∂θ` is verified, not assumed. -/
theorem constantRate_sensitivity_is_the_theta_derivative (x₀ θ t : ℝ) :
    HasDerivAt (fun p : ℝ => x₀ - p * t) (-t) θ := by
  simpa using (((hasDerivAt_id θ).mul_const t).const_sub x₀)

/-! ## §4 What a trajectory sensitivity buys the experiment designer -/

/-- **A nonzero trajectory sensitivity gives local identifiability.**  If the
prediction at the measurement time depends on the parameter with nonvanishing
strict derivative, no other nearby parameter produces the same reading. -/
theorem locally_identifiable_of_nonzero_sensitivity {g : ℝ → ℝ} {θ d : ℝ}
    (h : HasStrictDerivAt g d θ) (hd : d ≠ 0) :
    ∃ u ∈ nhds θ, InjOn g u := by
  obtain ⟨u, hu, hleft⟩ := Filter.eventually_iff_exists_mem.1 (h.eventually_left_inverse hd)
  refine ⟨u, hu, ?_⟩
  intro a ha b hb hab
  have h1 := hleft a ha
  have h2 := hleft b hb
  rw [← h1, ← h2, hab]

/-- **A zero sensitivity marks a first-order blind measurement time.**  Reading
the observable at such a time cannot distinguish nearby parameters to first
order, whatever tolerance the instrument declares. -/
theorem zero_sensitivity_time_is_first_order_blind {g : ℝ → ℝ} {θ : ℝ}
    (h : HasDerivAt g 0 θ) : deriv g θ = 0 := h.deriv

/-- **Measurement selection driven by a computed sensitivity.**  Feeding the
trajectory sensitivity to the Stage-4 selector picks, among the offered
candidate readings, one whose time has maximal sensitivity magnitude.  The
Stage-5 ranking used a *declared* modulus; this one uses a function obtained
from the model's own variational equation. -/
theorem most_sensitive_reading_is_maximal (s : ℝ → ℝ) (r : Reading) (cs : List Reading)
    (c : Reading) (hc : c ∈ r :: cs) :
    |s c.time| ≤ |s (Integration.Experiment.BestReading.steepest s r cs).time| :=
  Integration.Experiment.BestReading.steepest_maximal s cs r c hc

/-- And the selection is one of the offered candidates. -/
theorem most_sensitive_reading_mem (s : ℝ → ℝ) (r : Reading) (cs : List Reading) :
    Integration.Experiment.BestReading.steepest s r cs ∈ r :: cs :=
  Integration.Experiment.BestReading.steepest_mem s cs r

end Integration.Experiment.TrajectorySensitivity

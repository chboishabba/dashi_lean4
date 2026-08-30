import Mathlib
import Integration.Experiment.TrajectorySensitivity
import Integration.Experiment.InformationMatrix

/-!
# Stage 7, lane 2 — vector states, several parameters, and controls

`TOE_STAGE6_INFERENCE.md` frontier item 7 records the gap closed here:

> **Only scalar dynamics.**  `ParamSystem` has a scalar state and a scalar
> parameter; vector states, several parameters, control inputs `u`, and Fisher
> information are all absent.

This file generalises exactly one level, to

```
x(t) ∈ ℝⁿ,   θ ∈ ℝᵖ,   u(t) ∈ ℝᵐ,   ẋ = f(t, x, θ, u),   y = h(x, θ) ∈ ℝᵠ
```

with the sensitivity of the trajectory to the parameters handled **one parameter
at a time**: the `k`-th sensitivity column `s_k(t) = ∂x(t)/∂θ_k` solves the
variational equation

```
ṡ_k  =  f_x · s_k  +  (f_θ)·e_k,        s_k(0) = 0.
```

Column-wise is not a restriction — the sensitivity matrix `S(t)` is exactly the
matrix whose columns are the `s_k` — and it keeps every statement inside the
normed space `Fin n → ℝ`, where Mathlib's ODE uniqueness and Grönwall lemmas
apply directly.

## What is proved

| Statement | Kind | Content |
|---|---|---|
| `VecSystem` | structure | vector field with certified `f_x`, `f_θ` (both as matrices of proved partial derivatives), a control input, and a horizon |
| `IsVecTrajectory`, `IsSensitivityColumn` | structure | the state equation and the variational equation |
| **`sensitivity_column_unique`** | theorem | the variational equation has at most one solution on the window, so `∂x/∂θ_k` names one function |
| **`sensitivity_column_bound`** | theorem | Grönwall: a *computed* modulus for how far the trajectory can move when a parameter moves |
| `sensitivityMatrix`, `sensitivityMatrix_col` | definition/theorem | the columns assemble into `S(t)` |
| **`output_sensitivity_chain_rule`** | theorem | `d/dε h(x(ε), θ(ε)) = h_x ẋ + h_θ θ̇`: the observation map's contribution, proved, not assumed |
| `outputJacobian`, `outputJacobian_apply` | definition/theorem | the measurement Jacobian `J = h_x S + h_θ` assembled from the certified pieces |
| **`unexcited_parameter_is_invisible`** | theorem | a parameter with zero sensitivity column and zero direct effect is an invisible direction of the design — the bridge into `InformationMatrix` |
| `information_of_trajectory_design` | theorem | and the information matrix of a dynamical design is `JᵀWJ` for that `J` |
| `sensitivity_of_a_flat_field_is_zero` | theorem | a system whose `f_θ` vanishes has zero sensitivity: no excitation, no information |

## What is *not* claimed

As in Stage 6, `IsSensitivityColumn` is a *hypothesis about* `(x, s)`: the
theorem that `∂x/∂θ_k` exists and satisfies the variational equation
(differentiability of the flow in the parameter) is still not proved in general.
`output_sensitivity_chain_rule` is the one place where a derivative is genuinely
composed rather than assumed.  No control-design, controllability, or observability
theory is claimed.
-/

namespace Integration.Experiment.VectorDynamics

open Set Matrix
open scoped NNReal ENNReal
open Integration.Experiment.JacobianSensitivity
open Integration.Experiment.InformationMatrix

/-! ## §0 Matrices as continuous linear maps -/

/-- A matrix, viewed as a continuous linear map `ℝⁿ → ℝᵐ`. -/
noncomputable def clm {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) : (Fin b → ℝ) →L[ℝ] (Fin a → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)

@[simp] theorem clm_apply {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) (v : Fin b → ℝ) :
    clm M v = M *ᵥ v := rfl

/-! ## §1 A vector system with certified partials -/

/-- **A vector dynamical model with a vector parameter and a control input**,
whose partial derivatives are supplied with their certificates.

`f t x θ u` is the vector field; `fx` and `fθ` are the declared Jacobians in the
state and in the parameter, each certified as an `HasFDerivAt`. -/
structure VecSystem (n p m : ℕ) where
  /-- Length of the run. -/
  horizon : ℝ
  /-- The run has nonnegative length. -/
  hT : 0 ≤ horizon
  /-- The initial state, taken not to depend on the parameter. -/
  init : Fin n → ℝ
  /-- The vector field `f(t, x, θ, u)`. -/
  f : ℝ → (Fin n → ℝ) → (Fin p → ℝ) → (Fin m → ℝ) → (Fin n → ℝ)
  /-- The declared state Jacobian `∂f/∂x`. -/
  fx : ℝ → (Fin n → ℝ) → (Fin p → ℝ) → (Fin m → ℝ) → Matrix (Fin n) (Fin n) ℝ
  /-- The declared parameter Jacobian `∂f/∂θ`. -/
  fθ : ℝ → (Fin n → ℝ) → (Fin p → ℝ) → (Fin m → ℝ) → Matrix (Fin n) (Fin p) ℝ
  /-- The obligation, discharged: `fx` is `∂f/∂x`. -/
  fx_cert : ∀ t x θ u, HasFDerivAt (fun y => f t y θ u) (clm (fx t x θ u)) x
  /-- The obligation, discharged: `fθ` is `∂f/∂θ`. -/
  fθ_cert : ∀ t x θ u, HasFDerivAt (fun q => f t x q u) (clm (fθ t x θ u)) θ

namespace VecSystem

variable {n p m : ℕ} (S : VecSystem n p m)

/-- The time window of a run. -/
def window : Set ℝ := Icc 0 S.horizon

/-- `x` is the trajectory of the system at parameter `θ` under control `u`. -/
structure IsVecTrajectory (θ : Fin p → ℝ) (u : ℝ → (Fin m → ℝ)) (x : ℝ → (Fin n → ℝ)) : Prop where
  /-- The initial condition. -/
  init : x 0 = S.init
  /-- Continuity on the window. -/
  cont : ContinuousOn x S.window
  /-- The state equation, as a one-sided derivative. -/
  deriv : ∀ t ∈ Ico 0 S.horizon, HasDerivWithinAt x (S.f t (x t) θ (u t)) (Ici t) t

/-- `s` is the `k`-th **sensitivity column** along `x`: the solution of the
variational equation `ṡ = f_x s + (f_θ) e_k` with `s(0) = 0`. -/
structure IsSensitivityColumn (θ : Fin p → ℝ) (u : ℝ → (Fin m → ℝ)) (x : ℝ → (Fin n → ℝ))
    (k : Fin p) (s : ℝ → (Fin n → ℝ)) : Prop where
  /-- The initial state does not depend on the parameter. -/
  init : s 0 = 0
  /-- Continuity on the window. -/
  cont : ContinuousOn s S.window
  /-- The variational equation. -/
  deriv : ∀ t ∈ Ico 0 S.horizon,
    HasDerivWithinAt s
      (S.fx t (x t) θ (u t) *ᵥ s t + (fun i => S.fθ t (x t) θ (u t) i k)) (Ici t) t

end VecSystem

open VecSystem

/-! ## §2 The sensitivity column is well defined -/

variable {n p m : ℕ}

/-- **Uniqueness of a trajectory sensitivity column.**  If the state Jacobian is
bounded along the trajectory then the variational equation has at most one
solution on the window: "the sensitivity of this state to this parameter" names
a single function. -/
theorem sensitivity_column_unique {S : VecSystem n p m} {θ : Fin p → ℝ}
    {u : ℝ → (Fin m → ℝ)} {x : ℝ → (Fin n → ℝ)} {k : Fin p} {s₁ s₂ : ℝ → (Fin n → ℝ)}
    {K : NNReal}
    (hK : ∀ t ∈ Ico 0 S.horizon, ∀ y : Fin n → ℝ, ‖S.fx t (x t) θ (u t) *ᵥ y‖ ≤ K * ‖y‖)
    (h₁ : S.IsSensitivityColumn θ u x k s₁) (h₂ : S.IsSensitivityColumn θ u x k s₂) :
    EqOn s₁ s₂ S.window := by
  refine ODE_solution_unique_of_mem_Icc_right (K := K)
    (v := fun t y => S.fx t (x t) θ (u t) *ᵥ y + (fun i => S.fθ t (x t) θ (u t) i k))
    (s := fun _ => univ)
    (fun t ht => ?_) h₁.cont h₁.deriv (fun _ _ => mem_univ _)
    h₂.cont h₂.deriv (fun _ _ => mem_univ _) (by rw [h₁.init, h₂.init])
  refine LipschitzWith.lipschitzOnWith ?_
  intro a b
  simp only [edist_dist, dist_eq_norm]
  have hdiff : S.fx t (x t) θ (u t) *ᵥ a + (fun i => S.fθ t (x t) θ (u t) i k)
      - (S.fx t (x t) θ (u t) *ᵥ b + (fun i => S.fθ t (x t) θ (u t) i k))
      = S.fx t (x t) θ (u t) *ᵥ (a - b) := by
    rw [Matrix.mulVec_sub]
    abel
  have habs : ‖S.fx t (x t) θ (u t) *ᵥ a + (fun i => S.fθ t (x t) θ (u t) i k)
      - (S.fx t (x t) θ (u t) *ᵥ b + (fun i => S.fθ t (x t) θ (u t) i k))‖
      ≤ (K : ℝ) * ‖a - b‖ := by
    rw [hdiff]
    exact hK t ht (a - b)
  calc ENNReal.ofReal ‖S.fx t (x t) θ (u t) *ᵥ a + (fun i => S.fθ t (x t) θ (u t) i k)
          - (S.fx t (x t) θ (u t) *ᵥ b + (fun i => S.fθ t (x t) θ (u t) i k))‖
      ≤ ENNReal.ofReal ((K : ℝ) * ‖a - b‖) := ENNReal.ofReal_le_ofReal habs
    _ = (K : ℝ≥0∞) * ENNReal.ofReal ‖a - b‖ := by
        rw [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal]

/-- **A computed modulus for a vector dynamical measurement.**  With
`‖f_x y‖ ≤ K‖y‖` and `‖(f_θ)e_k‖ ≤ B` along the trajectory, the `k`-th
sensitivity column obeys Grönwall's bound.  This is the multi-parameter
successor of `TrajectorySensitivity.sensitivity_bound`. -/
theorem sensitivity_column_bound {S : VecSystem n p m} {θ : Fin p → ℝ}
    {u : ℝ → (Fin m → ℝ)} {x s : ℝ → (Fin n → ℝ)} {k : Fin p} {K B : ℝ}
    (hs : S.IsSensitivityColumn θ u x k s)
    (hK : ∀ t ∈ Ico 0 S.horizon, ∀ y : Fin n → ℝ, ‖S.fx t (x t) θ (u t) *ᵥ y‖ ≤ K * ‖y‖)
    (hB : ∀ t ∈ Ico 0 S.horizon, ‖(fun i => S.fθ t (x t) θ (u t) i k)‖ ≤ B) :
    ∀ t ∈ Icc 0 S.horizon, ‖s t‖ ≤ gronwallBound 0 K B t := by
  intro t ht
  have hmain := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := s)
    (f' := fun t => S.fx t (x t) θ (u t) *ᵥ s t + (fun i => S.fθ t (x t) θ (u t) i k))
    (δ := 0) (K := K) (ε := B) (a := 0) (b := S.horizon)
    hs.cont hs.deriv (by rw [hs.init]; simp)
    (fun w hw => by
      have h1 := norm_add_le (S.fx w (x w) θ (u w) *ᵥ s w)
        ((fun i => S.fθ w (x w) θ (u w) i k) : Fin n → ℝ)
      have h2 := hK w hw (s w)
      have h3 := hB w hw
      linarith)
    t ht
  simpa using hmain

/-! ## §3 The sensitivity matrix -/

/-- The **sensitivity matrix** `S(t) = ∂x(t)/∂θ`, assembled from the columns. -/
def sensitivityMatrix (cols : Fin p → ℝ → (Fin n → ℝ)) (t : ℝ) : Matrix (Fin n) (Fin p) ℝ :=
  fun i k => cols k t i

@[simp] theorem sensitivityMatrix_col (cols : Fin p → ℝ → (Fin n → ℝ)) (t : ℝ) (k : Fin p) :
    (fun i => sensitivityMatrix cols t i k) = cols k t := rfl

/-! ## §4 The observation map -/

/-- **The chain rule for the observation map.**  Moving along a curve of states
and parameters, the observation moves by `h_x ẋ + h_θ θ̇`.  This is the one place
in the lane where a derivative is genuinely composed: `y = h(x, θ)` contributes
*both* through the state and directly. -/
theorem output_sensitivity_chain_rule {q : ℕ}
    {h : (Fin n → ℝ) × (Fin p → ℝ) → (Fin q → ℝ)}
    {hx : Matrix (Fin q) (Fin n) ℝ} {hθ : Matrix (Fin q) (Fin p) ℝ}
    {x₀ : Fin n → ℝ} {θ₀ : Fin p → ℝ}
    (hd : HasFDerivAt h
      ((clm hx).comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin p → ℝ))
        + (clm hθ).comp (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin p → ℝ))) (x₀, θ₀))
    {xc : ℝ → (Fin n → ℝ)} {θc : ℝ → (Fin p → ℝ)} {sx : Fin n → ℝ} {sθ : Fin p → ℝ} {e : ℝ}
    (hxc : HasDerivAt xc sx e) (hθc : HasDerivAt θc sθ e)
    (hx0 : xc e = x₀) (hθ0 : θc e = θ₀) :
    HasDerivAt (fun ε => h (xc ε, θc ε)) (hx *ᵥ sx + hθ *ᵥ sθ) e := by
  have hcurve : HasDerivAt (fun ε => (xc ε, θc ε)) (sx, sθ) e := hxc.prodMk hθc
  have hpt : (xc e, θc e) = (x₀, θ₀) := by rw [hx0, hθ0]
  have := (hpt ▸ hd).comp_hasDerivAt e hcurve
  simpa using this

/-- **The measurement Jacobian of a dynamical design**: `J = h_x S(t) + h_θ`, the
matrix whose `(i, k)` entry is the sensitivity of output `i` to parameter `k`. -/
def outputJacobian {q : ℕ} (hx : Matrix (Fin q) (Fin n) ℝ) (hθ : Matrix (Fin q) (Fin p) ℝ)
    (Smat : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin q) (Fin p) ℝ :=
  hx * Smat + hθ

theorem outputJacobian_apply {q : ℕ} (hx : Matrix (Fin q) (Fin n) ℝ)
    (hθ : Matrix (Fin q) (Fin p) ℝ) (Smat : Matrix (Fin n) (Fin p) ℝ) (v : Fin p → ℝ) :
    outputJacobian hx hθ Smat *ᵥ v = hx *ᵥ (Smat *ᵥ v) + hθ *ᵥ v := by
  simp [outputJacobian, Matrix.add_mulVec, Matrix.mulVec_mulVec]

/-! ## §5 The bridge to experiment design -/

/-- **An unexcited parameter is an invisible direction.**  If parameter `k` has a
vanishing sensitivity column and no direct effect on the observation, then the
coordinate direction `e_k` is in the kernel of the measurement Jacobian: the
design cannot see that parameter at all, to first order.

This is the dynamical source of the rank deficiency that
`InformationMatrix.singular_iff_invisible_direction` detects. -/
theorem unexcited_parameter_is_invisible {q : ℕ} (hx : Matrix (Fin q) (Fin n) ℝ)
    (hθ : Matrix (Fin q) (Fin p) ℝ) (Smat : Matrix (Fin n) (Fin p) ℝ) (k : Fin p)
    (hS : ∀ i, Smat i k = 0) (hh : ∀ i, hθ i k = 0) :
    outputJacobian hx hθ Smat *ᵥ (Pi.single k 1) = 0 := by
  classical
  funext i
  simp only [outputJacobian, Matrix.mulVec, dotProduct,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Pi.zero_apply]
  simp [Matrix.add_apply, Matrix.mul_apply, hS, hh]

/-- With a positive-definite weighting, an unexcited parameter makes the
information matrix of the design singular. -/
theorem unexcited_parameter_makes_information_singular {q : ℕ}
    (hx : Matrix (Fin q) (Fin n) ℝ) (hθ : Matrix (Fin q) (Fin p) ℝ)
    (Smat : Matrix (Fin n) (Fin p) ℝ) (W : RCov q) (hW : PosDefWeight W)
    (k : Fin p) (hS : ∀ i, Smat i k = 0) (hh : ∀ i, hθ i k = 0) :
    (infoMatrix (outputJacobian hx hθ Smat) W).toMatrix.det = 0 := by
  classical
  refine (singular_iff_invisible_direction hW).2 ⟨Pi.single k 1, ?_, ?_⟩
  · intro hzero
    have := congrFun hzero k
    simp at this
  · exact unexcited_parameter_is_invisible hx hθ Smat k hS hh

/-- **The information matrix of a dynamical design** is the general one, applied
to the trajectory-sensitivity Jacobian: nothing new is declared, the Jacobian is
assembled from certified partials and solved sensitivity columns. -/
theorem information_of_trajectory_design {q : ℕ} (hx : Matrix (Fin q) (Fin n) ℝ)
    (hθ : Matrix (Fin q) (Fin p) ℝ) (cols : Fin p → ℝ → (Fin n → ℝ)) (t : ℝ) (W : RCov q) :
    (infoMatrix (outputJacobian hx hθ (sensitivityMatrix cols t)) W).toMatrix
      = (outputJacobian hx hθ (sensitivityMatrix cols t)).transpose * W.toMatrix
        * outputJacobian hx hθ (sensitivityMatrix cols t) :=
  infoMatrix_toMatrix _ _

/-- **No excitation, no information.**  If the parameter Jacobian of the vector
field vanishes identically along the run, the zero function is a sensitivity
column: the parameter leaves no trace in the state. -/
theorem sensitivity_of_a_flat_field_is_zero {S : VecSystem n p m} {θ : Fin p → ℝ}
    {u : ℝ → (Fin m → ℝ)} {x : ℝ → (Fin n → ℝ)} (k : Fin p)
    (hflat : ∀ t ∈ Ico 0 S.horizon, ∀ i, S.fθ t (x t) θ (u t) i k = 0) :
    S.IsSensitivityColumn θ u x k (fun _ => 0) where
  init := rfl
  cont := continuousOn_const
  deriv := by
    intro t ht
    have hz : S.fx t (x t) θ (u t) *ᵥ (0 : Fin n → ℝ)
        + (fun i => S.fθ t (x t) θ (u t) i k) = 0 := by
      funext i
      simp [hflat t ht i]
    rw [hz]
    exact (hasDerivWithinAt_const t _ (0 : Fin n → ℝ))

end Integration.Experiment.VectorDynamics

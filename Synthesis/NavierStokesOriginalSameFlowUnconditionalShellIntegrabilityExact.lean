import Synthesis.NavierStokesOriginalSameFlowDualSpacetimeCompactnessExact

/-!
Section 36: discharge the last explicit original R-shell
integrability input from the SAME physical global Galerkin ODE.

The ORIGINAL finitely many zero-extended Fourier coefficients
are differentiable along the actual state X_N on [0,T].
The true high-shell energy is a finite sum of squared complex
coefficients, therefore ContinuousOn and IntervalIntegrable.
No new auxiliary solution trajectory is chosen. This does not
assert time-uniform H1 or nonlinear signed quarter source
control, and cannot be promoted to 3D NSE regularity.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open DASHI.NavierStokes.RealContinuation
open Set MeasureTheory
open scoped BigOperators
noncomputable section

theorem original_actual_finite_high_shell_interval_integrable
    (N : ℕ) (ν T a R : ℝ)
    (hT : 0 ≤ T) (ha : a < 0)
    (X : ℝ → FiniteState N)
    (hODE : SolvesOn (finiteForce N ν) X (Ioi a)) :
    IntervalIntegrable
      (fun t => originalPhysicalHighShell N X R t) volume 0 T := by
  let U : Vec3 → ℝ → CVec3 :=
    fun k t => zeroExtend (X t) k
  have hderiv (t : ℝ) (ht : t ∈ uIcc 0 T)
      (k : Vec3) (i : Fin 3) :
      HasDerivAt (fun s => U k s i)
        (-((ν * massSq k : ℝ) : ℂ) * U k t i +
          galerkinForce N U k t i) t := by
    have ht0 : 0 ≤ t := by
      rw [uIcc_of_le hT] at ht
      exact ht.1
    exact zeroExtend_ODE_of_derivative N ν X t
      (hODE t (ha.trans_le ht0)) k i
  have hcoord (k : Vec3) (i : Fin 3) :
      ContinuousOn (fun t => U k t i) (uIcc 0 T) :=
    fun t ht => (hderiv t ht k i).continuousAt.continuousWithinAt
  have hsum : ContinuousOn
      (fun t => originalPhysicalHighShell N X R t) (uIcc 0 T) := by
    unfold originalPhysicalHighShell
    apply continuousOn_finset_sum
    intro k hk
    unfold realHermitian
    simp only [Fin.sum_univ_three]
    fun_prop
  exact hsum.intervalIntegrable

/-- All finite-original shell and quarter-energy compactness
payments are now provided for every T,R on ONE global Galerkin
solution, without an external integrability input. -/
theorem actual_original_one_flow_full_dual_time_compactness
    (N : ℕ) (ν : ℝ) (hν : 0 < ν)
    (x₀ : FiniteState N)
    (hr : reflectState x₀ = x₀)
    (ht : ∀ k, outputDot k (zeroExtend x₀ k) = 0) :
    ∃ a < 0, ∃ X : ℝ → FiniteState N,
      X 0 = x₀ ∧
      SolvesOn (finiteForce N ν) X (Ioi a) ∧
      (∀ t ≥ 0, reflectState (X t) = X t) ∧
      (∀ t ≥ 0, ∀ k,
        outputDot k (zeroExtend (X t) k) = 0) ∧
      (∀ t ≥ 0,
        stateEnergy (X t) ≤ stateEnergy x₀ ∧
        2 * ν * (∫ s in 0..t,
          periodicDissipation N
            (fun k s => zeroExtend (X s) k) s) ≤ stateEnergy x₀) ∧
      (∀ t R : ℝ, 0 < R →
        R^2 * originalPhysicalHighShell N X R t ≤
        periodicDissipation N (fun k s => zeroExtend (X s) k) t) ∧
      (∀ T : ℝ, 0 ≤ T →
        2 * ν * (∫ t in 0..T,
          (fractionalEnergy N quarterWeight
            (fun k s => zeroExtend (X s) k) t)^4)
          ≤ (stateEnergy x₀)^4) ∧
      (∀ T R : ℝ, 0 ≤ T → 0 < R →
        (∫ t in 0..T, originalPhysicalHighShell N X R t)
        ≤ stateEnergy x₀ / (2 * ν * R^2)) := by
  obtain ⟨a,ha,X,hzero,hODE,hreal,htrans,hbudget,htail,hquarter,hspace⟩ :=
    actual_original_same_flow_both_spacetime_payments N ν hν x₀ hr ht
  refine ⟨a,ha,X,hzero,hODE,hreal,htrans,hbudget,htail,hquarter,?_⟩
  intro T R hT hR
  exact hspace T R hT hR
    (original_actual_finite_high_shell_interval_integrable
      N ν T a R hT ha X hODE)

end
end DASHI.NavierStokes.PhysicalMixed

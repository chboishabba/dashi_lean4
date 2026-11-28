import Synthesis.NavierStokesOriginalSameFlowUnconditionalShellIntegrabilityExact

/-!
Section38 — reverse-solve the original physical high-frequency ledger
against a prescribed positive epsilon and its exact geometric radius.

Source: actual global Galerkin flow, original physical energy and
viscosity, original high-shell time integral. No independent cutoff
model, Sobolev norm or additional trajectory is created.

This is the exact threshold to select R for spatial L1_t tail
tightness, rather than pretending the quarter-L4 payment directly
bounds the signed nonlinear transport. The R admissibility
condition is explicit; genuine uniform cutoff limit / compactness
requires the original family of solutions and a uniform E0 ceiling.
Pending pinned Lean elaboration; no universal NS solution claimed.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open DASHI.NavierStokes.RealContinuation
open Set MeasureTheory
open scoped BigOperators
noncomputable section

/-- On the SAME original global X_N, any radius with
E0 < 2 ν R² ε pays the desired uniform-in-T finite
space-time tail below ε. This is a concrete geometric
reverse-solve condition for an arbitrary positive tolerance. -/
theorem actual_original_same_flow_high_shell_epsilon_from_radius
    (N : ℕ) (ν : ℝ) (hν : 0 < ν)
    (x₀ : FiniteState N)
    (hr : reflectState x₀ = x₀)
    (ht : ∀ k, outputDot k (zeroExtend x₀ k) = 0) :
    ∃ a < 0, ∃ X : ℝ → FiniteState N,
      X 0 = x₀ ∧
      SolvesOn (finiteForce N ν) X (Ioi a) ∧
      (∀ T R ε : ℝ, 0 ≤ T → 0 < R → 0 < ε →
        stateEnergy x₀ < 2 * ν * R^2 * ε →
        (∫ t in 0..T, originalPhysicalHighShell N X R t) < ε) := by
  obtain ⟨a,ha,X,hzero,hODE,_hreal,_htrans,_hbudget,_htail,
    _hquarter,hspace⟩ :=
    actual_original_one_flow_full_dual_time_compactness N ν hν x₀ hr ht
  refine ⟨a,ha,X,hzero,hODE,?_⟩
  intro T R ε hT hR hε hthreshold
  have hbound := hspace T R hT hR
  have hden : 0 < 2 * ν * R^2 := by positivity
  have hstrict : stateEnergy x₀ / (2 * ν * R^2) < ε :=
    (div_lt_iff₀ hden).2 (by nlinarith [hthreshold])
  exact lt_of_le_of_lt hbound hstrict

/-- An explicit *uniform initial-energy ceiling* Emax makes
the radius threshold independent of the Galerkin cutoff N.
This is the exact interface for a future genuine continuum
compactness argument, not a claim that that argument is paid. -/
theorem original_high_shell_uniform_energy_epsilon_payment
    (N : ℕ) (ν Emax T R ε : ℝ)
    (hν : 0 < ν) (hT : 0 ≤ T)
    (hR : 0 < R) (hε : 0 < ε)
    (x₀ : FiniteState N)
    (hr : reflectState x₀ = x₀)
    (ht : ∀ k, outputDot k (zeroExtend x₀ k) = 0)
    (hE : stateEnergy x₀ ≤ Emax)
    (hthreshold : Emax < 2 * ν * R^2 * ε) :
    ∃ X : ℝ → FiniteState N,
      X 0 = x₀ ∧
      (∫ t in 0..T, originalPhysicalHighShell N X R t) < ε := by
  obtain ⟨a,ha,X,hzero,hODE,hbound⟩ :=
    actual_original_same_flow_high_shell_epsilon_from_radius
      N ν hν x₀ hr ht
  exact ⟨X,hzero,hbound T R ε hT hR hε (lt_of_le_of_lt hE hthreshold)⟩

end
end DASHI.NavierStokes.PhysicalMixed

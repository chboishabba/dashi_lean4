import Synthesis.NavierStokesOriginalSameFlowEpsilonRadiusTightnessExact

/-!
Section39 — one geometric frequency radius for ALL original finite
Galerkin cutoffs under a shared physical initial-energy ceiling.

The exact same cutoff-dependent original global ODE trajectories,
energy/dissipation ledger, and R^-2 Fourier shell receipt are
retained. Radius R is selected ONCE from ν, ε, and Emax, before
quantifying over N and its actual initial state x₀.

Crucial distinction: this only proves UNIFORM TIME-INTEGRATED
HIGH-SHELL TIGHTNESS in the finite-flow family. It does NOT
give pointwise H¹, critical signed nonlinear transport, a compact
global smooth continuum solution or the Clay endpoint.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open DASHI.NavierStokes.RealContinuation
open Set MeasureTheory
open scoped BigOperators
noncomputable section

/-- A specific positive radius depending only on the original
ν>0, Emax>=0 and epsilon>0 suffices for the exact R^-2
physical ledger. No nonconstructive choice of a different radius
at each Fourier cutoff is permitted. -/
def originalCommonHighShellRadius (ν Emax ε : ℝ) : ℝ :=
  1 + Emax / (2 * ν * ε)

theorem original_common_high_shell_radius_threshold
    (ν Emax ε : ℝ)
    (hν : 0 < ν) (hE : 0 ≤ Emax) (hε : 0 < ε) :
    0 < originalCommonHighShellRadius ν Emax ε ∧
      Emax < 2 * ν *
        (originalCommonHighShellRadius ν Emax ε)^2 * ε := by
  have hd : 0 < 2 * ν * ε := by positivity
  let t := Emax / (2 * ν * ε)
  have ht : 0 ≤ t := div_nonneg hE hd.le
  have hcancel : t * (2 * ν * ε) = Emax := by
    dsimp [t]
    exact div_mul_cancel₀ Emax (ne_of_gt hd)
  have hpos : 0 < 1 + t := by linarith
  constructor
  · exact hpos
  · change Emax < 2 * ν * (1 + t)^2 * ε
    have hstrict : t < (1 + t)^2 := by nlinarith [sq_nonneg t]
    nlinarith [mul_pos hd (sub_pos.mpr hstrict)]

/-- One radius, fixed BEFORE selecting the original N-indexed
physical trajectories, pays the same epsilon high-shell envelope
for EVERY finite cutoff and time horizon. The actual per-cutoff
global ODE remains in the conclusion; this is not an arbitrary
independently fitted Fourier field. -/
theorem actual_original_uniform_all_cutoffs_high_shell_epsilon
    (ν Emax ε : ℝ)
    (hν : 0 < ν) (hE : 0 ≤ Emax) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧
      (∀ (N : ℕ) (x₀ : FiniteState N),
        reflectState x₀ = x₀ →
        (∀ k, outputDot k (zeroExtend x₀ k) = 0) →
        stateEnergy x₀ ≤ Emax →
        ∃ a < 0, ∃ X : ℝ → FiniteState N,
          X 0 = x₀ ∧
          SolvesOn (finiteForce N ν) X (Ioi a) ∧
          ∀ T : ℝ, 0 ≤ T →
            (∫ t in 0..T, originalPhysicalHighShell N X R t)
              < ε) := by
  obtain ⟨hR, hthreshold⟩ :=
    original_common_high_shell_radius_threshold ν Emax ε hν hE hε
  refine ⟨originalCommonHighShellRadius ν Emax ε, hR, ?_⟩
  intro N x₀ hr ht henergy
  obtain ⟨a,ha,X,hzero,hODE,hbound⟩ :=
    actual_original_same_flow_high_shell_epsilon_from_radius
      N ν hν x₀ hr ht
  refine ⟨a,ha,X,hzero,hODE,?_⟩
  intro T hT
  exact hbound T (originalCommonHighShellRadius ν Emax ε)
    ε hT hR hε (lt_of_le_of_lt henergy hthreshold)

end
end DASHI.NavierStokes.PhysicalMixed

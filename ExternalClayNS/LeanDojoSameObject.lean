import LeanDojoSameObjectCore
import LiteralABCD
import Mathlib.Algebra.Ring.Periodic

/-!
# Concrete same-object transport to the pinned LeanDojo Navier--Stokes target

No statement-weld hypothesis is introduced here.  Each lemma transports an
existing comparator/Clay fact onto LeanDojo's literal carrier.  The terminal C/D
theorems are added only after every premise and every putative solution can be
transported in the direction needed for the contradiction.
-/

noncomputable section

open ClaySpec
open NavierStokes
open NavierStokesOnR3

namespace DASHILiteralClayNS

/-! ## Initial spatial data: literally the same R3 carrier -/

/-- Comparator divergence-free data is LeanDojo divergence-free data on the
same literal Euclidean `Fin 3` carrier. -/
theorem comparatorInitialDivergence_to_leanDojo
    {u₀ : R3 → R3}
    (h : NavierStokes.Comparator.InitialVelocityCondition u₀) :
    NavierStokesOnR3.DivergenceFreeInitial u₀ := by
  intro x
  change ClaySpec.initialDivergence u₀ x = 0
  rw [SemanticGap.initialDivergence_eq u₀ h.smooth x]
  exact h.div_free x

/-- One-coordinate unit periodicity is a genuine period, hence automatically
extends to every integer translate required by LeanDojo's torus statement. -/
theorem comparatorOnePeriodic_to_leanDojo
    {α : Type*} {f : R3 → α}
    (h : NavierStokes.Comparator.IsOnePeriodic f) :
    NavierStokesPeriodic.IsPeriodic f := by
  intro x i n
  let e : R3 := EuclideanSpace.single i 1
  have hp : Function.Periodic f e := by
    intro y
    simpa [e] using h y i
  have hpn : Function.Periodic f (n • e) := hp.zsmul n
  simpa [e] using hpn x

/-- The periodic initial-data part of Fefferman D is already paid without a
new representation: smoothness and divergence are reused directly, and unit
periodicity is closed under integer multiples. -/
theorem comparatorInitialPeriodic_to_leanDojo
    {u₀ : R3 → R3}
    (h : NavierStokes.Comparator.InitialVelocityConditionPeriodic u₀) :
    ContDiff ℝ (⊤ : ℕ∞) u₀ ∧
      NavierStokesPeriodic.PeriodicInitial u₀ ∧
      NavierStokesOnR3.DivergenceFreeInitial u₀ := by
  exact ⟨h.smooth,
    comparatorOnePeriodic_to_leanDojo h.isOnePeriodic,
    comparatorInitialDivergence_to_leanDojo h.toInitialVelocityCondition⟩

/-! ## Coordinate directional derivatives -/

/-- A scalar coordinate partial in LeanDojo is the same directional derivative
used by the frozen Clay specification. -/
theorem leanDojo_partialDeriv_eq_clay_direction
    {g : R3 → ℝ} (i : Fin 3) (x : R3) :
    partial_deriv i g x =
      fderiv ℝ g x (ClaySpec.spatialBasis i) := by
  rfl

/-- The zeroth spatial derivative vector is the original initial field. -/
@[simp] theorem leanDojo_spatialDerivativeVector_nil
    (u₀ : R3 → R3) (x : R3) :
    NavierStokesOnR3.spatial_derivative_vector u₀ [] x = u₀ x := by
  ext i
  simp [NavierStokesOnR3.spatial_derivative_vector,
    iterated_partial_deriv]

/-- Exact bridge between LeanDojo's coordinate-word derivative vector and the
frozen Clay directional-word derivative vector. -/
theorem leanDojo_spatialDerivativeVector_eq_clay
    {u₀ : R3 → R3} (hu₀ : ContDiff ℝ ∞ u₀)
    (α : List (Fin 3)) (x : R3) :
    NavierStokesOnR3.spatial_derivative_vector u₀ α x =
      ClaySpec.iteratedSpatialDirectional (ClaySpec.initialSpatialWord α) u₀ x := by
  induction α generalizing x with
  | nil =>
      simp [NavierStokesOnR3.spatial_derivative_vector,
        iterated_partial_deriv, ClaySpec.iteratedSpatialDirectional,
        ClaySpec.initialSpatialWord]
  | cons j α ih =>
      ext i
      simp only [NavierStokesOnR3.spatial_derivative_vector,
        ClaySpec.initialSpatialWord, List.map_cons,
        ClaySpec.iteratedSpatialDirectional, iterated_partial_deriv]
      change
        partial_deriv j
            (fun y =>
              (NavierStokesOnR3.spatial_derivative_vector u₀ α y) i) x =
          (fderiv ℝ
            (fun y => ClaySpec.iteratedSpatialDirectional
              (ClaySpec.initialSpatialWord α) u₀ y) x
            (ClaySpec.spatialBasis j)) i
      rw [show
        (fun y => (NavierStokesOnR3.spatial_derivative_vector u₀ α y) i) =
          (fun y =>
            (ClaySpec.iteratedSpatialDirectional
              (ClaySpec.initialSpatialWord α) u₀ y) i) by
        funext y
        rw [ih y]]
      rw [leanDojo_partialDeriv_eq_clay_direction]
      have hs : ContDiff ℝ ∞
          (fun y => ClaySpec.iteratedSpatialDirectional
            (ClaySpec.initialSpatialWord α) u₀ y) := by
        rw [show
          (fun y => ClaySpec.iteratedSpatialDirectional
            (ClaySpec.initialSpatialWord α) u₀ y) =
            (fun y => iteratedFDeriv ℝ
              (ClaySpec.initialSpatialWord α).length u₀ y
              (ClaySpec.initialSpatialWord α).get) by
          funext y
          exact SemanticGap.iteratedSpatialDirectional_eq_iteratedFDeriv
            hu₀ (ClaySpec.initialSpatialWord α) y]
        exact (ContDiff.contDiff_iteratedFDeriv le_top hu₀).clm_apply
          contDiff_const
      exact SemanticGap.fderiv_component_basic
        (hs.differentiable (by simp) x) i (ClaySpec.spatialBasis j)

/-- Comparator's stronger full-jet decay immediately gives LeanDojo's displayed
coordinate-word decay, via the already-paid frozen-Clay directional bound. -/
theorem comparatorInitialDecay_to_leanDojo
    {u₀ : R3 → R3}
    (h : NavierStokes.Comparator.InitialVelocityConditionDecay u₀) :
    NavierStokesOnR3.SmoothRapidDecayInitial u₀ := by
  refine ⟨h.smooth, ?_⟩
  intro α K
  obtain ⟨C, hC0, hC⟩ := SemanticGap.initialRapidDecay_of_comparator h α K
  refine ⟨max C 1, by positivity, ?_⟩
  intro x
  rw [leanDojo_spatialDerivativeVector_eq_clay h.smooth α x]
  calc
    ‖ClaySpec.iteratedSpatialDirectional
        (ClaySpec.initialSpatialWord α) u₀ x‖
        ≤ C / (1 + ‖x‖) ^ K := hC x
    _ ≤ max C 1 / (1 + ‖x‖) ^ K := by
      exact div_le_div_of_nonneg_right (le_max_left C 1) (by positivity)

/-- Whole-space comparator initial data is now literally LeanDojo admissible
initial data. -/
theorem comparatorInitialDecayData_to_leanDojo
    {u₀ : R3 → R3}
    (h : NavierStokes.Comparator.InitialVelocityConditionDecay u₀) :
    NavierStokesOnR3.SmoothRapidDecayInitial u₀ ∧
      NavierStokesOnR3.DivergenceFreeInitial u₀ :=
  ⟨comparatorInitialDecay_to_leanDojo h,
    comparatorInitialDivergence_to_leanDojo h.toInitialVelocityCondition⟩

/-!
The remaining implementation in this module is deliberately theorem-level:

* comparator force jet/periodicity -> LeanDojo force hypotheses under
  `comparatorForceToLean`;
* LeanDojo `GlobalSmoothSolution` -> comparator solution under the exact field
  round-trips, including the `t=0` boundary extension;
* contradiction with `literalClayC` / `literalClayD`, yielding the literal
  `MillenniumNavierStokes.FeffermanC/D` terms.

No proposition-level weld structure is used by these completed data lemmas.
-/

end DASHILiteralClayNS

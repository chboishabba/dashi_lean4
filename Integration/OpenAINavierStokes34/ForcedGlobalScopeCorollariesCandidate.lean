import NavierStokes.ComparatorSolution

/-!
# Bidirectional DASHI / OpenAI Navier--Stokes scope cut

Original mathematical construction: OpenAI (September 2026).
External comparator definitions: FormalConjectures authors; see source
attribution in NavierStokes.ComparatorDefinitions.
DASHI contribution: explicit non-promotion corollaries from the very
same external Comparator (C) and (D) theorem statements.

This is an *external Lean 4.34.0-rc2 staging file*, NOT imported into
native DASHI Lean 4.28 and NOT checked on this exact branch.

Both corollaries refute a UNIVERSAL SMOOTH-FORCING global solution
statement. They say nothing against the strictly f=0 periodic R736
strategy. In particular, this is not a new blow-up construction.
-/

set_option autoImplicit false
noncomputable section

namespace DASHI.OpenAINavierStokes
open NavierStokes.Comparator

abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- The original external option D witness rules out the universal
FORCED torus version, with the comparator's own data and quantifiers.
This implication is not about the unforced B statement. -/
theorem no_universal_forced_periodic_global
    (ν : ℝ) (hν : 0 < ν) :
    ¬ (∀ (u₀ : R3 → R3) (f : R3 → ℝ → R3),
        InitialVelocityConditionPeriodic u₀ →
        ForceConditionPeriodic f →
        ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic ν u₀ f v p) := by
  intro hall
  obtain ⟨u₀, f, hu, hf, hno⟩ :=
    NavierStokes.Comparator.navier_stokes_breakdown_periodic ν hν
  exact hno (hall u₀ f hu hf)

/-- Whole-space option C provides the corresponding non-universal-forced
statement with the *actual comparator uniform-energy solution class*.
It does not assert failure of every possible weaker solution notion. -/
theorem no_universal_forced_R3_global_energy
    (ν : ℝ) (hν : 0 < ν) :
    ¬ (∀ (u₀ : R3 → R3) (f : R3 → ℝ → R3),
        InitialVelocityConditionDecay u₀ →
        ForceConditionDecay f →
        ∃ v p, NavierStokesExistenceAndSmoothnessRn ν u₀ f v p) := by
  intro hall
  obtain ⟨u₀, f, hu, hf, hno⟩ :=
    NavierStokes.Comparator.navier_stokes_breakdown_R3 ν hν
  exact hno (hall u₀ f hu hf)

/-- Reverse direction: an actual unforced no-solution datum gives a forced
option-D counterexample, IF zero forcing meets the comparator's force
hypotheses. This does not construct that unforced datum. -/
theorem unforced_no_solution_to_forced_periodic_breakdown
    (ν : ℝ) (u₀ : R3 → R3)
    (hInitial : InitialVelocityConditionPeriodic u₀)
    (hZeroForce : ForceConditionPeriodic (fun _ _ => (0 : R3)))
    (hNoGlobal :
      ¬ (∃ v p,
          NavierStokesExistenceAndSmoothnessPeriodic
            ν u₀ (fun _ _ => (0 : R3)) v p)) :
    ∃ (u : R3 → R3) (f : R3 → ℝ → R3),
      InitialVelocityConditionPeriodic u ∧
      ForceConditionPeriodic f ∧
      ¬ (∃ v p, NavierStokesExistenceAndSmoothnessPeriodic ν u f v p) :=
  ⟨u₀, (fun _ _ => 0), hInitial, hZeroForce, hNoGlobal⟩

/-- Same reverse boundary for the R³ class with uniform-energy solutions. -/
theorem unforced_no_solution_to_forced_R3_breakdown
    (ν : ℝ) (u₀ : R3 → R3)
    (hInitial : InitialVelocityConditionDecay u₀)
    (hZeroForce : ForceConditionDecay (fun _ _ => (0 : R3)))
    (hNoGlobal :
      ¬ (∃ v p,
          NavierStokesExistenceAndSmoothnessRn
            ν u₀ (fun _ _ => (0 : R3)) v p)) :
    ∃ (u : R3 → R3) (f : R3 → ℝ → R3),
      InitialVelocityConditionDecay u ∧
      ForceConditionDecay f ∧
      ¬ (∃ v p, NavierStokesExistenceAndSmoothnessRn ν u f v p) :=
  ⟨u₀, (fun _ _ => 0), hInitial, hZeroForce, hNoGlobal⟩

#print axioms DASHI.OpenAINavierStokes.no_universal_forced_periodic_global
#print axioms DASHI.OpenAINavierStokes.no_universal_forced_R3_global_energy

end DASHI.OpenAINavierStokes

import LeanDojoCoordinateWordJet
import LeanDojoForceTransport
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Quantitative force-decay transport

Comparator `ForceConditionDecay` controls the operator norm of the complete
Frechet jet on the product half-space. LeanDojo asks only for coordinate-word
evaluations of the transported jet. The exact spacetime linear equivalence and
the coordinate-word theorem pay the latter without a new fluid estimate.
-/

noncomputable section

open Filter Set
open ClaySpec NavierStokes NavierStokesOnR3
open scoped ContDiff

namespace DASHILiteralClayNS

theorem spacetimeDerivativeVector_eq_fullJet_apply
    {f : ForceField 3}
    (hf : ContDiffOn ℝ ∞ f (global_spacetime_domain 3))
    (α : List (Fin 3)) (m : ℕ) (z : Spacetime3)
    (hz : 0 < time z) :
    NavierStokesOnR3.spacetime_derivative_vector f α m z =
      iteratedFDeriv ℝ
        ((List.replicate m (0 : Fin 4) ++ α.map Fin.succ).length)
        f z
        (coordinateWordDirections
          (List.replicate m (0 : Fin 4) ++ α.map Fin.succ)) := by
  let idx : List (Fin 4) := List.replicate m (0 : Fin 4) ++ α.map Fin.succ
  have hfAt : ContDiffAt ℝ ∞ f z := contDiffAt_of_global_time_pos hf hz
  ext i
  have hcomp :=
    (EuclideanSpace.proj i).iteratedFDeriv_comp_left
      hfAt (i := idx.length) (by simp)
  have hscalar :
      ContDiffAt ℝ (idx.length + 1 : ℕ) (fun y => f y i) z := by
    exact ((hfAt.continuousLinearMap (EuclideanSpace.proj i)).of_le (by simp))
  change iterated_partial_deriv (n := 4) idx (fun y => f y i) z = _
  rw [iteratedPartialDeriv_eq_iteratedFDeriv_apply idx z hscalar]
  have happ := congrArg (fun L => L (coordinateWordDirections idx)) hcomp
  simpa [idx, Function.comp_def] using happ

theorem norm_spacetimeDerivativeVector_le_fullJet
    {f : ForceField 3}
    (hf : ContDiffOn ℝ ∞ f (global_spacetime_domain 3))
    (α : List (Fin 3)) (m : ℕ) (z : Spacetime3)
    (hz : 0 < time z) :
    ‖NavierStokesOnR3.spacetime_derivative_vector f α m z‖ ≤
      ‖iteratedFDeriv ℝ
        ((List.replicate m (0 : Fin 4) ++ α.map Fin.succ).length) f z‖ := by
  rw [spacetimeDerivativeVector_eq_fullJet_apply hf α m z hz]
  calc
    ‖iteratedFDeriv ℝ
        ((List.replicate m (0 : Fin 4) ++ α.map Fin.succ).length) f z
        (coordinateWordDirections
          (List.replicate m (0 : Fin 4) ++ α.map Fin.succ))‖ ≤
      ‖iteratedFDeriv ℝ
        ((List.replicate m (0 : Fin 4) ++ α.map Fin.succ).length) f z‖ *
        ∏ k : Fin ((List.replicate m (0 : Fin 4) ++ α.map Fin.succ).length),
          ‖coordinateWordDirections
            (List.replicate m (0 : Fin 4) ++ α.map Fin.succ) k‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ = _ := by
      simp [coordinateWordDirections, standard_basis]

theorem norm_targetJet_le_sourceJet
    {f : R3 → ℝ → R3}
    (hf : NavierStokes.Comparator.ForceCondition f)
    (N : ℕ) (z : Spacetime3) (hz : z ∈ global_spacetime_domain 3) :
    ‖iteratedFDerivWithin ℝ N (comparatorForceToLean f)
        (global_spacetime_domain 3) z‖ ≤
      ‖iteratedFDerivWithin ℝ N (Function.uncurry f)
          nonnegativeTime (leanSpacetimeToPair z)‖ *
        ‖pairLeanSpacetimeContinuousLinearEquiv.symm.toContinuousLinearMap‖ ^ N := by
  rw [iteratedFDerivWithin_comparatorFieldToLean hf.smooth N z hz]
  exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _

theorem comparatorForceDecay_to_leanDojo
    {f : R3 → ℝ → R3}
    (h : NavierStokes.Comparator.ForceConditionDecay f) :
    NavierStokesOnR3.SmoothRapidDecayForce (comparatorForceToLean f) := by
  refine ⟨comparatorDecayForce_smooth h, ?_⟩
  intro α m K
  let idx : List (Fin 4) := List.replicate m (0 : Fin 4) ++ α.map Fin.succ
  obtain ⟨C, hC⟩ := h.decay idx.length (K : ℝ)
  let A : ℝ := ‖pairLeanSpacetimeContinuousLinearEquiv.symm.toContinuousLinearMap‖ ^ idx.length
  refine ⟨max (C * A) 1, by positivity, ?_⟩
  intro z hz
  have hzdom : z ∈ global_spacetime_domain 3 := le_of_lt hz
  have htargetAt : ContDiffAt ℝ idx.length (comparatorForceToLean f) z :=
    (contDiffAt_of_global_time_pos (comparatorDecayForce_smooth h) hz).of_le (by simp)
  calc
    ‖NavierStokesOnR3.spacetime_derivative_vector
        (comparatorForceToLean f) α m z‖ ≤
      ‖iteratedFDeriv ℝ idx.length (comparatorForceToLean f) z‖ := by
        simpa [idx] using
          norm_spacetimeDerivativeVector_le_fullJet
            (comparatorDecayForce_smooth h) α m z hz
    _ = ‖iteratedFDerivWithin ℝ idx.length (comparatorForceToLean f)
          (global_spacetime_domain 3) z‖ := by
        rw [iteratedFDerivWithin_eq_iteratedFDeriv
          uniqueDiffOn_leanDojoGlobal htargetAt hzdom]
    _ ≤ ‖iteratedFDerivWithin ℝ idx.length (Function.uncurry f)
          nonnegativeTime (leanSpacetimeToPair z)‖ * A := by
        simpa [A] using norm_targetJet_le_sourceJet h.toForceCondition idx.length z hzdom
    _ ≤ (C / (1 + ‖space z‖ + time z) ^ K) * A := by
        gcongr
        simpa [SemanticGap.nonnegativeTime_eq, leanSpacetimeToPair, time] using
          hC (space z) (time z) (le_of_lt hz)
    _ = (C * A) / (1 + ‖space z‖ + z 0) ^ K := by
        simp [time]
        ring
    _ ≤ max (C * A) 1 / (1 + ‖space z‖ + z 0) ^ K := by
        exact div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)

theorem comparatorPeriodicForceDecay_to_leanDojo
    {f : R3 → ℝ → R3}
    (h : NavierStokes.Comparator.ForceConditionPeriodic f) :
    NavierStokesPeriodic.PeriodicForceDecay (comparatorForceToLean f) := by
  refine ⟨comparatorForceSmooth_to_leanDojo h.toForceCondition, ?_⟩
  intro α m K
  let idx : List (Fin 4) := List.replicate m (0 : Fin 4) ++ α.map Fin.succ
  obtain ⟨C, hC⟩ := h.decay idx.length (K : ℝ)
  let A : ℝ := ‖pairLeanSpacetimeContinuousLinearEquiv.symm.toContinuousLinearMap‖ ^ idx.length
  refine ⟨max (C * A) 1, by positivity, ?_⟩
  intro z hz
  have hzdom : z ∈ global_spacetime_domain 3 := le_of_lt hz
  have htargetAt : ContDiffAt ℝ idx.length (comparatorForceToLean f) z :=
    (contDiffAt_of_global_time_pos
      (comparatorForceSmooth_to_leanDojo h.toForceCondition) hz).of_le (by simp)
  calc
    ‖NavierStokesOnR3.spacetime_derivative_vector
        (comparatorForceToLean f) α m z‖ ≤
      ‖iteratedFDeriv ℝ idx.length (comparatorForceToLean f) z‖ := by
        simpa [idx] using
          norm_spacetimeDerivativeVector_le_fullJet
            (comparatorForceSmooth_to_leanDojo h.toForceCondition) α m z hz
    _ = ‖iteratedFDerivWithin ℝ idx.length (comparatorForceToLean f)
          (global_spacetime_domain 3) z‖ := by
        rw [iteratedFDerivWithin_eq_iteratedFDeriv
          uniqueDiffOn_leanDojoGlobal htargetAt hzdom]
    _ ≤ ‖iteratedFDerivWithin ℝ idx.length (Function.uncurry f)
          nonnegativeTime (leanSpacetimeToPair z)‖ * A := by
        simpa [A] using norm_targetJet_le_sourceJet h.toForceCondition idx.length z hzdom
    _ ≤ (C / (1 + time z) ^ K) * A := by
        gcongr
        simpa [SemanticGap.nonnegativeTime_eq, leanSpacetimeToPair, time] using
          hC (space z) (time z) (le_of_lt hz)
    _ = (C * A) / (1 + |z 0|) ^ K := by
        have habs : |z 0| = z 0 := abs_of_pos hz
        rw [habs]
        simp [time]
        ring
    _ ≤ max (C * A) 1 / (1 + |z 0|) ^ K := by
        exact div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)

end DASHILiteralClayNS

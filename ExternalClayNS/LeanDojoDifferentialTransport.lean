import LeanDojoJetTransport
import Mathlib.Analysis.Calculus.FDeriv.Basic

noncomputable section

open ClaySpec
open NavierStokes

namespace DASHILiteralClayNS

theorem leanDojoGlobal_mem_nhds_of_time_pos
    (z : Spacetime3) (hz : 0 < time z) :
    global_spacetime_domain 3 ∈ 𝓝 z := by
  have hopen : IsOpen {w : Spacetime3 | 0 < time w} :=
    isOpen_lt continuous_const (continuous_apply (0 : Fin 4))
  have hmem : z ∈ {w : Spacetime3 | 0 < time w} := hz
  refine Filter.mem_of_superset (hopen.mem_nhds hmem) ?_
  intro w hw
  exact le_of_lt hw

theorem nonnegativeTime_mem_nhds_of_pos
    (q : SpaceTime) (hq : 0 < q.2) :
    nonnegativeTime ∈ 𝓝 q := by
  have hopen : IsOpen {w : SpaceTime | 0 < w.2} :=
    isOpen_lt continuous_const continuous_snd
  have hmem : q ∈ {w : SpaceTime | 0 < w.2} := hq
  refine Filter.mem_of_superset (hopen.mem_nhds hmem) ?_
  intro w hw
  exact le_of_lt hw

theorem contDiffAt_of_global_time_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Spacetime3 → E}
    (hf : ContDiffOn ℝ ∞ f (global_spacetime_domain 3))
    {z : Spacetime3} (hz : 0 < time z) :
    ContDiffAt ℝ ∞ f z :=
  (hf z (le_of_lt hz)).contDiffAt (leanDojoGlobal_mem_nhds_of_time_pos z hz)

theorem fderivWithin_global_eq_fderiv_of_time_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Spacetime3 → E}
    (hf : ContDiffOn ℝ ∞ f (global_spacetime_domain 3))
    {z : Spacetime3} (hz : 0 < time z) :
    fderivWithin ℝ f (global_spacetime_domain 3) z = fderiv ℝ f z := by
  exact fderivWithin_of_mem_nhds (leanDojoGlobal_mem_nhds_of_time_pos z hz)

theorem fderiv_pullback_eq_leanDojo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Spacetime3 → E}
    (hf : ContDiffOn ℝ ∞ f (global_spacetime_domain 3))
    (q : SpaceTime) (hq : 0 < q.2) (v : SpaceTime) :
    fderiv ℝ (Function.uncurry (leanFieldToComparator f)) q v =
      fderiv ℝ f (pairToLeanSpacetime q) (pairToLeanSpacetime v) := by
  have hz : 0 < time (pairToLeanSpacetime q) := by simpa using hq
  have hdiff : DifferentiableAt ℝ f (pairToLeanSpacetime q) :=
    (contDiffAt_of_global_time_pos hf hz).differentiable (by simp)
  have hpair : DifferentiableAt ℝ pairToLeanSpacetime q :=
    pairLeanSpacetimeContinuousLinearEquiv.differentiableAt
  have hcomp := fderiv_comp q hdiff hpair
  have happ := congrArg (fun L => L v) hcomp
  have hfpair : fderiv ℝ pairToLeanSpacetime q =
      pairLeanSpacetimeContinuousLinearEquiv.toContinuousLinearMap :=
    pairLeanSpacetimeContinuousLinearEquiv.toContinuousLinearMap.fderiv
  rw [hfpair] at happ
  simpa [leanFieldToComparator_uncurry_eq_comp, Function.comp_def] using happ

theorem fderiv_pullback_time_eq_leanDojo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Spacetime3 → E}
    (hf : ContDiffOn ℝ ∞ f (global_spacetime_domain 3))
    (q : SpaceTime) (hq : 0 < q.2) :
    fderiv ℝ (Function.uncurry (leanFieldToComparator f)) q ClaySpec.timeDirection =
      fderiv ℝ f (pairToLeanSpacetime q) (standard_basis (n := 4) (0 : Fin 4)) := by
  rw [fderiv_pullback_eq_leanDojo hf q hq]
  simp

theorem fderiv_pullback_space_eq_leanDojo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Spacetime3 → E}
    (hf : ContDiffOn ℝ ∞ f (global_spacetime_domain 3))
    (q : SpaceTime) (hq : 0 < q.2) (i : Fin 3) :
    fderiv ℝ (Function.uncurry (leanFieldToComparator f)) q (ClaySpec.spatialDirection i) =
      fderiv ℝ f (pairToLeanSpacetime q) (standard_basis (n := 4) i.succ) := by
  rw [fderiv_pullback_eq_leanDojo hf q hq]
  simp

theorem clayPartialTime_pullback_eq_leanDojo
    {f : Spacetime3 → ℝ}
    (hf : ContDiffOn ℝ ∞ f (global_spacetime_domain 3))
    (q : SpaceTime) (hq : 0 < q.2) :
    ClaySpec.partialTime (Function.uncurry (leanFieldToComparator f)) q =
      partial_deriv (n := 4) (0 : Fin 4) f (pairToLeanSpacetime q) := by
  unfold ClaySpec.partialTime
  rw [fderivWithin_of_mem_nhds (nonnegativeTime_mem_nhds_of_pos q hq)]
  exact fderiv_pullback_time_eq_leanDojo hf q hq

theorem clayPartialSpace_pullback_eq_leanDojo
    {f : Spacetime3 → ℝ}
    (hf : ContDiffOn ℝ ∞ f (global_spacetime_domain 3))
    (q : SpaceTime) (hq : 0 < q.2) (i : Fin 3) :
    ClaySpec.partialSpace i (Function.uncurry (leanFieldToComparator f)) q =
      partial_deriv (n := 4) i.succ f (pairToLeanSpacetime q) := by
  unfold ClaySpec.partialSpace
  rw [fderivWithin_of_mem_nhds (nonnegativeTime_mem_nhds_of_pos q hq)]
  exact fderiv_pullback_space_eq_leanDojo hf q hq i

end DASHILiteralClayNS

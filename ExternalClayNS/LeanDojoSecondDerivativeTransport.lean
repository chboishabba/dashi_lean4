import LeanDojoDifferentialTransport
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

noncomputable section

open ClaySpec
open NavierStokes

namespace DASHILiteralClayNS

theorem leanDojo_secondPartial_eq_iteratedFDeriv
    {f : Spacetime3 → ℝ} {z : Spacetime3}
    (hf : ContDiffAt ℝ 2 f z) (i : Fin 4) :
    partial_deriv (n := 4) i
        (fun y => partial_deriv (n := 4) i f y) z =
      iteratedFDeriv ℝ 2 f z
        ![standard_basis (n := 4) i, standard_basis (n := 4) i] := by
  rw [iteratedFDeriv_two_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  rw [fderiv_clm_apply hd
    (differentiableAt_const (standard_basis (n := 4) i))]
  rfl

theorem claySecondPartial_pullback_eq_leanDojo
    {f : Spacetime3 → ℝ}
    (hf : ContDiffOn ℝ ∞ f (global_spacetime_domain 3))
    (q : SpaceTime) (hq : 0 < q.2) (i : Fin 3) :
    ClaySpec.partialSpace i
        (ClaySpec.partialSpace i
          (Function.uncurry (leanFieldToComparator f))) q =
      partial_deriv (n := 4) i.succ
        (fun y => partial_deriv (n := 4) i.succ f y)
        (pairToLeanSpacetime q) := by
  let g : SpaceTime → ℝ := Function.uncurry (leanFieldToComparator f)
  have hg : ContDiffOn ℝ ∞ g nonnegativeTime :=
    contDiffOn_leanFieldToComparator hf
  have hq0 : q ∈ nonnegativeTime := le_of_lt hq
  have hz0 : pairToLeanSpacetime q ∈ global_spacetime_domain 3 :=
    (pairToLeanSpacetime_nonnegative_iff q).2 hq0
  have hzpos : 0 < time (pairToLeanSpacetime q) := by simpa using hq
  have hdir := SemanticGap.iteratedDirectionalWithin_eq_iteratedFDerivWithin
    hg [ClaySpec.spatialDirection i, ClaySpec.spatialDirection i] q hq0
  have hjet := iteratedFDerivWithin_leanField_eq_pullback
    hf 2 (pairToLeanSpacetime q) hz0
  have hjetApply := congrArg
    (fun L => L ![standard_basis (n := 4) i.succ,
      standard_basis (n := 4) i.succ]) hjet
  have hamb :
      iteratedFDerivWithin ℝ 2 f (global_spacetime_domain 3)
          (pairToLeanSpacetime q) =
        iteratedFDeriv ℝ 2 f (pairToLeanSpacetime q) := by
    exact iteratedFDerivWithin_eq_iteratedFDeriv
      uniqueDiffOn_leanDojoGlobal
      ((contDiffAt_of_global_time_pos hf hzpos).of_le (by norm_num)) hz0
  have hcomponent :
      iteratedFDerivWithin ℝ 2 g nonnegativeTime q
          ![ClaySpec.spatialDirection i, ClaySpec.spatialDirection i] =
        iteratedFDeriv ℝ 2 f (pairToLeanSpacetime q)
          ![standard_basis (n := 4) i.succ,
            standard_basis (n := 4) i.succ] := by
    rw [hamb] at hjetApply
    simpa [g, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      leanSpacetimeToPair_spatialBasis] using hjetApply.symm
  calc
    ClaySpec.partialSpace i (ClaySpec.partialSpace i g) q =
        ClaySpec.iteratedDirectionalWithin
          [ClaySpec.spatialDirection i, ClaySpec.spatialDirection i] g q := by rfl
    _ = iteratedFDerivWithin ℝ 2 g nonnegativeTime q
          ![ClaySpec.spatialDirection i, ClaySpec.spatialDirection i] := by
          simpa using hdir
    _ = iteratedFDeriv ℝ 2 f (pairToLeanSpacetime q)
          ![standard_basis (n := 4) i.succ,
            standard_basis (n := 4) i.succ] := hcomponent
    _ = partial_deriv (n := 4) i.succ
          (fun y => partial_deriv (n := 4) i.succ f y)
          (pairToLeanSpacetime q) := by
          symm
          exact leanDojo_secondPartial_eq_iteratedFDeriv
            ((contDiffAt_of_global_time_pos hf hzpos).of_le (by norm_num)) i.succ

end DASHILiteralClayNS

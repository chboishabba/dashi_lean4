import Synthesis.NavierStokesOriginalRealitySymmetryExact
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Finite original signed cube as a real Banach-space ODE. No
continuum or uniform critical-norm claim. All input addresses, including
zero, remain in the same cutoffModes carrier. -/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open scoped BigOperators
noncomputable section

abbrev CutIndex (N : ℕ) := {k : Lattice // k ∈ cutoffModes N}
abbrev CutState (N : ℕ) := CutIndex N → CVec3

def cutExtend (N : ℕ) (u : CutState N) (k : Vec3) : CVec3 :=
  if h : ∃ p : CutIndex N, embedMode p.1=k then u (Classical.choose h) else 0

theorem cutExtend_at (N : ℕ) (u : CutState N) (p : CutIndex N) :
    cutExtend N u (embedMode p.1)=u p := by
  classical
  have h : ∃ q : CutIndex N, embedMode q.1=embedMode p.1 := ⟨p,rfl⟩
  have he : Classical.choose h=p :=
    Subtype.ext (embedMode_injective (Classical.choose_spec h))
  simp [cutExtend,h,he]

def cutRHS (N : ℕ) (ν : ℝ) (u : CutState N) : CutState N :=
  fun p i => -((ν*massSq (embedMode p.1):ℝ):ℂ)*u p i+
    galerkinForce N (fun k _=>cutExtend N u k) (embedMode p.1) 0 i

/-- The original force is a finite polynomial in the actual state.
The cutoff and resonance decisions are constants as u varies. -/
theorem cutRHS_contDiff (N : ℕ) (ν : ℝ) :
    ContDiff ℝ 1 (cutRHS N ν) := by
  classical
  apply contDiff_pi.mpr
  intro p
  apply contDiff_pi.mpr
  intro i
  have he (k : Vec3) (j : Fin 3) :
      ContDiff ℝ 1 (fun u : CutState N=>cutExtend N u k j) := by
    unfold cutExtend
    split
    · fun_prop
    · fun_prop
  unfold cutRHS galerkinForce
  split
  · apply ContDiff.add
    · fun_prop
    · apply contDiff_finset_sum
      intro a ha
      split
      · unfold orderedRHS lerayVector outputDot
        simp only [Fin.sum_univ_three]
        fun_prop
      · fun_prop
  · simp only [add_zero]
    fun_prop

/-- Local existence at every finite original state, obtained from
the actual polynomial RHS and Mathlib Picard–Lindelöf. -/
theorem cut_local_exists (N : ℕ) (ν : ℝ) (u₀ : CutState N) :
    ∃ U : ℝ → CutState N, U 0=u₀ ∧
      ∃ ε>0, ∀ t∈Set.Ioo (-ε) ε,
        HasDerivAt U (cutRHS N ν (U t)) t := by
  simpa using (cutRHS_contDiff N ν).contDiffAt
    (x:=u₀) |>.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ (0:ℝ)

/-- Finite state trajectory is an original modal solution after zero
extension, including modes outside the retained cube. -/
theorem cut_trajectory_modal (N : ℕ) (ν : ℝ) (U : ℝ → CutState N)
    (t : ℝ) (h : HasDerivAt U (cutRHS N ν (U t)) t)
    (k : Vec3) (i : Fin 3) :
    HasDerivAt (fun s=>cutExtend N (U s) k i)
      (-((ν*massSq k:ℝ):ℂ)*cutExtend N (U t) k i+
        galerkinForce N (fun k s=>cutExtend N (U s) k) k t i) t := by
  classical
  by_cases hk : ∃ p : CutIndex N, embedMode p.1=k
  · obtain ⟨p,rfl⟩ := hk
    let E : CutState N →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.proj p)
    have hd := E.hasFDerivAt.comp_hasDerivAt h
    simpa [E,cutRHS,cutExtend_at,galerkinForce] using hd
  · have hn : k∉(outputModes N).image embedMode := by
      intro hm
      obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hm
      exact hk ⟨⟨p,(Finset.mem_erase.mp hp).2⟩,he⟩
    simp [cutExtend,hk,galerkinForce,hn]

/-- Actual reflected curve obeys the same original modal ODE. -/
theorem reflected_modal_derivative (N : ℕ) (ν : ℝ)
    (U : Vec3 → ℝ → CVec3) (t : ℝ)
    (h : ∀ k i,HasDerivAt (fun s=>U k s i)
      (-((ν*massSq k:ℝ):ℂ)*U k t i+galerkinForce N U k t i) t)
    (k : Vec3) (i : Fin 3) :
    HasDerivAt (fun s=>realReflect U k s i)
      (-((ν*massSq k:ℝ):ℂ)*realReflect U k t i+
        galerkinForce N (realReflect U) k t i) t := by
  have hm : massSq (-k)=massSq k := by
    simp [massSq,neg_sq]
  have hd := (h (-k) i).star
  rw [actual_force_realReflect]
  simpa [realReflect,hm,star_add,star_mul,star_neg] using hd

/-- On every actual finite closed ball, smoothness gives a Lipschitz
constant. This is local-in-state and not uniform in N. -/
theorem cut_rhs_lipschitz_on_ball (N : ℕ) (ν : ℝ)
    (c : CutState N) (R : ℝ) :
    ∃ K : NNReal, LipschitzOnWith K (cutRHS N ν) (Metric.closedBall c R) :=
  (cutRHS_contDiff N ν).contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_closedBall c R) (isCompact_closedBall c R)

end
end DASHI.NavierStokes.PhysicalMixed

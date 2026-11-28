import Synthesis.NavierStokesOriginalRealitySymmetryExact
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Pi

/-! Finite original signed cube as a real Banach-space ODE. No
continuum or uniform critical-norm claim. All input addresses, including
zero, remain in the same cutoffModes carrier. -/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open scoped BigOperators
open Classical
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
  have hc : ContDiffAt ℝ 1 (cutRHS N ν) u₀ := (cutRHS_contDiff N ν).contDiffAt
  simpa using hc.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ (0:ℝ)

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

/-- The negated index belongs to exactly the same original signed cube. -/
def cutNeg (N : ℕ) (p : CutIndex N) : CutIndex N :=
  ⟨-p.1,cutoff_neg N p.1 p.2⟩

def cutReflect (N : ℕ) (u : CutState N) : CutState N :=
  fun p i=>star (u (cutNeg N p) i)

theorem cutExtend_reflect (N : ℕ) (u : CutState N) (k : Vec3) :
    cutExtend N (cutReflect N u) k =
      fun i=>star (cutExtend N u (-k) i) := by
  classical
  by_cases hk : ∃ p : CutIndex N, embedMode p.1=k
  · obtain ⟨p,rfl⟩ := hk
    rw [cutExtend_at,← embedMode_neg p.1]
    change cutReflect N u p=fun i=>star (cutExtend N u (embedMode (cutNeg N p).1) i)
    rw [cutExtend_at]
    rfl
  · have hn : ¬ ∃ p : CutIndex N, embedMode p.1= -k := by
      rintro ⟨p,hp⟩
      apply hk
      exact ⟨cutNeg N p,by change embedMode (-p.1)=k; rw [embedMode_neg,hp,neg_neg]⟩
    simp [cutExtend,hk,hn]

/-- Reflect the finite state trajectory itself, on the same Banach
carrier. Modal reflection and finite-coordinate derivative are paid
by the previously derived literal modal force. -/
theorem cut_reflect_derivative (N : ℕ) (ν : ℝ)
    (U : ℝ → CutState N) (t : ℝ)
    (hd : HasDerivAt U (cutRHS N ν (U t)) t) :
    HasDerivAt (fun s=>cutReflect N (U s))
      (cutRHS N ν (cutReflect N (U t))) t := by
  apply hasDerivAt_pi.mpr
  intro p
  apply hasDerivAt_pi.mpr
  intro i
  have h := reflected_modal_derivative N ν
    (fun k s=>cutExtend N (U s) k) t
    (fun k i=>cut_trajectory_modal N ν U t hd k i)
    (embedMode p.1) i
  have he (k : Vec3) (s : ℝ) :
      realReflect (fun k s=>cutExtend N (U s) k) k s=
        cutExtend N (cutReflect N (U s)) k := by
    rw [cutExtend_reflect]
    rfl
  simp_rw [he] at h
  simpa [cutRHS,cutExtend_at,galerkinForce] using h

/-- Actual finite-state uniqueness on a common closed ball containing
both trajectories. The constant is produced by the original field,
not an assumed Lipschitz bound. -/
theorem cut_unique_on_ball (N : ℕ) (ν T : ℝ)
    (U V : ℝ → CutState N) (c : CutState N) (R : ℝ)
    (hU : ContinuousOn U (Set.Icc 0 T)) (hV : ContinuousOn V (Set.Icc 0 T))
    (dU : ∀ t∈Set.Ico 0 T,HasDerivAt U (cutRHS N ν (U t)) t)
    (dV : ∀ t∈Set.Ico 0 T,HasDerivAt V (cutRHS N ν (V t)) t)
    (bU : ∀ t∈Set.Ico 0 T,U t∈Metric.closedBall c R)
    (bV : ∀ t∈Set.Ico 0 T,V t∈Metric.closedBall c R)
    (h0 : U 0=V 0) : Set.EqOn U V (Set.Icc 0 T) := by
  obtain ⟨K,hK⟩ := cut_rhs_lipschitz_on_ball N ν c R
  exact ODE_solution_unique_of_mem_Icc_right
    (v:=fun _=>cutRHS N ν) (s:=fun _=>Metric.closedBall c R) (K:=K)
    (fun _ _=>hK) hU (fun t ht=>(dU t ht).hasDerivWithinAt) bU
    hV (fun t ht=>(dV t ht).hasDerivWithinAt) bV h0

/-- Reality preservation now follows from actual finite uniqueness.
Boundedness on a common finite closed ball is explicit; no claim of
a cutoff-uniform radius or critical-time ceiling. -/
theorem cut_reality_on_ball (N : ℕ) (ν T : ℝ)
    (U : ℝ → CutState N) (c : CutState N) (R : ℝ)
    (hU : ContinuousOn U (Set.Icc 0 T))
    (dU : ∀ t∈Set.Ico 0 T,HasDerivAt U (cutRHS N ν (U t)) t)
    (bU : ∀ t∈Set.Ico 0 T,U t∈Metric.closedBall c R)
    (bV : ∀ t∈Set.Ico 0 T,cutReflect N (U t)∈Metric.closedBall c R)
    (h0 : U 0=cutReflect N (U 0)) :
    ∀ t∈Set.Icc 0 T,U t=cutReflect N (U t) := by
  have hc : Continuous (cutReflect N) := by
    unfold cutReflect
    fun_prop
  exact cut_unique_on_ball N ν T U (fun s=>cutReflect N (U s)) c R hU
    (hc.comp_continuousOn hU) dU
    (fun t ht=>cut_reflect_derivative N ν U t (dU t ht)) bU bV h0

end
end DASHI.NavierStokes.PhysicalMixed

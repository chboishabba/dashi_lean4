import Synthesis.NavierStokesOriginalPeriodicEnergyFTCExact
import Mathlib.Analysis.ODE.PicardLindelof

/-!
Actual finite Galerkin local flow by Picard-Lindelöf on the literal
finite cube, with a zero extension to the real frequency carrier.
The original R71/R74 classical selected local existence is a donor,
not a second nonlinear field. All frequencies outside outputModes
remain zero by construction; zero mode is included in input enumeration
but has zero state. No cutoff-independent critical bound is asserted.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open scoped BigOperators
noncomputable section

abbrev Mode (N : ℕ) := {k // k∈outputModes N}
abbrev FiniteState (N : ℕ) := Mode N → CVec3

def zeroExtend {N : ℕ} (x : FiniteState N) (k : Vec3) : CVec3 :=
  if h : ∃ p : Mode N,embedMode p.1=k then x (Classical.choose h) else 0

theorem zeroExtend_at {N : ℕ} (x : FiniteState N) (p : Mode N) :
    zeroExtend x (embedMode p.1)=x p := by
  have h : ∃ q : Mode N,embedMode q.1=embedMode p.1 := ⟨p,rfl⟩
  unfold zeroExtend
  rw [dif_pos h]
  congr 1
  apply Subtype.ext
  exact embedMode_injective (Classical.choose_spec h)

theorem zeroExtend_outside {N : ℕ} (x : FiniteState N) (k : Vec3)
    (h : k∉(outputModes N).image embedMode) : zeroExtend x k=0 := by
  unfold zeroExtend
  apply dif_neg
  rintro ⟨p,hp⟩
  exact h (Finset.mem_image.mpr ⟨p.1,p.2,hp⟩)

theorem zeroExtend_mean {N : ℕ} (x : FiniteState N) :
    zeroExtend x (embedMode 0)=0 := by
  apply zeroExtend_outside
  intro h
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
  have hz := embedMode_injective he
  exact (Finset.mem_erase.mp hp).1 hz

def finiteForce (N : ℕ) (ν : ℝ) (x : FiniteState N) : FiniteState N :=
  fun p i => -((ν*massSq (embedMode p.1):ℝ):ℂ)*x p i+
    galerkinForce N (fun k _=>zeroExtend x k) (embedMode p.1) 0 i

/-- Evaluation of the zero extension is either an actual coordinate
projection or the zero map; there is no variable support decision in x. -/
theorem zeroExtend_contDiff (N : ℕ) (k : Vec3) (i : Fin 3) :
    ContDiff ℝ 1 (fun x : FiniteState N=>zeroExtend x k i) := by
  classical
  unfold zeroExtend
  by_cases h : ∃ p : Mode N,embedMode p.1=k
  · simp only [dif_pos h]
    fun_prop
  · simp only [dif_neg h,Pi.zero_apply]
    exact contDiff_const

theorem finiteForce_contDiff (N : ℕ) (ν : ℝ) :
    ContDiff ℝ 1 (finiteForce N ν) := by
  apply contDiff_pi.mpr
  intro p
  apply contDiff_pi.mpr
  intro i
  unfold finiteForce
  apply ContDiff.add
  · fun_prop
  · rw [show (fun x : FiniteState N =>
        galerkinForce N (fun k _=>zeroExtend x k) (embedMode p.1) 0 i)=
      (fun x=>∑ a ∈ orderedFibre N p.1,
        orderedRHS (embedMode p.1) (embedMode a.2)
          (zeroExtend x (embedMode a.1)) (zeroExtend x (embedMode a.2)) i) by
        funext x
        exact galerkinForce_eq_orderedFibre N _ p.1 p.2 0 i]
    apply ContDiff.sum
    intro a ha
    unfold orderedRHS lerayVector outputDot
    simp only [Fin.sum_univ_three]
    have h (k : Vec3) (j : Fin 3) :=
      zeroExtend_contDiff N k j
    fun_prop

theorem finite_local_solution (N : ℕ) (ν : ℝ) (x₀ : FiniteState N) :
    ∃ x : ℝ → FiniteState N, x 0=x₀ ∧ ∃ ε>0,
      ∀ t ∈ Set.Ioo (-ε) ε,HasDerivAt x (finiteForce N ν (x t)) t := by
  obtain ⟨x,hx,ε,hε,hd⟩ :=
    (finiteForce_contDiff N ν).contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  refine ⟨x,hx,ε,hε,?_⟩
  simpa using hd

/-- The local finite ODE is the original force on the real-frequency
zero extension, not just an abstract ODE with an assigned RHS. -/
theorem local_solution_zero_extension (N : ℕ) (ν : ℝ) (x₀ : FiniteState N) :
    ∃ U : Vec3 → ℝ → CVec3, (∀ k,U k 0=zeroExtend x₀ k) ∧
      (∀ t k,k∉(outputModes N).image embedMode → U k t=0) ∧
      ∃ ε>0,∀ t ∈ Set.Ioo (-ε) ε,∀ k i,
        HasDerivAt (fun s=>U k s i)
          (-((ν*massSq k:ℝ):ℂ)*U k t i+galerkinForce N U k t i) t := by
  obtain ⟨x,hx,ε,hε,hd⟩ := finite_local_solution N ν x₀
  let U := fun k t=>zeroExtend (x t) k
  refine ⟨U,fun k=>by simp [U,hx],fun t k hk=>zeroExtend_outside _ _ hk,ε,hε,?_⟩
  intro t ht k i
  by_cases hk : k∈(outputModes N).image embedMode
  · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hk
    let a : Mode N := ⟨p,hp⟩
    have hcoord : HasDerivAt (fun s=>x s a i) (finiteForce N ν (x t) a i) t :=
      ((ContinuousLinearMap.proj (R:=ℝ) i).hasFDerivAt.comp_hasDerivAt
        ((ContinuousLinearMap.proj (R:=ℝ) a).hasFDerivAt.comp_hasDerivAt (hd t ht)))
    simpa [U,finiteForce,a,zeroExtend_at,galerkinForce] using hcoord
  · have hz : ∀ s,U k s i=0 := by
      intro s
      simp [U,zeroExtend_outside _ _ hk]
    have hf : galerkinForce N U k t i=0 := by simp [galerkinForce,hk]
    simp only [hz,hf,mul_zero,add_zero]
    exact hasDerivAt_const t 0

end
end DASHI.NavierStokes.PhysicalMixed

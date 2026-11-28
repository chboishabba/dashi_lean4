import Synthesis.NavierStokesOriginalPhysicalInvarianceExact
import Mathlib.Analysis.ODE.Gronwall

/-! Conjugate reality is an involution of the entire finite vector field,
including states not already fixed by it. Local ODE uniqueness then
identifies the reflected trajectory with the original trajectory. -/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open scoped BigOperators Topology
open Filter
noncomputable section

def oppositeMode {N : ℕ} (p : Mode N) : Mode N :=
  ⟨-p.1, Finset.mem_erase.mpr
    ⟨neg_ne_zero.mpr (Finset.mem_erase.mp p.2).1,
      cutoff_neg N p.1 (Finset.mem_erase.mp p.2).2⟩⟩

theorem oppositeMode_involutive {N : ℕ} (p : Mode N) :
    oppositeMode (oppositeMode p)=p := by
  apply Subtype.ext
  simp [oppositeMode]

def reflectState {N : ℕ} (x : FiniteState N) : FiniteState N :=
  fun p i=>star (x (oppositeMode p) i)

theorem reflectState_involutive {N : ℕ} (x : FiniteState N) :
    reflectState (reflectState x)=x := by
  funext p i
  simp [reflectState,oppositeMode_involutive]

def reflectLinear (N : ℕ) : FiniteState N →L[ℝ] FiniteState N :=
  ContinuousLinearMap.pi fun p =>
    ContinuousLinearMap.pi fun i =>
      Complex.conjCLE.toContinuousLinearMap.comp
        ((ContinuousLinearMap.proj (R:=ℝ) i).comp
          (ContinuousLinearMap.proj (R:=ℝ) (oppositeMode p)))

theorem reflectLinear_apply (N : ℕ) (x : FiniteState N) :
    reflectLinear N x=reflectState x := by
  rfl

theorem zeroExtend_reflect {N : ℕ} (x : FiniteState N) (k : Lattice) (i : Fin 3) :
    zeroExtend (reflectState x) (embedMode k) i =
      star (zeroExtend x (embedMode (-k)) i) := by
  classical
  by_cases hk : k∈outputModes N
  · let p : Mode N := ⟨k,hk⟩
    change zeroExtend (reflectState x) (embedMode p.1) i =
      star (zeroExtend x (embedMode (oppositeMode p).1) i)
    rw [zeroExtend_at,zeroExtend_at]
    rfl
  · have hn : -k∉outputModes N := by
      intro h
      exact hk (by simpa using (oppositeMode (⟨-k,h⟩:Mode N)).2)
    have hout (q : Lattice) (hq : q∉outputModes N) :
        embedMode q∉(outputModes N).image embedMode := by
      intro h
      obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
      exact hq (embedMode_injective he ▸ hp)
    rw [zeroExtend_outside _ _ (hout k hk),zeroExtend_outside _ _ (hout (-k) hn)]
    simp

/-- Unlike fixed-state reality, this identity is equivariance for
arbitrary original source U. -/
theorem reflected_force (N : ℕ) (U : Vec3 → ℝ → CVec3)
    (k : Lattice) (hk : k∈outputModes N) (t : ℝ) (i : Fin 3) :
    galerkinForce N (fun q s j=>star (U (-q) s j)) (embedMode k) t i =
      star (galerkinForce N U (embedMode (-k)) t i) := by
  classical
  have hn := (oppositeMode (⟨k,hk⟩:Mode N)).2
  rw [galerkinForce_eq_orderedFibre N _ k hk,
    galerkinForce_eq_orderedFibre N _ (-k) hn,star_sum]
  apply Finset.sum_nbij' negPair negPair
  · exact negPair_fibre N k
  · intro a ha
    simpa using negPair_fibre N (-k) a ha
  · intro a _
    simp [negPair]
  · intro a _
    simp [negPair]
  · intro a _
    simp only [negPair,embedMode_neg]
    simpa using orderedRHS_reality (-embedMode k) (-embedMode a.2)
      (U (-embedMode a.1) t) (U (-embedMode a.2) t) i

theorem finiteForce_reflect (N : ℕ) (ν : ℝ) (x : FiniteState N) :
    finiteForce N ν (reflectState x)=reflectState (finiteForce N ν x) := by
  classical
  funext p i
  unfold finiteForce reflectState
  have hmass : massSq (embedMode (oppositeMode p).1)=massSq (embedMode p.1) := by
    simp [oppositeMode,embedMode_neg,massSq,Fin.sum_univ_three]
  rw [hmass,star_add,star_mul]
  simp only [star_neg,Complex.star_def,Complex.conj_ofReal]
  congr 1
  -- The force uses only the literal lattice inputs; extend the equality
  -- on those coordinates by congruence of the finite ordered sum.
  rw [← reflected_force N (fun k _=>zeroExtend x k) p.1 p.2 0 i]
  rw [galerkinForce_eq_orderedFibre N _ p.1 p.2,
    galerkinForce_eq_orderedFibre N _ p.1 p.2]
  apply Finset.sum_congr rfl
  intro a _
  congr 1 <;> funext j <;>
    simpa only [embedMode_neg] using zeroExtend_reflect x _ j

theorem local_reality_of_solution (N : ℕ) (ν : ℝ)
    (x : ℝ → FiniteState N) (h0 : reflectState (x 0)=x 0)
    (hd : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt x (finiteForce N ν (x t)) t) :
    ∀ᶠ t in 𝓝 (0:ℝ), reflectState (x t)=x t := by
  let F := finiteForce N ν
  let y : ℝ → FiniteState N := fun t=>reflectLinear N (x t)
  have hy0 : y 0=x 0 := by simpa [y,reflectLinear_apply] using h0
  have hy : ∀ᶠ t in 𝓝 (0:ℝ),HasDerivAt y (F (y t)) t := by
    filter_upwards [hd] with t ht
    have h := (reflectLinear N).hasFDerivAt.comp_hasDerivAt ht
    simpa [y,F,reflectLinear_apply,finiteForce_reflect] using h
  obtain ⟨K,S,hS,hLip⟩ :=
    (finiteForce_contDiff N ν).contDiffAt.exists_lipschitzOnWith (x:=x 0)
  have hxC : ContinuousAt x 0 := (hd.self_of_nhds).continuousAt
  have hyC : ContinuousAt y 0 := (hy.self_of_nhds).continuousAt
  have hxS : ∀ᶠ t in 𝓝 (0:ℝ),x t∈S := hxC hS
  have hyS : ∀ᶠ t in 𝓝 (0:ℝ),y t∈S := hyC (by rwa [hy0])
  have h := ODE_solution_unique_of_eventually (v:=fun _=>F) (s:=fun _=>S)
    (Filter.Eventually.of_forall fun _=>hLip) (hy.and hyS) (hd.and hxS) hy0
  simpa [y,reflectLinear_apply,Filter.EventuallyEq] using h

end
end DASHI.NavierStokes.PhysicalMixed

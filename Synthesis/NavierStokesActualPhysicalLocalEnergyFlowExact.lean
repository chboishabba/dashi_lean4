import Synthesis.NavierStokesOriginalRealityUniquenessExact

/-!
A nontrivial local interval of the actual finite Galerkin trajectory
with all three physical invariants and the exact energy FTC. No
globally defined continuous curve is required outside that interval.
The finite cutoff, initial state, signed force and trajectory are the
same throughout.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open MeasureTheory Metric Filter
open scoped Topology BigOperators
noncomputable section

theorem actual_physical_local_energy_flow (N : ℕ) (ν : ℝ)
    (x₀ : FiniteState N)
    (hr : reflectState x₀=x₀)
    (ht : ∀ k : Vec3,outputDot k (zeroExtend x₀ k)=0) :
    ∃ U : Vec3 → ℝ → CVec3, ∃ T>0,
      (∀ k,U k 0=zeroExtend x₀ k) ∧
      (∀ t∈Set.Icc 0 T,∀ k i,
        HasDerivAt (fun s=>U k s i)
          (-((ν*massSq k:ℝ):ℂ)*U k t i+galerkinForce N U k t i) t) ∧
      (∀ t∈Set.Icc 0 T,∀ k,outputDot k (U k t)=0) ∧
      (∀ t∈Set.Icc 0 T,∀ k : Lattice,∀ i,
        U (embedMode (-k)) t i=star (U (embedMode k) t i)) ∧
      (∀ t,U (embedMode 0) t=0) ∧
      (∀ t∈Set.Icc 0 T,
        periodicEnergy N U t+2*ν*(∫ s in 0..t,periodicDissipation N U s)=
          periodicEnergy N U 0) := by
  obtain ⟨x,hx,ε,hε,hd⟩ := finite_local_solution N ν x₀
  have hde : ∀ᶠ t in 𝓝 (0:ℝ),HasDerivAt x (finiteForce N ν (x t)) t := by
    filter_upwards [Ioo_mem_nhds (show -ε<0 by linarith) hε] with t h
    exact hd t h
  have h0 : reflectState (x 0)=x 0 := by rw [hx]; exact hr
  obtain ⟨δ,hδ,hre⟩ := eventually_nhds_iff_ball.mp
    (local_reality_of_solution N ν x h0 hde)
  let T := min ε δ/2
  have hT : 0<T := div_pos (lt_min hε hδ) (by norm_num)
  have hTε : T<ε := by
    have h := min_le_left ε δ
    dsimp [T]
    linarith
  have hTδ : T<δ := by
    have h := min_le_right ε δ
    dsimp [T]
    linarith
  let U := fun k s=>zeroExtend (x s) k
  have hu : ∀ k,U k 0=zeroExtend x₀ k := by intro k; simp [U,hx]
  have ho (t : ℝ) (hh : t∈Set.Icc 0 T) (k : Vec3) (i : Fin 3) :
      HasDerivAt (fun s=>U k s i)
        (-((ν*massSq k:ℝ):ℂ)*U k t i+galerkinForce N U k t i) t := by
    exact zeroExtend_ODE_of_derivative N ν x t
      (hd t ⟨by linarith [hh.1],hh.2.trans_lt hTε⟩) k i
  have htrans (t : ℝ) (hh : t∈Set.Icc 0 T) (k : Vec3) :
      outputDot k (U k t)=0 := by
    apply transverse_preserved N ν U t hh.1 k
    · rw [hu]; exact ht k
    · intro s hs i
      exact ho s ⟨hs.1,hs.2.trans hh.2⟩ k i
  have hreal (t : ℝ) (hh : t∈Set.Icc 0 T) (k : Lattice) (i : Fin 3) :
      U (embedMode (-k)) t i=star (U (embedMode k) t i) := by
    have hball : t∈ball (0:ℝ) δ := by
      rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hh.1]
      exact hh.2.trans_lt hTδ
    have h := zeroExtend_reflect (x t) (-k) i
    rw [hre t hball,neg_neg] at h
    exact h
  have hmean (t : ℝ) : U (embedMode 0) t=0 := zeroExtend_mean (x t)
  refine ⟨U,T,hT,hu,ho,htrans,hreal,hmean,?_⟩
  intro t hh
  have hI : Set.uIcc 0 t⊆Set.Icc 0 T := by
    rw [Set.uIcc_of_le hh.1]
    exact fun s hs=>⟨hs.1,hs.2.trans hh.2⟩
  apply periodic_energy_FTC_on_interval N ν U t
  · intro k i s hs
    exact (ho s (hI hs) k i).continuousAt.continuousWithinAt
  · exact fun s hs=>ho s (hI hs)
  · exact fun s hs k=>htrans s (hI hs) (embedMode k)
  · exact fun s hs=>hreal s (hI hs)
  · exact fun s _=>hmean s

end
end DASHI.NavierStokes.PhysicalMixed

import Synthesis.NavierStokesIntegratedConvolutionLimitExact

/-! Initial data and diagonal trajectories on the original lattice.
All finite data are literal restrictions of ONE initial Fourier state.
The zero extension and finite energy/dissipation budget are derived
from that state and the original energy theorem, not fresh premises.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open DASHI.NavierStokes.RealContinuation
open Set Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section

def initialProjection (u₀ : Lattice → CVec3) (N : ℕ) : FiniteState N :=
  fun p=>u₀ p.1

theorem initialProjection_at (u₀ : Lattice → CVec3) (N : ℕ)
    (k : Lattice) (hk : k∈outputModes N) :
    zeroExtend (initialProjection u₀ N) (embedMode k)=u₀ k :=
  zeroExtend_at (initialProjection u₀ N) ⟨k,hk⟩

theorem cutoff_eventually_contains (k : Lattice) (hk : k≠0)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) :
    ∀ᶠ n in atTop,k∈outputModes (σ n) := by
  let R : ℕ := ∑ i : Fin 3,(k i).natAbs
  have hR (i : Fin 3) : (k i).natAbs≤R :=
    Finset.single_le_sum (fun j _=>Nat.zero_le _) (Finset.mem_univ i)
  filter_upwards [hσ.tendsto_atTop.eventually_ge_atTop R] with n hn
  apply Finset.mem_erase.mpr
  refine ⟨hk,(mem_cutoffModes _ _).mpr fun i=>?_⟩
  have hh := (hR i).trans hn
  omega

theorem projection_reality (u₀ : Lattice → CVec3)
    (h : ∀ k i,u₀ (-k) i=star (u₀ k i)) (N : ℕ) :
    reflectState (initialProjection u₀ N)=initialProjection u₀ N := by
  funext p i
  simp [reflectState,initialProjection,oppositeMode,h]

theorem projection_transverse (u₀ : Lattice → CVec3)
    (h : ∀ k,outputDot (embedMode k) (u₀ k)=0) (N : ℕ) :
    ∀ k,outputDot k (zeroExtend (initialProjection u₀ N) k)=0 := by
  classical
  intro k
  by_cases hk : k∈(outputModes N).image embedMode
  · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hk
    rw [initialProjection_at _ _ _ hp]
    exact h p
  · rw [zeroExtend_outside _ _ hk]
    simp [outputDot]

theorem projection_energy_bound (u₀ : Lattice → CVec3) (B : ℝ)
    (hE : ∀ S : Finset Lattice,∑ k ∈ S,phaseMass (u₀ k)≤B) (N : ℕ) :
    stateEnergy (initialProjection u₀ N)≤B := by
  unfold stateEnergy periodicEnergy
  rw [show (∑ k ∈ outputModes N,realHermitian
      (zeroExtend (initialProjection u₀ N) (embedMode k))
      (zeroExtend (initialProjection u₀ N) (embedMode k))) =
      ∑ k ∈ outputModes N,phaseMass (u₀ k) by
    apply Finset.sum_congr rfl
    intro k hk
    rw [initialProjection_at _ _ _ hk,phaseMass_eq_energy]]
  exact hE _

theorem actual_weighted_integrated_budget (N : ℕ) (ν B T : ℝ)
    (hν : 0<ν) (hT : 0≤T)
    (x : ℝ → FiniteState N) (a : ℝ) (ha : a<0)
    (hr : reflectState (x 0)=x 0)
    (ht : ∀ k,outputDot k (zeroExtend (x 0) k)=0)
    (hE : stateEnergy (x 0)≤B)
    (hd : SolvesOn (finiteForce N ν) x (Ioi a))
    (S : Finset Lattice) :
    ∑ k ∈ S,(∫ t in 0..T,massSq (embedMode k)*phaseMass (zeroExtend (x t) (embedMode k)))≤B/(2*ν) := by
  let U := fun k t=>zeroExtend (x t) k
  have hc (k : Vec3) (i : Fin 3) :
      ContinuousOn (fun t=>U k t i) (uIcc 0 T) := by
    intro t ht'
    have hh : 0≤t := by rw [uIcc_of_le hT] at ht'; exact ht'.1
    exact (zeroExtend_ODE_of_derivative N ν x t (hd t (ha.trans_le hh)) k i).continuousAt.continuousWithinAt
  have hci (k : Lattice) : ContinuousOn (fun t=>massSq (embedMode k)*phaseMass (U (embedMode k) t)) (uIcc 0 T) := by
    apply ContinuousOn.const_mul
    apply phaseMass_continuous.comp_continuousOn
    exact continuousOn_pi.mpr (fun i=>hc (embedMode k) i)
  have henergy := energy_on_forward_interval N ν a (T+1) x ha (by linarith)
    hr ht (fun t ht'=>hd t ht'.1) T ⟨hT,by linarith⟩
  have hnon := stateEnergy_nonneg (x T)
  have hD : (∫ t in 0..T,periodicDissipation N U t)≤B/(2*ν) := by
    apply (le_div_iff₀ (by positivity : 0<2*ν)).mpr
    change stateEnergy (x T)+2*ν*(∫ t in 0..T,periodicDissipation N U t)=stateEnergy (x 0) at henergy
    linarith
  rw [← intervalIntegral.integral_finset_sum (fun k _=>(hci k).intervalIntegrable)]
  have hsum : ContinuousOn (fun t=>∑ k ∈ S,massSq (embedMode k)*phaseMass (U (embedMode k) t)) (uIcc 0 T) :=
    continuousOn_finset_sum _ fun k _=>hci k
  apply le_trans _ hD
  apply intervalIntegral.integral_mono_on hT hsum.intervalIntegrable
    (dissipation_continuousOn N T U hc).intervalIntegrable
  intro t _
  have h := zeroExtended_weighted_subset (x t) S (fun k=>massSq (embedMode k)) (fun k=>massSq_nonnegative _)
  simpa [periodicDissipation,phaseMass_eq_energy,U] using h

/-- One selected limit on the actual original time chart. Extend each
coordinate continuously to real time by clamping only OUTSIDE [0,T].
No endpoint or force is modified on the physical interval. -/
def chartClamp (T : ℝ) (hT : 0≤T) (t : ℝ) : TimeChart T :=
  ⟨min T (max 0 t),le_min hT (le_max_left _ _),min_le_left _ _⟩

theorem chartClamp_on (T : ℝ) (hT : 0≤T) (t : ℝ) (ht : t∈Icc 0 T) :
    (chartClamp T hT t:ℝ)=t := by
  simp [chartClamp,max_eq_right ht.1,min_eq_right ht.2]

theorem chartClamp_continuous (T : ℝ) (hT : 0≤T) :
    Continuous (chartClamp T hT) := by
  apply Continuous.subtype_mk
  fun_prop

def limitVelocity (T : ℝ) (hT : 0≤T)
    (g : ModalAddress → TimeChart T →ᵇ ℂ) (k : Lattice) (t : ℝ) : CVec3 :=
  fun i=>g (k,i) (chartClamp T hT t)

theorem limitVelocity_continuous (T : ℝ) (hT : 0≤T)
    (g : ModalAddress → TimeChart T →ᵇ ℂ) (k : Lattice) :
    Continuous (limitVelocity T hT g k) :=
  continuous_pi fun i=>(g (k,i)).continuous.comp (chartClamp_continuous T hT)

theorem modal_diagonal_pointwise (T : ℝ) (hT : 0≤T)
    (X : (N : ℕ) → ℝ → FiniteState N) (σ : ℕ → ℕ)
    (g : ModalAddress → TimeChart T →ᵇ ℂ)
    (hg : ∀ i,TendstoUniformly (fun n (t : TimeChart T)=>chartValue (X (σ n)) i t) (g i) atTop)
    (k : Lattice) (t : ℝ) (ht : t∈Icc 0 T) :
    Tendsto (fun n=>zeroExtend (X (σ n) t) (embedMode k)) atTop
      (𝓝 (limitVelocity T hT g k t)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have hh := (hg (k,i)).tendsto_at (chartClamp T hT t)
  simpa [chartValue,limitVelocity,chartClamp_on T hT t ht] using hh

/-- Actual initial recovery, including the original zero mode. -/
theorem modal_diagonal_initial (T : ℝ) (hT : 0≤T)
    (u₀ : Lattice → CVec3) (hmean : u₀ 0=0)
    (X : (N : ℕ) → ℝ → FiniteState N) (hx : ∀ N,X N 0=initialProjection u₀ N)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (g : ModalAddress → TimeChart T →ᵇ ℂ)
    (hg : ∀ i,TendstoUniformly (fun n (t : TimeChart T)=>chartValue (X (σ n)) i t) (g i) atTop) :
    ∀ k,limitVelocity T hT g k 0=u₀ k := by
  intro k
  have h := modal_diagonal_pointwise T hT X σ g hg k 0 ⟨le_rfl,hT⟩
  have hinit : (fun n=>zeroExtend (X (σ n) 0) (embedMode k))=ᶠ[atTop] (fun _=>u₀ k) := by
    by_cases hk : k=0
    · subst k
      exact Eventually.of_forall fun n=>by rw [zeroExtend_mean,hmean]
    · filter_upwards [cutoff_eventually_contains k hk hσ] with n hn
      rw [hx,initialProjection_at _ _ _ hn]
  exact tendsto_nhds_unique h (tendsto_const_nhds.congr' hinit.symm)

end
end DASHI.NavierStokes.PhysicalMixed

import Synthesis.NavierStokesOriginalFixedModeEquicontinuityExact
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Sequences

/-!
Actual simultaneous subsequence, not separate shellwise selections.
Compact countable product of Arzela--Ascoli closures of the original
modal time charts. Classical Arzela--Ascoli, Tychonoff, Galerkin.
The DASHI attachment retains the original Fourier addresses and one
strictly increasing cutoff subsequence.
-/
namespace DASHI.NavierStokes.RealContinuation
open Set Filter Metric
open scoped Topology
noncomputable section

theorem countable_chart_subsequence {I A E : Type*}
    [Countable I] [MetricSpace A] [CompactSpace A]
    [MetricSpace E] [ProperSpace E]
    (f : ℕ → I → A →ᵇ E) (o : E) (B : ℝ) (L : I → ℝ)
    (hL : ∀ i,0≤L i)
    (hb : ∀ n i t,dist (f n i t) o≤B)
    (hlip : ∀ n i s t,dist (f n i s) (f n i t)≤L i*dist s t) :
    ∃ σ : ℕ → ℕ,StrictMono σ ∧ ∃ g : I → A →ᵇ E,
      ∀ i, TendstoUniformly (fun n t=>f (σ n) i t) (g i) atTop := by
  classical
  let K : I → Set (A →ᵇ E) := fun i=>closure (range (fun n=>f n i))
  have hK (i : I) : IsCompact (K i) := by
    apply BoundedContinuousFunction.arzela_ascoli (closedBall o B) (isCompact_closedBall _ _)
    · intro u t hu
      obtain ⟨n,rfl⟩ := hu
      exact hb n i t
    · apply UniformEquicontinuous.equicontinuous
      apply Metric.uniformEquicontinuous_iff.mpr
      intro ε hε
      refine ⟨ε/(L i+1),by positivity,?_⟩
      intro s t hst u
      obtain ⟨n,hn⟩ := u.2
      change dist (u.1 s) (u.1 t)<ε
      rw [← hn]
      have h := hlip n i s t
      have h' := (lt_div_iff₀ (by linarith [hL i] : 0<L i+1)).mp hst
      nlinarith [dist_nonneg (x:=s) (y:=t)]
  have hp : IsCompact {x : I → A →ᵇ E | ∀ i,x i∈K i} :=
    isCompact_pi_infinite hK
  obtain ⟨g,hg,σ,hσ,hconv⟩ := hp.tendsto_subseq
    (x:=f) (fun n i=>subset_closure (mem_range_self n))
  refine ⟨σ,hσ,g,fun i=>?_⟩
  apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
  exact ((continuous_apply i).tendsto g).comp hconv

end
end DASHI.NavierStokes.RealContinuation

namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open DASHI.NavierStokes.RealContinuation
open Set Filter Metric
open scoped Topology BigOperators
noncomputable section

abbrev ModalAddress := Lattice × Fin 3
abbrev TimeChart (T : ℝ) := Set.Icc (0:ℝ) T

def chartValue {N : ℕ} (x : ℝ → FiniteState N) (i : ModalAddress) (t : ℝ) : ℂ :=
  zeroExtend (x t) (embedMode i.1) i.2

theorem chartValue_bound {N : ℕ} (x : FiniteState N) (B : ℝ)
    (hB : 0≤B) (hE : stateEnergy x≤B) (k : Lattice) (i : Fin 3) :
    ‖zeroExtend x (embedMode k) i‖≤Real.sqrt B := by
  classical
  by_cases hk : k∈outputModes N
  · let p : Mode N := ⟨k,hk⟩
    change ‖zeroExtend x (embedMode p.1) i‖≤_
    rw [zeroExtend_at]
    exact Real.le_sqrt_of_sq_le ((coordinate_square_le_energy x p i).trans hE)
  · have ho : embedMode k∉(outputModes N).image embedMode := by
      intro h
      obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
      exact hk (embedMode_injective he ▸ hp)
    simp [zeroExtend_outside _ _ ho,Real.sqrt_nonneg]

/-- Actual Galerkin trajectories generated from arbitrary physical
finite projections with uniformly bounded initial energy. No choice
of unrelated per-mode subsequences. Fixed T includes t=0. -/
theorem actual_modal_diagonal (ν B T : ℝ) (hν : 0≤ν) (hB : 0≤B) (hT : 0≤T)
    (x₀ : (N : ℕ) → FiniteState N)
    (hr : ∀ N,reflectState (x₀ N)=x₀ N)
    (ht : ∀ N k,outputDot k (zeroExtend (x₀ N) k)=0)
    (hE : ∀ N,stateEnergy (x₀ N)≤B) :
    ∃ X : (N : ℕ) → ℝ → FiniteState N,
      (∀ N,X N 0=x₀ N) ∧
      (∀ N,∃ a<0,SolvesOn (finiteForce N ν) (X N) (Ioi a)) ∧
      (∀ N t,0≤t → stateEnergy (X N t)≤B) ∧
      ∃ σ : ℕ → ℕ,StrictMono σ ∧
      ∃ g : ModalAddress → TimeChart T →ᵇ ℂ,
        ∀ i,TendstoUniformly (fun n (t : TimeChart T)=>chartValue (X (σ n)) i t)
          (g i) atTop := by
  classical
  have hflow (N : ℕ) := actual_global_forward_finite_flow N ν hν (x₀ N) (hr N) (ht N)
  choose a ha X hx hd hre htr henergy using hflow
  have hbound (N : ℕ) (t : ℝ) (ht' : 0≤t) : stateEnergy (X N t)≤B := by
    have he := henergy N t ht'
    have hi := intervalIntegral.integral_nonneg_of_forall ht'
      (periodicDissipation_nonneg N (fun k s=>zeroExtend (X N s) k))
    nlinarith [hE N,mul_nonneg hν hi]
  let f (N : ℕ) (i : ModalAddress) : TimeChart T →ᵇ ℂ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨fun t=>chartValue (X N) i t,
        continuousOn_iff_continuous_restrict.mp (by
          intro t ht'
          exact (zeroExtend_ODE_of_derivative N ν (X N) t
            (hd N t ((ha N).trans_le ht'.1)) (embedMode i.1) i.2).continuousAt.continuousWithinAt)⟩
  let L : ModalAddress → ℝ := fun i=>
    ν*massSq (embedMode i.1)*Real.sqrt B+Real.sqrt (massSq (embedMode i.1))*B
  have hL (i : ModalAddress) : 0≤L i := by
    dsimp [L]
    positivity
  have hfb (N : ℕ) (i : ModalAddress) (t : TimeChart T) :
      dist (f N i t) 0≤Real.sqrt B := by
    simpa [f,chartValue,dist_zero_right] using
      chartValue_bound (X N t) B hB (hbound N t t.2.1) i.1 i.2
  have hforward (N : ℕ) (i : ModalAddress) (s t : TimeChart T) (hst : (s:ℝ)≤t) :
      ‖chartValue (X N) i t-chartValue (X N) i s‖≤L i*((t:ℝ)-s) := by
    exact fixed_mode_time_bound N ν B T hν hB (X N) (a N) (ha N) hT
      (by rw [hx]; exact hr N) (by rw [hx]; exact ht N)
      (by rw [hx]; exact hE N) (hd N) i.1 i.2 s t s.2.1 hst t.2.2
  have hfl (N : ℕ) (i : ModalAddress) (s t : TimeChart T) :
      dist (f N i s) (f N i t)≤L i*dist s t := by
    by_cases hst : (s:ℝ)≤t
    · rw [dist_comm (f N i s),dist_comm s]
      simpa [f,dist_eq_norm,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hst)] using
        hforward N i s t hst
    · have hts : (t:ℝ)≤s := le_of_not_ge hst
      simpa [f,dist_eq_norm,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hts)] using
        hforward N i t s hts
  obtain ⟨σ,hσ,g,hg⟩ := countable_chart_subsequence f (0:ℂ) (Real.sqrt B) L hL hfb hfl
  exact ⟨X,hx,fun N=>⟨a N,ha N,hd N⟩,hbound,σ,hσ,g,by simpa [f] using hg⟩

end
end DASHI.NavierStokes.PhysicalMixed

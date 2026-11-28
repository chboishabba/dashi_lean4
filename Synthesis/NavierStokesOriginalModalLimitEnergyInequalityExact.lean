import Synthesis.NavierStokesOriginalPeriodicModalIntegralLimitExact

/-! Preserve the JOINT initial-energy budget in the periodic limit.
The separate estimates E<=B and integral D<=B/(2nu) are insufficient
to conclude E+2nu integral D<=B. Use two arbitrary finite mode subsets,
pass both on the SAME subsequence, then take the two positive sums.
This is the Fourier-side energy inequality from initial time.
Physical-space Parseval/Tonelli and the local-in-time energy inequality
from almost every starting time remain separate.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open DASHI.NavierStokes.RealContinuation
open Set Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section

theorem actual_joint_energy_subset (N : ℕ) (ν t a : ℝ)
    (hν : 0≤ν) (ht : 0≤t) (ha : a<0)
    (x : ℝ → FiniteState N)
    (hr : reflectState (x 0)=x 0)
    (htr : ∀ k,outputDot k (zeroExtend (x 0) k)=0)
    (hd : SolvesOn (finiteForce N ν) x (Ioi a))
    (S R : Finset Lattice) :
    (∑ k ∈ S,phaseMass (zeroExtend (x t) (embedMode k)))+
      2*ν*(∑ k ∈ R,∫ s in 0..t,massSq (embedMode k)*
        phaseMass (zeroExtend (x s) (embedMode k)))≤stateEnergy (x 0) := by
  let U := fun k s=>zeroExtend (x s) k
  have hc (k : Vec3) (i : Fin 3) :
      ContinuousOn (fun s=>U k s i) (uIcc 0 t) := by
    intro s hs
    rw [uIcc_of_le ht] at hs
    exact (zeroExtend_ODE_of_derivative N ν x s (hd s (ha.trans_le hs.1)) k i).continuousAt.continuousWithinAt
  have hci (k : Lattice) :
      ContinuousOn (fun s=>massSq (embedMode k)*phaseMass (U (embedMode k) s)) (uIcc 0 t) := by
    apply ContinuousOn.const_mul
    exact phaseMass_continuous.comp_continuousOn (continuousOn_pi.mpr (fun i=>hc _ i))
  have hD : (∑ k ∈ R,∫ s in 0..t,massSq (embedMode k)*phaseMass (U (embedMode k) s))≤
      ∫ s in 0..t,periodicDissipation N U s := by
    rw [← intervalIntegral.integral_finset_sum (fun k _=>(hci k).intervalIntegrable)]
    apply intervalIntegral.integral_mono_on ht
      (continuousOn_finset_sum _ (fun k _=>hci k)).intervalIntegrable
      (dissipation_continuousOn N t U hc).intervalIntegrable
    intro s _
    simpa [periodicDissipation,phaseMass_eq_energy,U] using
      zeroExtended_weighted_subset (x s) R (fun k=>massSq (embedMode k))
        (fun k=>massSq_nonnegative _)
  have hE := zeroExtended_mass_subset (x t) S
  have henergy := energy_on_forward_interval N ν a (t+1) x ha (by linarith)
    hr htr (fun s hs=>hd s hs.1) t ⟨ht,by linarith⟩
  change stateEnergy (x t)+2*ν*(∫ s in 0..t,periodicDissipation N U s)=stateEnergy (x 0) at henergy
  have h := add_le_add hE (mul_le_mul_of_nonneg_left hD (by positivity : 0≤2*ν))
  exact h.trans_eq henergy

/-- Two independent positive sums with a joint finite-subset bound.
Summability is constructed before extracting either infinite sum. -/
theorem joint_positive_tsum_bound {I J : Type*}
    (f : I → ℝ) (g : J → ℝ) (c B : ℝ) (hc : 0<c)
    (hf : ∀ i,0≤f i) (hg : ∀ j,0≤g j)
    (h : ∀ (S : Finset I) (R : Finset J),(∑ i ∈ S,f i)+c*(∑ j ∈ R,g j)≤B) :
    Summable f ∧ Summable g ∧ (∑' i,f i)+c*(∑' j,g j)≤B := by
  have hsf : Summable f := summable_of_sum_le hf fun S=>by simpa using h S ∅
  have hsg : Summable g := summable_of_sum_le hg (c:=B/c) fun R=>by
    apply (le_div_iff₀ hc).mpr
    simpa [mul_comm] using h ∅ R
  have hfirst (R : Finset J) : (∑' i,f i)≤B-c*(∑ j ∈ R,g j) :=
    Real.tsum_le_of_sum_le hf fun S=>by linarith [h S R]
  have hlast : (∑' j,g j)≤(B-(∑' i,f i))/c :=
    Real.tsum_le_of_sum_le hg fun R=>by
      apply (le_div_iff₀ hc).mpr
      linarith [hfirst R,mul_comm c (∑ j ∈ R,g j)]
  exact ⟨hsf,hsg,by have hh := (le_div_iff₀ hc).mp hlast; linarith [mul_comm c (∑' j,g j)]⟩

/-- Any limit of the actual selected original flows inherits the joint
budget. It is not necessary to assume a second energy-bounded limit. -/
theorem original_modal_limit_energy_inequality (ν B T : ℝ)
    (hν : 0<ν) (hB : 0≤B) (hT : 0≤T)
    (u₀ : Lattice → CVec3)
    (hr : ∀ k i,u₀ (-k) i=star (u₀ k i))
    (htr : ∀ k,outputDot (embedMode k) (u₀ k)=0)
    (hE : ∀ S : Finset Lattice,∑ k ∈ S,phaseMass (u₀ k)≤B)
    (X : (N : ℕ) → ℝ → FiniteState N)
    (hx : ∀ N,X N 0=initialProjection u₀ N)
    (hd : ∀ N,∃ a<0,SolvesOn (finiteForce N ν) (X N) (Ioi a))
    (σ : ℕ → ℕ) (V : Lattice → ℝ → CVec3)
    (hconv : ∀ k t,t∈Icc 0 T → Tendsto
      (fun n=>zeroExtend (X (σ n) t) (embedMode k)) atTop (𝓝 (V k t)))
    (t : ℝ) (ht : t∈Icc 0 T) :
    Summable (fun k=>phaseMass (V k t)) ∧
    Summable (fun k=>∫ s in 0..t,massSq (embedMode k)*phaseMass (V k s)) ∧
    (∑' k,phaseMass (V k t))+2*ν*(∑' k,∫ s in 0..t,
      massSq (embedMode k)*phaseMass (V k s))≤B := by
  classical
  choose a ha hODE using hd
  let U := fun n k s=>zeroExtend (X (σ n) s) (embedMode k)
  have hbound (n : ℕ) (s : ℝ) (hs : s∈Icc 0 t) :
      stateEnergy (X (σ n) s)≤B := by
    have h := forward_energy_bound (σ n) ν (a (σ n)) (t+1) hν.le (X (σ n))
      (ha (σ n)) (by linarith [ht.1])
      (by rw [hx]; exact projection_reality u₀ hr _)
      (by rw [hx]; exact projection_transverse u₀ htr _)
      (fun r hr'=>hODE (σ n) r hr'.1) s ⟨hs.1,by linarith [hs.2]⟩
    change stateEnergy (X (σ n) s)≤stateEnergy (X (σ n) 0) at h
    exact h.trans (by rw [hx]; exact projection_energy_bound u₀ B hE _)
  have hci (n : ℕ) (k : Lattice) : ContinuousOn (U n k) (Icc 0 t) := by
    apply continuousOn_pi.mpr
    intro i s hs
    exact (zeroExtend_ODE_of_derivative (σ n) ν (X (σ n)) s
      (hODE (σ n) s ((ha (σ n)).trans_le hs.1)) _ i).continuousAt.continuousWithinAt
  have hV (k : Lattice) : Tendsto (fun n=>phaseMass (U n k t)) atTop
      (𝓝 (phaseMass (V k t))) :=
    phaseMass_continuous.continuousAt.tendsto.comp (hconv k t ht)
  have hD (k : Lattice) : Tendsto
      (fun n=>∫ s in 0..t,massSq (embedMode k)*phaseMass (U n k s))
      atTop (𝓝 (∫ s in 0..t,massSq (embedMode k)*phaseMass (V k s))) := by
    apply interval_limit_of_bounded_modes t (massSq (embedMode k)*B) ht.1
    · intro n
      exact (phaseMass_continuous.comp_continuousOn (hci n k)).const_mul _
    · intro n s hs
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (massSq_nonnegative _) (phaseMass_nonneg _))]
      apply mul_le_mul_of_nonneg_left _ (massSq_nonnegative _)
      exact (by simpa [U] using zeroExtended_mass_subset (X (σ n) s) {k}).trans (hbound n s hs)
    · intro s hs
      exact tendsto_const_nhds.mul (phaseMass_continuous.continuousAt.tendsto.comp
        (hconv k s ⟨hs.1,hs.2.trans ht.2⟩))
  apply joint_positive_tsum_bound _ _ (2*ν) B (by positivity)
    (fun k=>phaseMass_nonneg _)
    (fun k=>intervalIntegral.integral_nonneg_of_forall ht.1 fun s=>
      mul_nonneg (massSq_nonnegative _) (phaseMass_nonneg _))
  intro S R
  have h := (tendsto_finset_sum S fun k _=>hV k).add
    (tendsto_const_nhds.mul (tendsto_finset_sum R fun k _=>hD k))
  apply le_of_tendsto h
  apply Eventually.of_forall
  intro n
  have hf := actual_joint_energy_subset (σ n) ν t (a (σ n)) hν.le ht.1 (ha (σ n))
    (X (σ n)) (by rw [hx]; exact projection_reality u₀ hr _)
    (by rw [hx]; exact projection_transverse u₀ htr _) (hODE (σ n)) S R
  exact hf.trans (by rw [hx]; exact projection_energy_bound u₀ B hE _)

end
end DASHI.NavierStokes.PhysicalMixed

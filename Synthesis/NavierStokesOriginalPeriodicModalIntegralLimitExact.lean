import Synthesis.NavierStokesOriginalDiagonalInitialBudgetExact

/-!
Same-subsequence periodic modal integral equation. This is a weak
Fourier-limit target, not a classical smooth solution or a Clay
regularity theorem. The signed critical-time estimate is independent.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open DASHI.NavierStokes.RealContinuation
open Set Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section

theorem modeForce_primitive_tendsto (T B : ℝ) (hT : 0≤T) (hB : 0≤B)
    (U : ℕ → Lattice → ℝ → CVec3) (V : Lattice → ℝ → CVec3)
    (hc : ∀ n k,ContinuousOn (U n k) (Icc 0 T))
    (hv : ∀ k,ContinuousOn (V k) (Icc 0 T))
    (hE : ∀ n t∈Icc 0 T,∀ S : Finset Lattice,∑ p ∈ S,phaseMass (U n p t)≤B)
    (hEV : ∀ t∈Icc 0 T,∀ S : Finset Lattice,∑ p ∈ S,phaseMass (V p t)≤B)
    (hs : ∀ n,Summable (fun p : Lattice=>∫ t in 0..T,phaseMass (U n p t-V p t)))
    (he : Tendsto (fun n=>∑' p : Lattice,∫ t in 0..T,phaseMass (U n p t-V p t)) atTop (𝓝 0))
    (k : Lattice) (hk : k≠0) (i : Fin 3) :
    Tendsto (fun n=>∫ t in 0..T,modeForceSeries k (fun p=>U n p t) i) atTop
      (𝓝 (∫ t in 0..T,modeForceSeries k (fun p=>V p t) i)) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  let r := Real.sqrt (massSq (embedMode k))
  have hr : 0≤r := Real.sqrt_nonneg _
  let M := B*T
  have hM : 0≤M := mul_nonneg hB hT
  let ε := η/(4*(r+1)*(M+1))
  have hε : 0<ε := by dsimp [ε]; positivity
  have hpay : ε*(4*(r+1)*(M+1))=η := by
    dsimp [ε]
    field_simp [show r+1≠0 by linarith,show M+1≠0 by linarith]
  have hsmall : r*(ε*M)≤η/4 := by
    have h1 : r*M≤(r+1)*(M+1) := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 hε.le
    nlinarith [hpay]
  have htol : 0<ε*η/(4*(r+1)) := by positivity
  filter_upwards [Metric.tendsto_nhds.mp he _ htol] with n hn
  let E := ∑' p : Lattice,∫ t in 0..T,phaseMass (U n p t-V p t)
  have hE0 : 0≤E := tsum_nonneg (fun p=>intervalIntegral.integral_nonneg_of_forall hT fun _=>phaseMass_nonneg _)
  have hn' : E<ε*η/(4*(r+1)) := by
    simpa [E,Real.dist_eq,abs_of_nonneg hE0] using hn
  have hE1 : E/ε≤η/(4*(r+1)) := by
    apply (div_le_iff₀ hε).mpr
    exact hn'.le.trans_eq (by ring)
  have hE2 : r*(E/ε)≤η/4 := by
    have h1 := mul_le_mul_of_nonneg_left hE1 hr
    have h2 : r*(η/(4*(r+1)))≤η/4 := by
      apply (mul_le_mul_right₀ (show 0<4*(r+1) by positivity)).mp
      field_simp [show r+1≠0 by linarith]
      nlinarith
    exact h1.trans h2
  have h := integrated_modeForce_difference T B hT (U n) V (hc n) hv
    (hE n) hEV (hs n) k hk i ε hε
  rw [dist_eq_norm]
  change _≤r*(E/ε+ε*M) at h
  linarith [mul_add r (E/ε) (ε*M)]

theorem original_periodic_modal_integral_limit
    (ν B T : ℝ) (hν : 0<ν) (hB : 0≤B) (hT : 0≤T)
    (u₀ : Lattice → CVec3) (hmean : u₀ 0=0)
    (hr : ∀ k i,u₀ (-k) i=star (u₀ k i))
    (ht : ∀ k,outputDot (embedMode k) (u₀ k)=0)
    (hE : ∀ S : Finset Lattice,∑ k ∈ S,phaseMass (u₀ k)≤B) :
    ∃ X : (N : ℕ) → ℝ → FiniteState N,∃ σ : ℕ → ℕ,StrictMono σ ∧
      ∃ V : Lattice → ℝ → CVec3,
        (∀ N,X N 0=initialProjection u₀ N) ∧
        (∀ N,∃ a<0,SolvesOn (finiteForce N ν) (X N) (Ioi a)) ∧
        (∀ k,Continuous (V k)) ∧
        (∀ k,V k 0=u₀ k) ∧
        (∀ t∈Icc 0 T,∀ S : Finset Lattice,∑ k ∈ S,phaseMass (V k t)≤B) ∧
        (∀ k t,t∈Icc 0 T → Tendsto (fun n=>zeroExtend (X (σ n) t) (embedMode k)) atTop (𝓝 (V k t))) ∧
        (∀ t∈Icc 0 T,V 0 t=0) ∧
        (∀ t∈Icc 0 T,∀ k,outputDot (embedMode k) (V k t)=0) ∧
        (∀ t∈Icc 0 T,∀ k i,V (-k) t i=star (V k t i)) ∧
        (∀ n,Summable (fun k : Lattice=>∫ t in 0..T,phaseMass (zeroExtend (X (σ n) t) (embedMode k)-V k t))) ∧
        Tendsto (fun n=>∑' k : Lattice,∫ t in 0..T,phaseMass (zeroExtend (X (σ n) t) (embedMode k)-V k t))
          atTop (𝓝 0) ∧
        (∀ k ≠ 0,∀ i,∀ t∈Icc 0 T,
          V k t i=u₀ k i+(-((ν*massSq (embedMode k):ℝ):ℂ))*(∫ s in 0..t,V k s i)+
            ∫ s in 0..t,modeForceSeries k (fun p=>V p s) i) := by
  classical
  obtain ⟨X,hx,hd,hbound,σ,hσ,g,hg⟩ :=
    actual_modal_diagonal ν B T hν.le hB hT (initialProjection u₀)
      (projection_reality u₀ hr) (projection_transverse u₀ ht) (projection_energy_bound u₀ B hE)
  let U : ℕ → Lattice → ℝ → CVec3 := fun n k t=>zeroExtend (X (σ n) t) (embedMode k)
  let V := limitVelocity T hT g
  choose a ha hODE using hd
  have hc (n : ℕ) (k : Lattice) : ContinuousOn (U n k) (Icc 0 T) := by
    apply continuousOn_pi.mpr
    intro i t ht'
    exact (zeroExtend_ODE_of_derivative (σ n) ν (X (σ n)) t
      (hODE (σ n) t ((ha (σ n)).trans_le ht'.1)) _ i).continuousAt.continuousWithinAt
  have hv (k : Lattice) : Continuous (V k) := limitVelocity_continuous T hT g k
  have hconv (k : Lattice) (t : ℝ) (ht' : t∈Icc 0 T) :
      Tendsto (fun n=>U n k t) atTop (𝓝 (V k t)) :=
    modal_diagonal_pointwise T hT X σ g hg k t ht'
  have hEU (n : ℕ) (t : ℝ) (ht' : t∈Icc 0 T) (S : Finset Lattice) :
      ∑ k ∈ S,phaseMass (U n k t)≤B :=
    (zeroExtended_mass_subset (X (σ n) t) S).trans (hbound _ _ ht'.1)
  have hEV (t : ℝ) (ht' : t∈Icc 0 T) (S : Finset Lattice) :
      ∑ k ∈ S,phaseMass (V k t)≤B :=
    finite_mass_limit (fun n k=>phaseMass (U n k t)) (fun k=>phaseMass (V k t))
      (fun k=>phaseMass_continuous.continuousAt.tendsto.comp (hconv k t ht')) B
      (fun n S=>hEU n t ht' S) S
  have hinit : ∀ k,V k 0=u₀ k := modal_diagonal_initial T hT u₀ hmean X hx σ hσ g hg
  have htr (n : ℕ) (t : ℝ) (h0 : 0≤t) (k : Lattice) :
      outputDot (embedMode k) (U n k t)=0 := by
    apply transverse_preserved (σ n) ν (fun k s=>zeroExtend (X (σ n) s) k) t h0 (embedMode k)
    · rw [hx]; exact projection_transverse u₀ ht _ _
    · intro s hs i
      exact zeroExtend_ODE_of_derivative (σ n) ν (X (σ n)) s
        (hODE (σ n) s ((ha (σ n)).trans_le hs.1)) _ i
  have hreal (n : ℕ) (t : ℝ) (h0 : 0≤t) (k : Lattice) (i : Fin 3) :
      U n (-k) t i=star (U n k t i) := by
    have hh := reality_on_open_interval (σ n) ν (a (σ n)) (t+1) (X (σ n))
      (ha (σ n)) (by linarith) (by rw [hx]; exact projection_reality u₀ hr _)
      (fun s hs=>hODE (σ n) s hs.1) t ⟨(ha (σ n)).trans_le h0,by linarith⟩
    have he := zeroExtend_reflect (X (σ n) t) (-k) i
    rw [hh,neg_neg] at he
    exact he
  have hD (n : ℕ) (t : ℝ) (h0 : 0≤t) (S : Finset Lattice) :
      ∑ k ∈ S,(∫ s in 0..t,massSq (embedMode k)*phaseMass (U n k s))≤B/(2*ν) :=
    actual_weighted_integrated_budget (σ n) ν B t hν h0 (X (σ n)) (a (σ n)) (ha (σ n))
      (by rw [hx]; exact projection_reality u₀ hr _)
      (by rw [hx]; exact projection_transverse u₀ ht _)
      (by rw [hx]; exact projection_energy_bound u₀ B hE _)
      (hODE (σ n)) S
  have hstrong (t : ℝ) (ht' : t∈Icc 0 T) :=
    integrated_modal_strong_limit t B (B/(2*ν)) ht'.1 hB (by positivity) U V
      (fun n k=>(hc n k).mono fun _ hs=>⟨hs.1,hs.2.trans ht'.2⟩)
      (fun k=>(hv k).continuousOn)
      (fun k s hs=>hconv k s ⟨hs.1,hs.2.trans ht'.2⟩)
      (fun n s hs=>hEU n s ⟨hs.1,hs.2.trans ht'.2⟩)
      (fun n=>hD n t ht'.1)
  refine ⟨X,σ,hσ,V,hx,hd,hv,hinit,hEV,hconv,?_,?_,?_,
    (hstrong T ⟨hT,le_rfl⟩).1,(hstrong T ⟨hT,le_rfl⟩).2,?_⟩
  · intro t ht'
    exact tendsto_nhds_unique (hconv 0 t ht') (by simpa [U,zeroExtend_mean] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0:CVec3)) atTop (𝓝 0)))
  · intro t ht' k
    have hcont : Continuous (outputDot (embedMode k)) := by
      unfold outputDot
      simp only [Fin.sum_univ_three]
      fun_prop
    have hh := hcont.continuousAt.tendsto.comp (hconv k t ht')
    exact tendsto_nhds_unique hh (by simpa [Function.comp_def,htr _ t ht'.1 k] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0:ℂ)) atTop (𝓝 0)))
  · intro t ht' k i
    have h1 := (continuous_apply i).continuousAt.tendsto.comp (hconv (-k) t ht')
    have h2 := Complex.continuous_conj.continuousAt.tendsto.comp
      ((continuous_apply i).continuousAt.tendsto.comp (hconv k t ht'))
    apply tendsto_nhds_unique h1
    exact h2.congr' (Eventually.of_forall fun n=>(hreal n t ht'.1 k i).symm)
  · intro k hk i t ht'
    have hforce := modeForce_primitive_tendsto t B ht'.1 hB U V
      (fun n k=>(hc n k).mono fun _ hs=>⟨hs.1,hs.2.trans ht'.2⟩)
      (fun k=>(hv k).continuousOn)
      (fun n s hs=>hEU n s ⟨hs.1,hs.2.trans ht'.2⟩)
      (fun s hs=>hEV s ⟨hs.1,hs.2.trans ht'.2⟩)
      (hstrong t ht').1 (hstrong t ht').2 k hk i
    have hlin := interval_limit_of_bounded_modes t (Real.sqrt B) ht'.1
      (fun n s=>U n k s i) (fun s=>V k s i)
      (fun n=>(continuous_apply i).comp_continuousOn
        ((hc n k).mono fun _ hs=>⟨hs.1,hs.2.trans ht'.2⟩))
      (fun n s hs=>chartValue_bound _ B hB (hbound _ _ hs.1) k i)
      (fun s hs=>(continuous_apply i).continuousAt.tendsto.comp
        (hconv k s ⟨hs.1,hs.2.trans ht'.2⟩))
    have hfinite : ∀ᶠ n in atTop,
        U n k t i=u₀ k i+(-((ν*massSq (embedMode k):ℝ):ℂ))*(∫ s in 0..t,U n k s i)+
          ∫ s in 0..t,modeForceSeries k (fun p=>U n p s) i := by
      filter_upwards [cutoff_eventually_contains k hk hσ] with n hn
      let W := fun k s=>zeroExtend (X (σ n) s) k
      let f := fun s=>galerkinForce (σ n) W (embedMode k) s i
      have hODE' (s : ℝ) (hs : s∈uIcc 0 t) :
          HasDerivAt (fun v=>U n k v i)
            (-((ν*massSq (embedMode k):ℝ):ℂ)*U n k s i+f s) s := by
        rw [uIcc_of_le ht'.1] at hs
        exact zeroExtend_ODE_of_derivative (σ n) ν (X (σ n)) s
          (hODE (σ n) s ((ha (σ n)).trans_le hs.1)) _ _
      have hfc : ContinuousOn f (uIcc 0 t) := by
        rw [uIcc_of_le ht'.1]
        unfold f
        rw [show (fun s=>galerkinForce (σ n) W (embedMode k) s i)=
          (fun s=>∑ p ∈ orderedFibre (σ n) k,
            orderedRHS (embedMode k) (embedMode p.2) (U n p.1 s) (U n p.2 s) i) by
          funext s; exact galerkinForce_eq_orderedFibre _ _ _ hn _ _]
        apply continuousOn_finset_sum
        intro p hp
        unfold orderedRHS lerayVector outputDot
        simp only [Fin.sum_univ_three]
        have h (q : Lattice) (j : Fin 3) :
            ContinuousOn (fun s=>U n q s j) (Icc 0 t) :=
          (continuous_apply j).comp_continuousOn ((hc n q).mono fun _ hs=>⟨hs.1,hs.2.trans ht'.2⟩)
        fun_prop
      have huc : ContinuousOn (fun s=>U n k s i) (uIcc 0 t) := by
        rw [uIcc_of_le ht'.1]
        exact (continuous_apply i).comp_continuousOn ((hc n k).mono fun _ hs=>⟨hs.1,hs.2.trans ht'.2⟩)
      have hlc := huc.const_mul (-((ν*massSq (embedMode k):ℝ):ℂ))
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hODE'
        ((hlc.add hfc).intervalIntegrable)
      rw [intervalIntegral.integral_add hlc.intervalIntegrable hfc.intervalIntegrable,
        intervalIntegral.integral_const_mul] at hFTC
      have h0 : U n k 0 i=u₀ k i := by
        change zeroExtend (X (σ n) 0) (embedMode k) i=u₀ k i
        rw [hx,initialProjection_at _ _ _ hn]
      have hident : (∫ s in 0..t,f s)=∫ s in 0..t,modeForceSeries k (fun p=>U n p s) i := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le ht'.1] at hs
        symm
        exact modeForceSeries_eq_galerkin _ (X (σ n) s) k hn (htr n s hs.1) i
      rw [h0,hident] at hFTC
      linear_combination -hFTC
    have hleft := (continuous_apply i).continuousAt.tendsto.comp (hconv k t ht')
    have hright := (tendsto_const_nhds.add (tendsto_const_nhds.mul hlin)).add hforce
    exact tendsto_nhds_unique hleft (hright.congr' hfinite.symm)

end
end DASHI.NavierStokes.PhysicalMixed

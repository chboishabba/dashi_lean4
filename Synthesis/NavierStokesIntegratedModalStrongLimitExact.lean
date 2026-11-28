import Synthesis.NavierStokesActualModalDiagonalExact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Countable positive-energy series and actual integrated prefix
convergence. Each limit retains the same selected modal coefficients.
The weak-energy compactness stage does not supply pointwise critical
regularity. -/
namespace DASHI.NavierStokes.RealContinuation
open Filter Set MeasureTheory
open scoped Topology BigOperators
noncomputable section

/-- Finite prefix convergence and uniformly small tails give convergence
of the whole nonnegative series. A tail estimate on every finite subset
also proves summability, so tsum is never used to mask divergence. -/
theorem positive_series_prefix_limit {I : Type*}
    (e : ℕ → I → ℝ) (he : ∀ n i,0≤e n i)
    (hpoint : ∀ i,Tendsto (fun n=>e n i) atTop (𝓝 0))
    (htail : ∀ ε>0,∃ S : Finset I,∀ n (V : Finset I),
      Disjoint V S → ∑ i ∈ V,e n i≤ε) :
    (∀ n,Summable (e n)) ∧ Tendsto (fun n=>∑' i,e n i) atTop (𝓝 0) := by
  classical
  have hpartition (n : ℕ) (S V : Finset I) :
      (∑ i ∈ V,e n i)≤(∑ i ∈ S,e n i)+(∑ i ∈ V\S,e n i) := by
    calc
      _ = (∑ i ∈ V∩S,e n i)+(∑ i ∈ V\S,e n i) := by
        rw [Finset.sum_inter_add_sum_sdiff]
      _ ≤ _ := add_le_add_right
        (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          (fun i _ _=>he n i)) _
  have hs : ∀ n,Summable (e n) := by
    intro n
    obtain ⟨S,hS⟩ := htail 1 (by norm_num)
    apply summable_of_sum_le (he n)
    intro V
    exact (hpartition n S V).trans (add_le_add_left (hS n _ Finset.sdiff_disjoint) _)
  refine ⟨hs,?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨S,hS⟩ := htail (ε/4) (by positivity)
  have hfin : Tendsto (fun n=>∑ i ∈ S,e n i) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum S (fun i _=>hpoint i)
  filter_upwards [Metric.tendsto_nhds.mp hfin (ε/4) (by positivity)] with n hn
  have hn' : (∑ i ∈ S,e n i)<ε/4 := by
    simpa [Real.dist_eq,abs_of_nonneg (Finset.sum_nonneg fun i _=>he n i)] using hn
  have htotal : (∑' i,e n i)≤(∑ i ∈ S,e n i)+ε/4 :=
    Real.tsum_le_of_sum_le (he n) fun V=>
      (hpartition n S V).trans (add_le_add_left (hS n _ Finset.sdiff_disjoint) _)
  have hnon : 0≤∑' i,e n i := tsum_nonneg (he n)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hnon]
  linarith

/-- Transfer any finite positive sum bound to a pointwise limit. -/
theorem finite_mass_limit {I : Type*} (e : ℕ → I → ℝ) (v : I → ℝ)
    (hv : ∀ i,Tendsto (fun n=>e n i) atTop (𝓝 (v i)))
    (B : ℝ) (h : ∀ n (S : Finset I),∑ i ∈ S,e n i≤B) :
    ∀ S : Finset I,∑ i ∈ S,v i≤B := by
  intro S
  exact le_of_tendsto (tendsto_finset_sum S fun i _=>hv i)
    (Eventually.of_forall fun n=>h n S)

/-- Exact dominated integration of one modal polynomial on the
selected compact time interval. -/
theorem interval_limit_of_bounded_modes {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T C : ℝ) (hT : 0≤T)
    (f : ℕ → ℝ → E) (g : ℝ → E)
    (hc : ∀ n,ContinuousOn (f n) (Icc 0 T))
    (hb : ∀ n t,t∈Icc 0 T → ‖f n t‖≤C)
    (h : ∀ t∈Icc 0 T,Tendsto (fun n=>f n t) atTop (𝓝 (g t))) :
    Tendsto (fun n=>∫ t in 0..T,f n t) atTop (𝓝 (∫ t in 0..T,g t)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _=>C)
  · apply Eventually.of_forall
    intro n
    have hi : ContinuousOn (f n) (uIcc 0 T) := by rwa [uIcc_of_le hT]
    exact hi.intervalIntegrable.aestronglyMeasurable
  · exact Eventually.of_forall fun n=>Eventually.of_forall fun t ht=>
      hb n t (by rw [uIoc_of_le hT] at ht; exact ⟨ht.1.le,ht.2⟩)
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun t ht=>h t (by
      rw [uIoc_of_le hT] at ht
      exact ⟨ht.1.le,ht.2⟩)

end
end DASHI.NavierStokes.RealContinuation

namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open DASHI.NavierStokes.RealContinuation
open Set Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section

theorem phaseMass_sub_le (u v : CVec3) :
    phaseMass (u-v)≤2*(phaseMass u+phaseMass v) := by
  simp [phaseMass,massSq,Fin.sum_univ_three,Complex.sub_re,Complex.sub_im]
  nlinarith [sq_nonneg ((u 0).re+(v 0).re),sq_nonneg ((u 1).re+(v 1).re),
    sq_nonneg ((u 2).re+(v 2).re),sq_nonneg ((u 0).im+(v 0).im),
    sq_nonneg ((u 1).im+(v 1).im),sq_nonneg ((u 2).im+(v 2).im)]

theorem phaseMass_continuous : Continuous (phaseMass : CVec3 → ℝ) := by
  unfold phaseMass massSq
  simp only [Fin.sum_univ_three]
  fun_prop

theorem zeroExtended_weighted_subset {N : ℕ} (x : FiniteState N)
    (S : Finset Lattice) (w : Lattice → ℝ) (hw : ∀ k,0≤w k) :
    (∑ k ∈ S,w k*phaseMass (zeroExtend x (embedMode k)))≤
      ∑ k ∈ outputModes N,w k*phaseMass (zeroExtend x (embedMode k)) := by
  classical
  have hz (k : Lattice) (hk : k∉outputModes N) :
      zeroExtend x (embedMode k)=0 := by
    apply zeroExtend_outside
    intro h
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
    exact hk (embedMode_injective he ▸ hp)
  have hzero : (∑ k ∈ S\outputModes N,w k*phaseMass (zeroExtend x (embedMode k)))=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [hz k (Finset.mem_sdiff.mp hk).2]
    simp [phaseMass,massSq]
  calc
    _ = (∑ k ∈ S∩outputModes N,w k*phaseMass (zeroExtend x (embedMode k)))+
        (∑ k ∈ S\outputModes N,w k*phaseMass (zeroExtend x (embedMode k))) := by
      rw [Finset.sum_inter_add_sum_sdiff]
    _ ≤ _ := by
      rw [hzero,add_zero]
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun k _ _=>mul_nonneg (hw k) (phaseMass_nonneg _))

/-- Bounds every finite subset of the actual zero extended state. -/
theorem zeroExtended_mass_subset {N : ℕ} (x : FiniteState N)
    (S : Finset Lattice) :
    (∑ k ∈ S,phaseMass (zeroExtend x (embedMode k)))≤stateEnergy x := by
  have h := zeroExtended_weighted_subset x S (fun _=>1) (fun _=>zero_le_one)
  simpa [stateEnergy,periodicEnergy,phaseMass_eq_energy] using h

/-- Finite-prefix energy and dissipation estimates pass to a selected
limit, with no uniform-in-time high-mode claim. The time integrated
strong norm is formed as a genuine summable series of modal integrals.
A separate Tonelli attachment identifies it with a spatial L² norm. -/
theorem integrated_modal_strong_limit (T B D : ℝ)
    (hT : 0≤T) (hB : 0≤B) (hD : 0≤D)
    (U : ℕ → Lattice → ℝ → CVec3) (V : Lattice → ℝ → CVec3)
    (hc : ∀ n k,ContinuousOn (U n k) (Icc 0 T))
    (hv : ∀ k,ContinuousOn (V k) (Icc 0 T))
    (hconv : ∀ k t,t∈Icc 0 T → Tendsto (fun n=>U n k t) atTop (𝓝 (V k t)))
    (hE : ∀ n t,t∈Icc 0 T → ∀ S : Finset Lattice,
      ∑ k ∈ S,phaseMass (U n k t)≤B)
    (hIntD : ∀ n (S : Finset Lattice),
      ∑ k ∈ S, (∫ t in 0..T,massSq (embedMode k)*phaseMass (U n k t))≤D) :
    (∀ n,Summable (fun k=>∫ t in 0..T,phaseMass (U n k t-V k t))) ∧
    Tendsto (fun n=>∑' k,∫ t in 0..T,phaseMass (U n k t-V k t))
      atTop (𝓝 0) := by
  classical
  have hV (t : ℝ) (ht : t∈Icc 0 T) (S : Finset Lattice) :
      ∑ k ∈ S,phaseMass (V k t)≤B :=
    finite_mass_limit (fun n k=>phaseMass (U n k t)) (fun k=>phaseMass (V k t))
      (fun k=>phaseMass_continuous.continuousAt.tendsto.comp (hconv k t ht)) B
      (fun n S=>hE n t ht S) S
  have hUone (n : ℕ) (k : Lattice) (t : ℝ) (ht : t∈Icc 0 T) :
      phaseMass (U n k t)≤B := by simpa using hE n t ht {k}
  have hVone (k : Lattice) (t : ℝ) (ht : t∈Icc 0 T) :
      phaseMass (V k t)≤B := by simpa using hV t ht {k}
  have hDI (k : Lattice) :
      Tendsto (fun n=>∫ t in 0..T,massSq (embedMode k)*phaseMass (U n k t))
      atTop (𝓝 (∫ t in 0..T,massSq (embedMode k)*phaseMass (V k t))) := by
    apply interval_limit_of_bounded_modes T (massSq (embedMode k)*B) hT
    · intro n
      exact (phaseMass_continuous.comp_continuousOn (hc n k)).const_mul _
    · intro n t ht
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (massSq_nonnegative _) (phaseMass_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hUone n k t ht) (massSq_nonnegative _)
    · intro t ht
      exact tendsto_const_nhds.mul (phaseMass_continuous.continuousAt.tendsto.comp (hconv k t ht))
  have hVD (S : Finset Lattice) :
      ∑ k ∈ S,(∫ t in 0..T,massSq (embedMode k)*phaseMass (V k t))≤D :=
    finite_mass_limit _ _ hDI D hIntD S
  let e := fun n k=>∫ t in 0..T,phaseMass (U n k t-V k t)
  have he : ∀ n k,0≤e n k := fun n k=>
    intervalIntegral.integral_nonneg_of_forall hT fun t=>phaseMass_nonneg _
  have hpoint (k : Lattice) : Tendsto (fun n=>e n k) atTop (𝓝 0) := by
    have h := interval_limit_of_bounded_modes T (4*B) hT
      (fun n t=>phaseMass (U n k t-V k t)) (fun _=>0)
      (fun n=>phaseMass_continuous.comp_continuousOn ((hc n k).sub (hv k)))
      (by
        intro n t ht
        rw [Real.norm_eq_abs,abs_of_nonneg (phaseMass_nonneg _)]
        have hh := phaseMass_sub_le (U n k t) (V k t)
        linarith [hUone n k t ht,hVone k t ht])
      (by
        intro t ht
        have hh := phaseMass_continuous.continuousAt.tendsto.comp
          ((hconv k t ht).sub tendsto_const_nhds)
        simpa [phaseMass,massSq] using hh)
    simpa [e] using h
  have htail : ∀ ε>0,∃ S : Finset Lattice,∀ n (W : Finset Lattice),
      Disjoint W S → ∑ k ∈ W,e n k≤ε := by
    intro ε hε
    obtain ⟨R,hR⟩ := exists_nat_gt (4*D/ε+1)
    have hq : 0≤4*D/ε := div_nonneg (by positivity) hε.le
    have hRpos : 0<(R:ℝ) := by linarith
    have hRge : 1≤(R:ℝ) := by linarith
    refine ⟨cutoffModes R,fun n W hW=>?_⟩
    have hfreq (k : Lattice) (hk : k∈W) : (R:ℝ)^2≤massSq (embedMode k) := by
      have hout : k∉cutoffModes R := fun hh=>Finset.disjoint_left.mp hW hk hh
      rw [mem_cutoffModes] at hout
      push_neg at hout
      obtain ⟨i,hi⟩ := hout
      have hi' : (R:ℝ)<|embedMode k i| := by
        rcases hi with h|h
        · have h' : (embedMode k i)< -(R:ℝ) := by exact_mod_cast h
          exact lt_abs.mpr (Or.inl (by linarith))
        · exact (lt_abs.mpr (Or.inr (by exact_mod_cast h)))
      have hs : (embedMode k i)^2≤massSq (embedMode k) :=
        Finset.single_le_sum (fun j _=>sq_nonneg (embedMode k j)) (Finset.mem_univ i)
      nlinarith [sq_abs (embedMode k i),abs_nonneg (embedMode k i)]
    have hint (k : Lattice) (hk : k∈W) :
        (R:ℝ)^2*e n k ≤ 2*((∫ t in 0..T,massSq (embedMode k)*phaseMass (U n k t))+
          (∫ t in 0..T,massSq (embedMode k)*phaseMass (V k t))) := by
      have hcU := (phaseMass_continuous.comp_continuousOn (hc n k)).const_mul (massSq (embedMode k))
      have hcV := (phaseMass_continuous.comp_continuousOn (hv k)).const_mul (massSq (embedMode k))
      have hcE := (phaseMass_continuous.comp_continuousOn ((hc n k).sub (hv k))).const_mul ((R:ℝ)^2)
      have h := intervalIntegral.integral_mono_on hT
        (by rw [← uIcc_of_le hT] at hcE; exact hcE.intervalIntegrable)
        (by have h' := (hcU.add hcV).const_mul 2
            rw [← uIcc_of_le hT] at h'
            exact h'.intervalIntegrable)
        (by
          intro t _
          have h1 := mul_le_mul_of_nonneg_left (phaseMass_sub_le (U n k t) (V k t)) (sq_nonneg (R:ℝ))
          have h2 := mul_le_mul_of_nonneg_right (hfreq k hk)
            (add_nonneg (phaseMass_nonneg (U n k t)) (phaseMass_nonneg (V k t)))
          nlinarith)
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add
          (by rw [← uIcc_of_le hT] at hcU; exact hcU.intervalIntegrable)
          (by rw [← uIcc_of_le hT] at hcV; exact hcV.intervalIntegrable)] at h
      exact h
    have hsum := Finset.sum_le_sum (s:=W) (fun k hk=>hint k hk)
    rw [← Finset.mul_sum,← Finset.mul_sum,Finset.sum_add_distrib] at hsum
    have hbudget : (R:ℝ)^2*(∑ k ∈ W,e n k)≤4*D := by
      linarith [hIntD n W,hVD W]
    have hR' := (div_lt_iff₀ hε).mp (show 4*D/ε<(R:ℝ) by linarith)
    have hR2 : 4*D<ε*(R:ℝ)^2 := by nlinarith
    by_contra! hbad
    have hh := mul_lt_mul_of_pos_left hbad (sq_pos_of_pos hRpos)
    nlinarith
  exact positive_series_prefix_limit e he hpoint htail

end
end DASHI.NavierStokes.PhysicalMixed

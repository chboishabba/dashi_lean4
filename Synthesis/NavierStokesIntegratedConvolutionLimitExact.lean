import Synthesis.NavierStokesOriginalConvolutionSeriesExact
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Time-integrated convergence of the actual fixed-output nonlinear
series, including the infinite summation/integration weld. Error
control uses the squared modal L² error, not a cutoff-dependent
pointwise derivative norm or an assumed smooth limit.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open DASHI.NavierStokes.RealContinuation
open Set Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section

theorem divergenceCell_continuousOn (k : Lattice) (i : Fin 3)
    (u v : ℝ → CVec3) (S : Set ℝ)
    (hu : ContinuousOn u S) (hv : ContinuousOn v S) :
    ContinuousOn (fun t=>divergenceCell k (u t) (v t) i) S := by
  unfold divergenceCell projectedConvection rawConvection outputDot
  simp only [Fin.sum_univ_three]
  fun_prop

theorem integrated_finite_mass_bound (T B : ℝ) (hT : 0≤T)
    (U : Lattice → ℝ → CVec3)
    (hc : ∀ k,ContinuousOn (U k) (Icc 0 T))
    (hE : ∀ t∈Icc 0 T,∀ S : Finset Lattice,∑ p ∈ S,phaseMass (U p t)≤B)
    (S : Finset Lattice) :
    ∑ p ∈ S,(∫ t in 0..T,phaseMass (U p t))≤B*T := by
  have hi (p : Lattice) : IntervalIntegrable (fun t=>phaseMass (U p t)) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT]
    exact phaseMass_continuous.comp_continuousOn (hc p)
  rw [← intervalIntegral.integral_finset_sum (fun p _=>hi p)]
  have hs : IntervalIntegrable (fun t=>∑ p ∈ S,phaseMass (U p t)) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT]
    apply continuousOn_finset_sum
    intro p _
    exact phaseMass_continuous.comp_continuousOn (hc p)
  have h := intervalIntegral.integral_mono_on hT hs intervalIntegrable_const
    (fun t ht=>hE t ht S)
  simpa [mul_comm] using h

theorem integrated_cell_abs_summable (T B : ℝ) (hT : 0≤T)
    (U : Lattice → ℝ → CVec3)
    (hc : ∀ k,ContinuousOn (U k) (Icc 0 T))
    (hE : ∀ t∈Icc 0 T,∀ S : Finset Lattice,∑ p ∈ S,phaseMass (U p t)≤B)
    (k : Lattice) (hk : k≠0) (i : Fin 3) :
    Summable (fun p : Lattice=>∫ t in 0..T,‖divergenceCell k (U p t) (U (k-p) t) i‖) := by
  classical
  have hinj : Function.Injective (fun p : Lattice=>k-p) := fun _ _ h=>sub_left_injective h
  have hmass := integrated_finite_mass_bound T B hT U hc hE
  apply summable_of_sum_le (c:=Real.sqrt (massSq (embedMode k))*B*T)
    (fun p=>intervalIntegral.integral_nonneg_of_forall hT fun t=>norm_nonneg _)
  intro S
  let r := Real.sqrt (massSq (embedMode k))
  have hr : 0≤r := Real.sqrt_nonneg _
  have hi (p : Lattice) : IntervalIntegrable (fun t=>phaseMass (U p t)) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT]
    exact phaseMass_continuous.comp_continuousOn (hc p)
  have hterm (p : Lattice) :
      (∫ t in 0..T,‖divergenceCell k (U p t) (U (k-p) t) i‖) ≤
      r*((∫ t in 0..T,phaseMass (U p t))+
        (∫ t in 0..T,phaseMass (U (k-p) t)))/2 := by
    have hf : IntervalIntegrable (fun t=>‖divergenceCell k (U p t) (U (k-p) t) i‖) volume 0 T := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hT]
      exact (divergenceCell_continuousOn k i _ _ _ (hc p) (hc (k-p))).norm
    have hg := ((hi p).add (hi (k-p))).const_mul (r/2)
    have h := intervalIntegral.integral_mono_on hT hf hg (by
      intro t _
      have h1 := divergenceCell_bound k hk (U p t) (U (k-p) t) i
      have h2 := weighted_young_amplitudes (U p t) (U (k-p) t) 1 (by norm_num)
      simp only [div_one,one_mul] at h2
      have hh := mul_le_mul_of_nonneg_left h2 hr
      change ‖divergenceCell k (U p t) (U (k-p) t) i‖≤_
      change ‖divergenceCell k (U p t) (U (k-p) t) i‖≤
        r*amplitude (U p t)*amplitude (U (k-p) t) at h1
      linarith [show r*amplitude (U p t)*amplitude (U (k-p) t)=
        r*(amplitude (U p t)*amplitude (U (k-p) t)) by ring])
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add (hi p) (hi (k-p))] at h
    linarith
  have ht : (∑ p ∈ S,∫ t in 0..T,phaseMass (U (k-p) t))≤B*T := by
    rw [← Finset.sum_image hinj.injOn]
    exact hmass _
  calc
    _ ≤ ∑ p ∈ S,r*((∫ t in 0..T,phaseMass (U p t))+
        (∫ t in 0..T,phaseMass (U (k-p) t)))/2 :=
      Finset.sum_le_sum fun p _=>hterm p
    _ ≤ _ := by
      rw [← Finset.sum_div,← Finset.mul_sum,Finset.sum_add_distrib]
      have hh := mul_le_mul_of_nonneg_left (add_le_add (hmass S) ht) hr
      change _≤r*B*T
      linarith

/-- Absolute summability of the time-integrated norms allows the
literal infinite convolution to commute with the real time integral. -/
theorem modeForceSeries_integral_eq (T B : ℝ) (hT : 0≤T)
    (U : Lattice → ℝ → CVec3)
    (hc : ∀ k,ContinuousOn (U k) (Icc 0 T))
    (hE : ∀ t∈Icc 0 T,∀ S : Finset Lattice,∑ p ∈ S,phaseMass (U p t)≤B)
    (k : Lattice) (hk : k≠0) (i : Fin 3) :
    (∫ t in 0..T,modeForceSeries k (fun p=>U p t) i)=
      ∑' p : Lattice,∫ t in 0..T,divergenceCell k (U p t) (U (k-p) t) i := by
  have hi (p : Lattice) :
      IntervalIntegrable (fun t=>divergenceCell k (U p t) (U (k-p) t) i) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT]
    exact divergenceCell_continuousOn k i _ _ _ (hc p) (hc (k-p))
  simp only [intervalIntegral.integral_of_le hT,modeForceSeries]
  symm
  apply MeasureTheory.integral_tsum_of_summable_integral_norm
  · exact fun p=>(hi p).1
  · simpa only [intervalIntegral.integral_of_le hT] using
      integrated_cell_abs_summable T B hT U hc hE k hk i

/-- The summable series of actual coefficient integrals has a quantitative
bilinear difference. This gives convergence of the time primitive
without assigning a new external forcing term. -/
theorem integrated_modeForce_difference (T B : ℝ) (hT : 0≤T)
    (U V : Lattice → ℝ → CVec3)
    (hcU : ∀ k,ContinuousOn (U k) (Icc 0 T))
    (hcV : ∀ k,ContinuousOn (V k) (Icc 0 T))
    (hEU : ∀ t∈Icc 0 T,∀ S : Finset Lattice,∑ p ∈ S,phaseMass (U p t)≤B)
    (hEV : ∀ t∈Icc 0 T,∀ S : Finset Lattice,∑ p ∈ S,phaseMass (V p t)≤B)
    (herror : Summable (fun p : Lattice=>∫ t in 0..T,phaseMass (U p t-V p t)))
    (k : Lattice) (hk : k≠0) (i : Fin 3) (ε : ℝ) (he : 0<ε) :
    ‖(∫ t in 0..T,modeForceSeries k (fun p=>U p t) i)-
      (∫ t in 0..T,modeForceSeries k (fun p=>V p t) i)‖≤
      Real.sqrt (massSq (embedMode k))*
        ((∑' p : Lattice,∫ t in 0..T,phaseMass (U p t-V p t))/ε+ε*B*T) := by
  classical
  let r := Real.sqrt (massSq (embedMode k))
  let e := fun p : Lattice=>∫ t in 0..T,phaseMass (U p t-V p t)
  let A := fun p : Lattice=>∫ t in 0..T,divergenceCell k (U p t) (U (k-p) t) i
  let C := fun p : Lattice=>∫ t in 0..T,divergenceCell k (V p t) (V (k-p) t) i
  have hinj : Function.Injective (fun p : Lattice=>k-p) := fun _ _ h=>sub_left_injective h
  have hr : 0≤r := Real.sqrt_nonneg _
  have he0 (p : Lattice) : 0≤e p :=
    intervalIntegral.integral_nonneg_of_forall hT fun t=>phaseMass_nonneg _
  have hsA : Summable A := (integrated_cell_abs_summable T B hT U hcU hEU k hk i).of_norm_bounded
    (fun p=>intervalIntegral.norm_integral_le_integral_norm hT)
  have hsC : Summable C := (integrated_cell_abs_summable T B hT V hcV hEV k hk i).of_norm_bounded
    (fun p=>intervalIntegral.norm_integral_le_integral_norm hT)
  have hmassU := integrated_finite_mass_bound T B hT U hcU hEU
  have hmassV := integrated_finite_mass_bound T B hT V hcV hEV
  have hbound (S : Finset Lattice) :
      ∑ p ∈ S,‖A p-C p‖≤r*((∑' p,e p)/ε+ε*B*T) := by
    have hi (W : Lattice → ℝ → CVec3) (hc : ∀ p,ContinuousOn (W p) (Icc 0 T)) (p : Lattice) :
        IntervalIntegrable (fun t=>phaseMass (W p t)) volume 0 T := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hT]
      exact phaseMass_continuous.comp_continuousOn (hc p)
    have hdiff (p : Lattice) :
        IntervalIntegrable (fun t=>phaseMass (U p t-V p t)) volume 0 T :=
      hi (fun p t=>U p t-V p t) (fun p=>(hcU p).sub (hcV p)) p
    have ha (p : Lattice) :
        IntervalIntegrable (fun t=>divergenceCell k (U p t) (U (k-p) t) i) volume 0 T := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hT]
      exact divergenceCell_continuousOn k i _ _ _ (hcU p) (hcU (k-p))
    have hb (p : Lattice) :
        IntervalIntegrable (fun t=>divergenceCell k (V p t) (V (k-p) t) i) volume 0 T := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hT]
      exact divergenceCell_continuousOn k i _ _ _ (hcV p) (hcV (k-p))
    have hterm (p : Lattice) :
        ‖A p-C p‖≤r/2*((e p+e (k-p))/ε+ε*
          ((∫ t in 0..T,phaseMass (U (k-p) t))+(∫ t in 0..T,phaseMass (V p t)))) := by
      dsimp [A,C]
      rw [← intervalIntegral.integral_sub (ha p) (hb p)]
      apply (intervalIntegral.norm_integral_le_integral_norm hT).trans
      have hm := (((hdiff p).add (hdiff (k-p))).div_const ε).add
        (((hi U hcU (k-p)).add (hi V hcV p)).const_mul ε)
      have h := intervalIntegral.integral_mono_on hT ((ha p).sub (hb p)).norm
        (hm.const_mul (r/2)) (by
          intro t _
          have hh := divergenceCell_difference_bound k hk (U p t) (U (k-p) t)
            (V p t) (V (k-p) t) i ε he
          change _≤r*((phaseMass (U p t-V p t)+phaseMass (U (k-p) t-V (k-p) t))/ε+
            ε*(phaseMass (U (k-p) t)+phaseMass (V p t)))/2 at hh
          convert hh using 1 <;> ring)
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (((hdiff p).add (hdiff (k-p))).div_const ε)
          (((hi U hcU (k-p)).add (hi V hcV p)).const_mul ε),
        intervalIntegral.integral_div,intervalIntegral.integral_add (hdiff p) (hdiff (k-p)),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (hi U hcU (k-p)) (hi V hcV p)] at h
      exact h
    have h1 := herror.sum_le_tsum S (fun p _=>he0 p)
    have h2 : ∑ p ∈ S,e (k-p)≤∑' p,e p := by
      rw [← Finset.sum_image hinj.injOn]
      exact herror.sum_le_tsum _ (fun p _=>he0 p)
    have h3 : (∑ p ∈ S,∫ t in 0..T,phaseMass (U (k-p) t))≤B*T := by
      rw [← Finset.sum_image hinj.injOn]
      exact hmassU _
    calc
      _ ≤ ∑ p ∈ S,r/2*((e p+e (k-p))/ε+ε*
          ((∫ t in 0..T,phaseMass (U (k-p) t))+(∫ t in 0..T,phaseMass (V p t)))) :=
        Finset.sum_le_sum fun p _=>hterm p
      _ ≤ _ := by
        rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.sum_div,
          Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_add_distrib]
        have hE := div_le_div_of_nonneg_right (add_le_add h1 h2) he.le
        have hM := mul_le_mul_of_nonneg_left (add_le_add h3 (hmassV S)) he.le
        have h := mul_le_mul_of_nonneg_left (add_le_add hE hM) (show 0≤r/2 by positivity)
        convert h using 1 <;> ring
  have hnorm := summable_of_sum_le (fun p=>norm_nonneg (A p-C p)) hbound
  rw [modeForceSeries_integral_eq T B hT U hcU hEU k hk i,
    modeForceSeries_integral_eq T B hT V hcV hEV k hk i]
  change ‖(∑' p,A p)-(∑' p,C p)‖≤_
  rw [← hsA.tsum_sub hsC]
  exact (norm_tsum_le_tsum_norm hnorm).trans (Real.tsum_le_of_sum_le (fun _=>norm_nonneg _) hbound)

end
end DASHI.NavierStokes.PhysicalMixed

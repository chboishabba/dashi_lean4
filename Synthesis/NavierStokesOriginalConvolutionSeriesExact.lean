import Synthesis.NavierStokesIntegratedModalStrongLimitExact
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! The original fixed-output divergence-form coefficient, on the
same signed complex Fourier carrier. The infinite sum is absolutely
summable on the energy ball; integrated difference is bounded by the
actual modal strong-error series. Classical Young/Cauchy estimates.
No uniform critical derivative estimate is claimed. -/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open DASHI.NavierStokes.RealContinuation
open Set Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section

def divergenceCell (k : Lattice) (u v : CVec3) (i : Fin 3) : ℂ :=
  -projectedConvection (embedMode k) u v i

theorem divergenceCell_bilinear_difference (k : Lattice)
    (u v u' v' : CVec3) (i : Fin 3) :
    divergenceCell k u v i-divergenceCell k u' v' i =
      divergenceCell k (u-u') v i+divergenceCell k u' (v-v') i := by
  unfold divergenceCell projectedConvection rawConvection outputDot
  simp only [Pi.sub_apply,Fin.sum_univ_three]
  ring

theorem divergenceCell_zero_left (k : Lattice) (v : CVec3) (i : Fin 3) :
    divergenceCell k 0 v i=0 := by
  simp [divergenceCell,projectedConvection,rawConvection,outputDot]

theorem divergenceCell_zero_right (k : Lattice) (u : CVec3) (i : Fin 3) :
    divergenceCell k u 0 i=0 := by
  simp [divergenceCell,projectedConvection,rawConvection,outputDot]

theorem divergenceCell_bound (k : Lattice) (hk : k≠0)
    (u v : CVec3) (i : Fin 3) :
    ‖divergenceCell k u v i‖≤
      Real.sqrt (massSq (embedMode k))*amplitude u*amplitude v := by
  unfold divergenceCell
  rw [norm_neg]
  calc
    _ ≤ amplitude (projectedConvection (embedMode k) u v) :=
      coord_norm_le_amplitude _ _
    _ ≤ _ := by
      unfold amplitude
      have h := Real.sqrt_le_sqrt (projected_cell_mass_bound (embedMode k) u v (mode_mass_pos k hk))
      rw [Real.sqrt_mul (mul_nonneg (massSq_nonnegative _) (phaseMass_nonneg u)),
        Real.sqrt_mul (massSq_nonnegative _)] at h
      exact h

theorem weighted_young_amplitudes (u v : CVec3) (ε : ℝ) (he : 0<ε) :
    amplitude u*amplitude v≤(phaseMass u/ε+ε*phaseMass v)/2 := by
  have h := sq_nonneg (amplitude u-ε*amplitude v)
  rw [sub_sq, mul_pow,amplitude_sq,amplitude_sq] at h
  have hh : (phaseMass u/ε+ε*phaseMass v)/2* (2*ε) =
      phaseMass u+ε^2*phaseMass v := by field_simp [he.ne'] <;> ring
  apply le_of_mul_le_mul_right (b:=2*ε) _ (by positivity)
  rw [hh]
  nlinarith only [h]

theorem divergenceCell_difference_bound (k : Lattice) (hk : k≠0)
    (u v u' v' : CVec3) (i : Fin 3) (ε : ℝ) (he : 0<ε) :
    ‖divergenceCell k u v i-divergenceCell k u' v' i‖≤
      Real.sqrt (massSq (embedMode k))*
        ((phaseMass (u-u')+phaseMass (v-v'))/ε+
          ε*(phaseMass v+phaseMass u'))/2 := by
  rw [divergenceCell_bilinear_difference]
  have h1 := divergenceCell_bound k hk (u-u') v i
  have h2 := divergenceCell_bound k hk u' (v-v') i
  have hy1 := weighted_young_amplitudes (u-u') v ε he
  have hy2 := weighted_young_amplitudes (v-v') u' ε he
  let r := Real.sqrt (massSq (embedMode k))
  have hr : 0≤r := Real.sqrt_nonneg _
  have h3 := mul_le_mul_of_nonneg_left hy1 hr
  have h4 := mul_le_mul_of_nonneg_left hy2 hr
  change ‖divergenceCell k (u-u') v i+divergenceCell k u' (v-v') i‖≤_
  calc
    _ ≤ ‖divergenceCell k (u-u') v i‖+‖divergenceCell k u' (v-v') i‖ :=
      norm_add_le _ _
    _ ≤ _ := by
      change ‖divergenceCell k (u-u') v i‖≤r*amplitude (u-u')*amplitude v at h1
      change ‖divergenceCell k u' (v-v') i‖≤r*amplitude u'*amplitude (v-v') at h2
      change _≤r*((phaseMass (u-u')+phaseMass (v-v'))/ε+
        ε*(phaseMass v+phaseMass u'))/2
      ring_nf at h1 h2 h3 h4 ⊢
      linarith

def modeForceSeries (k : Lattice) (U : Lattice → CVec3) (i : Fin 3) : ℂ :=
  ∑' p : Lattice,divergenceCell k (U p) (U (k-p)) i

/-- Fixed-output absolute convergence from finite energy budgets,
including the reflected translate p -> k-p as an injective map. -/
theorem modeForceSeries_summable (k : Lattice) (hk : k≠0)
    (U : Lattice → CVec3) (B : ℝ)
    (hE : ∀ S : Finset Lattice,∑ p ∈ S,phaseMass (U p)≤B)
    (i : Fin 3) :
    Summable (fun p : Lattice=>‖divergenceCell k (U p) (U (k-p)) i‖) ∧
    ‖modeForceSeries k U i‖≤Real.sqrt (massSq (embedMode k))*B := by
  classical
  have hinj : Function.Injective (fun p : Lattice=>k-p) := by
    intro a b h
    exact sub_left_injective h
  have hs (S : Finset Lattice) :
      ∑ p ∈ S,‖divergenceCell k (U p) (U (k-p)) i‖≤
        Real.sqrt (massSq (embedMode k))*B := by
    have htranslate : ∑ p ∈ S,phaseMass (U (k-p))≤B := by
      rw [← Finset.sum_image hinj.injOn]
      exact hE _
    calc
      _ ≤ ∑ p ∈ S,Real.sqrt (massSq (embedMode k))*
          ((phaseMass (U p)+phaseMass (U (k-p)))/2) := by
        apply Finset.sum_le_sum
        intro p _
        have h := divergenceCell_bound k hk (U p) (U (k-p)) i
        have hy := weighted_young_amplitudes (U p) (U (k-p)) 1 (by norm_num)
        simp only [div_one,one_mul] at hy
        calc
          _ ≤ _ := h
          _ = Real.sqrt (massSq (embedMode k))*(amplitude (U p)*amplitude (U (k-p))) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hy (Real.sqrt_nonneg _)
      _ ≤ _ := by
        rw [← Finset.mul_sum,← Finset.sum_div,Finset.sum_add_distrib]
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        linarith [hE S,htranslate]
  have hsum := summable_of_sum_le (fun p=>norm_nonneg (divergenceCell k (U p) (U (k-p)) i)) hs
  refine ⟨hsum,?_⟩
  unfold modeForceSeries
  exact (norm_tsum_le_tsum_norm hsum).trans (Real.tsum_le_of_sum_le (fun _=>norm_nonneg _) hs)

/-- The full series is literally the finite ordered RHS on its
zero-extended cutoff, for every nonzero retained output. -/
theorem modeForceSeries_eq_galerkin (N : ℕ) (x : FiniteState N)
    (k : Lattice) (hk : k∈outputModes N)
    (ht : ∀ p,outputDot (embedMode p) (zeroExtend x (embedMode p))=0)
    (i : Fin 3) :
    modeForceSeries k (fun p=>zeroExtend x (embedMode p)) i =
      galerkinForce N (fun p _=>zeroExtend x p) (embedMode k) 0 i := by
  classical
  let U := fun p : Lattice=>zeroExtend x (embedMode p)
  let S := (orderedFibre N k).image Prod.fst
  have hz (p : Lattice) (hp : p∉cutoffModes N) : U p=0 := by
    apply zeroExtend_outside
    intro h
    obtain ⟨q,hq,he⟩ := Finset.mem_image.mp h
    exact hp (embedMode_injective he ▸ (Finset.mem_erase.mp hq).2)
  have hout (p : Lattice) (hp : p∉S) :
      divergenceCell k (U p) (U (k-p)) i=0 := by
    by_cases h : p∈cutoffModes N
    · have hn : k-p∉cutoffModes N := by
        intro hq
        apply hp
        apply Finset.mem_image.mpr
        refine ⟨(p,k-p), (mem_orderedFibre N k _).mpr ⟨h,hq,?_⟩,rfl⟩
        abel
      rw [hz _ hn,divergenceCell_zero_right]
    · rw [hz _ h,divergenceCell_zero_left]
  unfold modeForceSeries
  rw [tsum_eq_sum (s:=S) hout,galerkinForce_eq_orderedFibre N _ k hk]
  unfold S
  rw [Finset.sum_image (orderedFibre_fst_injOn N k)]
  apply Finset.sum_congr rfl
  intro p hp
  have hr := ((mem_orderedFibre N k p).mp hp).2.2
  have hq : k-p.1=p.2 := by rw [← hr]; abel
  have he := incidence_resonance (⟨p,hp⟩:Incidence N k)
  rw [hq,orderedRHS_divergence _ _ _ _ _ he (ht p.1)]
  rfl

end
end DASHI.NavierStokes.PhysicalMixed

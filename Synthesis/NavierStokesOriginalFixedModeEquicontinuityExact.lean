import Synthesis.NavierStokesRealEnergyPrefixTailExact
import Mathlib.Analysis.Calculus.MeanValue

/-!
Fixed-output equicontinuity on the original finite ordered Fourier
fibre. Both projection maps p and q are injective at fixed k; hence
the energy cost of each is at most one global energy, not the number
of resonances. This is the low-prefix companion to integrated tails.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open MeasureTheory Set
open scoped BigOperators
noncomputable section

theorem phaseMass_eq_energy (u : CVec3) : phaseMass u=realHermitian u u := by
  rw [phaseMass_eq_complex_normSq_sum]
  simp [realHermitian,Complex.normSq_apply]

theorem coord_norm_le_amplitude (u : CVec3) (i : Fin 3) :
    ‖u i‖≤amplitude u := by
  apply Real.le_sqrt_of_sq_le
  rw [Complex.sq_norm,phaseMass_eq_complex_normSq_sum]
  exact Finset.single_le_sum (fun j _=>Complex.normSq_nonneg (u j)) (Finset.mem_univ i)

theorem ordered_coordinate_bound (k p q : Vec3) (u v : CVec3)
    (hk : p+q=k) (ht : outputDot p u=0) (hm : 0<massSq k)
    (i : Fin 3) :
    ‖orderedRHS k q u v i‖≤
      Real.sqrt (massSq k)*(phaseMass u+phaseMass v)/2 := by
  rw [orderedRHS_divergence k p q u v hk ht,norm_neg]
  calc
    _ ≤ amplitude (projectedConvection k u v) := coord_norm_le_amplitude _ _
    _ ≤ Real.sqrt (massSq k)*amplitude u*amplitude v := by
      unfold amplitude
      have h := Real.sqrt_le_sqrt (projected_cell_mass_bound k u v hm)
      rw [Real.sqrt_mul (mul_nonneg hm.le (phaseMass_nonneg u)),
        Real.sqrt_mul hm.le] at h
      exact h
    _ ≤ _ := by
      have h := sq_nonneg (amplitude u-amplitude v)
      rw [sub_sq,amplitude_sq,amplitude_sq] at h
      have he : amplitude u*amplitude v≤(phaseMass u+phaseMass v)/2 := by linarith
      calc
        _ = Real.sqrt (massSq k)*(amplitude u*amplitude v) := by ring
        _ ≤ Real.sqrt (massSq k)*((phaseMass u+phaseMass v)/2) :=
          mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)
        _ = _ := by ring

theorem orderedFibre_fst_injOn (N : ℕ) (k : Lattice) :
    Set.InjOn Prod.fst (orderedFibre N k : Set (Lattice×Lattice)) := by
  intro a ha b hb he
  have ha' := (mem_orderedFibre N k a).mp ha
  have hb' := (mem_orderedFibre N k b).mp hb
  apply Prod.ext
  · exact he
  · have h : a.1+a.2=a.1+b.2 := by rw [ha'.2.2,he,hb'.2.2]
    exact add_left_cancel h

theorem orderedFibre_snd_injOn (N : ℕ) (k : Lattice) :
    Set.InjOn Prod.snd (orderedFibre N k : Set (Lattice×Lattice)) := by
  intro a ha b hb he
  have ha' := (mem_orderedFibre N k a).mp ha
  have hb' := (mem_orderedFibre N k b).mp hb
  apply Prod.ext
  · have h : a.1+a.2=b.1+a.2 := by rw [ha'.2.2,he,hb'.2.2]
    exact add_right_cancel h
  · exact he

theorem allModes_energy_eq (N : ℕ) (U : Vec3 → ℝ → CVec3) (t : ℝ)
    (hmean : U (embedMode 0) t=0) :
    (∑ k∈cutoffModes N,phaseMass (U (embedMode k) t))=periodicEnergy N U t := by
  have hz : (0:Lattice)∈cutoffModes N := (mem_cutoffModes N 0).mpr (by intro i; simp)
  rw [← Finset.sum_erase_add _ _ hz]
  simp [outputModes,periodicEnergy,phaseMass_eq_energy,hmean,realHermitian]

theorem ordered_fst_energy_le (N : ℕ) (k : Lattice) (U : Vec3 → ℝ → CVec3) (t : ℝ)
    (hmean : U (embedMode 0) t=0) :
    (∑ a∈orderedFibre N k,phaseMass (U (embedMode a.1) t))≤periodicEnergy N U t := by
  rw [← allModes_energy_eq N U t hmean,← Finset.sum_image (orderedFibre_fst_injOn N k)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    exact ((mem_orderedFibre N k a).mp ha).1
  · intro p _ _
    exact phaseMass_nonneg _

theorem ordered_snd_energy_le (N : ℕ) (k : Lattice) (U : Vec3 → ℝ → CVec3) (t : ℝ)
    (hmean : U (embedMode 0) t=0) :
    (∑ a∈orderedFibre N k,phaseMass (U (embedMode a.2) t))≤periodicEnergy N U t := by
  rw [← allModes_energy_eq N U t hmean,← Finset.sum_image (orderedFibre_snd_injOn N k)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    exact ((mem_orderedFibre N k a).mp ha).2.1
  · intro p _ _
    exact phaseMass_nonneg _

theorem mode_mass_pos (k : Lattice) (hk : k≠0) : 0<massSq (embedMode k) := by
  by_contra! hn
  have hzero : massSq (embedMode k)=0 := le_antisymm hn (massSq_nonnegative _)
  apply hk
  apply embedMode_injective
  funext i
  have hi : (embedMode k i)^2≤massSq (embedMode k) :=
    Finset.single_le_sum (fun j _=>sq_nonneg (embedMode k j)) (Finset.mem_univ i)
  rw [hzero] at hi
  have he : embedMode k i=0 := by nlinarith
  simpa [embedMode] using he

theorem original_force_coordinate_bound (N : ℕ) (k : Lattice)
    (U : Vec3 → ℝ → CVec3) (t : ℝ) (i : Fin 3)
    (htrans : ∀ p,outputDot (embedMode p) (U (embedMode p) t)=0)
    (hmean : U (embedMode 0) t=0) :
    ‖galerkinForce N U (embedMode k) t i‖≤
      Real.sqrt (massSq (embedMode k))*periodicEnergy N U t := by
  classical
  have he : 0≤periodicEnergy N U t :=
    Finset.sum_nonneg fun j _=>modeEnergy_nonnegative _
  by_cases hk : k∈outputModes N
  · rw [galerkinForce_eq_orderedFibre N U k hk]
    calc
      _ ≤ ∑ a∈orderedFibre N k,
          ‖orderedRHS (embedMode k) (embedMode a.2)
            (U (embedMode a.1) t) (U (embedMode a.2) t) i‖ := norm_sum_le _ _
      _ ≤ ∑ a∈orderedFibre N k,
          Real.sqrt (massSq (embedMode k))*
            (phaseMass (U (embedMode a.1) t)+phaseMass (U (embedMode a.2) t))/2 := by
        apply Finset.sum_le_sum
        intro a ha
        have h := incidence_resonance (⟨a,ha⟩:Incidence N k)
        exact ordered_coordinate_bound _ _ _ _ _ h (htrans a.1)
          (mode_mass_pos k (Finset.mem_erase.mp hk).1) i
      _ ≤ _ := by
        have hp := ordered_fst_energy_le N k U t hmean
        have hq := ordered_snd_energy_le N k U t hmean
        have hs := add_le_add hp hq
        have h := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (massSq (embedMode k)))
        rw [← Finset.sum_div,← Finset.mul_sum,Finset.sum_add_distrib]
        linarith
  · have hout : embedMode k∉(outputModes N).image embedMode := by
      intro h
      obtain ⟨p,hp,heq⟩ := Finset.mem_image.mp h
      exact hk (embedMode_injective heq ▸ hp)
    simp [galerkinForce,hout,mul_nonneg (Real.sqrt_nonneg _) he]

/-- The fixed mode has a cutoff-independent time Lipschitz constant.
This is sufficient for finite-prefix Arzela-Ascoli, not full strong
continuity in the critical norm. -/
theorem fixed_mode_time_bound (N : ℕ) (ν B T : ℝ)
    (hν : 0≤ν) (hB : 0≤B)
    (x : ℝ → FiniteState N) (a : ℝ) (ha : a<0) (hT : 0≤T)
    (hr : reflectState (x 0)=x 0)
    (ht : ∀ k,outputDot k (zeroExtend (x 0) k)=0)
    (henergy : stateEnergy (x 0)≤B)
    (hd : DASHI.NavierStokes.RealContinuation.SolvesOn (finiteForce N ν) x (Ioi a))
    (k : Lattice) (i : Fin 3) (s t : ℝ) (hs : 0≤s) (hst : s≤t) (htT : t≤T) :
    ‖zeroExtend (x t) (embedMode k) i-zeroExtend (x s) (embedMode k) i‖≤
      (ν*massSq (embedMode k)*Real.sqrt B+Real.sqrt (massSq (embedMode k))*B)*(t-s) := by
  let U := fun k s=>zeroExtend (x s) k
  let b := T+1
  have hb : 0<b := by dsimp [b]; linarith
  have hsol : DASHI.NavierStokes.RealContinuation.SolvesOn (finiteForce N ν) x (Ioo a b) :=
    fun r hr'=>hd r hr'.1
  have htr (r : ℝ) (hr0 : 0≤r) (p : Vec3) :
      outputDot p (U p r)=0 := by
    apply transverse_preserved N ν U r hr0 p (ht p)
    intro v hv j
    exact zeroExtend_ODE_of_derivative N ν x v (hd v (ha.trans_le hv.1)) p j
  apply norm_image_sub_le_of_norm_deriv_le_segment'
    (f':=fun r=>-((ν*massSq (embedMode k):ℝ):ℂ)*U (embedMode k) r i+
      galerkinForce N U (embedMode k) r i) _ _ t ⟨hst,le_rfl⟩
  · intro r hr'
    exact (zeroExtend_ODE_of_derivative N ν x r (hd r (ha.trans_le (hs.trans hr'.1))) _ _).hasDerivWithinAt
  · intro r hr'
    have hr0 := hs.trans hr'.1
    have hrb : r<b := by dsimp [b]; linarith [hr'.2]
    have hEn₀ := forward_energy_bound N ν a b hν x ha hb hr ht hsol r ⟨hr0,hrb⟩
    change stateEnergy (x r)≤stateEnergy (x 0) at hEn₀
    have hEn : stateEnergy (x r)≤B := hEn₀.trans henergy
    have hforce := original_force_coordinate_bound N k U r i
      (fun p=>htr r hr0 _) (zeroExtend_mean (x r))
    have hcoord : ‖U (embedMode k) r i‖≤Real.sqrt B := by
      by_cases hk : k∈outputModes N
      · rw [show U (embedMode k) r=zeroExtend (x r) (embedMode (⟨k,hk⟩:Mode N).1) from rfl,
          zeroExtend_at]
        exact Real.le_sqrt_of_sq_le ((coordinate_square_le_energy (x r) ⟨k,hk⟩ i).trans hEn)
      · have ho : embedMode k∉(outputModes N).image embedMode := by
          intro h
          obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
          exact hk (embedMode_injective he ▸ hp)
        simp [U,zeroExtend_outside _ _ ho,Real.sqrt_nonneg]
    have hmass := massSq_nonnegative (embedMode k)
    calc
      _ ≤ ‖-((ν*massSq (embedMode k):ℝ):ℂ)*U (embedMode k) r i‖+
          ‖galerkinForce N U (embedMode k) r i‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg hν hmass)]
        exact add_le_add (mul_le_mul_of_nonneg_left hcoord (mul_nonneg hν hmass))
          (hforce.trans (mul_le_mul_of_nonneg_left hEn (Real.sqrt_nonneg _)))

end
end DASHI.NavierStokes.PhysicalMixed

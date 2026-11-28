import Synthesis.NavierStokesOriginalPeriodicEnergyFTCExact

namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem galerkinForce_zero_mode (N : ℕ) (U : Vec3 → ℝ → CVec3) (t : ℝ) :
    galerkinForce N U (embedMode 0) t=0 := by
  have h : embedMode 0 ∉ (outputModes N).image embedMode := by
    intro hm
    obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hm
    have hk0 := embedMode_injective he
    exact (Finset.mem_erase.mp hk).1 hk0
  funext i
  simp [galerkinForce,h]

/-- Mean is preserved on the same actual modal ODE, not imposed at
every time. No reality or transverse hypothesis is needed. -/
theorem periodic_mean_preserved (N : ℕ) (ν T : ℝ)
    (U : Vec3 → ℝ → CVec3)
    (hODE : ∀ t ∈ Set.uIcc 0 T,∀ k i,HasDerivAt (fun s=>U k s i)
      (-((ν*massSq k:ℝ):ℂ)*U k t i+galerkinForce N U k t i) t) :
    U (embedMode 0) T=U (embedMode 0) 0 := by
  funext i
  have hd : ∀ t ∈ Set.uIcc 0 T,HasDerivAt
      (fun s=>U (embedMode 0) s i) 0 t := by
    intro t ht
    have h := hODE t ht (embedMode 0) i
    simpa [galerkinForce_zero_mode,embedMode,massSq] using h
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ=>(0:ℂ)) volume 0 T)
  exact sub_eq_zero.mp (by simpa using h.symm)

/-- Exact unweighted tail estimate on the original output cube:
the large-radius energy tail is paid by actual dissipation.
This is not a critical-time uniform estimate. -/
theorem periodic_tail_energy_le (N : ℕ) (U : Vec3 → ℝ → CVec3)
    (t R : ℝ) (hR : 0<R) :
    R^2*(∑ k ∈ (outputModes N).filter (fun k=>R^2≤massSq (embedMode k)),
      realHermitian (U (embedMode k) t) (U (embedMode k) t))≤
      periodicDissipation N U t := by
  classical
  have hn (k : Lattice) :
      0≤realHermitian (U (embedMode k) t) (U (embedMode k) t) := by
    unfold realHermitian
    apply Finset.sum_nonneg
    intro i _
    positivity
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ k ∈ (outputModes N).filter (fun k=>R^2≤massSq (embedMode k)),
      massSq (embedMode k)*realHermitian (U (embedMode k) t) (U (embedMode k) t) := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_right (Finset.mem_filter.mp hk).2 (hn k)
    _ ≤ periodicDissipation N U t := by
        unfold periodicDissipation
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro k _ _
        exact mul_nonneg (massSq_nonnegative _) (hn k)

/-- The actual Leray output is transverse, including the zero mode.
The mass-zero branch is handled explicitly rather than dividing by it. -/
theorem actual_leray_transverse (k : Vec3) (v : CVec3) :
    outputDot k (lerayVector k v)=0 := by
  by_cases hm : massSq k=0
  · have hk (i : Fin 3) : k i=0 := by
      have hb : (k i)^2≤massSq k :=
        Finset.single_le_sum (fun j _=>sq_nonneg (k j)) (Finset.mem_univ i)
      rw [hm] at hb
      nlinarith [sq_nonneg (k i)]
    simp [outputDot,hk]
  · have hm' : (massSq k:ℂ)≠0 := by exact_mod_cast hm
    let d := outputDot k v
    change (∑ i : Fin 3,(k i:ℂ)*(v i-((k i/massSq k:ℝ):ℂ)*d))=0
    have hs : (∑ i : Fin 3,(k i:ℂ)^2)=(massSq k:ℂ) := by
      simp [massSq,Fin.sum_univ_three]
    have hd : (∑ i : Fin 3,(k i:ℂ)*v i)=d := rfl
    simp only [Complex.ofReal_div,mul_sub,Finset.sum_sub_distrib]
    rw [hd]
    have he : (∑ i : Fin 3,(k i:ℂ)*((k i:ℂ)/(massSq k:ℂ)*d))=d := by
      calc
        _ = (∑ i : Fin 3,(k i:ℂ)^2)/(massSq k:ℂ)*d := by
          simp only [Fin.sum_univ_three]
          ring
        _ = d := by rw [hs,div_self hm',one_mul]
    rw [he,sub_self]

theorem actual_ordered_rhs_transverse (k q : Vec3) (u v : CVec3) :
    outputDot k (orderedRHS k q u v)=0 := by
  let w : CVec3 := fun j=>outputDot q u*v j
  have h := actual_leray_transverse k w
  change (∑ i : Fin 3,(k i:ℂ)*(-Complex.I*lerayVector k w i))=0
  calc
    _ = -Complex.I*outputDot k (lerayVector k w) := by
      simp [outputDot,Fin.sum_univ_three] <;> ring
    _ = 0 := by rw [h,mul_zero]

/-- Invariance of the actual finite force's divergence, not a separate
transverse force assumed on the trajectory. -/
theorem actual_galerkin_force_transverse (N : ℕ) (U : Vec3 → ℝ → CVec3)
    (k : Vec3) (t : ℝ) : outputDot k (galerkinForce N U k t)=0 := by
  classical
  unfold galerkinForce
  by_cases hk : k∈(outputModes N).image embedMode
  · simp only [if_pos hk,outputDot,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : embedMode a.1+embedMode a.2=k
    · simp only [if_pos ha]
      exact actual_ordered_rhs_transverse k (embedMode a.2)
        (U (embedMode a.1) t) (U (embedMode a.2) t)
    · simp [ha]
  · simp [hk,outputDot]

end
end DASHI.NavierStokes.PhysicalMixed

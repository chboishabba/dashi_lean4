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

end
end DASHI.NavierStokes.PhysicalMixed

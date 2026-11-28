import Synthesis.NavierStokesActualGlobalFiniteFlowExact

/-!
Real energy-ball prefix reconstruction. The discrete Base369 prefix
balls refine by containment; their real realizations must be closed
and have vanishing diameter, not be ambient clopen. This pays the
actual singleton-intersection property of such a compatible thread.
-/
namespace DASHI.NavierStokes.RealContinuation
open Set Metric
noncomputable section

theorem nested_real_energy_cells_singleton {E : Type*} [MetricSpace E]
    (K : Set E) (hK : IsCompact K)
    (cell : ℕ → Set E) (hsub : cell 0⊆K)
    (hnest : ∀ n,cell (n+1)⊆cell n)
    (hclosed : ∀ n,IsClosed (cell n))
    (hne : ∀ n,(cell n).Nonempty)
    (hdiam : ∀ ε>0,∃ n,∀ x∈cell n,∀ y∈cell n,dist x y≤ε) :
    ∃ x∈K, (⋂ n,cell n)={x} := by
  have h0 : IsCompact (cell 0) := hK.of_isClosed_subset (hclosed 0) hsub
  obtain ⟨x,hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    cell hnest hne h0 hclosed
  refine ⟨x,hsub (mem_iInter.mp hx 0),?_⟩
  ext y
  constructor
  · intro hy
    change y=x
    by_contra hn
    have hd : 0<dist y x := dist_pos.mpr hn
    obtain ⟨n,h⟩ := hdiam (dist y x/2) (by positivity)
    have he := h y (mem_iInter.mp hy n) x (mem_iInter.mp hx n)
    linarith
  · intro hy
    have he : y=x := hy
    simpa [he] using hx

/-- Actual closed ternary interval child. Unlike disjoint address
cylinders, the geometric children share their boundary points. -/
def ternaryChildLower (l h : ℝ) (j : Fin 3) := l+(j.val:ℝ)*h/3

theorem ternary_child_contained (l h : ℝ) (hh : 0≤h) (j : Fin 3) :
    Icc (ternaryChildLower l h j) (ternaryChildLower l h j+h/3)⊆Icc l (l+h) := by
  intro x hx
  fin_cases j <;> simp [ternaryChildLower] at hx <;>
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩

theorem ternary_children_cover (l h : ℝ) (hh : 0≤h) :
    (⋃ j : Fin 3,Icc (ternaryChildLower l h j) (ternaryChildLower l h j+h/3)) =
      Icc l (l+h) := by
  apply Subset.antisymm
  · exact iUnion_subset fun j=>ternary_child_contained l h hh j
  · intro x hx
    by_cases h1 : x≤l+h/3
    · exact mem_iUnion.mpr ⟨0,by simp [ternaryChildLower]; exact ⟨hx.1,h1⟩⟩
    by_cases h2 : x≤l+2*h/3
    · refine mem_iUnion.mpr ⟨1,?_⟩
      simp [ternaryChildLower]
      exact ⟨by linarith,by linarith⟩
    · refine mem_iUnion.mpr ⟨2,?_⟩
      simp [ternaryChildLower]
      exact ⟨by linarith,by linarith [hx.2]⟩

end
end DASHI.NavierStokes.RealContinuation

namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open DASHI.NavierStokes.RealContinuation
open MeasureTheory Set
open scoped BigOperators
noncomputable section

def highEnergy (N : ℕ) (R : ℝ) (U : Vec3 → ℝ → CVec3) (t : ℝ) :=
  ∑ k ∈ (outputModes N).filter (fun k=>R≤Real.sqrt (massSq (embedMode k))),
    realHermitian (U (embedMode k) t) (U (embedMode k) t)

def highHalfEnergy (N : ℕ) (R : ℝ) (U : Vec3 → ℝ → CVec3) (t : ℝ) :=
  ∑ k ∈ (outputModes N).filter (fun k=>R≤Real.sqrt (massSq (embedMode k))),
    Real.sqrt (massSq (embedMode k))*
      realHermitian (U (embedMode k) t) (U (embedMode k) t)

theorem modeEnergy_nonnegative (u : CVec3) : 0≤realHermitian u u := by
  unfold realHermitian
  apply Finset.sum_nonneg
  intro i _
  positivity

theorem highEnergy_payment (N : ℕ) (R : ℝ) (hR : 0≤R)
    (U : Vec3 → ℝ → CVec3) (t : ℝ) :
    R^2*highEnergy N R U t≤periodicDissipation N U t := by
  unfold highEnergy periodicDissipation
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ k ∈ (outputModes N).filter (fun k=>R≤Real.sqrt (massSq (embedMode k))),
        massSq (embedMode k)*realHermitian (U (embedMode k) t) (U (embedMode k) t) := by
      apply Finset.sum_le_sum
      intro k hk
      have h := (Finset.mem_filter.mp hk).2
      apply mul_le_mul_of_nonneg_right _ (modeEnergy_nonnegative _)
      nlinarith [Real.sq_sqrt (massSq_nonnegative (embedMode k)),
        Real.sqrt_nonneg (massSq (embedMode k))]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun k _ _=>
      mul_nonneg (massSq_nonnegative _) (modeEnergy_nonnegative _))

theorem highHalfEnergy_payment (N : ℕ) (R : ℝ)
    (U : Vec3 → ℝ → CVec3) (t : ℝ) :
    R*highHalfEnergy N R U t≤periodicDissipation N U t := by
  unfold highHalfEnergy periodicDissipation
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ k ∈ (outputModes N).filter (fun k=>R≤Real.sqrt (massSq (embedMode k))),
        massSq (embedMode k)*realHermitian (U (embedMode k) t) (U (embedMode k) t) := by
      apply Finset.sum_le_sum
      intro k hk
      have h := (Finset.mem_filter.mp hk).2
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (modeEnergy_nonnegative _)
      have hh := mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg (massSq (embedMode k)))
      simpa [← pow_two,Real.sq_sqrt (massSq_nonnegative (embedMode k))] using hh
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun k _ _=>
      mul_nonneg (massSq_nonnegative _) (modeEnergy_nonnegative _))

theorem highEnergy_continuousOn (N : ℕ) (R T : ℝ) (U : Vec3 → ℝ → CVec3)
    (hc : ∀ k i,ContinuousOn (fun t=>U k t i) (uIcc 0 T)) :
    ContinuousOn (highEnergy N R U) (uIcc 0 T) := by
  unfold highEnergy
  apply continuousOn_finset_sum
  intro k _
  unfold realHermitian
  simp only [Fin.sum_univ_three]
  fun_prop

theorem highHalfEnergy_continuousOn (N : ℕ) (R T : ℝ) (U : Vec3 → ℝ → CVec3)
    (hc : ∀ k i,ContinuousOn (fun t=>U k t i) (uIcc 0 T)) :
    ContinuousOn (highHalfEnergy N R U) (uIcc 0 T) := by
  unfold highHalfEnergy
  apply continuousOn_finset_sum
  intro k _
  apply ContinuousOn.const_mul
  unfold realHermitian
  simp only [Fin.sum_univ_three]
  fun_prop

theorem dissipation_continuousOn (N : ℕ) (T : ℝ) (U : Vec3 → ℝ → CVec3)
    (hc : ∀ k i,ContinuousOn (fun t=>U k t i) (uIcc 0 T)) :
    ContinuousOn (periodicDissipation N U) (uIcc 0 T) := by
  unfold periodicDissipation
  apply continuousOn_finset_sum
  intro k _
  apply ContinuousOn.const_mul
  unfold realHermitian
  simp only [Fin.sum_univ_three]
  fun_prop

/-- Cutoff-uniform INTEGRATED tail from the original energy identity.
This is not a pointwise-in-time critical H^(1/2) bound. -/
theorem integrated_prefix_tail_payment (N : ℕ) (ν R T : ℝ)
    (hν : 0<ν) (hR : 0<R) (hT : 0≤T)
    (U : Vec3 → ℝ → CVec3)
    (hc : ∀ k i,ContinuousOn (fun t=>U k t i) (uIcc 0 T))
    (henergy : periodicEnergy N U T+2*ν*(∫ t in 0..T,periodicDissipation N U t)=
      periodicEnergy N U 0) :
    (∫ t in 0..T,highEnergy N R U t)≤periodicEnergy N U 0/(2*ν*R^2) ∧
    (∫ t in 0..T,highHalfEnergy N R U t)≤periodicEnergy N U 0/(2*ν*R) := by
  have hD := (dissipation_continuousOn N T U hc).intervalIntegrable
  have hE := (highEnergy_continuousOn N R T U hc).const_mul (R^2)
  have hH := (highHalfEnergy_continuousOn N R T U hc).const_mul R
  have he := intervalIntegral.integral_mono_on hT hE.intervalIntegrable hD
    (fun t _=>highEnergy_payment N R hR.le U t)
  have hh := intervalIntegral.integral_mono_on hT hH.intervalIntegrable hD
    (fun t _=>highHalfEnergy_payment N R U t)
  rw [intervalIntegral.integral_const_mul] at he hh
  have hn : 0≤periodicEnergy N U T := by
    unfold periodicEnergy
    exact Finset.sum_nonneg fun k _=>modeEnergy_nonnegative _
  have hd : 2*ν*(∫ t in 0..T,periodicDissipation N U t)≤periodicEnergy N U 0 := by linarith
  constructor
  · apply (le_div_iff₀ (by positivity : 0<2*ν*R^2)).mpr
    have h := mul_le_mul_of_nonneg_left he (by positivity : 0≤2*ν)
    nlinarith
  · apply (le_div_iff₀ (by positivity : 0<2*ν*R)).mpr
    have h := mul_le_mul_of_nonneg_left hh (by positivity : 0≤2*ν)
    nlinarith

end
end DASHI.NavierStokes.PhysicalMixed

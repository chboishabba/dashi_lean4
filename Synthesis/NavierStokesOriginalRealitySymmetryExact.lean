import Synthesis.NavierStokesOriginalDivergenceEvolutionExact

namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open scoped BigOperators
noncomputable section

def realReflect (U : Vec3 → ℝ → CVec3) : Vec3 → ℝ → CVec3 :=
  fun k t i => star (U (-k) t i)

theorem embedMode_neg (p : Lattice) : embedMode (-p) = -embedMode p := by
  funext i
  simp [embedMode]

theorem orderedRHS_neg_conjugate (k q : Vec3) (u v : CVec3) (i : Fin 3) :
    orderedRHS (-k) (-q) (fun j=>star (u j)) (fun j=>star (v j)) i =
      star (orderedRHS k q u v i) := by
  unfold orderedRHS lerayVector outputDot massSq
  simp [Fin.sum_univ_three,Complex.star_def,Complex.conj_ofReal,
    map_add,map_sub,map_mul,map_div,Complex.ofReal_neg,neg_sq] <;> ring

theorem outputModes_neg (N : ℕ) (k : Lattice) (hk : k∈outputModes N) :
    -k∈outputModes N := by
  have h := Finset.mem_erase.mp hk
  exact Finset.mem_erase.mpr ⟨neg_ne_zero.mpr h.1,cutoff_neg N k h.2⟩

/-- Exact signed conjugation of the literal finite ordered force.
The bijection is on the existing ordered pair carrier, not a new
Fourier discretization. -/
theorem actual_force_realReflect (N : ℕ) (U : Vec3 → ℝ → CVec3)
    (k : Vec3) (t : ℝ) (i : Fin 3) :
    galerkinForce N (realReflect U) k t i =
      star (galerkinForce N U (-k) t i) := by
  classical
  have hmem : k∈(outputModes N).image embedMode ↔ -k∈(outputModes N).image embedMode := by
    constructor
    · rintro h
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_image.mpr ⟨-p,outputModes_neg N p hp,embedMode_neg p⟩
    · rintro h
      obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
      exact Finset.mem_image.mpr ⟨-p,outputModes_neg N p hp,by rw [embedMode_neg,he,neg_neg]⟩
  unfold galerkinForce
  by_cases hk : k∈(outputModes N).image embedMode
  · simp only [if_pos hk,if_pos (hmem.mp hk),star_sum]
    apply Finset.sum_nbij' (fun a : Lattice × Lattice => (-a.1,-a.2))
      (fun a : Lattice × Lattice => (-a.1,-a.2))
    · intro a ha
      obtain ⟨hp,hq⟩ := Finset.mem_product.mp ha
      exact Finset.mem_product.mpr ⟨cutoff_neg N _ hp,cutoff_neg N _ hq⟩
    · intro a ha
      obtain ⟨hp,hq⟩ := Finset.mem_product.mp ha
      exact Finset.mem_product.mpr ⟨cutoff_neg N _ hp,cutoff_neg N _ hq⟩
    · intro a _
      simp
    · intro a _
      simp
    · intro a _
      have he : embedMode (-a.1)+embedMode (-a.2)= -k ↔
          embedMode a.1+embedMode a.2=k := by
        rw [embedMode_neg,embedMode_neg,← neg_add,neg_inj]
      by_cases h : embedMode a.1+embedMode a.2=k
      · simp only [if_pos h,if_pos (he.mpr h),realReflect,embedMode_neg]
        have e := orderedRHS_neg_conjugate (-k) (-embedMode a.2)
          (U (-embedMode a.1) t) (U (-embedMode a.2) t) i
        simpa using e
      · simp [h,he]
  · have hn : -k∉(outputModes N).image embedMode := fun h=>hk (hmem.mpr h)
    simp [hk,hn]

/-- Uniqueness on the original ODE carrier, once proved, converts
conjugation covariance into reality. This theorem does not supply ODE
existence or uniqueness. -/
theorem realReflect_fixed_of_unique (U : Vec3 → ℝ → CVec3)
    (hunique : realReflect U=U) (k : Vec3) (t : ℝ) (i : Fin 3) :
    U (-k) t i=star (U k t i) := by
  have h := congrFun (congrFun (congrFun hunique k) t) i
  exact (by simpa [realReflect] using congrArg star h)

end
end DASHI.NavierStokes.PhysicalMixed

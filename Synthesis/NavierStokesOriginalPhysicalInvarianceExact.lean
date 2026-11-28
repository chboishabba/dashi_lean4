import Synthesis.NavierStokesOriginalFiniteLocalFlowExact

/-!
Physical transverse and conjugate-real invariants of the original
Galerkin field. Reality is an equivariance of the same ordered
nonlinearity, not a projection that changes its dynamics.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open scoped BigOperators
noncomputable section

theorem dot_orderedRHS_zero (k q : Vec3) (u v : CVec3) :
    outputDot k (orderedRHS k q u v)=0 := by
  by_cases hk : massSq k=0
  · have h0 (i : Fin 3) : k i=0 := by
      have hi : (k i)^2≤massSq k :=
        Finset.single_le_sum (fun j _=>sq_nonneg (k j)) (Finset.mem_univ i)
      rw [hk] at hi
      nlinarith [sq_nonneg (k i)]
    simp [outputDot,h0]
  · have hkc : (massSq k:ℂ)≠0 := by exact_mod_cast hk
    unfold outputDot orderedRHS lerayVector
    simp only [Fin.sum_univ_three]
    push_cast
    field_simp [hk,hkc]
    unfold massSq
    simp [Fin.sum_univ_three]
    ring

theorem dot_sum_left {J : Type*} (S : Finset J) (k : Vec3) (v : J → CVec3) :
    outputDot k (fun i=>∑ j ∈ S,v j i)=∑ j ∈ S,outputDot k (v j) := by
  classical
  unfold outputDot
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem galerkinForce_transverse (N : ℕ) (U : Vec3 → ℝ → CVec3)
    (k : Vec3) (t : ℝ) :
    outputDot k (galerkinForce N U k t)=0 := by
  by_cases hk : k∈(outputModes N).image embedMode
  · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hk
    rw [show galerkinForce N U (embedMode p) t=
      fun i=>∑ a ∈ orderedFibre N p,
        orderedRHS (embedMode p) (embedMode a.2)
          (U (embedMode a.1) t) (U (embedMode a.2) t) i by
        funext i
        exact galerkinForce_eq_orderedFibre N U p hp t i]
    rw [dot_sum_left]
    simp only [dot_orderedRHS_zero,Finset.sum_const_zero]
  · have h : galerkinForce N U k t=0 := by
      funext i
      simp [galerkinForce,hk]
    simp [h,outputDot]

theorem dot_derivative (k : Vec3) (u : ℝ → CVec3) (d : CVec3) (t : ℝ)
    (h : ∀ i,HasDerivAt (fun s=>u s i) (d i) t) :
    HasDerivAt (fun s=>outputDot k (u s)) (outputDot k d) t := by
  simp only [outputDot,Fin.sum_univ_three]
  exact (((h 0).const_mul (k 0:ℂ)).add ((h 1).const_mul (k 1:ℂ))).add
    ((h 2).const_mul (k 2:ℂ))

theorem dot_damped (k : Vec3) (r : ℝ) (u v : CVec3) :
    outputDot k (fun i=>-(r:ℂ)*u i+v i)=-(r:ℂ)*outputDot k u+outputDot k v := by
  simp [outputDot,Fin.sum_univ_three]
  ring

/-- Scalar heat evolution with zero initial datum. No Lipschitz or
uniqueness assumption about the full nonlinear solution is required. -/
theorem zero_of_damped_real (f : ℝ → ℝ) (r T : ℝ) (hT : 0≤T)
    (h0 : f 0=0)
    (hd : ∀ t ∈ Set.Icc 0 T,HasDerivAt f (-r*f t) t) :
    f T=0 := by
  rcases hT.eq_or_lt with he|hp
  · simpa [← he] using h0
  have hG (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      HasDerivAt (fun s=>Real.exp (r*s)*f s) 0 t := by
    have he := (((hasDerivAt_id t).const_mul r).exp).mul (hd t ht)
    convert he using 1 <;> ring
  have hc : ContinuousOn (fun s=>Real.exp (r*s)*f s) (Set.Icc 0 T) :=
    fun t ht=>(hG t ht).continuousAt.continuousWithinAt
  obtain ⟨c,hc',hs⟩ := exists_hasDerivAt_eq_slope
    (fun s=>Real.exp (r*s)*f s) (fun _=>0) hp hc
    (fun t ht=>hG t (Set.Ioo_subset_Icc_self ht))
  have hz : Real.exp (r*T)*f T=0 := by
    simp [h0] at hs
    exact (div_eq_zero_iff.mp hs.symm).resolve_right (by linarith)
  exact (mul_eq_zero.mp hz).resolve_left (Real.exp_ne_zero _)

theorem transverse_preserved (N : ℕ) (ν : ℝ) (U : Vec3 → ℝ → CVec3)
    (T : ℝ) (hT : 0≤T) (k : Vec3)
    (h0 : outputDot k (U k 0)=0)
    (hODE : ∀ t ∈ Set.Icc 0 T,∀ i,HasDerivAt (fun s=>U k s i)
      (-((ν*massSq k:ℝ):ℂ)*U k t i+galerkinForce N U k t i) t) :
    outputDot k (U k T)=0 := by
  have hd (t : ℝ) (ht : t∈Set.Icc 0 T) :
      HasDerivAt (fun s=>outputDot k (U k s))
        (-((ν*massSq k:ℝ):ℂ)*outputDot k (U k t)) t := by
    have h := dot_derivative k (U k) _ t (hODE t ht)
    rwa [dot_damped,galerkinForce_transverse,add_zero] at h
  apply Complex.ext
  · apply zero_of_damped_real _ (ν*massSq k) T hT (by simp [h0])
    intro t ht
    simpa [Function.comp_def,Complex.mul_re] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt (hd t ht)
  · apply zero_of_damped_real _ (ν*massSq k) T hT (by simp [h0])
    intro t ht
    simpa [Function.comp_def,Complex.mul_im] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt (hd t ht)

theorem orderedRHS_reality (k q : Vec3) (u v : CVec3) (i : Fin 3) :
    orderedRHS (-k) (-q) (fun j=>star (u j)) (fun j=>star (v j)) i =
      star (orderedRHS k q u v i) := by
  have hm : massSq (-k)=massSq k := by
    simp [massSq,Fin.sum_univ_three]
  unfold orderedRHS lerayVector outputDot
  rw [hm]
  apply Complex.ext <;>
    simp [Fin.sum_univ_three,Complex.mul_re,Complex.mul_im,Complex.add_re,
      Complex.add_im,Complex.sub_re,Complex.sub_im,neg_div] <;> ring

def negPair (a : Lattice × Lattice) := (-a.1,-a.2)

theorem negPair_fibre (N : ℕ) (k : Lattice) (a : Lattice × Lattice)
    (ha : a∈orderedFibre N k) : negPair a∈orderedFibre N (-k) := by
  obtain ⟨hp,hq,hk⟩ := (mem_orderedFibre N k a).mp ha
  exact (mem_orderedFibre N (-k) _).mpr
    ⟨cutoff_neg N _ hp,cutoff_neg N _ hq,by simp [negPair,← neg_add,hk]⟩

theorem embedMode_neg (k : Lattice) : embedMode (-k)=-embedMode k := by
  funext i
  simp [embedMode]

/-- Actual force preserves conjugate reality on the full symmetric
cutoff, including zero inputs. -/
theorem galerkinForce_reality (N : ℕ) (U : Vec3 → ℝ → CVec3) (t : ℝ)
    (k : Lattice) (hk : k∈outputModes N)
    (hreal : ∀ p i,U (embedMode (-p)) t i=star (U (embedMode p) t i))
    (i : Fin 3) :
    galerkinForce N U (embedMode (-k)) t i =
      star (galerkinForce N U (embedMode k) t i) := by
  classical
  have hneg : -k∈outputModes N := by
    obtain ⟨hn,hc⟩ := Finset.mem_erase.mp hk
    exact Finset.mem_erase.mpr ⟨neg_ne_zero.mpr hn,cutoff_neg N _ hc⟩
  rw [galerkinForce_eq_orderedFibre N U (-k) hneg,
    galerkinForce_eq_orderedFibre N U k hk,star_sum]
  symm
  apply Finset.sum_nbij' negPair negPair
  · exact negPair_fibre N k
  · intro a ha
    simpa using negPair_fibre N (-k) a ha
  · intro a _
    simp [negPair]
  · intro a _
    simp [negPair]
  · intro a _
    simp only [negPair,hreal,embedMode_neg]
    rw [← orderedRHS_reality]

end
end DASHI.NavierStokes.PhysicalMixed

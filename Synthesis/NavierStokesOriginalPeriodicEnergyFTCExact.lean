import Synthesis.NavierStokesOriginalOrderedEnergyCancellationExact

/-!
Finite original periodic Galerkin energy equality on an actual modal
trajectory, conditional on reality, transverse and mean-zero invariance.
No uniform critical regularity or ODE existence assertion.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open MeasureTheory
open scoped BigOperators
noncomputable section

private theorem derivSum {J : Type*} (S : Finset J) (f : J → ℝ → ℝ)
    (d : J → ℝ) (t : ℝ)
    (h : ∀ j ∈ S,HasDerivAt (f j) (d j) t) :
    HasDerivAt (fun s=>∑ j ∈ S,f j s) (∑ j ∈ S,d j) t := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hasDerivAt_const t (0:ℝ)
  | @insert j S hj ih =>
    have he := (h j (Finset.mem_insert_self j S)).add
      (ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)))
    simpa [Finset.sum_insert hj] using he

theorem modal_energy_derivative (u : ℝ → CVec3) (d : CVec3) (t : ℝ)
    (h : ∀ i,HasDerivAt (fun s=>u s i) (d i) t) :
    HasDerivAt (fun s=>realHermitian (u s) (u s))
      (2*realHermitian d (u t)) t := by
  have hr (i : Fin 3) : HasDerivAt (fun s=>(u s i).re) (d i).re t := by
    simpa [Function.comp_def] using Complex.reCLM.hasFDerivAt.comp_hasDerivAt (h i)
  have hi (i : Fin 3) : HasDerivAt (fun s=>(u s i).im) (d i).im t := by
    simpa [Function.comp_def] using Complex.imCLM.hasFDerivAt.comp_hasDerivAt (h i)
  unfold realHermitian
  rw [Finset.mul_sum]
  apply derivSum
  intro i _
  convert ((hr i).mul (hr i)).add ((hi i).mul (hi i)) using 1 <;> ring

theorem modal_rhs_pair (r : ℝ) (u f : CVec3) :
    realHermitian (fun i=> -(r:ℂ)*u i+f i) u =
      -r*realHermitian u u+realHermitian f u := by
  unfold realHermitian
  simp [Fin.sum_univ_three,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
  ring

def periodicEnergy (N : ℕ) (U : Vec3 → ℝ → CVec3) (t : ℝ) :=
  ∑ k ∈ outputModes N,realHermitian (U (embedMode k) t) (U (embedMode k) t)

def periodicDissipation (N : ℕ) (U : Vec3 → ℝ → CVec3) (t : ℝ) :=
  ∑ k ∈ outputModes N,massSq (embedMode k)*
    realHermitian (U (embedMode k) t) (U (embedMode k) t)

theorem periodicDissipation_nonneg (N : ℕ) (U : Vec3 → ℝ → CVec3) (t : ℝ) :
    0≤periodicDissipation N U t := by
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg (massSq_nonnegative _)
  apply Finset.sum_nonneg
  intro i _
  change 0≤(U (embedMode k) t i).re*(U (embedMode k) t i).re+
    (U (embedMode k) t i).im*(U (embedMode k) t i).im
  positivity

theorem realHermitian_sum_left {J : Type*} (S : Finset J) (f : J → CVec3)
    (v : CVec3) :
    realHermitian (fun i=>∑ j ∈ S,f j i) v =
      ∑ j ∈ S,realHermitian (f j) v := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [realHermitian]
  | @insert j S hj ih =>
    simp only [Finset.sum_insert hj,← ih]
    unfold realHermitian
    simp [Fin.sum_univ_three,Complex.add_re,Complex.add_im]
    ring

theorem literal_force_energy_zero (N : ℕ) (U : Vec3 → ℝ → CVec3) (t : ℝ)
    (htrans : ∀ k,outputDot (embedMode k) (U (embedMode k) t)=0)
    (hreal : ∀ k i,U (embedMode (-k)) t i=star (U (embedMode k) t i))
    (hmean : U (embedMode 0) t=0) :
    (∑ k ∈ outputModes N,realHermitian (galerkinForce N U (embedMode k) t)
      (U (embedMode k) t))=0 := by
  let u : Lattice → CVec3 := fun k=>U (embedMode k) t
  have he := outputEnergyFold_zero N u htrans hreal hmean
  rw [← he]
  apply Finset.sum_congr rfl
  intro k hk
  have hf : galerkinForce N U (embedMode k) t =
      fun i=>∑ a ∈ orderedFibre N k,
        orderedRHS (embedMode k) (embedMode a.2) (u a.1) (u a.2) i :=
    funext fun i=>galerkinForce_eq_orderedFibre N U k hk t i
  rw [hf,realHermitian_sum_left]

theorem periodic_energy_derivative (N : ℕ) (ν : ℝ)
    (U : Vec3 → ℝ → CVec3) (t : ℝ)
    (hODE : ∀ k i,HasDerivAt (fun s=>U k s i)
      (-((ν*massSq k:ℝ):ℂ)*U k t i+galerkinForce N U k t i) t)
    (htrans : ∀ k,outputDot (embedMode k) (U (embedMode k) t)=0)
    (hreal : ∀ k i,U (embedMode (-k)) t i=star (U (embedMode k) t i))
    (hmean : U (embedMode 0) t=0) :
    HasDerivAt (periodicEnergy N U) (-2*ν*periodicDissipation N U t) t := by
  have hd := derivSum (outputModes N)
    (fun k s=>realHermitian (U (embedMode k) s) (U (embedMode k) s))
    (fun k=>2*realHermitian (fun i=> -((ν*massSq (embedMode k):ℝ):ℂ)*
      U (embedMode k) t i+galerkinForce N U (embedMode k) t i)
      (U (embedMode k) t)) t
    (fun k _=>modal_energy_derivative _ _ t (hODE (embedMode k)))
  convert hd using 1
  simp_rw [modal_rhs_pair,mul_add]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,literal_force_energy_zero N U t htrans hreal hmean,mul_zero,add_zero]
  unfold periodicDissipation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Same trajectory, exact finite energy equality over real time.
Integrability of dissipation is supplied by continuity of the modes. -/
theorem periodic_energy_FTC_on_interval (N : ℕ) (ν : ℝ)
    (U : Vec3 → ℝ → CVec3) (T : ℝ)
    (hc : ∀ k i,ContinuousOn (fun s=>U k s i) (Set.uIcc 0 T))
    (hODE : ∀ t ∈ Set.uIcc 0 T,∀ k i,HasDerivAt (fun s=>U k s i)
      (-((ν*massSq k:ℝ):ℂ)*U k t i+galerkinForce N U k t i) t)
    (htrans : ∀ t ∈ Set.uIcc 0 T,∀ k,outputDot (embedMode k) (U (embedMode k) t)=0)
    (hreal : ∀ t ∈ Set.uIcc 0 T,∀ k i,U (embedMode (-k)) t i=star (U (embedMode k) t i))
    (hmean : ∀ t ∈ Set.uIcc 0 T,U (embedMode 0) t=0) :
    periodicEnergy N U T+2*ν*(∫ t in 0..T,periodicDissipation N U t)=
      periodicEnergy N U 0 := by
  have hd : ∀ t ∈ Set.uIcc 0 T,
      HasDerivAt (periodicEnergy N U) (-2*ν*periodicDissipation N U t) t :=
    fun t ht=>periodic_energy_derivative N ν U t (hODE t ht) (htrans t ht)
      (hreal t ht) (hmean t ht)
  have hcont : ContinuousOn (periodicDissipation N U) (Set.uIcc 0 T) := by
    unfold periodicDissipation
    apply continuousOn_finset_sum
    intro k _
    apply ContinuousOn.const_mul
    unfold realHermitian
    simp only [Fin.sum_univ_three]
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((hcont.const_mul (-2*ν)).intervalIntegrable)
  rw [intervalIntegral.integral_const_mul] at hi
  linarith


theorem periodic_energy_FTC (N : ℕ) (ν : ℝ)
    (U : Vec3 → ℝ → CVec3) (T : ℝ)
    (hc : ∀ k i,Continuous (fun s=>U k s i))
    (hODE : ∀ t ∈ Set.uIcc 0 T,∀ k i,HasDerivAt (fun s=>U k s i)
      (-((ν*massSq k:ℝ):ℂ)*U k t i+galerkinForce N U k t i) t)
    (htrans : ∀ t ∈ Set.uIcc 0 T,∀ k,outputDot (embedMode k) (U (embedMode k) t)=0)
    (hreal : ∀ t ∈ Set.uIcc 0 T,∀ k i,U (embedMode (-k)) t i=star (U (embedMode k) t i))
    (hmean : ∀ t ∈ Set.uIcc 0 T,U (embedMode 0) t=0) :
    periodicEnergy N U T+2*ν*(∫ t in 0..T,periodicDissipation N U t)=
      periodicEnergy N U 0 :=
  periodic_energy_FTC_on_interval N ν U T (fun k i=>(hc k i).continuousOn)
    hODE htrans hreal hmean

end
end DASHI.NavierStokes.PhysicalMixed

import Synthesis.NavierStokesOriginalPeriodicModalIntegralLimitExact
import Synthesis.NavierStokesFractionalR568EndpointWeldExact

/-!
Populate the original N2e fractional energy-square FTC input from
the literal Galerkin RHS. Preserve the SIGN of T_a. A uniform upper
bound on integral E_a T_a is not implied by this equality.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open MeasureTheory Set
open scoped BigOperators
noncomputable section

def fractionalEnergy (N : ℕ) (w : Lattice → ℝ) (U : Vec3 → ℝ → CVec3) (t : ℝ) :=
  ∑ k ∈ outputModes N,w k*realHermitian (U (embedMode k) t) (U (embedMode k) t)

def fractionalDissipation (N : ℕ) (w : Lattice → ℝ) (U : Vec3 → ℝ → CVec3) (t : ℝ) :=
  ∑ k ∈ outputModes N,w k*massSq (embedMode k)*realHermitian (U (embedMode k) t) (U (embedMode k) t)

def fractionalTransfer (N : ℕ) (w : Lattice → ℝ) (U : Vec3 → ℝ → CVec3) (t : ℝ) :=
  2*∑ k ∈ outputModes N,w k*realHermitian (galerkinForce N U (embedMode k) t) (U (embedMode k) t)

def quarterWeight (k : Lattice) : ℝ := Real.sqrt (Real.sqrt (massSq (embedMode k)))

private theorem weighted_derivSum {J : Type*} (S : Finset J) (f : J → ℝ → ℝ)
    (d : J → ℝ) (t : ℝ)
    (h : ∀ j∈S,HasDerivAt (f j) (d j) t) :
    HasDerivAt (fun s=>∑ j ∈ S,f j s) (∑ j ∈ S,d j) t := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (hasDerivAt_const t (0:ℝ))
  | @insert j S hj ih =>
    simpa only [Finset.sum_insert hj] using
      (h j (Finset.mem_insert_self _ _)).add
        (ih fun k hk=>h k (Finset.mem_insert_of_mem hk))

theorem fractional_energy_derivative (N : ℕ) (ν : ℝ) (w : Lattice → ℝ)
    (U : Vec3 → ℝ → CVec3) (t : ℝ)
    (hODE : ∀ k i,HasDerivAt (fun s=>U k s i)
      (-((ν*massSq k:ℝ):ℂ)*U k t i+galerkinForce N U k t i) t) :
    HasDerivAt (fractionalEnergy N w U)
      (fractionalTransfer N w U t-2*ν*fractionalDissipation N w U t) t := by
  have hd := weighted_derivSum (outputModes N)
    (fun k s=>w k*realHermitian (U (embedMode k) s) (U (embedMode k) s))
    (fun k=>w k*(2*realHermitian
      (fun i=> -((ν*massSq (embedMode k):ℝ):ℂ)*U (embedMode k) t i+
        galerkinForce N U (embedMode k) t i) (U (embedMode k) t))) t
    (fun k _=>(modal_energy_derivative _ _ t (hODE (embedMode k))).const_mul (w k))
  convert hd using 1
  unfold fractionalTransfer fractionalDissipation
  simp_rw [modal_rhs_pair,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Native real FTC with the literal weighted transfer, on the same
physical trajectory. This is the missing hFTC input of N2e, not
its still-open signedUpper input. -/
theorem fractional_energy_square_FTC (N : ℕ) (ν T : ℝ) (w : Lattice → ℝ)
    (U : Vec3 → ℝ → CVec3)
    (hODE : ∀ t∈uIcc 0 T,∀ k i,HasDerivAt (fun s=>U k s i)
      (-((ν*massSq k:ℝ):ℂ)*U k t i+galerkinForce N U k t i) t)
    (hcT : ContinuousOn (fractionalTransfer N w U) (uIcc 0 T))
    (hcD : ContinuousOn (fractionalDissipation N w U) (uIcc 0 T)) :
    fractionalEnergy N w U T^2-fractionalEnergy N w U 0^2 =
      2*(∫ t in 0..T,fractionalEnergy N w U t*fractionalTransfer N w U t)-
      4*ν*(∫ t in 0..T,fractionalEnergy N w U t*fractionalDissipation N w U t) := by
  let E := fractionalEnergy N w U
  let D := fractionalDissipation N w U
  let P := fractionalTransfer N w U
  have hd (t : ℝ) (ht : t∈uIcc 0 T) : HasDerivAt E (P t-2*ν*D t) t :=
    fractional_energy_derivative N ν w U t (hODE t ht)
  have hcE : ContinuousOn E (uIcc 0 T) := fun t ht=>(hd t ht).continuousAt.continuousWithinAt
  have hsq (t : ℝ) (ht : t∈uIcc 0 T) :
      HasDerivAt (fun s=>E s^2) (2*(E t*P t)-4*ν*(E t*D t)) t := by
    have h := (hd t ht).pow 2
    convert h using 1 <;> ring
  have hc1 := (hcE.mul hcT).const_mul 2
  have hc2 := (hcE.mul hcD).const_mul (4*ν)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hsq
    (hc1.sub hc2).intervalIntegrable
  rw [intervalIntegral.integral_sub hc1.intervalIntegrable hc2.intervalIntegrable,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at h
  exact h.symm

/-- The original quarter-derivative energy is uniformly integrable to
the fourth power by the two successive physical Fourier Cauchy bounds.
This scalar interpolation is subcritical in time and cannot replace
the signed nonlinear transfer ceiling. -/
theorem quarter_energy_fourth_le (N : ℕ) (U : Vec3 → ℝ → CVec3) (t : ℝ) :
    fractionalEnergy N quarterWeight U t^4≤
      periodicEnergy N U t^3*periodicDissipation N U t := by
  let S := outputModes N
  let m := fun k=>realHermitian (U (embedMode k) t) (U (embedMode k) t)
  let r := fun k=>Real.sqrt (massSq (embedMode k))
  let A := ∑ k ∈ S,m k
  let C := ∑ k ∈ S,r k*m k
  let D := ∑ k ∈ S,massSq (embedMode k)*m k
  let Q := ∑ k ∈ S,Real.sqrt (r k)*m k
  have hm (k : Lattice) : 0≤m k := modeEnergy_nonnegative _
  have hr (k : Lattice) : 0≤r k := Real.sqrt_nonneg _
  have hA : 0≤A := Finset.sum_nonneg fun k _=>hm k
  have hC : 0≤C := Finset.sum_nonneg fun k _=>mul_nonneg (hr k) (hm k)
  have hD : 0≤D := Finset.sum_nonneg fun k _=>mul_nonneg (massSq_nonnegative _) (hm k)
  have hQ : 0≤Q := Finset.sum_nonneg fun k _=>mul_nonneg (Real.sqrt_nonneg _) (hm k)
  have h1 := Real.sum_sqrt_mul_sqrt_le S hm (g:=fun k=>r k*m k)
    (fun k=>mul_nonneg (hr k) (hm k))
  have h2 := Real.sum_sqrt_mul_sqrt_le S hm (g:=fun k=>massSq (embedMode k)*m k)
    (fun k=>mul_nonneg (massSq_nonnegative _) (hm k))
  have h1' : Q≤Real.sqrt A*Real.sqrt C := by
    change _≤Real.sqrt A*Real.sqrt C at h1
    convert h1 using 1
    apply Finset.sum_congr rfl
    intro k _
    rw [Real.sqrt_mul (hr k)]
    have h := Real.sq_sqrt (hm k)
    nlinarith
  have h2' : C≤Real.sqrt A*Real.sqrt D := by
    change _≤Real.sqrt A*Real.sqrt D at h2
    convert h2 using 1
    apply Finset.sum_congr rfl
    intro k _
    rw [Real.sqrt_mul (massSq_nonnegative _)]
    have h := Real.sq_sqrt (hm k)
    dsimp [r]
    nlinarith
  have hq2 := pow_le_pow_left₀ hQ h1' 2
  rw [mul_pow,Real.sq_sqrt hA,Real.sq_sqrt hC] at hq2
  have hc2 := pow_le_pow_left₀ hC h2' 2
  rw [mul_pow,Real.sq_sqrt hA,Real.sq_sqrt hD] at hc2
  have hq4 := pow_le_pow_left₀ (sq_nonneg Q) hq2 2
  have hAC := mul_le_mul_of_nonneg_left hc2 (sq_nonneg A)
  change Q^4≤A^3*D
  calc
    _ = (Q^2)^2 := by ring
    _ ≤ (A*C)^2 := hq4
    _ = A^2*C^2 := by ring
    _ ≤ A^2*(A*D) := hAC
    _ = _ := by ring

/-- The previous FTC has no additional continuity premise on the
actual finite flow: all source polynomials are continuous on its
physical interval. Attach the quarter-weight, not a free scalar T. -/
theorem actual_quarter_signed_FTC (N : ℕ) (ν T a : ℝ) (hT : 0≤T) (ha : a<0)
    (x : ℝ → FiniteState N)
    (hd : DASHI.NavierStokes.RealContinuation.SolvesOn (finiteForce N ν) x (Ioi a)) :
    let U := fun k t=>zeroExtend (x t) k
    fractionalEnergy N quarterWeight U T^2-fractionalEnergy N quarterWeight U 0^2 =
      2*(∫ t in 0..T,fractionalEnergy N quarterWeight U t*fractionalTransfer N quarterWeight U t)-
      4*ν*(∫ t in 0..T,fractionalEnergy N quarterWeight U t*fractionalDissipation N quarterWeight U t) := by
  let U := fun k t=>zeroExtend (x t) k
  have ho (t : ℝ) (ht : t∈uIcc 0 T) (k : Vec3) (i : Fin 3) :
      HasDerivAt (fun s=>U k s i)
        (-((ν*massSq k:ℝ):ℂ)*U k t i+galerkinForce N U k t i) t := by
    have h0 : 0≤t := by rw [uIcc_of_le hT] at ht; exact ht.1
    exact zeroExtend_ODE_of_derivative N ν x t (hd t (ha.trans_le h0)) k i
  have hc (k : Vec3) (i : Fin 3) : ContinuousOn (fun t=>U k t i) (uIcc 0 T) :=
    fun t ht=>(ho t ht k i).continuousAt.continuousWithinAt
  apply fractional_energy_square_FTC N ν T quarterWeight U ho
  · unfold fractionalTransfer
    apply ContinuousOn.const_mul
    apply continuousOn_finset_sum
    intro k hk
    apply ContinuousOn.const_mul
    unfold realHermitian
    have hF (i : Fin 3) : ContinuousOn (fun t=>galerkinForce N U (embedMode k) t i) (uIcc 0 T) := by
      rw [show (fun t=>galerkinForce N U (embedMode k) t i)=
        (fun t=>∑ p ∈ orderedFibre N k,
          orderedRHS (embedMode k) (embedMode p.2) (U (embedMode p.1) t) (U (embedMode p.2) t) i) by
          funext t; exact galerkinForce_eq_orderedFibre N U k hk t i]
      apply continuousOn_finset_sum
      intro p _
      unfold orderedRHS lerayVector outputDot
      simp only [Fin.sum_univ_three]
      fun_prop
    simp only [Fin.sum_univ_three]
    fun_prop
  · unfold fractionalDissipation
    apply continuousOn_finset_sum
    intro k _
    apply ContinuousOn.const_mul
    unfold realHermitian
    simp only [Fin.sum_univ_three]
    fun_prop

end
end DASHI.NavierStokes.PhysicalMixed

import Synthesis.NavierStokesLiteralHelicalRealTraceExact

/-!
Literal ordered Fourier cutoff: all input pairs, including zero addresses,
with p+q=k. The mean-zero restriction is a property of the velocity,
not a change in the incidence enumeration. R30/R408 original sign is -i.
Construct forcing, trace integrability and global finite output FTC
on one fixed Galerkin solution, without a separately chosen forcing.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open DASHI.NavierStokes.RealCauchyTrace
open MeasureTheory
open scoped BigOperators
noncomputable section

abbrev Lattice := Fin 3 → ℤ

def embedMode (k : Lattice) : Vec3 := fun i => (k i : ℝ)

def cutoffModes (N : ℕ) : Finset Lattice :=
  Finset.univ.image (fun k : Fin 3 → Fin (2*N+1) =>
    fun i => (k i : ℤ)-(N : ℤ))

def outputModes (N : ℕ) : Finset Lattice := (cutoffModes N).erase 0

def orderedFibre (N : ℕ) (k : Lattice) : Finset (Lattice × Lattice) :=
  ((cutoffModes N).product (cutoffModes N)).filter (fun a => a.1+a.2=k)

theorem mem_orderedFibre (N : ℕ) (k : Lattice) (a : Lattice × Lattice) :
    a ∈ orderedFibre N k ↔
    a.1 ∈ cutoffModes N ∧ a.2 ∈ cutoffModes N ∧ a.1+a.2=k := by
  simp [orderedFibre,and_assoc]

abbrev Incidence (N : ℕ) (k : Lattice) := {a // a ∈ orderedFibre N k}

def inputP {N k} (a : Incidence N k) : Vec3 := embedMode a.1.1
def inputQ {N k} (a : Incidence N k) : Vec3 := embedMode a.1.2

theorem incidence_resonance {N k} (a : Incidence N k) :
    inputP a+inputQ a=embedMode k := by
  have h := (mem_orderedFibre N k a.1).mp a.2
  funext i
  have hi := congrFun h.2.2 i
  change (a.1.1 i+a.1.2 i : ℤ)=k i at hi
  change (a.1.1 i : ℝ)+(a.1.2 i : ℝ)=(k i : ℝ)
  exact_mod_cast hi

theorem incidence_rate_pos (ν : ℝ) (hν : 0<ν) {N k}
    (hk : k≠0) (a : Incidence N k) :
    0 < mixedRates ν (inputP (N:=N) (k:=k)) inputQ a := by
  have hp := massSq_nonnegative (inputP a)
  have hq := massSq_nonnegative (inputQ a)
  by_contra! h
  have hsum : massSq (inputP a)+massSq (inputQ a)≤0 := by
    apply nonpos_of_mul_nonpos_left ?_ hν
    simpa [mixedRates,mul_add] using h
  have hz (i : Fin 3) : inputP a i=0 ∧ inputQ a i=0 := by
    have hp0 : (inputP a i)^2 ≤ massSq (inputP a) :=
      Finset.single_le_sum (fun j _ => sq_nonneg (inputP a j)) (Finset.mem_univ i)
    have hq0 : (inputQ a i)^2 ≤ massSq (inputQ a) :=
      Finset.single_le_sum (fun j _ => sq_nonneg (inputQ a j)) (Finset.mem_univ i)
    constructor <;> nlinarith [sq_nonneg (inputP a i),sq_nonneg (inputQ a i)]
  apply hk
  funext i
  have hi := congrFun (incidence_resonance a) i
  change inputP a i+inputQ a i=(k i : ℝ) at hi
  rw [(hz i).1,(hz i).2,zero_add] at hi
  exact_mod_cast hi.symm

/-- Exact R30 ordered term, no second multiplicity or sign change. -/
def orderedRHS (k q : Vec3) (u v : CVec3) : CVec3 :=
  fun i => -Complex.I * lerayVector k (fun j => outputDot q u*v j) i

theorem orderedRHS_divergence (k p q : Vec3) (u v : CVec3)
    (hk : p+q=k) (hu : outputDot p u=0) (i : Fin 3) :
    orderedRHS k q u v i = -projectedConvection k u v i := by
  have he : outputDot k u=outputDot q u := by
    rw [← hk]
    have h : outputDot (p+q) u=outputDot p u+outputDot q u := by
      simp [outputDot,Fin.sum_univ_three] <;> ring
    rw [h,hu,zero_add]
  rw [projectedConvection_eq_lerayVector]
  unfold orderedRHS lerayVector rawConvection
  rw [he]
  simp [outputDot,Fin.sum_univ_three] <;> ring

def galerkinForce (N : ℕ) (U : Vec3 → ℝ → CVec3)
    (k : Vec3) (t : ℝ) : CVec3 :=
  fun i => if k ∈ (outputModes N).image embedMode then
    ∑ a ∈ (cutoffModes N).product (cutoffModes N),
    if embedMode a.1+embedMode a.2=k then
      orderedRHS k (embedMode a.2) (U (embedMode a.1) t) (U (embedMode a.2) t) i
    else 0
  else 0

/-- Continuity follows from the actual finite ordered source. No assumed
F/H interval-integrability fields are needed for a continuous modal curve. -/
theorem galerkinForce_continuous (N : ℕ) (U : Vec3 → ℝ → CVec3)
    (hU : ∀ k i,Continuous (fun t => U k t i)) (k : Vec3) (i : Fin 3) :
    Continuous (fun t => galerkinForce N U k t i) := by
  unfold galerkinForce
  by_cases hk : k ∈ (outputModes N).image embedMode
  · simp only [if_pos hk]
    apply continuous_finset_sum
    intro a ha
    by_cases h : embedMode a.1+embedMode a.2=k
    · simp only [if_pos h]
      unfold orderedRHS lerayVector outputDot
      simp only [Fin.sum_univ_three]
      fun_prop
    · simp only [if_neg h]
      exact continuous_const
  · simp only [if_neg hk]
    exact continuous_const

theorem mixedCells_continuous {I : Type*} [Fintype I] (p q : I → Vec3)
    (U : Vec3 → ℝ → CVec3) (hU : ∀ k i,Continuous (fun t => U k t i))
    (a : I) (c : Coord) : Continuous (mixedCells p q U a c) := by
  fin_cases c <;>
    simp [mixedCells,phaseVector,doubleMixed,mixed,helical,lerayVector,
      curl3,cross3,outputDot,Fin.sum_univ_three] <;> fun_prop

theorem mixedForces_continuous {I : Type*} [Fintype I] (p q : I → Vec3)
    (U V : Vec3 → ℝ → CVec3)
    (hU : ∀ k i,Continuous (fun t => U k t i))
    (hV : ∀ k i,Continuous (fun t => V k t i)) (a : I) (c : Coord) :
    Continuous (mixedForces p q U V a c) := by
  fin_cases c <;>
    simp [mixedForces,phaseVector,doubleForcing,doubleMixed,mixed,helical,
      lerayVector,curl3,cross3,outputDot,Fin.sum_univ_three] <;> fun_prop

def fibreQ (N : ℕ) (ν : ℝ) (U : Vec3 → ℝ → CVec3) (k : Lattice) :=
  Q (mixedRates ν (inputP (N:=N) (k:=k)) inputQ) (mixedCells inputP inputQ U)

def fibreH (N : ℕ) (U : Vec3 → ℝ → CVec3) (k : Lattice) :=
  H (mixedCells (inputP (N:=N) (k:=k)) inputQ U)

def fibreF (N : ℕ) (ν : ℝ) (U : Vec3 → ℝ → CVec3) (k : Lattice) :=
  F (mixedRates ν (inputP (N:=N) (k:=k)) inputQ)
    (mixedCells inputP inputQ U) (mixedForces inputP inputQ U (galerkinForce N U))

theorem fibreH_continuous (N : ℕ) (U : Vec3 → ℝ → CVec3)
    (hU : ∀ k i,Continuous (fun t => U k t i)) (k : Lattice) :
    Continuous (fibreH N U k) := by
  unfold fibreH H cellProduct
  apply continuous_finset_sum
  intro p _
  exact (mixedCells_continuous _ _ U hU _ _).mul
    (mixedCells_continuous _ _ U hU _ _)

theorem fibreF_continuous (N : ℕ) (ν : ℝ) (U : Vec3 → ℝ → CVec3)
    (hU : ∀ k i,Continuous (fun t => U k t i)) (k : Lattice) :
    Continuous (fibreF N ν U k) := by
  unfold fibreF F
  apply Continuous.div_const
  apply continuous_finset_sum
  intro p _
  unfold nonlinearPair
  apply Continuous.div_const
  apply Continuous.const_mul
  exact ((mixedForces_continuous _ _ U _ hU
    (galerkinForce_continuous N U hU) _ _).mul
      (mixedCells_continuous _ _ U hU _ _)).add
    ((mixedCells_continuous _ _ U hU _ _).mul
      (mixedForces_continuous _ _ U _ hU (galerkinForce_continuous N U hU) _ _))

/-- Fixed-output FTC with the actual nonlinear sum and no free forcing. -/
theorem fibre_FTC (N : ℕ) (ν : ℝ) (hν : 0<ν)
    (U : Vec3 → ℝ → CVec3) (k : Lattice) (hk : k≠0) (T : ℝ)
    (hc : ∀ k i,Continuous (fun t => U k t i))
    (hODE : ∀ t ∈ Set.uIcc 0 T,∀ k i,
      HasDerivAt (fun x : ℝ => U k x i)
        (-((ν*massSq k : ℝ):ℂ)*U k t i+galerkinForce N U k t i) t) :
    4*(∫ t in 0..T,fibreF N ν U k t)=
      fibreQ N ν U k T-fibreQ N ν U k 0+2*(∫ t in 0..T,fibreH N U k t) :=
  literal_mixed_FTC ν inputP inputQ U (galerkinForce N U) T
    (incidence_rate_pos ν hν hk) hODE
    ((fibreF_continuous N ν U hc k).intervalIntegrable _ _)
    ((fibreH_continuous N U hc k).intervalIntegrable _ _)

/-- All original nonzero outputs, one fixed cutoff and one trajectory.
Retain arbitrary fixed output weights, including N2e fractional weights. -/
theorem weighted_output_FTC (N : ℕ) (ν : ℝ) (hν : 0<ν)
    (U : Vec3 → ℝ → CVec3) (w : Lattice → ℝ) (T : ℝ)
    (hc : ∀ k i,Continuous (fun t => U k t i))
    (hODE : ∀ t ∈ Set.uIcc 0 T,∀ k i,
      HasDerivAt (fun x : ℝ => U k x i)
        (-((ν*massSq k : ℝ):ℂ)*U k t i+galerkinForce N U k t i) t) :
    4*(∫ t in 0..T,∑ k ∈ outputModes N,w k*fibreF N ν U k t)=
    (∑ k ∈ outputModes N,w k*fibreQ N ν U k T)-
    (∑ k ∈ outputModes N,w k*fibreQ N ν U k 0)+
      2*(∫ t in 0..T,∑ k ∈ outputModes N,w k*fibreH N U k t) := by
  rw [intervalIntegral.integral_finset_sum (fun k _ =>
    ((fibreF_continuous N ν U hc k).const_mul (w k)).intervalIntegrable _ _),
    intervalIntegral.integral_finset_sum (fun k _ =>
    ((fibreH_continuous N U hc k).const_mul (w k)).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have he := fibre_FTC N ν hν U k (Finset.mem_erase.mp hk).1 T hc hODE
  linear_combination w k*he

end
end DASHI.NavierStokes.PhysicalMixed

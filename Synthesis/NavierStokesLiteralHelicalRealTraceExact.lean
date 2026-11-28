import Synthesis.NavierStokesRealCauchyLaplaceCoherentExact
import Synthesis.NavierStokesEuclideanSignedProductMajorantExact

/-!
Real-time realization of the original R224/R225/R387/R388/R560
double-mixed cross cell. This is NOT the divergence-form projected
convection Gram from the Euclidean spatial companion. R406's actual
nonlinear tangent has degree five in its Gram work; the quartic cell
Gram cannot be substituted for it. Rates and helical matrices are fixed
by the actual mode, not varied with time.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open DASHI.NavierStokes.RealCauchyTrace
open MeasureTheory
open scoped BigOperators
noncomputable section

def cross3 (u v : CVec3) : CVec3 :=
  ![u 1*v 2-u 2*v 1,u 2*v 0-u 0*v 2,u 0*v 1-u 1*v 0]

def curl3 (k : Vec3) (u : CVec3) : CVec3 :=
  fun i => Complex.I * cross3 (fun j => (k j : ℂ)) u i

/-- Actual +/- curl projection, with real mode norm and fixed half.
Zero mode is totalized here; original R406 enumerates nonzero outputs. -/
def helical (sign : ℝ) (k : Vec3) (u : CVec3) : CVec3 :=
  fun i => (1/2 : ℂ) *
    (lerayVector k u i + ((sign/Real.sqrt (massSq k) : ℝ) : ℂ)*curl3 k u i)

theorem cross3_swap (u v : CVec3) (i : Fin 3) :
    cross3 v u i = -cross3 u v i := by
  fin_cases i <;> simp [cross3] <;> ring

theorem helical_damped (s r : ℝ) (k : Vec3) (u f : CVec3) (i : Fin 3) :
    helical s k (fun j => -(r:ℂ)*u j+f j) i =
      -(r:ℂ)*helical s k u i+helical s k f i := by
  fin_cases i <;>
    simp [helical,lerayVector,outputDot,curl3,cross3,Fin.sum_univ_three] <;> ring

/-- The literal two complex linear helical projections are
differentiated in real time. -/
theorem helical_hasDeriv (s : ℝ) (k : Vec3) (u : ℝ → CVec3)
    (d : CVec3) (t : ℝ)
    (hu : ∀ i, HasDerivAt (fun x : ℝ => u x i) (d i) t)
    (i : Fin 3) :
    HasDerivAt (fun x : ℝ => helical s k (u x) i) (helical s k d i) t := by
  have hdot : HasDerivAt (fun x : ℝ => outputDot k (u x)) (outputDot k d) t := by
    simp only [outputDot,Fin.sum_univ_three]
    exact (((hu 0).const_mul (k 0 : ℂ)).add
      ((hu 1).const_mul (k 1 : ℂ))).add ((hu 2).const_mul (k 2 : ℂ))
  have hL : HasDerivAt (fun x : ℝ => lerayVector k (u x) i)
      (lerayVector k d i) t := by
    exact (hu i).sub (hdot.const_mul (k i/massSq k : ℝ))
  have hC : HasDerivAt (fun x : ℝ => curl3 k (u x) i) (curl3 k d i) t := by
    fin_cases i
    · exact (((hu 2).const_mul (k 1 : ℂ)).sub
        ((hu 1).const_mul (k 2 : ℂ))).const_mul Complex.I
    · exact (((hu 0).const_mul (k 2 : ℂ)).sub
        ((hu 2).const_mul (k 0 : ℂ))).const_mul Complex.I
    · exact (((hu 1).const_mul (k 0 : ℂ)).sub
        ((hu 0).const_mul (k 1 : ℂ))).const_mul Complex.I
  exact (hL.add (hC.const_mul ((s/Real.sqrt (massSq k) : ℝ) : ℂ))).const_mul (1/2)

theorem cross3_hasDeriv (u v : ℝ → CVec3) (du dv : CVec3)
    (t : ℝ)
    (hu : ∀ i,HasDerivAt (fun x : ℝ => u x i) (du i) t)
    (hv : ∀ i,HasDerivAt (fun x : ℝ => v x i) (dv i) t)
    (i : Fin 3) :
    HasDerivAt (fun x : ℝ => cross3 (u x) (v x) i)
      (cross3 du (v t) i+cross3 (u t) dv i) t := by
  fin_cases i
  · convert ((hu 1).mul (hv 2)).sub ((hu 2).mul (hv 1)) using 1 <;>
      simp [cross3] <;> ring
  · convert ((hu 2).mul (hv 0)).sub ((hu 0).mul (hv 2)) using 1 <;>
      simp [cross3] <;> ring
  · convert ((hu 0).mul (hv 1)).sub ((hu 1).mul (hv 0)) using 1 <;>
      simp [cross3] <;> ring

def mixed (p q : Vec3) (u v : CVec3) : CVec3 :=
  cross3 (helical 1 p u) (helical (-1) q v)

def doubleMixed (p q : Vec3) (u v : CVec3) : CVec3 :=
  fun i => 2*(mixed p q u v i+mixed q p v u i)

/-- R225 = R387: minus-plus is the negative of the swapped plus-minus. -/
theorem doubleMixed_original_difference (p q : Vec3) (u v : CVec3) (i : Fin 3) :
    doubleMixed p q u v i =
      2*(mixed p q u v i-cross3 (helical (-1) p u) (helical 1 q v) i) := by
  unfold doubleMixed mixed
  rw [cross3_swap (helical (-1) p u) (helical 1 q v)]
  ring

def doubleForcing (p q : Vec3) (u v fu fv : CVec3) : CVec3 :=
  fun i => doubleMixed p q fu v i+doubleMixed p q u fv i

theorem mixed_hasDeriv (p q : Vec3) (u v : ℝ → CVec3) (du dv : CVec3)
    (t : ℝ) (hu : ∀ i,HasDerivAt (fun x : ℝ => u x i) (du i) t)
    (hv : ∀ i,HasDerivAt (fun x : ℝ => v x i) (dv i) t)
    (i : Fin 3) :
    HasDerivAt (fun x : ℝ => mixed p q (u x) (v x) i)
      (mixed p q du (v t) i+mixed p q (u t) dv i) t :=
  cross3_hasDeriv _ _ _ _ t
    (helical_hasDeriv 1 p u du t hu) (helical_hasDeriv (-1) q v dv t hv) i

theorem doubleMixed_hasDeriv (p q : Vec3) (u v : ℝ → CVec3) (du dv : CVec3)
    (t : ℝ) (hu : ∀ i,HasDerivAt (fun x : ℝ => u x i) (du i) t)
    (hv : ∀ i,HasDerivAt (fun x : ℝ => v x i) (dv i) t)
    (i : Fin 3) :
    HasDerivAt (fun x : ℝ => doubleMixed p q (u x) (v x) i)
      (doubleForcing p q (u t) (v t) du dv i) t := by
  have h := ((mixed_hasDeriv p q u v du dv t hu hv i).add
    (mixed_hasDeriv q p v u dv du t hv hu i)).const_mul 2
  convert h using 1 <;> unfold doubleForcing doubleMixed <;> ring

theorem mixed_damped_left (p q : Vec3) (u v f : CVec3) (r : ℝ) (i : Fin 3) :
    mixed p q (fun j => -(r:ℂ)*u j+f j) v i =
      -(r:ℂ)*mixed p q u v i+mixed p q f v i := by
  unfold mixed
  fin_cases i <;> simp [cross3,helical_damped] <;> ring

theorem mixed_damped_right (p q : Vec3) (u v f : CVec3) (r : ℝ) (i : Fin 3) :
    mixed p q u (fun j => -(r:ℂ)*v j+f j) i =
      -(r:ℂ)*mixed p q u v i+mixed p q u f i := by
  unfold mixed
  fin_cases i <;> simp [cross3,helical_damped] <;> ring

/-- Actual R388 decay + force from literal modal ODE derivatives.
Both input rates are retained, and swapped cell has identical decay. -/
theorem doubleMixed_damped_derivative (p q : Vec3) (u v fu fv : ℝ → CVec3)
    (rp rq : ℝ) (t : ℝ)
    (hu : ∀ i,HasDerivAt (fun x : ℝ => u x i)
      (-(rp:ℂ)*u t i+fu t i) t)
    (hv : ∀ i,HasDerivAt (fun x : ℝ => v x i)
      (-(rq:ℂ)*v t i+fv t i) t) (i : Fin 3) :
    HasDerivAt (fun x : ℝ => doubleMixed p q (u x) (v x) i)
      (-((rp+rq : ℝ):ℂ)*doubleMixed p q (u t) (v t) i+
        doubleForcing p q (u t) (v t) (fu t) (fv t) i) t := by
  have h := doubleMixed_hasDeriv p q u v _ _ t hu hv i
  convert h using 1
  unfold doubleForcing doubleMixed
  rw [mixed_damped_left,mixed_damped_right,mixed_damped_right,mixed_damped_left]
  push_cast
  ring

/-- Real six-coordinate representation; signs and complex phases are
retained exactly, matching the R291 real Hermitian pairing. -/
def phaseVector (u : CVec3) : Coord → ℝ :=
  ![(u 0).re,(u 0).im,(u 1).re,(u 1).im,(u 2).re,(u 2).im]

theorem phaseVector_derivative (u : ℝ → CVec3) (d f : CVec3)
    (r t : ℝ)
    (hu : ∀ i,HasDerivAt (fun x : ℝ => u x i) (-(r:ℂ)*d i+f i) t)
    (c : Coord) :
    HasDerivAt (fun x : ℝ => phaseVector (u x) c)
      (-r*phaseVector d c+phaseVector f c) t := by
  fin_cases c
  · simpa [phaseVector,Function.comp_def,Complex.mul_re] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt (hu 0)
  · simpa [phaseVector,Function.comp_def,Complex.mul_im] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt (hu 0)
  · simpa [phaseVector,Function.comp_def,Complex.mul_re] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt (hu 1)
  · simpa [phaseVector,Function.comp_def,Complex.mul_im] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt (hu 1)
  · simpa [phaseVector,Function.comp_def,Complex.mul_re] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt (hu 2)
  · simpa [phaseVector,Function.comp_def,Complex.mul_im] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt (hu 2)

variable {I : Type*} [Fintype I]

/-- Same fixed-output incidence family, physical frequencies p and q;
one common Fourier curve U and one common modal forcing N. -/
def mixedCells (p q : I → Vec3) (U : Vec3 → ℝ → CVec3) :
    I → Coord → ℝ → ℝ :=
  fun a c t => phaseVector (doubleMixed (p a) (q a) (U (p a) t) (U (q a) t)) c

def mixedForces (p q : I → Vec3) (U N : Vec3 → ℝ → CVec3) :
    I → Coord → ℝ → ℝ :=
  fun a c t => phaseVector
    (doubleForcing (p a) (q a) (U (p a) t) (U (q a) t) (N (p a) t) (N (q a) t)) c

def mixedRates (ν : ℝ) (p q : I → Vec3) : I → ℝ :=
  fun a => ν*massSq (p a)+ν*massSq (q a)

theorem literal_mixed_cell_derivative (ν : ℝ) (p q : I → Vec3)
    (U N : Vec3 → ℝ → CVec3) (t : ℝ)
    (hU : ∀ k i,HasDerivAt (fun x : ℝ => U k x i)
      (-((ν*massSq k : ℝ):ℂ)*U k t i+N k t i) t)
    (a : I) (c : Coord) :
    HasDerivAt (mixedCells p q U a c)
      (-mixedRates ν p q a*mixedCells p q U a c t+mixedForces p q U N a c t) t := by
  exact phaseVector_derivative
    (fun x => doubleMixed (p a) (q a) (U (p a) x) (U (q a) x)) _ _
    (mixedRates ν p q a) t
    (doubleMixed_damped_derivative (p a) (q a) (U (p a)) (U (q a))
      (N (p a)) (N (q a)) _ _ t (hU _) (hU _)) c

/-- Real FTC on actual R225 helical cells, not on an unconstrained
cell curve. The modal ODE hypothesis still has to be attached to
the selected finite original projected nonlinear RHS. -/
theorem literal_mixed_FTC (ν : ℝ) (p q : I → Vec3)
    (U N : Vec3 → ℝ → CVec3) (T : ℝ)
    (hr : ∀ a,0 < mixedRates ν p q a)
    (hU : ∀ t ∈ Set.uIcc 0 T,∀ k i,
      HasDerivAt (fun x : ℝ => U k x i)
        (-((ν*massSq k : ℝ):ℂ)*U k t i+N k t i) t)
    (hF : IntervalIntegrable
      (F (mixedRates ν p q) (mixedCells p q U) (mixedForces p q U N)) volume 0 T)
    (hH : IntervalIntegrable (H (mixedCells p q U)) volume 0 T) :
    4*(∫ t in 0..T,F (mixedRates ν p q) (mixedCells p q U) (mixedForces p q U N) t) =
      Q (mixedRates ν p q) (mixedCells p q U) T-
      Q (mixedRates ν p q) (mixedCells p q U) 0+
      2*(∫ t in 0..T,H (mixedCells p q U) t) :=
  coherent_trace_FTC _ _ _ hr T
    (fun t ht => literal_mixed_cell_derivative ν p q U N t (hU t ht)) hF hH

end
end DASHI.NavierStokes.PhysicalMixed

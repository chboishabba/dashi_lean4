import Integration.Paper9HypergeometricQTransport
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! Source-written, uncompiled. Original cusp-order filtration and literal
factorial coefficient identities. No identification with a finite ternary
metric. The analytic solution and global disk estimates are separate. -/
namespace Integration.Paper9CuspOrderFactorial

open Complex Filter
open scoped Topology
open Integration.Paper9OriginalEisensteinDerivative
open Integration.Paper9BracketCuspClosure
open Integration.Paper9E2CorrectedClosure
open Integration.Paper9HypergeometricQTransport

noncomputable section

-- Branch selected by the actual x(0)=1, not an arbitrary square root.
def rootF (q : ℂ) : ℂ := Complex.exp (Complex.log (x q)/2)

theorem rootFZero : rootF 0 = 1 := by simp [rootF,xZero]

theorem rootFSquare (q : ℂ) (hx : x q ≠ 0) : rootF q^2 = x q := by
  unfold rootF
  rw [pow_two,← Complex.exp_add]
  rw [show Complex.log (x q)/2+Complex.log (x q)/2 =
    Complex.log (x q) by ring,Complex.exp_log hx]

theorem rootFDeriv (q : ℂ) (hq : ‖q‖ < 1)
    (hx : x q ∈ Complex.slitPlane) :
    HasDerivAt rootF (rootF q*(deriv x q/x q)/2) q := by
  have hd := ((xDifferentiable q hq).hasDerivAt.clog hx).div_const 2
  have h := (Complex.hasDerivAt_exp (Complex.log (x q)/2)).comp q hd
  simpa [rootF,mul_div_assoc,mul_comm] using h

theorem rootFirst (q : ℂ) (hq : ‖q‖ < 1) (hn : q ≠ 0)
    (hx : x q ∈ Complex.slitPlane) (hy : y q ≠ 0) :
    L rootF q = aCoord q*rootF q := by
  obtain ⟨_,h,_⟩ := ramanujanQ q hq hn
  unfold euler at h
  have hdx : deriv x q = (e2Q q*x q-y q)/(3*q) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hn)).2
    linear_combination h
  unfold L euler aCoord
  rw [(rootFDeriv q hq hx).deriv,hdx]
  field_simp [Complex.slitPlane_ne_zero hx,hy,hn] <;> ring

-- Actual U_L and z retain the normalized cusp values.
def transportUnit (q : ℂ) : ℂ := x q/y q

theorem transportUnitZero : transportUnit 0 = 1 := by
  simp [transportUnit,xZero,yZero]

theorem zZero : zCoord 0 = 0 := by simp [zCoord,xZero,yZero]

theorem transportUnitAnalytic : AnalyticAt ℂ transportUnit 0 := by
  exact xAnalyticZero.div yAnalyticZero (by simp [yZero])

theorem zAnalytic : AnalyticAt ℂ zCoord 0 := by
  unfold zCoord
  exact analyticAt_const.sub ((yAnalyticZero.pow 2).div (xAnalyticZero.pow 3)
    (by simp [xZero]))

def leadStep (n : ℕ) (g : ℂ → ℂ) (q : ℂ) : ℂ :=
  transportUnit q*((n : ℂ)*g q+q*deriv g q)

theorem leadStepZero (n : ℕ) (g : ℂ → ℂ) :
    leadStep n g 0 = (n : ℂ)*g 0 := by simp [leadStep,transportUnitZero]

theorem leadStepAnalytic (n : ℕ) (g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0) :
    AnalyticAt ℂ (leadStep n g) 0 := by
  unfold leadStep
  exact transportUnitAnalytic.mul ((analyticAt_const.mul hg).add
    (analyticAt_id.mul hg.deriv))

-- Actual operator's filtered edge, n>0. Neighborhood differentiability
-- is a named premise here; analytic germs supply it via openness.
theorem leadTransport (n : ℕ) (f g : ℂ → ℂ)
    (hd : ∀ᶠ q in 𝓝 (0 : ℂ), DifferentiableAt ℂ g q)
    (hf : f =ᶠ[𝓝 (0 : ℂ)] fun q => q^(n+1)*g q) :
    L f =ᶠ[𝓝 (0 : ℂ)] fun q => q^(n+1)*leadStep (n+1) g q := by
  filter_upwards [hf.deriv,hd] with q he hdq
  have hp := ((hasDerivAt_id q).pow (n+1)).mul hdq.hasDerivAt
  unfold L euler leadStep transportUnit
  rw [he,hp.deriv]
  simp only [Nat.add_sub_cancel,pow_succ,Nat.cast_add,Nat.cast_one]
  ring

-- If g0 is the retained first nonzero coefficient of a difference,
-- these are the actual 1st, 2nd and 3rd leading multipliers.
theorem leadThird (n : ℕ) (g : ℂ → ℂ) :
    leadStep n (leadStep n (leadStep n g)) 0 =
      (n : ℂ)^3*g 0 := by simp only [leadStepZero]; ring

def residualUnit (n : ℕ) (g : ℂ → ℂ) (q : ℂ) : ℂ :=
  let a := leadStep n g
  let b := leadStep n a
  let c := leadStep n b
  c q-zCoord q*(c q+3/2*b q+23/36*a q+5/72*g q)

theorem residualUnitZero (n : ℕ) (g : ℂ → ℂ) :
    residualUnit n g 0 = (n : ℂ)^3*g 0 := by
  simp [residualUnit,zZero,leadThird]

theorem residualUnitAnalytic (n : ℕ) (g : ℂ → ℂ)
    (hg : AnalyticAt ℂ g 0) : AnalyticAt ℂ (residualUnit n g) 0 := by
  have ha := leadStepAnalytic n g hg
  have hb := leadStepAnalytic n _ ha
  have hc := leadStepAnalytic n _ hb
  exact hc.sub (zAnalytic.mul (((hc.add (analyticAt_const.mul hb)).add
    (analyticAt_const.mul ha)).add (analyticAt_const.mul hg)))

-- Isolated-zero theorem rules out a nonzero leading residual, using
-- the original cusp rather than evaluation at finitely many samples.
theorem nonzeroLeadingObstruction (n : ℕ) (hn : n ≠ 0)
    (g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0) (hg0 : g 0 ≠ 0) :
    ¬ (∀ᶠ q in 𝓝 (0 : ℂ), q^n*residualUnit n g q = 0) := by
  let f : ℂ → ℂ := fun q => q^n*residualUnit n g q
  have hf : AnalyticAt ℂ f 0 :=
    (analyticAt_id.pow n).mul (residualUnitAnalytic n g hg)
  apply (hf.exists_eventuallyEq_pow_smul_nonzero_iff).mp
  refine ⟨n,residualUnit n g,residualUnitAnalytic n g hg,?_,?_⟩
  · rw [residualUnitZero]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hn)) hg0
  · filter_upwards with q
    simp [f,smul_eq_mul]

-- Factorial coefficients of the literal 3F2 (not a finite ratio test).
def coeff (n : ℕ) : ℚ :=
  ((6*n).factorial : ℚ) /
    ((3*n).factorial * (n.factorial : ℚ)^3 * 1728^n)

def ratio (n : ℕ) : ℚ :=
  ((n : ℚ)+1/6)*((n : ℚ)+1/2)*((n : ℚ)+5/6)/((n : ℚ)+1)^3

theorem factorial3 (n : ℕ) :
    ((3*(n+1)).factorial : ℚ) =
      ((3*n).factorial : ℚ)*(3*(n : ℚ)+1)*(3*(n : ℚ)+2)*(3*(n : ℚ)+3) := by
  rw [show 3*(n+1)=Nat.succ (Nat.succ (Nat.succ (3*n))) by omega]
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
  push_cast
  ring

theorem factorial6 (n : ℕ) :
    ((6*(n+1)).factorial : ℚ) =
      ((6*n).factorial : ℚ)*(6*(n : ℚ)+1)*(6*(n : ℚ)+2)*(6*(n : ℚ)+3)*
      (6*(n : ℚ)+4)*(6*(n : ℚ)+5)*(6*(n : ℚ)+6) := by
  rw [show 6*(n+1)=Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (6*n)))))) by omega]
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
  push_cast
  ring

theorem coeffZero : coeff 0 = 1 := by norm_num [coeff]

theorem coeffSucc (n : ℕ) : coeff (n+1) = ratio n*coeff n := by
  unfold coeff ratio
  rw [factorial6,factorial3,Nat.factorial_succ,pow_succ]
  push_cast
  have h3 : ((3*n).factorial : ℚ) ≠ 0 := by positivity
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  have h1 : (n : ℚ)+1 ≠ 0 := by positivity
  have h31 : 3*(n : ℚ)+1 ≠ 0 := by positivity
  have h32 : 3*(n : ℚ)+2 ≠ 0 := by positivity
  have h33 : 3*(n : ℚ)+3 ≠ 0 := by positivity
  field_simp [h3,hn,h1,h31,h32,h33] <;> ring

-- The literal signed Chudnovsky step p_(n+1)/q_(n+1).
def C : ℚ := 640320^3
def cmZ : ℚ := -1728/C
theorem cmRatio (n : ℕ) :
    cmZ*ratio n =
    -(24*(2*(n : ℚ)+1)*(6*(n : ℚ)+1)*(6*(n : ℚ)+5))/
      (C*((n : ℚ)+1)^3) := by
  unfold cmZ ratio C
  ring

theorem cmTermSucc (n : ℕ) :
    coeff (n+1)*cmZ^(n+1) =
    (-(24*(2*(n : ℚ)+1)*(6*(n : ℚ)+1)*(6*(n : ℚ)+5))/
      (C*((n : ℚ)+1)^3))*(coeff n*cmZ^n) := by
  rw [coeffSucc,pow_succ,← cmRatio]
  ring

end
end Integration.Paper9CuspOrderFactorial

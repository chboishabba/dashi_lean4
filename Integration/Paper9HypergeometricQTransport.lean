import Integration.Paper9E2CorrectedClosure

/-!
Source-written, uncompiled. Actual cusp-coordinate Ramanujan system
and a small differential closure for the hypergeometric operator.
No inverse j or inverse z. The binomial square-root branch and
convergent-series coefficient interpretation remain separate.
-/
namespace Integration.Paper9HypergeometricQTransport

open Complex Function Filter
open scoped Topology Real
open Integration.Paper9OriginalEisensteinDerivative
open Integration.Paper9BracketCuspClosure
open Integration.Paper9EulerMobiusTransport
open Integration.Paper9E2CorrectedClosure

noncomputable section

-- Recover the actual q coordinates via the original inverse qParam
-- chart; this is NOT an inverse of j or of the hypergeometric coordinate.
theorem ramanujanQ (q : ℂ) (hq : ‖q‖ < 1) (hn : q ≠ 0) :
    12 * euler e2Q q = (e2Q q)^2-x q ∧
    3 * euler x q = e2Q q*x q-y q ∧
    2 * euler y q = e2Q q*y q-(x q)^2 := by
  let τ : UpperHalfPlane := ⟨Periodic.invQParam 1 q,
    Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq hn⟩
  have hr : qExt τ = q := Periodic.qParam_right_inv one_ne_zero hn
  have h := originalRamanujanSystem τ
  rw [← e2QAt τ,← xAtQ τ,← yAtQ τ] at h
  change 12*euler e2Q (qExt τ) = e2Q (qExt τ)^2-x (qExt τ) ∧
    3*euler x (qExt τ) = e2Q (qExt τ)*x (qExt τ)-y (qExt τ) ∧
    2*euler y (qExt τ) = e2Q (qExt τ)*y (qExt τ)-x (qExt τ)^2 at h
  rwa [hr] at h

def L (f : ℂ → ℂ) (q : ℂ) : ℂ := (x q/y q)*euler f q

def aCoord (q : ℂ) : ℂ := (e2Q q*x q/y q-1)/6
def hCoord (q : ℂ) : ℂ := x q^3/y q^2-1
def zCoord (q : ℂ) : ℂ := 1-y q^2/x q^3

def aFlow (a h : ℂ) : ℂ := -a^2/2+h*(a/2+5/72)
def hFlow (h : ℂ) : ℂ := h*(h+1)
def bCoord (a h : ℂ) : ℂ := a^2/2+h*(a/2+5/72)

-- Algebra on the original vector field, denominator apartness explicit.
theorem aVectorField (e X Y : ℂ) (hy : Y ≠ 0) :
    (X/Y) * ((((e^2-X)/12*X+e*((e*X-Y)/3))*Y
      - e*X*((e*Y-X^2)/2))/Y^2) / 6 =
    aFlow ((e*X/Y-1)/6) (X^3/Y^2-1) := by
  unfold aFlow
  field_simp [hy] <;> ring

theorem hVectorField (e X Y : ℂ) (hy : Y ≠ 0) :
    (X/Y) * ((3*X^2*((e*X-Y)/3)*Y^2
      - X^3*(2*Y*((e*Y-X^2)/2)))/(Y^2)^2) =
    hFlow (X^3/Y^2-1) := by
  unfold hFlow
  field_simp [hy] <;> ring

theorem zVectorField (e X Y : ℂ) (hx : X ≠ 0) (hy : Y ≠ 0) :
    -(X/Y)*((2*Y*((e*Y-X^2)/2)*X^3
      - Y^2*(3*X^2*((e*X-Y)/3)))/(X^3)^2) =
    1-Y^2/X^3 := by
  field_simp [hx,hy] <;> ring

theorem coordBridge (X Y : ℂ) (hx : X ≠ 0) (hy : Y ≠ 0) :
    (1-(1-Y^2/X^3))*(X^3/Y^2-1) = 1-Y^2/X^3 ∧
    1-(1-Y^2/X^3) ≠ 0 := by
  constructor
  · field_simp [hx,hy] <;> ring
  · ring_nf
    exact div_ne_zero (pow_ne_zero _ hy) (pow_ne_zero _ hx)

-- The actual q derivatives, using the pinned analytic cusp functions
-- and the original Ramanujan theorem, not a replacement vector field.
theorem aTransport (q : ℂ) (hq : ‖q‖ < 1) (hn : q ≠ 0) (hy : y q ≠ 0) :
    L aCoord q = aFlow (aCoord q) (hCoord q) := by
  obtain ⟨he,hx,hyD⟩ := ramanujanQ q hq hn
  have he' : deriv e2Q q = ((e2Q q)^2-x q)/(12*q) := by
    unfold euler at he
    apply (eq_div_iff (mul_ne_zero (by norm_num) hn)).2
    linear_combination he
  have hx' : deriv x q = (e2Q q*x q-y q)/(3*q) := by
    unfold euler at hx
    apply (eq_div_iff (mul_ne_zero (by norm_num) hn)).2
    linear_combination hx
  have hy' : deriv y q = (e2Q q*y q-x q^2)/(2*q) := by
    unfold euler at hyD
    apply (eq_div_iff (mul_ne_zero (by norm_num) hn)).2
    linear_combination hyD
  have h := (((((e2QAnalytic q hq).differentiableAt.hasDerivAt.mul
    (xDifferentiable q hq).hasDerivAt).div
      (yDifferentiable q hq).hasDerivAt hy).sub_const 1).div_const 6)
  unfold L euler aCoord hCoord
  rw [h.deriv,he',hx',hy']
  calc
    _ = (x q/y q)*((((e2Q q^2-x q)/12*x q+
      e2Q q*((e2Q q*x q-y q)/3))*y q-
      e2Q q*x q*((e2Q q*y q-x q^2)/2))/y q^2)/6 := by
      field_simp [hn,hy] <;> ring
    _ = _ := aVectorField (e2Q q) (x q) (y q) hy

theorem hTransport (q : ℂ) (hq : ‖q‖ < 1) (hn : q ≠ 0) (hy : y q ≠ 0) :
    L hCoord q = hFlow (hCoord q) := by
  obtain ⟨_,hx,hyD⟩ := ramanujanQ q hq hn
  have hx' : deriv x q = (e2Q q*x q-y q)/(3*q) := by
    unfold euler at hx
    apply (eq_div_iff (mul_ne_zero (by norm_num) hn)).2
    linear_combination hx
  have hy' : deriv y q = (e2Q q*y q-x q^2)/(2*q) := by
    unfold euler at hyD
    apply (eq_div_iff (mul_ne_zero (by norm_num) hn)).2
    linear_combination hyD
  have h := ((((xDifferentiable q hq).hasDerivAt.pow 3).div
    ((yDifferentiable q hq).hasDerivAt.pow 2) (pow_ne_zero _ hy)).sub_const 1)
  unfold L euler hCoord
  rw [h.deriv,hx',hy']
  calc
    _ = (x q/y q)*((3*x q^2*((e2Q q*x q-y q)/3)*y q^2
      - x q^3*(2*y q*((e2Q q*y q-x q^2)/2)))/(y q^2)^2) := by
      field_simp [hn,hy] <;> ring
    _ = _ := hVectorField (e2Q q) (x q) (y q) hy

theorem zTransport (q : ℂ) (hq : ‖q‖ < 1) (hn : q ≠ 0)
    (hx0 : x q ≠ 0) (hy0 : y q ≠ 0) : L zCoord q = zCoord q := by
  obtain ⟨_,hx,hyD⟩ := ramanujanQ q hq hn
  have hx' : deriv x q = (e2Q q*x q-y q)/(3*q) := by
    unfold euler at hx
    apply (eq_div_iff (mul_ne_zero (by norm_num) hn)).2
    linear_combination hx
  have hy' : deriv y q = (e2Q q*y q-x q^2)/(2*q) := by
    unfold euler at hyD
    apply (eq_div_iff (mul_ne_zero (by norm_num) hn)).2
    linear_combination hyD
  have h := (hasDerivAt_const q (1 : ℂ)).sub
    (((yDifferentiable q hq).hasDerivAt.pow 2).div
      ((xDifferentiable q hq).hasDerivAt.pow 3) (pow_ne_zero _ hx0))
  unfold L euler zCoord
  rw [h.deriv,hx',hy']
  calc
    _ = -(x q/y q)*((2*y q*((e2Q q*y q-x q^2)/2)*x q^3
      - y q^2*(3*x q^2*((e2Q q*x q-y q)/3)))/(x q^3)^2) := by
      field_simp [hn,hx0,hy0] <;> ring
    _ = _ := zVectorField (e2Q q) (x q) (y q) hx0 hy0

-- Once LF=aF has been bound to the original binomial sqrt E4,
-- these polynomial identities give the next two derivatives.
-- No division by F in this closure.
theorem secondMultiplier (a h : ℂ) :
    aFlow a h+a^2 = bCoord a h := by
  unfold aFlow bCoord
  ring

theorem thirdMultiplier (a h : ℂ) :
    (a+h/2)*aFlow a h+(a/2+5/72)*hFlow h+a*bCoord a h =
      h*(3/2*bCoord a h+23/36*a+5/72) := by
  unfold aFlow hFlow bCoord
  ring

-- Denominator-cleared ODE consumer. The three inputs below must
-- still be proved for the actual analytic branch, not assumed from
-- finite coefficient samples.
theorem odeFromMultiplier (F F1 F2 F3 a h z : ℂ)
    (h1 : F1=a*F) (h2 : F2=bCoord a h*F)
    (h3 : F3=h*(3/2*bCoord a h+23/36*a+5/72)*F)
    (hz : (1-z)*h=z) :
    F3=z*(F3+3/2*F2+23/36*F1+5/72*F) := by
  rw [h1,h2,h3]
  linear_combination ((3/2*bCoord a h+23/36*a+5/72)*F)*hz

end
end Integration.Paper9HypergeometricQTransport

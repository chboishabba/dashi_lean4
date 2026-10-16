import Mathlib.Tactic
import Synthesis.RiemannG21CommonLiteralParityMinors

/-!
# G21 parity minors imply independence modulo the two pole-parity directions

For symmetric samples `r,-r,2r,-2r`, write the off-line response directions as
an even block E_a=(ea1,ea1,ea2,ea2) and odd block
O_a=(oa1,-oa1,oa2,-oa2).  The two pole nuisance directions have the same parity
forms E_p and O_p.

If both 2x2 parity minors are nonzero, then

  c E_a + d O_a = lambda E_p + mu O_p

forces all four coefficients to vanish.  Thus the two off-line parity
directions are linearly independent modulo the span of the two pole-parity
nuisance directions.

This is exactly the finite rank-two quotient algebra.  It does NOT by itself
identify the literal post-explicit-formula nuisance span with E_p,O_p; that
same-object transport remains a separate source/analytic obligation.
-/

namespace Synthesis

/-- Two nonzero parity minors force full coefficient triviality in the four
symmetric sample equations. -/
theorem parityMinors_force_modPole_independence
    {ea1 ea2 ep1 ep2 oa1 oa2 op1 op2 c d lam mu : ℝ}
    (he : ea1*ep2 - ea2*ep1 ≠ 0)
    (ho : oa1*op2 - oa2*op1 ≠ 0)
    (h1 : c*ea1 + d*oa1 = lam*ep1 + mu*op1)
    (h2 : c*ea1 - d*oa1 = lam*ep1 - mu*op1)
    (h3 : c*ea2 + d*oa2 = lam*ep2 + mu*op2)
    (h4 : c*ea2 - d*oa2 = lam*ep2 - mu*op2) :
    c = 0 ∧ d = 0 ∧ lam = 0 ∧ mu = 0 := by
  have he1 : c*ea1 = lam*ep1 := by linarith
  have ho1 : d*oa1 = mu*op1 := by linarith
  have he2 : c*ea2 = lam*ep2 := by linarith
  have ho2 : d*oa2 = mu*op2 := by linarith
  have hcDet : c * (ea1*ep2 - ea2*ep1) = 0 := by
    calc
      c * (ea1*ep2 - ea2*ep1)
          = (c*ea1)*ep2 - (c*ea2)*ep1 := by ring
      _ = (lam*ep1)*ep2 - (lam*ep2)*ep1 := by rw [he1,he2]
      _ = 0 := by ring
  have hlamDet : lam * (ea1*ep2 - ea2*ep1) = 0 := by
    calc
      lam * (ea1*ep2 - ea2*ep1)
          = ea1*(lam*ep2) - ea2*(lam*ep1) := by ring
      _ = ea1*(c*ea2) - ea2*(c*ea1) := by rw [← he2,← he1]
      _ = 0 := by ring
  have hdDet : d * (oa1*op2 - oa2*op1) = 0 := by
    calc
      d * (oa1*op2 - oa2*op1)
          = (d*oa1)*op2 - (d*oa2)*op1 := by ring
      _ = (mu*op1)*op2 - (mu*op2)*op1 := by rw [ho1,ho2]
      _ = 0 := by ring
  have hmuDet : mu * (oa1*op2 - oa2*op1) = 0 := by
    calc
      mu * (oa1*op2 - oa2*op1)
          = oa1*(mu*op2) - oa2*(mu*op1) := by ring
      _ = oa1*(d*oa2) - oa2*(d*oa1) := by rw [← ho2,← ho1]
      _ = 0 := by ring
  have hc : c = 0 := (mul_eq_zero.mp hcDet).resolve_right he
  have hlam : lam = 0 := (mul_eq_zero.mp hlamDet).resolve_right he
  have hd : d = 0 := (mul_eq_zero.mp hdDet).resolve_right ho
  have hmu : mu = 0 := (mul_eq_zero.mp hmuDet).resolve_right ho
  exact ⟨hc,hd,hlam,hmu⟩

/-- Sign information is stronger than needed: strictly negative parity
minors are automatically nonzero and hence satisfy the quotient-rank gate. -/
theorem negativeParityMinors_force_modPole_independence
    {ea1 ea2 ep1 ep2 oa1 oa2 op1 op2 c d lam mu : ℝ}
    (he : ea1*ep2 - ea2*ep1 < 0)
    (ho : oa1*op2 - oa2*op1 < 0)
    (h1 : c*ea1 + d*oa1 = lam*ep1 + mu*op1)
    (h2 : c*ea1 - d*oa1 = lam*ep1 - mu*op1)
    (h3 : c*ea2 + d*oa2 = lam*ep2 + mu*op2)
    (h4 : c*ea2 - d*oa2 = lam*ep2 - mu*op2) :
    c = 0 ∧ d = 0 ∧ lam = 0 ∧ mu = 0 := by
  exact parityMinors_force_modPole_independence he.ne' ho.ne' h1 h2 h3 h4

end Synthesis

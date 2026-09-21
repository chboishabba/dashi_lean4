import Zeta23.GammaFacts.Complete
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact integration by parts for the theorem-bearing RvM mu density

This pays the smooth half of the N-mu Stieltjes formula.  With

  M_A(x) = integral_A^x mu,

and a C1 test phi,

  integral_A^B phi(x) mu(x) dx
    = phi(B) M_A(B) - integral_A^B phi'(x) M_A(x) dx.

The lower endpoint vanishes because M_A(A)=0.  The density is exactly
`Zeta23.mu`, using the proved GammaFacts package.
-/

noncomputable section

open MeasureTheory
open scoped Interval Real

namespace Synthesis

def zetaMuPrimitive (A x : ℝ) : ℝ :=
  ∫ tau in A..x, Zeta23.mu tau

theorem zetaMuPrimitive_self (A : ℝ) :
    zetaMuPrimitive A A = 0 := by
  simp [zetaMuPrimitive]


theorem zetaMuPrimitive_continuous (A : ℝ) :
    Continuous (zetaMuPrimitive A) := by
  have hcont : Continuous Zeta23.mu :=
    Zeta23.RvM.mu_continuous Zeta23.gammaFacts
  unfold zetaMuPrimitive
  exact intervalIntegral.continuous_primitive
    (fun a b => hcont.intervalIntegrable a b) A

theorem phi_mul_zetaMuPrimitive_intervalIntegrable
    {A B : ℝ} {phi' : ℝ -> ℝ}
    (hint : IntervalIntegrable phi' volume A B) :
    IntervalIntegrable
      (fun x => phi' x * zetaMuPrimitive A x)
      volume A B := by
  exact hint.mul_continuousOn
    (zetaMuPrimitive_continuous A).continuousOn

theorem zetaMuPrimitive_hasDerivAt
    (A x : ℝ) :
    HasDerivAt (zetaMuPrimitive A) (Zeta23.mu x) x := by
  have hcont : Continuous Zeta23.mu :=
    Zeta23.RvM.mu_continuous Zeta23.gammaFacts
  unfold zetaMuPrimitive
  exact intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable A x)
    hcont.stronglyMeasurableAtFilter
    hcont.continuousAt

theorem zetaMu_integrationByParts
    {A B : ℝ}
    {phi phi' : ℝ -> ℝ}
    (hphi :
      ∀ x ∈ Set.uIcc A B, HasDerivAt phi (phi' x) x)
    (hphiInt : IntervalIntegrable phi' volume A B) :
    (∫ x in A..B, phi x * Zeta23.mu x)
      =
    phi B * zetaMuPrimitive A B
      - ∫ x in A..B, phi' x * zetaMuPrimitive A x := by
  have hmuCont : Continuous Zeta23.mu :=
    Zeta23.RvM.mu_continuous Zeta23.gammaFacts
  have hM :
      ∀ x ∈ Set.uIcc A B,
        HasDerivAt (zetaMuPrimitive A) (Zeta23.mu x) x := by
    intro x hx
    exact zetaMuPrimitive_hasDerivAt A x
  have hMInt :
      IntervalIntegrable (fun x => Zeta23.mu x) volume A B :=
    hmuCont.intervalIntegrable A B
  have hibp :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := phi)
      (v := zetaMuPrimitive A)
      (u' := phi')
      (v' := Zeta23.mu)
      hphi hM hphiInt hMInt
  rw [zetaMuPrimitive_self] at hibp
  simpa using hibp

end Synthesis

import Synthesis.RiemannZetaFiniteAtomicCumulativeAbel
import Synthesis.RiemannRvMMuIntegrationByParts

/-!
# Exact literal N-mu Abel identity

The atomic zero pairing and the theorem-bearing RvM density now have matching
integration-by-parts formulas.  Subtracting them before any absolute value gives
the exact centered discrepancy consumer.

Let

  D_A(x) = Ncount A x - integral_A^x mu.

Then for every C1 test phi on [A,B],

  [sum_{A<gamma<=B} m_rho phi(gamma)] - integral_A^B phi(x) mu(x) dx
    =
  phi(B) D_A(B) - integral_A^B phi'(x) D_A(x) dx.

This is the prize-facing order of operations: N-mu first, estimate second.
No smooth-main decomposition, missing-tail split, or quadrature occurs.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Interval Real

namespace Synthesis

open Zeta23

def zetaMuCumulativeDiscrepancy (A x : ℝ) : ℝ :=
  (Ncount A x : ℝ) - zetaMuPrimitive A x

def zetaWindowMinusMuPair
    (A B : ℝ) (phi : ℝ -> ℝ) : ℝ :=
  zetaWindowWeightedPair A B phi
    - ∫ x in A..B, phi x * Zeta23.mu x

theorem zetaMuCumulativeDiscrepancy_endpoint
    (A B : ℝ) :
    zetaMuCumulativeDiscrepancy A B
      =
    zetaMuWindowDiscrepancy A B := by
  unfold zetaMuCumulativeDiscrepancy
    zetaMuPrimitive zetaMuWindowDiscrepancy
  rfl

/--
Exact same-object Abel identity for the literal zero count centered by the
actual theorem-bearing RvM density mu.
-/


theorem zetaWindowMinusMuPair_eq_discrepancyAbel
    {A B : ℝ}
    {phi phi' : ℝ -> ℝ}
    (hAB : A <= B)
    (hderiv : ∀ x ∈ Set.Icc A B, HasDerivAt phi (phi' x) x)
    (hphiInt : IntervalIntegrable phi' volume A B) :
    zetaWindowMinusMuPair A B phi
      =
    phi B * zetaMuCumulativeDiscrepancy A B
      -
    ∫ x in A..B,
      phi' x * zetaMuCumulativeDiscrepancy A x := by
  have hzero :=
    zetaWindowWeightedPair_eq_endpoint_sub_tail
      (A := A) (B := B) hderiv hphiInt
  have htail :=
    zetaWindowWeightedTailIntegral_eq_cumulativeCountIntegral
      (A := A) (B := B) hAB hphiInt
  have hmu :=
    zetaMu_integrationByParts
      (A := A) (B := B) hderiv hphiInt
  have hNint :
      IntervalIntegrable
        (fun x => phi' x * (Ncount A x : ℝ))
        volume A B :=
    phi_mul_Ncount_intervalIntegrable hAB hphiInt
  have hMint :
      IntervalIntegrable
        (fun x => phi' x * zetaMuPrimitive A x)
        volume A B :=
    phi_mul_zetaMuPrimitive_intervalIntegrable hphiInt
  unfold zetaWindowMinusMuPair
  rw [hzero, htail, hmu]
  unfold zetaMuCumulativeDiscrepancy
  rw [← intervalIntegral.integral_sub hNint hMint]
  ring

end Synthesis

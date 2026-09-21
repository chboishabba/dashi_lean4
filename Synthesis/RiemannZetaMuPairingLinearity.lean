import Synthesis.RiemannZetaMuExactAbel

/-!
# Linearity of the literal finite N-mu pairing

The finite-window zero-minus-mu functional

  L_{A,B}(phi)
    = sum_{A<gamma<=B} m_gamma phi(gamma)
      - integral_A^B phi(x) mu(x) dx

is linear in the real test phi whenever the relevant mu-weighted functions are
interval-integrable.

This elementary layer lets the exact quadratic dependence of a projective
kernel on taper coefficients pass directly to the theorem-bearing N-mu
consumer.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Interval Real

namespace Synthesis

open Zeta23

theorem zetaWindowWeightedPair_add
    (A B : ℝ)
    (phi psi : ℝ -> ℝ) :
    zetaWindowWeightedPair A B (fun x => phi x + psi x)
      =
    zetaWindowWeightedPair A B phi
      + zetaWindowWeightedPair A B psi := by
  classical
  let hfin : (zetaZeroConfig.window A B).Finite :=
    zetaZeroConfig.finite_window A B
  let F : Finset ℂ := hfin.toFinset
  unfold zetaWindowWeightedPair
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
      finsum_mem_eq_finite_toFinset_sum _ hfin,
      finsum_mem_eq_finite_toFinset_sum _ hfin,
      ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  ring

theorem zetaWindowWeightedPair_smul
    (A B c : ℝ)
    (phi : ℝ -> ℝ) :
    zetaWindowWeightedPair A B (fun x => c * phi x)
      =
    c * zetaWindowWeightedPair A B phi := by
  classical
  let hfin : (zetaZeroConfig.window A B).Finite :=
    zetaZeroConfig.finite_window A B
  unfold zetaWindowWeightedPair
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
      finsum_mem_eq_finite_toFinset_sum _ hfin,
      Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  ring

theorem zetaWindowMinusMuPair_add
    {A B : ℝ}
    {phi psi : ℝ -> ℝ}
    (hphi :
      IntervalIntegrable
        (fun x => phi x * Zeta23.mu x) volume A B)
    (hpsi :
      IntervalIntegrable
        (fun x => psi x * Zeta23.mu x) volume A B) :
    zetaWindowMinusMuPair A B (fun x => phi x + psi x)
      =
    zetaWindowMinusMuPair A B phi
      + zetaWindowMinusMuPair A B psi := by
  unfold zetaWindowMinusMuPair
  rw [zetaWindowWeightedPair_add]
  have hpoint :
      (fun x : ℝ => (phi x + psi x) * Zeta23.mu x)
        =
      fun x => phi x * Zeta23.mu x + psi x * Zeta23.mu x := by
    funext x
    ring
  rw [hpoint, intervalIntegral.integral_add hphi hpsi]
  ring

theorem zetaWindowMinusMuPair_smul
    {A B c : ℝ}
    {phi : ℝ -> ℝ}
    (hphi :
      IntervalIntegrable
        (fun x => phi x * Zeta23.mu x) volume A B) :
    zetaWindowMinusMuPair A B (fun x => c * phi x)
      =
    c * zetaWindowMinusMuPair A B phi := by
  unfold zetaWindowMinusMuPair
  rw [zetaWindowWeightedPair_smul]
  have hpoint :
      (fun x : ℝ => (c * phi x) * Zeta23.mu x)
        =
      fun x => c * (phi x * Zeta23.mu x) := by
    funext x
    ring
  rw [hpoint, intervalIntegral.integral_const_mul]
  ring

end Synthesis

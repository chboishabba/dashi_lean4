import Synthesis.MillenniumBSDCMSplitJacobiPrimaryResidual
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Tactic

/-!
# Specialized primary cube congruence for J(χ,χ²)

For the split quartic character χ and its quadratic shadow χ², the generic
Jacobi congruence can be strengthened by one power of `I-1`.

* `χ(x)-1` is divisible by `I-1`;
* for nonzero input, `χ²(y)-1` is either `0` or `-2`, hence divisible by
  `(I-1)^2` because `-2 = (-I)(I-1)^2`;
* the cardinal correction is divisible by `(I-1)^3` because
  `4 = (1-I)(I-1)^3` and `p ≡ 1 (mod 4)`.

This proves exactly the primary cube congruence required by the signed
split-prime Frobenius trace route.
-/

namespace Synthesis.Millennium.BSD

open Complex Algebra
open scoped BigOperators

private theorem quartic_apply_sub_one_linear_factor
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1)
    {x : ZMod p} (hx : x ≠ 0) :
    ∃ z : ℂ,
      z ∈ Algebra.adjoin ℤ ({Complex.I} : Set ℂ) ∧
      splitQuarticCharacter p hmod x - 1 = z * (Complex.I - 1) := by
  have hpow := splitQuarticCharacter_pow_four_eq_one hmod
  letI : NeZero 4 := ⟨by norm_num⟩
  obtain ⟨k,hklt,hk⟩ :=
    MulChar.exists_apply_eq_pow hpow Complex.isPrimitiveRoot_I hx
  refine ⟨(Finset.range k).sum (Complex.I ^ ·), ?_, ?_⟩
  · exact Subalgebra.sum_mem _ fun m _ =>
      Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ Complex.I) _
  · rw [hk]
    exact (geom_sum_mul Complex.I k).symm

private theorem quadraticShadow_sub_one_square_factor
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1)
    {y : ZMod p} (hy : y ≠ 0) :
    ∃ z : ℂ,
      z ∈ Algebra.adjoin ℤ ({Complex.I} : Set ℂ) ∧
      splitQuadraticShadow p hmod y - 1 =
        z * (Complex.I - 1) ^ 2 := by
  have hquad := complexQuadraticChar_isQuadratic p y
  rw [← splitQuadraticShadow_eq_complexQuadraticChar hmod] at hquad
  rcases hquad with h0 | h1 | hm1
  · have hunit : IsUnit y := isUnit_iff_ne_zero.mpr hy
    have hne : splitQuadraticShadow p hmod y ≠ 0 :=
      (MulChar.apply_ne_zero_iff.mpr hunit)
    exact (hne h0).elim
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    rw [h1]
    ring
  · refine ⟨-Complex.I, Subalgebra.neg_mem _
      (Algebra.self_mem_adjoin_singleton ℤ Complex.I), ?_⟩
    rw [hm1, Complex.I_sq]
    ring

private theorem splitJacobi_local_cube_factor
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1)
    (x : ZMod p) :
    ∃ z : ℂ,
      z ∈ Algebra.adjoin ℤ ({Complex.I} : Set ℂ) ∧
      (splitQuarticCharacter p hmod x - 1) *
          (splitQuadraticShadow p hmod (1-x) - 1)
        = z * (Complex.I - 1) ^ 3 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    simp
  rcases eq_or_ne x 1 with rfl | hx1
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    simp
  have hy : (1 - x : ZMod p) ≠ 0 := sub_ne_zero.mpr hx1.symm
  rcases quartic_apply_sub_one_linear_factor hmod hx0 with ⟨z1,hz1,e1⟩
  rcases quadraticShadow_sub_one_square_factor hmod hy with ⟨z2,hz2,e2⟩
  refine ⟨z1*z2, Subalgebra.mul_mem _ hz1 hz2, ?_⟩
  rw [e1,e2]
  ring

private theorem four_eq_gaussian_cube_factor :
    (4 : ℂ) = (1 - Complex.I) * (Complex.I - 1) ^ 3 := by
  rw [Complex.I_sq]
  ring

theorem splitJacobiPlus_primary_cube_gaussian
    {p : ℕ} [Fact hp : p.Prime] (hmod : p % 4 = 1) :
    ∃ z : ℂ,
      z ∈ Algebra.adjoin ℤ ({Complex.I} : Set ℂ) ∧
      splitJacobiPlus p hmod =
        -1 + z * (Complex.I - 1) ^ 3 := by
  classical
  let χ := splitQuarticCharacter p hmod
  let ψ := splitQuadraticShadow p hmod
  have hχ0 : χ ≠ 1 := splitQuarticCharacter_ne_one hmod
  have hψ0 : ψ ≠ 1 := splitQuadraticShadow_ne_one hmod
  obtain ⟨q,hq⟩ := four_dvd_prime_sub_one_of_mod_four_eq_one hmod
  rw [Nat.sub_eq_iff_eq_add NeZero.one_le] at hq
  have H := splitJacobi_local_cube_factor hmod
  have Hcs x := (H x)
  unfold splitJacobiPlus
  rw [jacobiSum_eq_aux, MulChar.sum_eq_zero_of_ne_one hχ0,
      MulChar.sum_eq_zero_of_ne_one hψ0, hq]
  let zCard : ℂ := 1 - Complex.I
  have hzCard : zCard ∈ Algebra.adjoin ℤ ({Complex.I} : Set ℂ) := by
    dsimp [zCard]
    exact Subalgebra.sub_mem _ (Subalgebra.one_mem _)
      (Algebra.self_mem_adjoin_singleton ℤ Complex.I)
  refine ⟨-q * zCard +
      ∑ x ∈ (Finset.univ \ {0,1} : Finset (ZMod p)), (H x).choose, ?_, ?_⟩
  · refine Subalgebra.add_mem _
      (Subalgebra.mul_mem _
        (Subalgebra.neg_mem _ (Subalgebra.natCast_mem _ q)) hzCard) ?_
    exact Subalgebra.sum_mem _ fun x hx => (Hcs x).1
  · conv => enter [1,2,2,x]; rw [(Hcs x).2]
    rw [← Finset.sum_mul, Nat.cast_add, Nat.cast_mul,
      four_eq_gaussian_cube_factor]
    dsimp [zCard]
    ring

theorem splitJacobiPrimaryCubeCongruence_paid :
    SplitJacobiPrimaryCubeCongruence := by
  intro p hp hmod
  letI : Fact p.Prime := ⟨hp⟩
  rcases splitJacobiPlus_primary_cube_gaussian hmod with ⟨z,hz,hJ⟩
  rcases exists_int_coords_of_mem_adjoin_I hz with ⟨c,d,hzcd⟩
  refine ⟨c,d,?_⟩
  simpa [hzcd] using hJ

end Synthesis.Millennium.BSD

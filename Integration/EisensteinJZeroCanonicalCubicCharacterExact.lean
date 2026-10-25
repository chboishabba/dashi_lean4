import Integration.EisensteinJZeroCubicJacobiExact
import Integration.EisensteinSplitPrimeExact
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic

/-!
# Canonical cubic-character certificate for the split j=0 branch

This file pays the finite-field producer left open by
`EisensteinJZeroCubicJacobiExact`.

For a finite field `F` with `#F ≡ 1 (mod 3)`, Mathlib supplies the existence
of a multiplicative character of exact order three.  We choose one such
character and prove the stronger fact needed by the j=0 trace compiler:

* on nonzero elements, `psi(t)=1` iff `t` is a cube;
* a nonzero cube has exactly three cube roots;
* a noncube has no cube roots, while zero has one;
* therefore the literal cube-fibre multiplicity is

      1 + psi(t) + psi(t)^2,

  and the weighted cube reindexing identity follows.

The resulting character is packaged into the existing
`CubicCharacterCertificate` and specialized to split prime fields `ZMod p`.
The final structure also welds the SAME split prime to the already-proved
Eisenstein norm-p witness.

Attribution: Mathlib owns the generic finite-field cyclicity, multiplicative
character, primitive-root, polynomial-root and finite-sum infrastructure used
below.  DASHI/Lean owns this specialization/composition.  No Jacobi-sum
Eisenstein-prime evaluation, Hecke character, or elliptic L-function theorem is
manufactured here.
-/

namespace Integration.EisensteinJZeroCanonicalCubicCharacterExact

open scoped BigOperators
open Finset
open Polynomial
open Integration.EisensteinJZeroFiniteFieldTraceExact
open Integration.EisensteinJZeroCubicJacobiExact
open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinSplitPrimeExact

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

------------------------------------------------------------------------
-- Order-three character selected from Mathlib's finite-field character API.
------------------------------------------------------------------------

private theorem three_dvd_card_sub_one
    (hq : Fintype.card F % 3 = 1) :
    3 ∣ Fintype.card F - 1 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have hcard : 1 < Fintype.card F := Fintype.one_lt_card
  omega

/-- A distinguished order-three multiplicative character.  The choice is
noncomputable, but every theorem below depends only on its exact order and the
cyclic unit group, not on an arbitrary phase convention. -/
noncomputable def canonicalCubicCharacter
    (hq : Fintype.card F % 3 = 1) : MulChar F ℂ :=
  Classical.choose <|
    MulChar.exists_mulChar_orderOf F
      (three_dvd_card_sub_one (F := F) hq)
      (Complex.isPrimitiveRoot_exp 3 (by norm_num))

/-- The chosen character has exact order three. -/
theorem canonicalCubicCharacter_order
    (hq : Fintype.card F % 3 = 1) :
    orderOf (canonicalCubicCharacter (F := F) hq) = 3 :=
  Classical.choose_spec <|
    MulChar.exists_mulChar_orderOf F
      (three_dvd_card_sub_one (F := F) hq)
      (Complex.isPrimitiveRoot_exp 3 (by norm_num))

/-- Hence the third power of the character is the trivial character. -/
theorem canonicalCubicCharacter_pow_three
    (hq : Fintype.card F % 3 = 1) :
    canonicalCubicCharacter (F := F) hq ^ 3 = 1 := by
  have h := pow_orderOf_eq_one (canonicalCubicCharacter (F := F) hq)
  simpa [canonicalCubicCharacter_order (F := F) hq] using h

/-- Exact order three forbids triviality. -/
theorem canonicalCubicCharacter_ne_one
    (hq : Fintype.card F % 3 = 1) :
    canonicalCubicCharacter (F := F) hq ≠ 1 := by
  intro h
  have ho := canonicalCubicCharacter_order (F := F) hq
  rw [h, orderOf_one] at ho
  norm_num at ho

/-- Its square is also nontrivial. -/
theorem canonicalCubicCharacter_sq_ne_one
    (hq : Fintype.card F % 3 = 1) :
    canonicalCubicCharacter (F := F) hq *
        canonicalCubicCharacter (F := F) hq ≠ 1 := by
  intro hsq
  have hp : canonicalCubicCharacter (F := F) hq ^ 2 = 1 := by
    simpa [pow_two] using hsq
  have hd := orderOf_dvd_of_pow_eq_one hp
  rw [canonicalCubicCharacter_order (F := F) hq] at hd
  norm_num at hd

------------------------------------------------------------------------
-- Kernel = nonzero cubes.
------------------------------------------------------------------------

private theorem generator_value_isPrimitiveRoot_three
    (ψ : MulChar F ℂ) (hψ : orderOf ψ = 3)
    {g : Fˣ} (hg : ∀ u : Fˣ, u ∈ Subgroup.zpowers g) :
    IsPrimitiveRoot (ψ g) 3 := by
  refine ⟨?_, ?_⟩
  · have hpow : ψ ^ 3 = 1 := by
      have h := pow_orderOf_eq_one ψ
      simpa [hψ] using h
    have hev := congrArg (fun χ : MulChar F ℂ => χ g) hpow
    simpa [MulChar.pow_apply_coe] using hev
  · intro n hn
    have hchar : ψ ^ n = 1 := by
      apply (MulChar.eq_iff hg (ψ ^ n) 1).2
      simpa [MulChar.pow_apply_coe] using hn
    have hd := orderOf_dvd_of_pow_eq_one hchar
    simpa [hψ] using hd

/-- For nonzero field elements, the kernel of the selected order-three
character is exactly the image of the cube map. -/
theorem canonicalCubicCharacter_eq_one_iff_cube
    (hq : Fintype.card F % 3 = 1) {t : F} (ht : t ≠ 0) :
    canonicalCubicCharacter (F := F) hq t = 1 ↔
      ∃ x : F, x ^ 3 = t := by
  let ψ := canonicalCubicCharacter (F := F) hq
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hprim : IsPrimitiveRoot (ψ g) 3 :=
    generator_value_isPrimitiveRoot_three
      (F := F) ψ (canonicalCubicCharacter_order (F := F) hq) hg
  constructor
  · intro hψt
    let u : Fˣ := Units.mk0 t ht
    obtain ⟨m, hm⟩ := hg u
    have hzm : (ψ g) ^ m = 1 := by
      have hmap := congrArg (fun v : Fˣ => ψ.toUnitHom v) hm
      have hval := congrArg (fun v : ℂˣ => (v : ℂ)) hmap
      simpa [map_zpow, MulChar.coe_toUnitHom, u, hψt] using hval
    obtain ⟨k, hk⟩ := (hprim.zpow_eq_one_iff_dvd m).1 hzm
    refine ⟨((g ^ k : Fˣ) : F), ?_⟩
    have hkm : k * (3 : ℤ) = m := by
      rw [hk]
      ring
    have hunit : (g ^ k) ^ (3 : ℕ) = u := by
      rw [← zpow_natCast, ← zpow_mul, hkm]
      exact hm
    have hval := congrArg Units.val hunit
    simpa [u] using hval
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      intro h0
      subst x
      simp at hx
      exact ht hx.symm
    have hpow := canonicalCubicCharacter_pow_three (F := F) hq
    have hev := congrArg (fun χ : MulChar F ℂ => χ x) hpow
    have hxchar : ψ x ^ 3 = 1 := by
      simpa [ψ, MulChar.pow_apply', MulChar.one_apply (isUnit_iff_ne_zero.mpr hx0)] using hev
    rw [← hx, map_pow]
    exact hxchar

------------------------------------------------------------------------
-- Literal cube fibres.
------------------------------------------------------------------------

/-- Literal cube fibre over `t`. -/
def cubeFiber (t : F) : Finset F :=
  Finset.univ.filter fun x => x ^ 3 = t

@[simp]
theorem mem_cubeFiber {t x : F} :
    x ∈ cubeFiber t ↔ x ^ 3 = t := by
  simp [cubeFiber]

private theorem exists_primitiveCubeRoot
    (hq : Fintype.card F % 3 = 1) :
    ∃ ξ : F, IsPrimitiveRoot ξ 3 := by
  have hdiv : 3 ∣ Fintype.card Fˣ := by
    rw [Fintype.card_units]
    exact three_dvd_card_sub_one (F := F) hq
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 hdiv
  refine ⟨(u : F), ?_⟩
  apply IsPrimitiveRoot.coe_units_iff.mpr
  simpa [hu] using (IsPrimitiveRoot.orderOf u)

private theorem cubeFiber_one_card
    (hq : Fintype.card F % 3 = 1) :
    (cubeFiber (1 : F)).card = 3 := by
  obtain ⟨ξ, hξ⟩ := exists_primitiveCubeRoot (F := F) hq
  calc
    (cubeFiber (1 : F)).card
        = #(Polynomial.nthRootsFinset 3 (1 : F)) := by
            congr 1
            ext x
            simp [cubeFiber, Polynomial.mem_nthRootsFinset]
    _ = 3 := hξ.card_nthRootsFinset

private theorem cubeFiber_card_eq_three_of_cube
    (hq : Fintype.card F % 3 = 1)
    {t : F} (ht : t ≠ 0) (hcube : ∃ r : F, r ^ 3 = t) :
    (cubeFiber t).card = 3 := by
  obtain ⟨r, hr⟩ := hcube
  have hr0 : r ≠ 0 := by
    intro h0
    subst r
    simp at hr
    exact ht hr.symm
  calc
    (cubeFiber t).card = (cubeFiber (1 : F)).card := by
      apply Finset.card_bij
        (s := cubeFiber t) (t := cubeFiber (1 : F))
        (fun x _ => x / r)
      · intro x hx
        rw [mem_cubeFiber] at hx ⊢
        rw [div_pow, hx, ← hr, div_self (pow_ne_zero 3 hr0)]
      · intro x₁ hx₁ x₂ hx₂ h
        exact (div_right_injective hr0).mp h
      · intro u hu
        refine ⟨u * r, ?_, ?_⟩
        · rw [mem_cubeFiber] at hu ⊢
          rw [mul_pow, hu, hr, one_mul]
        · exact mul_div_cancel_right₀ u hr0
    _ = 3 := cubeFiber_one_card (F := F) hq

private theorem cubeFiber_card_eq_zero_of_not_cube
    {t : F} (h : ¬ ∃ r : F, r ^ 3 = t) :
    (cubeFiber t).card = 0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact h ⟨x, (mem_cubeFiber.mp hx)⟩

private theorem cubeFiber_zero_card :
    (cubeFiber (0 : F)).card = 1 := by
  have heq : cubeFiber (0 : F) = {0} := by
    ext x
    simp [cubeFiber]
  rw [heq, Finset.card_singleton]

------------------------------------------------------------------------
-- Character weight = literal fibre multiplicity.
------------------------------------------------------------------------

/-- The order-three character weight used by the Jacobi compiler. -/
noncomputable def canonicalCubicWeight
    (hq : Fintype.card F % 3 = 1) (t : F) : ℂ :=
  1 + canonicalCubicCharacter (F := F) hq t +
    (canonicalCubicCharacter (F := F) hq *
      canonicalCubicCharacter (F := F) hq) t

private theorem character_weight_zero_of_not_cube
    (hq : Fintype.card F % 3 = 1)
    {t : F} (ht : t ≠ 0) (hnot : ¬ ∃ r : F, r ^ 3 = t) :
    canonicalCubicWeight (F := F) hq t = 0 := by
  let ψ := canonicalCubicCharacter (F := F) hq
  have hψne : ψ t ≠ 1 := by
    intro h
    exact hnot ((canonicalCubicCharacter_eq_one_iff_cube (F := F) hq ht).1 h)
  have hpow := canonicalCubicCharacter_pow_three (F := F) hq
  have hev := congrArg (fun χ : MulChar F ℂ => χ t) hpow
  have hψ3 : ψ t ^ 3 = 1 := by
    simpa [ψ, MulChar.pow_apply', MulChar.one_apply (isUnit_iff_ne_zero.mpr ht)] using hev
  have hfac : (ψ t - 1) * (ψ t ^ 2 + ψ t + 1) = 0 := by
    calc
      (ψ t - 1) * (ψ t ^ 2 + ψ t + 1) = ψ t ^ 3 - 1 := by ring
      _ = 0 := by rw [hψ3]; ring
  have hsecond : ψ t ^ 2 + ψ t + 1 = 0 :=
    (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hψne)
  unfold canonicalCubicWeight
  rw [MulChar.mul_apply]
  change 1 + ψ t + ψ t * ψ t = 0
  calc
    1 + ψ t + ψ t * ψ t = ψ t ^ 2 + ψ t + 1 := by ring
    _ = 0 := hsecond

/-- Exact equality between the character weight and the cardinality of the
literal cube fibre. -/
theorem cubeFiber_card_cast_eq_canonicalCubicWeight
    (hq : Fintype.card F % 3 = 1) (t : F) :
    ((cubeFiber t).card : ℂ) = canonicalCubicWeight (F := F) hq t := by
  by_cases ht : t = 0
  · subst t
    rw [cubeFiber_zero_card]
    simp [canonicalCubicWeight, MulChar.mul_apply]
  · by_cases hcube : ∃ r : F, r ^ 3 = t
    · rw [cubeFiber_card_eq_three_of_cube (F := F) hq ht hcube]
      have hψ := (canonicalCubicCharacter_eq_one_iff_cube (F := F) hq ht).2 hcube
      simp [canonicalCubicWeight, MulChar.mul_apply, hψ]
    · rw [cubeFiber_card_eq_zero_of_not_cube (F := F) hcube]
      simpa using (character_weight_zero_of_not_cube (F := F) hq ht hcube).symm

/-- The selected order-three character literally records the cube fibres, not
merely an abstract C3 phase. -/
theorem canonicalCubicCharacter_cubeWeightedReindex
    (hq : Fintype.card F % 3 = 1) (f : F → ℂ) :
    (∑ x : F, f (x ^ 3)) =
      ∑ t : F,
        (1 + canonicalCubicCharacter (F := F) hq t +
          (canonicalCubicCharacter (F := F) hq *
            canonicalCubicCharacter (F := F) hq) t) * f t := by
  classical
  calc
    (∑ x : F, f (x ^ 3))
        = ∑ t : F, ∑ x ∈ cubeFiber t, f t := by
            symm
            simpa [cubeFiber] using
              (Finset.sum_fiberwise_eq_sum_filter'
                (s := (Finset.univ : Finset F))
                (t := (Finset.univ : Finset F))
                (g := fun x : F => x ^ 3) f)
    _ = ∑ t : F, (cubeFiber t).card • f t := by
          apply Finset.sum_congr rfl
          intro t ht
          simp
    _ = ∑ t : F, canonicalCubicWeight (F := F) hq t * f t := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [nsmul_eq_mul]
          rw [cubeFiber_card_cast_eq_canonicalCubicWeight (F := F) hq t]
    _ = _ := rfl

------------------------------------------------------------------------
-- Package the producer expected by the existing Jacobi compiler.
------------------------------------------------------------------------

/-- The previously-open cubic-character certificate is now constructed for
all finite fields with cardinality `1 mod 3`. -/
noncomputable def canonicalCubicCharacterCertificate
    (hq : Fintype.card F % 3 = 1) :
    CubicCharacterCertificate F where
  character := canonicalCubicCharacter (F := F) hq
  nontrivial := canonicalCubicCharacter_ne_one (F := F) hq
  squareNontrivial := canonicalCubicCharacter_sq_ne_one (F := F) hq
  cubeWeightedReindex := canonicalCubicCharacter_cubeWeightedReindex (F := F) hq

/-- Prime-field adapter for the split residue class. -/
noncomputable def splitPrimeCubicCharacterCertificate
    (p : Nat) [Fact p.Prime] (hp3 : p % 3 = 1) :
    CubicCharacterCertificate (ZMod p) := by
  apply canonicalCubicCharacterCertificate (F := ZMod p)
  simpa [ZMod.card] using hp3

------------------------------------------------------------------------
-- Same-prime weld to the existing Eisenstein split witness.
------------------------------------------------------------------------

/-- A split rational prime now has, on the same prime:

* an Eisenstein integer of norm `p`;
* a literal cubic-character cube-fibre certificate on `F_p`;
* the already-proved Jacobi expression for the j=0 Frobenius trace.

The Jacobi sum is NOT yet evaluated as the selected Eisenstein factor. -/
structure SplitPrimeArithmeticJacobiWeld (p : Nat) [Fact p.Prime] where
  eisensteinFactor : EisensteinQA
  eisensteinFactorNorm : QuadraticAlgebra.norm eisensteinFactor = p
  cubicCertificate : CubicCharacterCertificate (ZMod p)
  jZeroTraceJacobi :
    ((jZeroFrobeniusTraceInt (ZMod p) : Int) : ℂ) =
      cubicJacobiTrace cubicCertificate

/-- Construct the same-prime split arithmetic/Jacobi weld. -/
noncomputable def splitPrimeArithmeticJacobiWeld
    (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    SplitPrimeArithmeticJacobiWeld p := by
  obtain ⟨z, hz⟩ := split_prime_has_norm_witness p Fact.out hp3
  let cert := splitPrimeCubicCharacterCertificate p hp3
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  exact
    { eisensteinFactor := z
      eisensteinFactorNorm := hz
      cubicCertificate := cert
      jZeroTraceJacobi :=
        jZeroTrace_cast_eq_cubicJacobiTrace
          (F := ZMod p) hchar cert }

------------------------------------------------------------------------
-- Honest terminal boundary.
------------------------------------------------------------------------

structure CanonicalCubicCharacterBoundary where
  orderThreeCharacterConstructed : Bool := true
  nonzeroKernelEqualsCubes : Bool := true
  literalCubeFiberMultiplicityPaid : Bool := true
  cubeWeightedReindexPaid : Bool := true
  cubicCharacterCertificatePaid : Bool := true
  splitPrimeSamePrimeEisensteinJacobiWeldPaid : Bool := true
  jacobiSumEvaluatedAsSelectedEisensteinPrime : Bool := false
  splitPrimeFrobeniusClosedFormPaid : Bool := false
  heckeCharacterPaid : Bool := false
  globalEllipticLFunctionPaid : Bool := false

/-- Machine-readable boundary for downstream terminal surfaces. -/
def canonicalBoundary : CanonicalCubicCharacterBoundary := {}

end Integration.EisensteinJZeroCanonicalCubicCharacterExact

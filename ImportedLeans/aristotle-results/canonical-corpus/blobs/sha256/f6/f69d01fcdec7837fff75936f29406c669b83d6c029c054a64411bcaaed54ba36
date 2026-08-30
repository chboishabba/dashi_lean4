import Synthesis.InferenceFibre

/-!
# Synthesis layer 2'''''''': exponent vectors over the base, and the observer residue

The repository's `MoonshineFractran` sketch works with *exponent vectors* over
the fifteen supersingular primes (`FractranState = Fin 15 → Nat`, states given
as lists of `(index, exponent)` pairs) and records, by `native_decide` on the
three particular numerals, that `196884` leaves residue `1` modulo each of
`47`, `59`, `71`.

This layer places that picture inside the spine and replaces the numeral checks
by a theorem:

* `fractranStateEquiv` — the exponent-vector carrier is the fibre over the prime
  base, so it is the same object as `Vec15 Nat` (`Synthesis.Vec15Fibre`);
* `exponentProduct` — the number an exponent vector denotes, generalising the
  mask product of `Synthesis.MoonshineBase` (`exponentProduct_indicator`);
* `exponentProduct_dvd_of_le`, `maskProduct_support_dvd_exponentProduct` — the
  exponent order refines the mask order, and a state's support mask always
  divides the state;
* `maskProduct_succ_mod` — **the observer residue, proved in general**: for
  *every* mask and *every* prime it keeps, `maskProduct m + 1 ≡ 1` modulo that
  prime.  The three supplied numeral facts are the instances
  `jCoefficient_mod_trivector` at `47`, `59`, `71`.

Provenance: `196883`/`196884` are numerals here, exactly as in
`Synthesis.MoonshineBase`; nothing about Monster representations or the
`j`-invariant is claimed.
-/

namespace Synthesis.ExponentFibre

open AgdaMirror.MonsterOntos (SSP toNat)
open Synthesis.MonsterFibre
open Synthesis.Vec15Fibre
open Synthesis.MoonshineBase

/-- The exponent-vector carrier is the fibre over the prime base. -/
def fractranStateEquiv : (Fin 15 → Nat) ≃ (SSP → Nat) :=
  Equiv.arrowCongr sspEquivFin15.symm (Equiv.refl Nat)

/-- The number denoted by an exponent vector over the base. -/
def exponentProduct (v : SSP → Nat) : Nat := ∏ p : SSP, toNat p ^ v p

/-- Enumeration of a product over the prime base. -/
theorem prod_over_base {M : Type*} [CommMonoid M] (f : SSP → M) :
    ∏ p : SSP, f p = f .p2 * f .p3 * f .p5 * f .p7 * f .p11 * f .p13 * f .p17 * f .p19
      * f .p23 * f .p29 * f .p31 * f .p41 * f .p47 * f .p59 * f .p71 := by
  rw [← Equiv.prod_comp sspEquivFin15.symm f]
  simp [Fin.prod_univ_succ, sspEquivFin15, finToSsp, mul_assoc]

/-- The support mask of an exponent vector. -/
def supportOf (v : SSP → Nat) : MaskSSP := fun p => decide (v p ≠ 0)

/-- On `0/1` exponent vectors the exponent product is the mask product. -/
theorem exponentProduct_indicator (m : MaskSSP) :
    exponentProduct (fun p => if m p then 1 else 0) = maskProduct m := by
  rw [exponentProduct, maskProduct, ← Finset.prod_filter_mul_prod_filter_not
    Finset.univ (fun p : SSP => m p = true)]
  have h₁ : ∀ p ∈ Finset.univ.filter (fun p : SSP => m p = true),
      toNat p ^ (if m p then 1 else 0) = toNat p := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    simp [hp.2]
  have h₂ : ∀ p ∈ Finset.univ.filter (fun p : SSP => ¬ (m p = true)),
      toNat p ^ (if m p then 1 else 0) = 1 := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    simp [hp.2]
  rw [Finset.prod_congr rfl h₁, Finset.prod_congr rfl h₂, Finset.prod_const_one, mul_one]

/-- Exponentwise domination gives divisibility. -/
theorem exponentProduct_dvd_of_le {v w : SSP → Nat} (h : ∀ p, v p ≤ w p) :
    exponentProduct v ∣ exponentProduct w :=
  Finset.prod_dvd_prod_of_dvd _ _ fun p _ => pow_dvd_pow (toNat p) (h p)

/-- A state's support mask always divides the state. -/
theorem maskProduct_support_dvd_exponentProduct (v : SSP → Nat) :
    maskProduct (supportOf v) ∣ exponentProduct v := by
  rw [← exponentProduct_indicator]
  refine exponentProduct_dvd_of_le fun p => ?_
  by_cases h : v p = 0
  · simp [supportOf, h]
  · simp only [supportOf, h, decide_true, ne_eq, not_false_eq_true, if_pos]
    omega

/-- The support mask of a 15-lane record, read as an exponent vector, is the
support mask of `Synthesis.InferenceFibre`. -/
theorem supportOf_vec15 (v : AgdaMirror.Vec15Order.PrimeCarrier15) :
    supportOf (vec15Equiv v) = Synthesis.InferenceFibre.supportMask v := rfl

/-- The prime factors of an everywhere-positive exponent vector are exactly the
fifteen primes of the base. -/
theorem primeFactors_prod_pow (s : Finset SSP) {v : SSP → Nat} (h : ∀ p, v p ≠ 0) :
    (∏ p ∈ s, toNat p ^ v p).primeFactors = s.image AgdaMirror.MonsterOntos.toNat := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hne : (toNat a ^ v a) ≠ 0 := pow_ne_zero _ (toNat_prime a).pos.ne'
      have hprod : (∏ p ∈ s, toNat p ^ v p) ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr fun p _ => ?_
        exact pow_ne_zero _ (toNat_prime p).pos.ne'
      rw [Finset.prod_insert ha, Nat.primeFactors_mul hne hprod,
        Nat.primeFactors_pow _ (h a), (toNat_prime a).primeFactors, ih,
        Finset.image_insert]
      rfl

/-- Consequently the prime factors of a positive exponent product are the base. -/
theorem exponentProduct_primeFactors {v : SSP → Nat} (h : ∀ p, v p ≠ 0) :
    (exponentProduct v).primeFactors =
      Finset.univ.image AgdaMirror.MonsterOntos.toNat :=
  primeFactors_prod_pow Finset.univ h

/-! ## The observer residue -/

/-- Every prime a mask keeps divides the mask's product. -/
theorem toNat_dvd_maskProduct {m : MaskSSP} {p : SSP} (h : m p = true) :
    toNat p ∣ maskProduct m :=
  Finset.dvd_prod_of_mem _ (by simp [h])

/-- **The observer residue, in general.**  Adding one to a mask product leaves
residue `1` modulo every prime the mask keeps. -/
theorem maskProduct_succ_mod {m : MaskSSP} {p : SSP} (h : m p = true) :
    (maskProduct m + 1) % toNat p = 1 := by
  obtain ⟨k, hk⟩ := toNat_dvd_maskProduct h
  rw [hk, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (toNat_prime p).one_lt

/-- The supplied `jCoefficient = 196884` leaves residue `1` modulo each of the
three primes of the trivector mask — one theorem in place of the three numeral
checks. -/
theorem jCoefficient_mod_trivector {p : SSP} (h : trivectorMask p = true) :
    AgdaMirror.Moonshine.jCoefficient % toNat p = 1 := by
  rw [← maskProduct_trivector_succ]
  exact maskProduct_succ_mod h

/-- Spelled out at the three primes. -/
theorem jCoefficient_mod_47_59_71 :
    AgdaMirror.Moonshine.jCoefficient % 47 = 1 ∧
    AgdaMirror.Moonshine.jCoefficient % 59 = 1 ∧
    AgdaMirror.Moonshine.jCoefficient % 71 = 1 :=
  ⟨jCoefficient_mod_trivector (p := .p47) rfl,
   jCoefficient_mod_trivector (p := .p59) rfl,
   jCoefficient_mod_trivector (p := .p71) rfl⟩

end Synthesis.ExponentFibre

import Synthesis.MonsterFibre
import AgdaMirror.Moonshine

/-!
# Synthesis layer 2'': the mask fibre as arithmetic of the Monster primes

`AgdaMirror.Moonshine` supplies the numerals `repDim = 47 · 59 · 71 = 196883`
and `jCoefficient = repDim + 1 = 196884`, with the informal reading that these
are the smallest faithful representation dimension of the Monster and the first
non-trivial `j`-invariant Fourier coefficient.  *That reading is provenance, not
theorem*: nothing in this repository proves anything about representations of
the Monster group or about modular forms, and nothing here does either.

What is proved here is the structural link that does exist: the supplied
numerals are the values of a *product over the mask fibre* of layer 2.  Masks
over the supersingular prime base thus have an arithmetic meaning, and the
moonshine numerals are the value of that arithmetic at one specific mask.

* `maskProduct` — the product of the primes selected by a mask;
* `maskProduct_trivector` — the mask selecting `{47, 59, 71}` has product exactly
  the supplied `repDim`, and `+1` gives the supplied `jCoefficient`;
* `trivectorMask_iff` — that mask is exactly "the primes `≥ 47`", i.e. the three
  largest elements of the base;
* `maskProduct_and_dvd`, `maskProduct_dvd_full` — masking only ever removes prime
  factors, so mask products form a divisor chain below the radical
  `maskProduct fullMaskSSP`.
-/

namespace Synthesis.MoonshineBase

open AgdaMirror.MonsterOntos (SSP)
open Synthesis.MonsterFibre

/-- The product of the primes selected by a mask. -/
def maskProduct (m : MaskSSP) : Nat :=
  ∏ p ∈ Finset.univ.filter (fun p => m p = true), AgdaMirror.MonsterOntos.toNat p

/-- The mask selecting the three largest supersingular primes. -/
def trivectorMask : MaskSSP := fun p => decide (47 ≤ AgdaMirror.MonsterOntos.toNat p)

/-- The trivector mask selects exactly `{47, 59, 71}`. -/
theorem trivectorMask_iff (p : SSP) :
    trivectorMask p = true ↔ (p = .p47 ∨ p = .p59 ∨ p = .p71) := by
  cases p <;> simp [trivectorMask, AgdaMirror.MonsterOntos.toNat]

/-- **The moonshine numeral is a mask product.**  The product over the trivector
mask is the supplied `repDim = 196883`. -/
theorem maskProduct_trivector : maskProduct trivectorMask = AgdaMirror.Moonshine.repDim := by
  decide

/-- ... and adding the supplied "observer" `+1` gives the supplied
`jCoefficient = 196884`. -/
theorem maskProduct_trivector_succ :
    maskProduct trivectorMask + 1 = AgdaMirror.Moonshine.jCoefficient := by
  decide

/-- The full mask has as product the radical of the supersingular primes. -/
theorem maskProduct_full :
    maskProduct fullMaskSSP =
      2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71 := by
  decide

/-- Masking removes factors: the product over a refined mask divides the
product over the coarser one. -/
theorem maskProduct_and_dvd (x y : MaskSSP) : maskProduct (maskAndSSP x y) ∣ maskProduct x := by
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, maskAndSSP] at hp ⊢
  exact (Bool.and_eq_true _ _ ▸ hp).1

/-- Every mask product divides the radical. -/
theorem maskProduct_dvd_full (x : MaskSSP) : maskProduct x ∣ maskProduct fullMaskSSP := by
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  simp [fullMaskSSP]

/-- In particular the moonshine numeral divides the radical of the base. -/
theorem repDim_dvd_radical : AgdaMirror.Moonshine.repDim ∣ maskProduct fullMaskSSP := by
  rw [← maskProduct_trivector]
  exact maskProduct_dvd_full trivectorMask

/-- The base numbering is injective, so masks are determined by their kept primes. -/
theorem toNat_injective : Function.Injective AgdaMirror.MonsterOntos.toNat := by decide

/-- **Mask arithmetic is mask order.**  Because the base consists of fifteen
*distinct primes*, divisibility of mask products is exactly the submask relation.
This is what lets an arithmetic admissibility test be read as a geometric one. -/
theorem maskProduct_dvd_iff (x y : MaskSSP) :
    maskProduct x ∣ maskProduct y ↔ ∀ p, x p = true → y p = true := by
  constructor
  · intro hdvd p hp
    have hmem : p ∈ Finset.univ.filter (fun q => x q = true) := by simp [hp]
    have h2 : AgdaMirror.MonsterOntos.toNat p ∣ maskProduct y :=
      (Finset.dvd_prod_of_mem _ hmem).trans hdvd
    have hprime : Nat.Prime (AgdaMirror.MonsterOntos.toNat p) := toNat_prime p
    rw [maskProduct] at h2
    obtain ⟨q, hq, hqd⟩ := (Nat.Prime.prime hprime).exists_mem_finset_dvd h2
    have hpq : p = q :=
      toNat_injective ((Nat.prime_dvd_prime_iff_eq hprime (toNat_prime q)).mp hqd)
    simpa [hpq] using (Finset.mem_filter.mp hq).2
  · intro h
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
    exact h p hp

end Synthesis.MoonshineBase

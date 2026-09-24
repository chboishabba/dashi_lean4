import Mathlib
import RequestProject.Sieve23

/-!
# The Legendre density of a finite sieve

`RequestProject.Sieve23` proves the exact statement for the two primes `2` and `3`: among the
first `6 * k` naturals exactly `4 * k` are divisible by `2` or `3`, a density of `2/3`.  This file
proves the general fact of which that is the specialisation.

Let `S` be a finite set of primes and `M = ∏_{p ∈ S} p`.  The sieved set is periodic mod `M`, and
in one period the survivors are exactly the residues coprime to `M`, of which there are
`φ(M) = ∏_{p ∈ S} (p - 1)`.  Hence

* `SieveGeneral.card_survivors_range` : `#{n < M * k : ∀ p ∈ S, ¬ p ∣ n} = k * ∏_{p ∈ S} (p - 1)`,
* `SieveGeneral.card_sieved_range`    : `#{n < M * k : ∃ p ∈ S, p ∣ n} = k * (M - ∏ (p - 1))`,
* `SieveGeneral.density_sieved`       : the density of the sieved set is `1 - ∏_{p ∈ S} (1 - 1/p)`.

For `S = {2, 3}` this reads `1 - (1/2)(2/3) = 2/3`, recovering `Sieve23.card_sieved_range`.
-/

namespace SieveGeneral

open Finset

variable {S : Finset ℕ}

/-- The modulus of the sieve: the product of the sieving primes. -/
def modulus (S : Finset ℕ) : ℕ := ∏ p ∈ S, p

/-- `n` is killed by the sieve if one of the sieving primes divides it. -/
def Sieved (S : Finset ℕ) (n : ℕ) : Prop := ∃ p ∈ S, p ∣ n

instance (S : Finset ℕ) (n : ℕ) : Decidable (Sieved S n) := by
  unfold Sieved; infer_instance

/-- **A periodic predicate is counted blockwise.**  If membership depends only on the residue
mod `m`, then the count over `range (m * k)` is `k` times the count over one period. -/
theorem card_filter_range_of_periodic {m : ℕ} (f : ℕ → Prop) [DecidablePred f]
    (hper : ∀ n, f n ↔ f (n % m)) (k : ℕ) :
    ((range (m * k)).filter f).card = k * ((range m).filter f).card := by
  induction k with
  | zero => simp
  | succ j ih =>
      have hrange : range (m * (j + 1)) = range (m * j) ∪ Ico (m * j) (m * j + m) := by
        have h : m * (j + 1) = m * j + m := by ring
        rw [h, range_eq_Ico, Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (by omega)]
      have hdisj : Disjoint ((range (m * j)).filter f) ((Ico (m * j) (m * j + m)).filter f) := by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp only [mem_filter, mem_range, mem_Ico] at hx hx'
        omega
      have hblock : ((Ico (m * j) (m * j + m)).filter f).card = ((range m).filter f).card := by
        have himg : Ico (m * j) (m * j + m) = (range m).image (fun r => m * j + r) := by
          ext x
          simp only [mem_Ico, mem_image, mem_range]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨x - m * j, by omega, by omega⟩
          · rintro ⟨r, hr, rfl⟩; omega
        rw [himg, Finset.filter_image, Finset.card_image_of_injective _ (add_right_injective (m * j))]
        congr 1
        refine Finset.filter_congr ?_
        intro r hr
        simp only [mem_range] at hr
        have hmod : (m * j + r) % m = r := by
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
        rw [hper (m * j + r), hper r, hmod, Nat.mod_eq_of_lt hr]
      rw [hrange, Finset.filter_union, Finset.card_union_of_disjoint hdisj, ih, hblock]
      ring

/-- Each sieving prime divides the modulus. -/
theorem dvd_modulus {p : ℕ} (hp : p ∈ S) : p ∣ modulus S :=
  Finset.dvd_prod_of_mem _ hp

/-- The sieve is periodic modulo `M = ∏ p`. -/
theorem sieved_periodic (n : ℕ) : Sieved S n ↔ Sieved S (n % modulus S) := by
  constructor
  · rintro ⟨p, hp, hdvd⟩
    exact ⟨p, hp, (Nat.dvd_mod_iff (dvd_modulus hp)).mpr hdvd⟩
  · rintro ⟨p, hp, hdvd⟩
    exact ⟨p, hp, (Nat.dvd_mod_iff (dvd_modulus hp)).mp hdvd⟩

/-- Surviving the sieve is the same as being coprime to the modulus. -/
theorem not_sieved_iff_coprime (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    ¬ Sieved S n ↔ Nat.Coprime (modulus S) n := by
  constructor
  · intro h
    by_contra hcop
    obtain ⟨q, hq, hqM, hqn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    obtain ⟨p, hp, hqp⟩ := (Nat.Prime.prime hq).exists_mem_finset_dvd hqM
    have : q = p := (Nat.prime_dvd_prime_iff_eq hq (hS p hp)).mp hqp
    exact h ⟨p, hp, this ▸ hqn⟩
  · rintro hcop ⟨p, hp, hdvd⟩
    have hpM : p ∣ modulus S := dvd_modulus hp
    have : p ∣ Nat.gcd (modulus S) n := Nat.dvd_gcd hpM hdvd
    rw [hcop] at this
    exact Nat.Prime.one_lt (hS p hp) |>.ne' (Nat.dvd_one.mp this)

/-- In one period there are exactly `φ(M)` survivors. -/
theorem card_survivors_period (hS : ∀ p ∈ S, p.Prime) :
    ((range (modulus S)).filter (fun n => ¬ Sieved S n)).card = Nat.totient (modulus S) := by
  rw [Nat.totient]
  congr 1
  refine Finset.filter_congr ?_
  intro n _
  simpa using not_sieved_iff_coprime hS n

/-- The modulus is positive. -/
theorem modulus_pos (hS : ∀ p ∈ S, p.Prime) : 0 < modulus S :=
  Finset.prod_pos (fun p hp => (hS p hp).pos)

/-- `φ(M) = ∏ (p - 1)` for a product of distinct primes. -/
theorem totient_modulus (hS : ∀ p ∈ S, p.Prime) :
    Nat.totient (modulus S) = ∏ p ∈ S, (p - 1) := by
  classical
  induction S using Finset.induction with
  | empty => simp [modulus]
  | insert q T hq ih =>
      have hqp : q.Prime := hS q (Finset.mem_insert_self q T)
      have hT : ∀ p ∈ T, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
      have hcop : Nat.Coprime q (modulus T) := by
        refine Nat.Coprime.prod_right ?_
        intro p hp
        exact (Nat.coprime_primes hqp (hT p hp)).mpr (by rintro rfl; exact hq hp)
      rw [modulus, Finset.prod_insert hq, ← modulus, Nat.totient_mul hcop,
        Nat.totient_prime hqp, ih hT, Finset.prod_insert hq]

/-- **The survivors of a finite sieve, counted exactly.**  Among the first `M * k` naturals,
exactly `k * ∏ (p - 1)` avoid all the primes of `S`. -/
theorem card_survivors_range (hS : ∀ p ∈ S, p.Prime) (k : ℕ) :
    ((range (modulus S * k)).filter (fun n => ¬ Sieved S n)).card = k * ∏ p ∈ S, (p - 1) := by
  rw [card_filter_range_of_periodic (fun n => ¬ Sieved S n)
      (fun n => not_congr (sieved_periodic n)) k,
    card_survivors_period hS, totient_modulus hS]

/-- **The sieved set, counted exactly.**  Among the first `M * k` naturals, exactly
`k * (M - ∏ (p - 1))` are divisible by some prime of `S`. -/
theorem card_sieved_range (hS : ∀ p ∈ S, p.Prime) (k : ℕ) :
    ((range (modulus S * k)).filter (fun n => Sieved S n)).card
      = k * (modulus S - ∏ p ∈ S, (p - 1)) := by
  have hsplit : ((range (modulus S * k)).filter (fun n => Sieved S n)).card
      + ((range (modulus S * k)).filter (fun n => ¬ Sieved S n)).card = modulus S * k := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_range]
  have hsurv := card_survivors_range hS k
  have hle : ∏ p ∈ S, (p - 1) ≤ modulus S := by
    rw [modulus]
    exact Finset.prod_le_prod' (fun p _ => Nat.sub_le p 1)
  rw [hsurv] at hsplit
  have hcomm : modulus S * k = k * modulus S := Nat.mul_comm _ _
  rw [Nat.mul_sub]
  omega

/-- **Legendre density.**  The proportion of the first `M * k` naturals removed by sieving with
the primes of `S` is exactly `1 - ∏_{p ∈ S} (1 - 1/p)`. -/
theorem density_sieved (hS : ∀ p ∈ S, p.Prime) {k : ℕ} (hk : 0 < k) :
    (((range (modulus S * k)).filter (fun n => Sieved S n)).card : ℚ) / (modulus S * k)
      = 1 - ∏ p ∈ S, (1 - 1 / (p : ℚ)) := by
  have hM : 0 < modulus S := modulus_pos hS
  have hprod : ∏ p ∈ S, (1 - 1 / (p : ℚ)) = (∏ p ∈ S, ((p : ℚ) - 1)) / (modulus S : ℚ) := by
    rw [modulus, Nat.cast_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl ?_
    intro p hp
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hS p hp).pos.ne'
    field_simp
  have hcast : ((∏ p ∈ S, (p - 1) : ℕ) : ℚ) = ∏ p ∈ S, ((p : ℚ) - 1) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl ?_
    intro p hp
    have := (hS p hp).one_lt
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
    ring
  have hle : ∏ p ∈ S, (p - 1) ≤ modulus S := by
    rw [modulus]
    exact Finset.prod_le_prod' (fun p _ => Nat.sub_le p 1)
  rw [card_sieved_range hS k, hprod]
  have hMk : ((modulus S : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hk' : ((k : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  rw [Nat.cast_mul, Nat.cast_sub hle, hcast]
  field_simp

/-- **Specialisation to `S = {2, 3}`.**  The modulus is `6`, the survivor count in a period is
`φ(6) = 2`, and the sieved count over `range (6 * k)` is `4 * k` — this is
`Sieve23.card_sieved_range` again. -/
theorem two_three : modulus {2, 3} = 6 ∧ (∀ k : ℕ,
    ((range (6 * k)).filter (fun n => Sieved {2, 3} n)).card = 4 * k) := by
  have hmod : modulus ({2, 3} : Finset ℕ) = 6 := by decide
  refine ⟨hmod, fun k => ?_⟩
  have hS : ∀ p ∈ ({2, 3} : Finset ℕ), p.Prime := by decide
  have := card_sieved_range hS k
  rw [hmod] at this
  rw [this]
  norm_num [Nat.mul_comm]

end SieveGeneral

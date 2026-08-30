import Cuisine.UmamiTransport

/-!
# The kernel of the cuisine transport

`Cuisine.UmamiTransport` maps a cuisine umami intensity `u` to the hyperfabric
section `umamiFabric u`, and proves that cubes die (`umamiFabric_cube`).  The
frontier report recorded the missing statement: *which* intensities die, and
when two intensities have the same shadow.  This file closes that gap.

Proved here (all sorry-free):

* `umamiFabric_eq_iff` — two blends have the same shadow exactly when the
  fifteen supersingular exponents of their successors agree modulo three;
* `primePow_dvd_self` — the supersingular part `∏ p ^ vₚ(m)` divides `m`
  (the fifteen primes are distinct, which is where the work is);
* `umamiFabric_eq_zero_iff` — **the kernel, exactly**: `umamiFabric u` is the
  neutral section iff `u + 1 = c ³ · d` for some positive `c` and some positive
  `d` divisible by no supersingular prime.  So the transport is reduction of the
  cuisine monoid modulo cubes *and* modulo the primes outside the Monster base,
  and nothing else is forgotten;
* `umamiFabric_eq_zero_of_coprime`, `umamiFabric_cube_mul` — the two special
  cases, as corollaries.

Boundary: this is arithmetic about `Nat.factorization` at fifteen fixed primes.
No claim about food, the Monster group, or moonshine is made or used.
-/

namespace Cuisine.TransportKernel

open AgdaMirror.MonsterOntos (SSP)
open Synthesis.MonsterFibre
open Synthesis.Hyperfabric
open Cuisine.UmamiTransport

/-! ## Two blends with the same shadow -/

/-- **The congruence the transport induces.** -/
theorem umamiFabric_eq_iff (a b : ℕ) :
    umamiFabric a = umamiFabric b ↔ ∀ p : SSP, toneAt (a + 1) p = toneAt (b + 1) p := by
  constructor
  · intro h p
    have := congrArg fabricZMod h
    rw [fabricZMod_umamiFabric, fabricZMod_umamiFabric] at this
    exact congrFun this p
  · intro h
    apply fabricZMod.injective
    rw [fabricZMod_umamiFabric, fabricZMod_umamiFabric]
    funext p
    exact h p

theorem umamiFabric_eq_zero_iff_tone (u : ℕ) :
    umamiFabric u = fabricZero ↔ ∀ p : SSP, toneAt (u + 1) p = 0 := by
  constructor
  · intro h p
    have := congrArg fabricZMod h
    rw [fabricZMod_umamiFabric, fabricZMod_zero] at this
    exact congrFun this p
  · intro h
    apply fabricZMod.injective
    rw [fabricZMod_umamiFabric, fabricZMod_zero]
    funext p
    exact h p

/-! ## The supersingular part of a natural number -/

/-- Raising an exponent vector to a power multiplies the exponents. -/
theorem primePow_pow (e : SSP → ℕ) (k : ℕ) :
    primePow e ^ k = primePow (fun p => k * e p) := by
  simp only [primePow, ← Finset.prod_pow, ← pow_mul, Nat.mul_comm]

/-- The exponent vector contributes nothing at a prime outside the Monster
base. -/
theorem factorization_primePow_of_ne (e : SSP → ℕ) {r : ℕ}
    (hr : ∀ p : SSP, prime p ≠ r) : (primePow e).factorization r = 0 := by
  have hne : ∀ p ∈ (Finset.univ : Finset SSP), prime p ^ e p ≠ 0 := by
    intro p _; exact pow_ne_zero _ (prime_ne_zero p)
  rw [primePow, Nat.factorization_prod hne, Finset.sum_apply']
  refine Finset.sum_eq_zero ?_
  intro p _
  rw [Nat.Prime.factorization_pow (toNat_prime p), Finsupp.single_apply]
  simp [hr p]

/-- The *supersingular part* of `m`: the product of the fifteen base primes to
their exact multiplicities in `m`. -/
noncomputable def sspPart (m : ℕ) : ℕ := primePow (fun p => m.factorization (prime p))

theorem sspPart_pos (m : ℕ) : 0 < sspPart m := primePow_pos _

theorem factorization_sspPart (m : ℕ) (q : SSP) :
    (sspPart m).factorization (prime q) = m.factorization (prime q) :=
  factorization_primePow _ q

/-- **The supersingular part divides.**  This uses that the fifteen primes are
distinct, through `factorization_primePow`. -/
theorem primePow_dvd_self {m : ℕ} (hm : m ≠ 0) : sspPart m ∣ m := by
  classical
  rw [← Nat.factorization_le_iff_dvd (sspPart_pos m).ne' hm]
  intro r
  by_cases hr : ∃ p : SSP, prime p = r
  · obtain ⟨p, rfl⟩ := hr
    simp [factorization_sspPart]
  · push_neg at hr
    simp [sspPart, factorization_primePow_of_ne _ hr]

/-- The complementary factor: `m` with all supersingular primes removed. -/
noncomputable def coprimePart (m : ℕ) : ℕ := m / sspPart m

theorem sspPart_mul_coprimePart {m : ℕ} (hm : m ≠ 0) :
    sspPart m * coprimePart m = m :=
  Nat.mul_div_cancel' (primePow_dvd_self hm)

theorem coprimePart_pos {m : ℕ} (hm : m ≠ 0) : 0 < coprimePart m := by
  rcases Nat.eq_zero_or_pos (coprimePart m) with h | h
  · exfalso
    have := sspPart_mul_coprimePart hm
    rw [h, Nat.mul_zero] at this
    exact hm this.symm
  · exact h

/-- No supersingular prime survives in the complementary factor. -/
theorem not_dvd_coprimePart {m : ℕ} (hm : m ≠ 0) (p : SSP) :
    ¬ (prime p ∣ coprimePart m) := by
  intro hdvd
  have hc : coprimePart m ≠ 0 := (coprimePart_pos hm).ne'
  have hs : sspPart m ≠ 0 := (sspPart_pos m).ne'
  have hfac : m.factorization (prime p)
      = (sspPart m).factorization (prime p) + (coprimePart m).factorization (prime p) := by
    conv_lhs => rw [← sspPart_mul_coprimePart hm]
    rw [Nat.factorization_mul hs hc]
    rfl
  rw [factorization_sspPart] at hfac
  have hpos : 0 < (coprimePart m).factorization (prime p) :=
    (toNat_prime p).factorization_pos_of_dvd hc hdvd
  omega

/-! ## The kernel -/

/-- **The kernel of the cuisine transport, exactly.**  A blend has neutral
hyperfabric shadow precisely when its successor is a cube times a factor carrying
no supersingular prime. -/
theorem umamiFabric_eq_zero_iff (u : ℕ) :
    umamiFabric u = fabricZero ↔
      ∃ c d : ℕ, 0 < c ∧ 0 < d ∧ u + 1 = c ^ 3 * d ∧ ∀ p : SSP, ¬ (prime p ∣ d) := by
  have hm : u + 1 ≠ 0 := Nat.succ_ne_zero u
  rw [umamiFabric_eq_zero_iff_tone]
  constructor
  · intro h
    -- every supersingular exponent is a multiple of three
    have hdvd3 : ∀ p : SSP, 3 ∣ (u + 1).factorization (prime p) := by
      intro p
      have := h p
      rw [toneAt] at this
      exact (ZMod.natCast_eq_zero_iff _ 3).1 this
    refine ⟨primePow (fun p => (u + 1).factorization (prime p) / 3), coprimePart (u + 1),
      primePow_pos _, coprimePart_pos hm, ?_, not_dvd_coprimePart hm⟩
    have hcube : (primePow (fun p => (u + 1).factorization (prime p) / 3)) ^ 3
        = sspPart (u + 1) := by
      rw [primePow_pow]
      unfold sspPart
      congr 1
      funext p
      exact Nat.mul_div_cancel' (hdvd3 p)
    rw [hcube, sspPart_mul_coprimePart hm]
  · rintro ⟨c, d, hc, hd, hud, hpd⟩ p
    have hc0 : c ^ 3 ≠ 0 := pow_ne_zero _ hc.ne'
    have hd0 : d ≠ 0 := hd.ne'
    have : toneAt (u + 1) p = toneAt (c ^ 3) p + toneAt d p := by
      rw [hud]; exact toneAt_mul hc0 hd0 p
    have hzero_d : toneAt d p = 0 := by
      simp [toneAt, Nat.factorization_eq_zero_of_not_dvd (hpd p)]
    have hzero_c : toneAt (c ^ 3) p = 0 := by
      rw [toneAt_pow, show ((3 : ℕ) : ZMod 3) = 0 by decide, zero_mul]
    rw [this, hzero_c, hzero_d, add_zero]

/-- Corollary: a blend whose successor meets no supersingular prime is
invisible to the transport. -/
theorem umamiFabric_eq_zero_of_coprime {u : ℕ} (h : ∀ p : SSP, ¬ (prime p ∣ (u + 1))) :
    umamiFabric u = fabricZero :=
  (umamiFabric_eq_zero_iff u).2 ⟨1, u + 1, Nat.one_pos, Nat.succ_pos u, by ring, h⟩

/-- Corollary: cube successors are invisible too — the special case
`Cuisine.UmamiTransport.umamiFabric_cube` isolates. -/
theorem umamiFabric_cube_mul {u c : ℕ} (hc : 0 < c) (h : u + 1 = c ^ 3) :
    umamiFabric u = fabricZero :=
  (umamiFabric_eq_zero_iff u).2
    ⟨c, 1, hc, Nat.one_pos, by rw [h, Nat.mul_one], fun p hp => by
      have hle : prime p ≤ 1 := Nat.le_of_dvd Nat.one_pos hp
      have h2 : 2 ≤ prime p := (toNat_prime p).two_le
      omega⟩

end Cuisine.TransportKernel

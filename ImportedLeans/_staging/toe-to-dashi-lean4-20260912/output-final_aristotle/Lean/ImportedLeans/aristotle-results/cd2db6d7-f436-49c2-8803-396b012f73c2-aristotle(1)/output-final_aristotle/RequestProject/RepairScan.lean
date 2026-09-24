import RequestProject.BigFieldSizeScan
import RequestProject.MultiplicativeRepairIff
import RequestProject.UniversalTraceRepair

/-!
# Repairing every error of the scan

`RequestProject/BigFieldSizeScan.lean` scans the candidate field sizes `q = 2 … 1824` and
finds `18` field sizes whose Frobenius orbit product `N(x) = x^(1+p+⋯+p^(k−1))` is **not** a
retraction onto the prime subfield (`bigScan_failing_sizes`).  This file says, for each of
them, exactly which repairs exist.  The two general theorems are

* `FrobeniusPrimeSubfield.exists_additive_retraction` — the twisted orbit sum
  `x ↦ Tr(c·x)` with `Tr(c) = 1` is an additive retraction onto `𝔽ₚ`, for **every** finite
  field.  So *every* one of the 18 errors is repairable additively.
* `FrobeniusPrimeSubfield.multiplicative_retraction_iff_coprime` — a *multiplicative*
  retraction onto `𝔽ₚ` exists **iff** `gcd (k, p − 1) = 1`, and then `x ↦ N(x)^t` with
  `t = k^(φ(p−1)−1)` is one.

Applying the criteria to the failing sizes (`repairTable_eq`):

* `multiplicatively_repairable_sizes` : only `q = 125 = 5³` and `q = 1331 = 11³` admit a
  multiplicative repair, by the power maps `x ↦ x^93` and `x ↦ x^931` respectively
  (`repair_exponents`); for the other `16` sizes the obstruction of
  `no_multiplicative_retraction_of_not_coprime` applies.
* `scaling_repair_fails_sizes` : the normalized orbit sum `x ↦ k⁻¹ Tr(x)` repairs `17` of the
  `18`; the exception is `q = 729 = 3⁶`, where `p ∣ k` makes the orbit sum vanish identically
  on `𝔽ₚ`, so no rescaling can help (`no_scalar_repair_of_dvd`) — and there the twist
  `x ↦ Tr(c·x)` is needed.

Read over the whole scan rather than only its failures (`fullVerdict_counts`,
`fullVerdict_irreparable`): of the `310` field sizes `q ≤ 1824`, `294` admit a multiplicative
retraction onto their prime subfield and `16` do not — and all `310` admit an additive one.

The instantiations at the end are the corresponding statements about Mathlib's own fields
`GaloisField p k`, and `all_errors_additively_repairable` is the statement that no error is
beyond repair: every finite field of every prime-power order admits an additive retraction
onto its prime subfield built from the Frobenius orbit sum.
-/

set_option maxRecDepth 40000

namespace RepairScan

open Finset

/-! ## The two criteria, as computations -/

/-- The exponent of the Frobenius orbit product: `N(x) = x^(orbitExp p k)`. -/
def orbitExp (p k : ℕ) : ℕ := ∑ i ∈ range k, p ^ i

/-- The correcting power `t` with `k·t ≡ 1 (mod p − 1)`, namely `t = k^(φ(p−1)−1)`. -/
def correctingPow (p k : ℕ) : ℕ := k ^ (Nat.totient (p - 1) - 1)

/-- The repaired multiplicative exponent `m = s·t`, reduced modulo `p^k − 1` (which does not
change the map `x ↦ x^m` on `K`, and gives the smallest exponent doing the job). -/
def repairExp (p k : ℕ) : ℕ := (orbitExp p k * correctingPow p k) % (p ^ k - 1)

/-- A multiplicative repair exists exactly when `gcd (k, p − 1) = 1`. -/
def multRepairable (p k : ℕ) : Bool := Nat.gcd k (p - 1) == 1

/-- The *scaling* repair `x ↦ k⁻¹ Tr(x)` of the additive error works exactly when `p ∤ k`;
otherwise the general twist `x ↦ Tr(c·x)` is needed. -/
def scalingRepairWorks (p k : ℕ) : Bool := ¬ (p ∣ k)

/-! ## The repair table for the 18 failing sizes -/

/-- The failing sizes of the big scan, as `(q, p, k, error)`. -/
def failing : List (ℕ × ℕ × ℕ × ℕ) :=
  BigFieldSizeScan.bigScan.filterMap fun r =>
    match r.2 with
    | some (p, k, d) => if d ≠ 0 then some (r.1, p, k, d) else none
    | none => none

/-- For every failing size: the size `q = p^k`, its error, whether the scaling repair of the
additive error works, whether a multiplicative repair exists at all, and — when it does — the
repairing exponent `m`. -/
def repairTable : List (ℕ × ℕ × ℕ × ℕ × Bool × Bool × ℕ) :=
  failing.map fun (q, p, k, d) =>
    (q, p, k, d, scalingRepairWorks p k, multRepairable p k,
      if multRepairable p k then repairExp p k else 0)

/-- The complete repair table of the scan. -/
theorem repairTable_eq :
    repairTable =
      [(9, 3, 2, 1, true, false, 0), (25, 5, 2, 3, true, false, 0),
       (49, 7, 2, 5, true, false, 0), (81, 3, 4, 1, true, false, 0),
       (121, 11, 2, 9, true, false, 0), (125, 5, 3, 2, true, true, 93),
       (169, 13, 2, 11, true, false, 0), (289, 17, 2, 15, true, false, 0),
       (343, 7, 3, 4, true, false, 0), (361, 19, 2, 17, true, false, 0),
       (529, 23, 2, 21, true, false, 0), (625, 5, 4, 3, true, false, 0),
       (729, 3, 6, 1, false, false, 0), (841, 29, 2, 27, true, false, 0),
       (961, 31, 2, 29, true, false, 0), (1331, 11, 3, 8, true, true, 931),
       (1369, 37, 2, 35, true, false, 0), (1681, 41, 2, 39, true, false, 0)] := by
  rfl

/-- **Only two of the eighteen errors can be repaired multiplicatively**: `q = 125 = 5³` and
`q = 1331 = 11³`, the two failing sizes with `gcd (k, p − 1) = 1`. -/
theorem multiplicatively_repairable_sizes :
    (repairTable.filterMap fun r => if r.2.2.2.2.2.1 then some r.1 else none) = [125, 1331] := by
  decide +kernel

/-- The repairing exponents: over `GF(125)` the map `x ↦ x^93 = N(x)^3` and over `GF(1331)`
the map `x ↦ x^931 = N(x)^7` is a multiplicative retraction onto the prime subfield.  Both
exponents satisfy the two defining congruences — divisible by the orbit exponent `s`, and
`≡ 1 (mod p − 1)`. -/
theorem repair_exponents :
    repairExp 5 3 = 93 ∧ repairExp 11 3 = 931 ∧
      orbitExp 5 3 ∣ 93 ∧ 93 % 4 = 1 ∧ orbitExp 11 3 ∣ 931 ∧ 931 % 10 = 1 ∧
      93 = orbitExp 5 3 * 3 ∧ 931 = orbitExp 11 3 * 7 := by
  decide +kernel

/-- **The scaling repair of the additive error works for all but one failing size.**  The
exception is `q = 729 = 3⁶`, where `p ∣ k`. -/
theorem scaling_repair_fails_sizes :
    (repairTable.filterMap fun r => if r.2.2.2.2.1 then none else some r.1) = [729] := by
  decide +kernel

/-- Counted: of the 18 errors, all 18 are repairable additively (17 already by rescaling, the
last one by twisting), and 2 are repairable multiplicatively. -/
theorem repair_counts :
    repairTable.length = 18 ∧
      (repairTable.filter fun r => r.2.2.2.2.1).length = 17 ∧
      (repairTable.filter fun r => r.2.2.2.2.2.1).length = 2 := by
  decide +kernel

/-! ## The whole scan, re-read through the sharp criterion -/

/-- Every field size in the scan, with the verdict "a multiplicative retraction onto `𝔽ₚ`
exists", i.e. `gcd (k, p − 1) = 1`. -/
def fullVerdict : List (ℕ × Bool) :=
  BigFieldSizeScan.bigScan.filterMap fun r =>
    match r.2 with
    | some (p, k, _) => some (r.1, Nat.gcd k (p - 1) == 1)
    | none => none

/-- Of the `310` field sizes `q ≤ 1824`, `294` admit a multiplicative retraction onto their
prime subfield and `16` do not — the `292` whose orbit product already retracts, plus exactly
`125` and `1331`.  So the sharp criterion corrects the verdict at two of the eighteen errors
and confirms it at the other sixteen. -/
theorem fullVerdict_counts :
    fullVerdict.length = 310 ∧
      (fullVerdict.filter fun r => r.2).length = 294 ∧
      (fullVerdict.filter fun r => ¬ r.2).length = 16 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The field sizes with **no** multiplicative retraction onto the prime subfield: the sixteen
errors of the scan that stay broken multiplicatively. -/
theorem fullVerdict_irreparable :
    (fullVerdict.filterMap fun r => if r.2 then none else some r.1) =
      [9, 25, 49, 81, 121, 169, 289, 343, 361, 529, 625, 729, 841, 961, 1369, 1681] := by
  decide +kernel

end RepairScan

/-! ## The repairs on Mathlib's fields `GaloisField p k` -/

namespace GaloisFieldRepair

open FrobeniusPrimeSubfield

noncomputable local instance instFintypeGaloisField (p k : ℕ) [Fact p.Prime] :
    Fintype (GaloisField p k) := Fintype.ofFinite _

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- **No error is beyond repair.**  For every prime `p` and every `k ≠ 0` the field with `p^k`
elements carries an additive retraction onto its prime subfield `𝔽ₚ`, of the shape
`x ↦ Tr(c·x)` for a scalar `c` with `Tr(c) = 1`, where `Tr` is the Frobenius orbit sum.  No
hypothesis relating `p` and `k` is needed: this repairs all 18 errors of the scan, and every
error there will ever be. -/
theorem all_errors_additively_repairable (p k : ℕ) [Fact p.Prime] (hk : k ≠ 0) :
    ∃ c : GaloisField p k, frobTrace p k c = 1 ∧
      (∀ x y : GaloisField p k, twistedTrace p k c (x + y)
          = twistedTrace p k c x + twistedTrace p k c y) ∧
      (∀ a x : GaloisField p k, a ^ p = a →
        twistedTrace p k c (a * x) = a * twistedTrace p k c x) ∧
      (∀ x : GaloisField p k,
        twistedTrace p k c x ∈ Set.range (primeSubfieldHom (GaloisField p k) p)) ∧
      (∀ a ∈ Set.range (primeSubfieldHom (GaloisField p k) p), twistedTrace p k c a = a) ∧
      (∀ a ∈ Set.range (primeSubfieldHom (GaloisField p k) p),
        ∃ x : GaloisField p k, twistedTrace p k c x = a) :=
  exists_additive_retraction (GaloisField.card p k hk) hk

/-- **`GF(125)`: the multiplicative error is repairable.**  Since `gcd (3, 4) = 1`, some power
map `x ↦ x^m` is a multiplicative retraction of `GF(125)` onto `𝔽₅`; concretely `m = 93`, the
cube of the orbit product. -/
theorem gf125_multiplicative_repair :
    ∃ m : ℕ, 0 < m ∧
      (∀ x y : GaloisField 5 3, (x * y) ^ m = x ^ m * y ^ m) ∧
      (∀ x : GaloisField 5 3, (x ^ m) ^ 5 = x ^ m) ∧
      (∀ a : GaloisField 5 3, a ^ 5 = a → a ^ m = a) ∧
      (∀ x : GaloisField 5 3, x ^ m = (frobNorm 5 3 x) ^ (3 ^ (Nat.totient 4 - 1))) :=
  exists_pow_multiplicative_retraction (GaloisField.card 5 3 (by norm_num)) (by norm_num)
    (by norm_num)

/-- **`GF(1331)`: the multiplicative error is repairable** as well, `gcd (3, 10) = 1`. -/
theorem gf1331_multiplicative_repair :
    ∃ m : ℕ, 0 < m ∧
      (∀ x y : GaloisField 11 3, (x * y) ^ m = x ^ m * y ^ m) ∧
      (∀ x : GaloisField 11 3, (x ^ m) ^ 11 = x ^ m) ∧
      (∀ a : GaloisField 11 3, a ^ 11 = a → a ^ m = a) ∧
      (∀ x : GaloisField 11 3, x ^ m = (frobNorm 11 3 x) ^ (3 ^ (Nat.totient 10 - 1))) :=
  exists_pow_multiplicative_retraction (GaloisField.card 11 3 (by norm_num)) (by norm_num)
    (by norm_num)

/-- **`GF(343)`: the multiplicative error is *not* repairable.**  Here `p = 7`, `k = 3` and
`gcd (3, 6) = 3 ≠ 1`, so every multiplicative map into `𝔽₇` moves a point of `𝔽₇` — the
first failing size where the obstruction is not the classical square obstruction but a cube
one. -/
theorem gf343_no_multiplicative_repair
    {f : GaloisField 7 3 → GaloisField 7 3} (hmul : ∀ x y, f (x * y) = f x * f y)
    (hfix : ∀ x, (f x) ^ 7 = f x) :
    ∃ a : GaloisField 7 3, a ^ 7 = a ∧ f a ≠ a :=
  no_multiplicative_retraction_of_not_coprime (GaloisField.card 7 3 (by norm_num))
    (by norm_num) hmul hfix

/-- **`GF(729)`: the additive error cannot be repaired by rescaling.**  Here `p = 3` divides
`k = 6`, so the Frobenius orbit sum vanishes identically on `𝔽₃` and no multiple `c·Tr` fixes
`1`.  The twisted orbit sum `x ↦ Tr(c·x)` of `all_errors_additively_repairable` still repairs
it. -/
theorem gf729_no_scalar_repair (c : GaloisField 3 6) :
    c * frobTrace 3 6 (1 : GaloisField 3 6) ≠ 1 :=
  no_scalar_repair_of_dvd (by norm_num) c



/-- **The complete verdict, for every finite field.**  For every prime `p` and every `k ≠ 0`:

* the additive error is *always* repairable — the twisted orbit sum `x ↦ Tr(c·x)` with
  `Tr(c) = 1` is an additive retraction of `GF(p^k)` onto `𝔽ₚ`;
* the multiplicative error is repairable **exactly** when `gcd (k, p−1) = 1`.

Applied to the 18 failing sizes of the scan this is `RepairScan.repairTable_eq`: all 18
additive errors are corrected, and exactly the two sizes `125` and `1331` also admit a
multiplicative correction. -/
theorem repair_verdict (p k : ℕ) [Fact p.Prime] (hk : k ≠ 0) :
    (∃ c : GaloisField p k, frobTrace p k c = 1 ∧
      (∀ x y : GaloisField p k, twistedTrace p k c (x + y)
          = twistedTrace p k c x + twistedTrace p k c y) ∧
      (∀ a x : GaloisField p k, a ^ p = a →
        twistedTrace p k c (a * x) = a * twistedTrace p k c x) ∧
      (∀ x : GaloisField p k,
        twistedTrace p k c x ∈ Set.range (primeSubfieldHom (GaloisField p k) p)) ∧
      (∀ a ∈ Set.range (primeSubfieldHom (GaloisField p k) p), twistedTrace p k c a = a) ∧
      (∀ a ∈ Set.range (primeSubfieldHom (GaloisField p k) p),
        ∃ x : GaloisField p k, twistedTrace p k c x = a)) ∧
    ((∃ f : GaloisField p k → GaloisField p k, (∀ x y, f (x * y) = f x * f y) ∧
        (∀ x, (f x) ^ p = f x) ∧ (∀ a : GaloisField p k, a ^ p = a → f a = a))
      ↔ Nat.gcd k (p - 1) = 1) :=
  ⟨all_errors_additively_repairable p k hk,
    multiplicative_retraction_iff_coprime (GaloisField.card p k hk) hk⟩

end GaloisFieldRepair

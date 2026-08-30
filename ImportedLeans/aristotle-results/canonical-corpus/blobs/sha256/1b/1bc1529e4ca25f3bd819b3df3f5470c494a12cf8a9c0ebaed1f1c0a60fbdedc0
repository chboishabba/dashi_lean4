import Mathlib

/-!
# The 26 sporadic groups, listed smallest to largest

This file is the catalogue the last stage of the construction is indexed by.  It does *not*
construct the sporadic simple groups — that is far out of reach of any current formal library, and
nothing here pretends otherwise.  What it fixes is their *arithmetic*: a 26-element index type
`Sporadic`, its list `Sporadic.all` in increasing order of group order, the order of each group,
and the prime factorisation of each order.  Every statement in this file is checked by the kernel
by `decide`, so the table is machine-verified against itself: each listed order really is the
product of the listed prime powers, the primes really are prime, and the 26 orders really are
distinct and increasing.

The groups are modelled — placed on a floor of the `GF` extension tower — in
`RequestProject/SporadicTower.lean`.  There the statements quantify over *any* finite group whose
order is one of these numbers, which is the honest way to speak about a group one has not built.
-/

namespace Sporadic

/-- An index for the 26 sporadic simple groups. -/
inductive Group where
  /-- Mathieu group `M₁₁`. -/            | M11
  /-- Mathieu group `M₁₂`. -/            | M12
  /-- Janko group `J₁`. -/               | J1
  /-- Mathieu group `M₂₂`. -/            | M22
  /-- Janko group `J₂` (Hall–Janko). -/  | J2
  /-- Mathieu group `M₂₃`. -/            | M23
  /-- Higman–Sims group `HS`. -/         | HS
  /-- Janko group `J₃`. -/               | J3
  /-- Mathieu group `M₂₄`. -/            | M24
  /-- McLaughlin group `McL`. -/         | McL
  /-- Held group `He`. -/                | He
  /-- Rudvalis group `Ru`. -/            | Ru
  /-- Suzuki group `Suz`. -/             | Suz
  /-- O'Nan group `O'N`. -/              | ON
  /-- Conway group `Co₃`. -/             | Co3
  /-- Conway group `Co₂`. -/             | Co2
  /-- Fischer group `Fi₂₂`. -/           | Fi22
  /-- Harada–Norton group `HN`. -/       | HN
  /-- Lyons group `Ly`. -/               | Ly
  /-- Thompson group `Th`. -/            | Th
  /-- Fischer group `Fi₂₃`. -/           | Fi23
  /-- Conway group `Co₁`. -/             | Co1
  /-- Janko group `J₄`. -/               | J4
  /-- Fischer group `Fi₂₄'`. -/          | Fi24prime
  /-- Baby monster `B`. -/               | B
  /-- Fischer–Griess monster `M`. -/     | M
  deriving DecidableEq, Repr

namespace Group

/-- The usual name of each group. -/
def name : Group → String
  | M11 => "M11" | M12 => "M12" | J1 => "J1" | M22 => "M22" | J2 => "J2" | M23 => "M23"
  | HS => "HS" | J3 => "J3" | M24 => "M24" | McL => "McL" | He => "He" | Ru => "Ru"
  | Suz => "Suz" | ON => "O'N" | Co3 => "Co3" | Co2 => "Co2" | Fi22 => "Fi22" | HN => "HN"
  | Ly => "Ly" | Th => "Th" | Fi23 => "Fi23" | Co1 => "Co1" | J4 => "J4"
  | Fi24prime => "Fi24'" | B => "B" | M => "M"

/-- The order of each sporadic simple group. -/
def order : Group → Nat
  | M11 => 7920
  | M12 => 95040
  | J1 => 175560
  | M22 => 443520
  | J2 => 604800
  | M23 => 10200960
  | HS => 44352000
  | J3 => 50232960
  | M24 => 244823040
  | McL => 898128000
  | He => 4030387200
  | Ru => 145926144000
  | Suz => 448345497600
  | ON => 460815505920
  | Co3 => 495766656000
  | Co2 => 42305421312000
  | Fi22 => 64561751654400
  | HN => 273030912000000
  | Ly => 51765179004000000
  | Th => 90745943887872000
  | Fi23 => 4089470473293004800
  | Co1 => 4157776806543360000
  | J4 => 86775571046077562880
  | Fi24prime => 1255205709190661721292800
  | B => 4154781481226426191177580544000000
  | M => 808017424794512875886459904961710757005754368000000000

/-- The prime factorisation of each order, as a list of `(prime, exponent)` pairs. -/
def factorization : Group → List (Nat × Nat)
  | M11 => [(2, 4), (3, 2), (5, 1), (11, 1)]
  | M12 => [(2, 6), (3, 3), (5, 1), (11, 1)]
  | J1 => [(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (19, 1)]
  | M22 => [(2, 7), (3, 2), (5, 1), (7, 1), (11, 1)]
  | J2 => [(2, 7), (3, 3), (5, 2), (7, 1)]
  | M23 => [(2, 7), (3, 2), (5, 1), (7, 1), (11, 1), (23, 1)]
  | HS => [(2, 9), (3, 2), (5, 3), (7, 1), (11, 1)]
  | J3 => [(2, 7), (3, 5), (5, 1), (17, 1), (19, 1)]
  | M24 => [(2, 10), (3, 3), (5, 1), (7, 1), (11, 1), (23, 1)]
  | McL => [(2, 7), (3, 6), (5, 3), (7, 1), (11, 1)]
  | He => [(2, 10), (3, 3), (5, 2), (7, 3), (17, 1)]
  | Ru => [(2, 14), (3, 3), (5, 3), (7, 1), (13, 1), (29, 1)]
  | Suz => [(2, 13), (3, 7), (5, 2), (7, 1), (11, 1), (13, 1)]
  | ON => [(2, 9), (3, 4), (5, 1), (7, 3), (11, 1), (19, 1), (31, 1)]
  | Co3 => [(2, 10), (3, 7), (5, 3), (7, 1), (11, 1), (23, 1)]
  | Co2 => [(2, 18), (3, 6), (5, 3), (7, 1), (11, 1), (23, 1)]
  | Fi22 => [(2, 17), (3, 9), (5, 2), (7, 1), (11, 1), (13, 1)]
  | HN => [(2, 14), (3, 6), (5, 6), (7, 1), (11, 1), (19, 1)]
  | Ly => [(2, 8), (3, 7), (5, 6), (7, 1), (11, 1), (31, 1), (37, 1), (67, 1)]
  | Th => [(2, 15), (3, 10), (5, 3), (7, 2), (13, 1), (19, 1), (31, 1)]
  | Fi23 => [(2, 18), (3, 13), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (23, 1)]
  | Co1 => [(2, 21), (3, 9), (5, 4), (7, 2), (11, 1), (13, 1), (23, 1)]
  | J4 => [(2, 21), (3, 3), (5, 1), (7, 1), (11, 3), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1)]
  | Fi24prime =>
      [(2, 21), (3, 16), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (23, 1), (29, 1)]
  | B => [(2, 41), (3, 13), (5, 6), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1),
      (47, 1)]
  | M => [(2, 46), (3, 20), (5, 9), (7, 6), (11, 2), (13, 3), (17, 1), (19, 1), (23, 1), (29, 1),
      (31, 1), (41, 1), (47, 1), (59, 1), (71, 1)]

/-- The primes dividing the order of a sporadic group. -/
def primes (S : Group) : List Nat := (factorization S).map Prod.fst

/-- The 26 sporadic groups, listed in increasing order of group order. -/
def all : List Group :=
  [M11, M12, J1, M22, J2, M23, HS, J3, M24, McL, He, Ru, Suz, ON, Co3, Co2, Fi22, HN, Ly, Th,
    Fi23, Co1, J4, Fi24prime, B, M]

/-- There are 26 sporadic groups. -/
theorem all_length : all.length = 26 := by decide

/-- The list has no repetitions. -/
theorem all_nodup : all.Nodup := by decide

/-- Every sporadic group occurs in the list. -/
theorem mem_all (S : Group) : S ∈ all := by cases S <;> decide

/-- The list really is ordered smallest to largest, so in particular the 26 orders are
pairwise distinct. -/
theorem orders_strictMono : List.IsChain (· < ·) (all.map order) := by decide

/-- Each listed order is the product of its listed prime powers. -/
theorem order_eq_prod_factorization (S : Group) :
    ((factorization S).map (fun pe => pe.1 ^ pe.2)).prod = order S := by
  cases S <;> decide

/-- Every base occurring in the factorisation table is prime. -/
theorem prime_of_mem_primes (S : Group) : ∀ q ∈ primes S, Nat.Prime q := by
  cases S <;> decide

/-- Every exponent occurring in the factorisation table is positive. -/
theorem exponent_pos (S : Group) : ∀ pe ∈ factorization S, 0 < pe.2 := by
  cases S <;> decide

/-- The primes are listed in increasing order, so each order's factorisation is the standard
one. -/
theorem primes_sorted (S : Group) : List.IsChain (· < ·) (primes S) := by
  cases S <;> decide

theorem order_pos (S : Group) : 0 < order S := by cases S <;> decide

/-- Each prime of the table divides the order. -/
theorem prime_dvd_order (S : Group) : ∀ q ∈ primes S, q ∣ order S := by
  cases S <;> decide

/-- The primes dividing the order of the Monster are the fifteen supersingular primes. -/
theorem primes_monster :
    primes M = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71] := by decide

/-- The primes that occur anywhere in the atlas: the fifteen primes of the Monster together with
`37`, `43` and `67`, which occur only in `Ly` and `J₄`. -/
def allPrimes : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 59, 67, 71]

theorem primes_subset_allPrimes (S : Group) : ∀ q ∈ primes S, q ∈ allPrimes := by
  cases S <;> decide

theorem allPrimes_covered : ∀ q ∈ allPrimes, ∃ S ∈ all, q ∈ primes S := by decide

/-- The smallest sporadic group is `M₁₁`, of order `7920`; the largest is the Monster. -/
theorem order_smallest_largest :
    (∀ S : Group, order M11 ≤ order S) ∧ (∀ S : Group, order S ≤ order M) := by
  constructor <;> intro S <;> cases S <;> decide

end Group

end Sporadic

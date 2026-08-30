/-
# Adding the fibers of `5`, `7`, `11` and `13`

The previous step expanded the fiber of `2` to its forty-six exponents, the exponents carried
by the Monster,

```
|M| = 2^46 · 3^20 · 5^9 · 7^6 · 11^2 · 13^3 · 17 · 19 · 23 · 29 · 31 · 41 · 47 · 59 · 71 .
```

This file adds the next four primes `5, 7, 11, 13` (alongside the two already drawn, `2` and
`3`) and proves everything the expanded diagram asserts about them:

* the exponents `9, 6, 2, 3` really are the `5`-, `7`-, `11`- and `13`-adic valuations of
  `|M|`, and the corresponding fibers `{p^1, …, p^{v_p}}` have exactly that many points;
* over the twenty-six sporadic groups the largest exponents are `5^9`, `7^6`, `13^3` — all in
  the Monster — but the largest power of `11` is `11^3`, carried by the pariah `J4` and *not*
  by the Monster (`exponent_eleven_max_is_J4`);
* the six small primes cut out the divisor `2^46·3^20·5^9·7^6·11^2·13^3` of `|M|`
  (`smallPart`), whose cofactor `17·19·23·29·31·41·47·59·71` is squarefree; `smallPart` has
  `829 080` divisors, exactly `1/512` of the Monster's `424 488 960`;
* on the zeta side, the six local factors of the Monster's divisor sum sit below the six
  Euler factors of `ζ`, whose product is `715715/442368 = 1.61792`: the six primes
  `2, 3, 5, 7, 11, 13` alone already account for more than `98.3 %` of `ζ(2) = π²/6`
  (`smallEulerProduct_two`, `smallEulerProduct_two_le`, `smallEulerProduct_two_gt`), and the
  four new primes `5, 7, 11, 13` contribute the factor `715715/663552 = 1.07861`.
-/
import Mathlib
import RequestProject.MonsterZeta
import RequestProject.MonsterSpiral

open Finset PrimeFibers MonsterSpiral

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Sporadic

variable {s : ℝ}

/-! ## The six small primes and the small part of `|M|` -/

/-- The four primes added at this step. -/
def newPrimes : Finset ℕ := {5, 7, 11, 13}

/-- The six small primes of the Monster: the two already drawn, `2` and `3`, together with
the four new ones `5, 7, 11, 13`. -/
def smallPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13}

theorem newPrimes_subset_smallPrimes : newPrimes ⊆ smallPrimes := by decide

theorem smallPrimes_subset_monsterPrimes : smallPrimes ⊆ monsterPrimes := by decide

/-- The factored form of the small part of `|M|`. -/
def smallFactors : List (ℕ × ℕ) := [(2, 46), (3, 20), (5, 9), (7, 6), (11, 2), (13, 3)]

/-- The `{2,3,5,7,11,13}`-part of the order of the Monster. -/
def smallPart : ℕ := factProd smallFactors

theorem wf_smallFactors : WF smallFactors := by decide

theorem smallPart_ne_zero : smallPart ≠ 0 := factProd_ne_zero _ wf_smallFactors

theorem smallPart_eq_pows : smallPart = 2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 := by
  norm_num [smallPart, smallFactors, factProd]

theorem smallPart_value : smallPart = 14987824576087776416687179431936000000000 := by
  norm_num [smallPart_eq_pows]

/-! ## The exponents of `5`, `7`, `11`, `13` -/

theorem factorization_smallPart (p : ℕ) :
    smallPart.factorization p = ((smallFactors.filter fun pe => pe.1 = p).map Prod.snd).sum :=
  factorization_factProd _ wf_smallFactors p

/-- The Monster's exponent of `5` is `9`. -/
theorem monster_exponent_five : monster.exponent 5 = 9 := by decide

/-- The Monster's exponent of `7` is `6`. -/
theorem monster_exponent_seven : monster.exponent 7 = 6 := by decide

/-- The Monster's exponent of `11` is `2`. -/
theorem monster_exponent_eleven : monster.exponent 11 = 2 := by decide

/-- The Monster's exponent of `13` is `3`. -/
theorem monster_exponent_thirteen : monster.exponent 13 = 3 := by decide

/-- On the six small primes the exponents of `smallPart` are exactly the valuations of `|M|`:
`smallPart` is the `{2,3,5,7,11,13}`-part of the Monster's order. -/
theorem factorization_smallPart_eq_monster {p : ℕ} (hp : p ∈ smallPrimes) :
    smallPart.factorization p = monsterOrder.factorization p := by
  rw [factorization_smallPart, MonsterSpiral.monster_factorization_eq]
  fin_cases hp <;> decide

/-- Outside the six small primes `smallPart` is trivial. -/
theorem factorization_smallPart_eq_zero {p : ℕ} (hp : p ∉ smallPrimes) :
    smallPart.factorization p = 0 := by
  have h : p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7 ∧ p ≠ 11 ∧ p ≠ 13 := by
    simpa [smallPrimes, not_or] using hp
  obtain ⟨h2, h3, h5, h7, h11, h13⟩ := h
  simp [factorization_smallPart, smallFactors, Ne.symm h2, Ne.symm h3, Ne.symm h5, Ne.symm h7,
    Ne.symm h11, Ne.symm h13]

/-! ## The largest exponents over the twenty-six sporadic groups -/

/-- No sporadic group carries a higher power of `5` than the Monster's `5^9`. -/
theorem exponent_five_le_9 : ∀ G ∈ groups, G.exponent 5 ≤ 9 := by decide

/-- No sporadic group carries a higher power of `7` than the Monster's `7^6`. -/
theorem exponent_seven_le_6 : ∀ G ∈ groups, G.exponent 7 ≤ 6 := by decide

/-- No sporadic group carries a higher power of `11` than `11^3`. -/
theorem exponent_eleven_le_3 : ∀ G ∈ groups, G.exponent 11 ≤ 3 := by decide

/-- No sporadic group carries a higher power of `13` than the Monster's `13^3`. -/
theorem exponent_thirteen_le_3 : ∀ G ∈ groups, G.exponent 13 ≤ 3 := by decide

/-- **The prime `11` is the exception.** The unique sporadic group attaining the maximal
power `11^3` is the pariah `J4`; the Monster only carries `11^2`. -/
theorem exponent_eleven_max_is_J4 :
    (groups.filter fun G => G.exponent 11 = 3).map Group.name = ["J4"] := by decide

/-- The maxima at `5`, `7` and `13` are attained by the Monster alone. -/
theorem exponent_five_max_is_monster :
    (groups.filter fun G => G.exponent 5 = 9).map Group.name = ["M"] := by decide

theorem exponent_seven_max_is_monster :
    (groups.filter fun G => G.exponent 7 = 6).map Group.name = ["M"] := by decide

theorem exponent_thirteen_max_is_monster :
    (groups.filter fun G => G.exponent 13 = 3).map Group.name = ["M"] := by decide

/-- Every sporadic group is divisible by at least one of the six small primes; in fact all
twenty-six are divisible by `2`, `3` and `5`. -/
theorem two_three_five_dvd_all : ∀ G ∈ groups,
    0 < G.exponent 2 ∧ 0 < G.exponent 3 ∧ 0 < G.exponent 5 := by decide

/-! ## The four new fibers -/

/-- The fiber of `p` cut off at `p ^ e` is the set of the `e` powers `p^1, …, p^e`. -/
theorem primePowerFiber_pow {p : ℕ} (hp : 1 < p) (e : ℕ) :
    primePowerFiber p (p ^ e) = (Finset.Icc 1 e).image (fun k => p ^ k) := by
  rw [primePowerFiber_eq_image hp (pow_ne_zero _ (by omega)), Nat.log_pow hp]

theorem card_primePowerFiber_pow {p : ℕ} (hp : 1 < p) (e : ℕ) :
    (primePowerFiber p (p ^ e)).card = e := by
  rw [card_primePowerFiber hp (pow_ne_zero _ (by omega)), Nat.log_pow hp]

/-- **Nine exponents of `5`.** -/
theorem card_primePowerFiber_five_9 : (primePowerFiber 5 (5 ^ 9)).card = 9 :=
  card_primePowerFiber_pow (by norm_num) 9

/-- **Six exponents of `7`.** -/
theorem card_primePowerFiber_seven_6 : (primePowerFiber 7 (7 ^ 6)).card = 6 :=
  card_primePowerFiber_pow (by norm_num) 6

/-- **Two exponents of `11`** in the Monster (three in `J4`). -/
theorem card_primePowerFiber_eleven_2 : (primePowerFiber 11 (11 ^ 2)).card = 2 :=
  card_primePowerFiber_pow (by norm_num) 2

theorem card_primePowerFiber_eleven_3 : (primePowerFiber 11 (11 ^ 3)).card = 3 :=
  card_primePowerFiber_pow (by norm_num) 3

/-- **Three exponents of `13`.** -/
theorem card_primePowerFiber_thirteen_3 : (primePowerFiber 13 (13 ^ 3)).card = 3 :=
  card_primePowerFiber_pow (by norm_num) 3

/-- The four new fibers, spelled out. -/
theorem primePowerFiber_five_9 :
    primePowerFiber 5 (5 ^ 9) = (Finset.Icc 1 9).image (fun k => 5 ^ k) :=
  primePowerFiber_pow (by norm_num) 9

theorem primePowerFiber_seven_6 :
    primePowerFiber 7 (7 ^ 6) = (Finset.Icc 1 6).image (fun k => 7 ^ k) :=
  primePowerFiber_pow (by norm_num) 6

theorem primePowerFiber_eleven_2 :
    primePowerFiber 11 (11 ^ 2) = (Finset.Icc 1 2).image (fun k => 11 ^ k) :=
  primePowerFiber_pow (by norm_num) 2

theorem primePowerFiber_thirteen_3 :
    primePowerFiber 13 (13 ^ 3) = (Finset.Icc 1 3).image (fun k => 13 ^ k) :=
  primePowerFiber_pow (by norm_num) 3

/-- The six small fibers of the Monster carry `46 + 20 + 9 + 6 + 2 + 3 = 86` points,
out of the `95` prime-power exponents of `|M|`: the nine remaining primes are simple. -/
theorem sum_small_exponents :
    ∑ p ∈ smallPrimes, monsterOrder.factorization p = 86 := by
  have h : ∀ p ∈ smallPrimes, monsterOrder.factorization p = monster.exponent p :=
    fun p _ => MonsterSpiral.monster_factorization_eq p
  rw [Finset.sum_congr rfl h]
  decide

/-- The six small fibers have `86` points in total. -/
theorem sum_card_small_fibers :
    ∑ p ∈ smallPrimes, (primePowerFiber p (p ^ monsterOrder.factorization p)).card = 86 := by
  have h : ∀ p ∈ smallPrimes,
      (primePowerFiber p (p ^ monsterOrder.factorization p)).card
        = monsterOrder.factorization p := by
    intro p hp
    have hp1 : 1 < p := by fin_cases hp <;> norm_num
    exact card_primePowerFiber_pow hp1 _
  rw [Finset.sum_congr rfl h, sum_small_exponents]

/-! ## The small part of the Monster -/

/-- The cofactor of `smallPart` in `|M|` is the product of the nine remaining primes. -/
theorem cofactor_value : 53911588082213 = 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71 := by
  norm_num

theorem smallPart_mul_cofactor : smallPart * 53911588082213 = monsterOrder := by
  rw [smallPart_value, monster_order_value]

theorem smallPart_dvd_monsterOrder : smallPart ∣ monsterOrder :=
  ⟨53911588082213, smallPart_mul_cofactor.symm⟩

/-- `smallPart` has `47 · 21 · 10 · 7 · 3 · 4 = 829 080` divisors. -/
theorem card_divisors_smallPart : smallPart.divisors.card = 829080 := by
  rw [Nat.card_divisors smallPart_ne_zero, smallPart, primeFactors_factProd _ wf_smallFactors]
  have h : ∀ p ∈ (smallFactors.map Prod.fst).toFinset,
      (factProd smallFactors).factorization p + 1
        = ((smallFactors.filter fun pe => pe.1 = p).map Prod.snd).sum + 1 :=
    fun p _ => by rw [← smallPart, factorization_smallPart]
  rw [Finset.prod_congr rfl h]
  decide

/-- The six small primes carry all but a factor `2^9 = 512` of the Monster's divisors: the
`829 080` divisors of `smallPart` times the `512` squarefree choices among the nine remaining
primes give the `424 488 960` divisors of `|M|`. -/
theorem card_divisors_smallPart_mul_512 :
    smallPart.divisors.card * 512 = monsterOrder.divisors.card := by
  rw [card_divisors_smallPart, MonsterSpiral.card_divisors_monsterOrder]

/-! ## Heights: how much of `log |M|` the six small primes carry -/

/-- The height of `smallPart` on the logarithmic scale used by the spiral pictures. -/
theorem log_smallPart :
    Real.log smallPart = 46 * Real.log 2 + 20 * Real.log 3 + 9 * Real.log 5
      + 6 * Real.log 7 + 2 * Real.log 11 + 3 * Real.log 13 := by
  have hc : (smallPart : ℝ)
      = (2 : ℝ) ^ (46 : ℕ) * 3 ^ (20 : ℕ) * 5 ^ (9 : ℕ) * 7 ^ (6 : ℕ) * 11 ^ (2 : ℕ) *
          13 ^ (3 : ℕ) := by
    rw [smallPart_eq_pows]; push_cast; ring
  rw [hc]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- `smallPart` has forty-one decimal digits, so its height lies between `40 log 10 = 92.1`
and `41 log 10 = 94.4` (it is `92.508`). -/
theorem log_smallPart_bounds :
    40 * Real.log 10 < Real.log smallPart ∧ Real.log smallPart < 41 * Real.log 10 := by
  constructor
  · have h : ((10 : ℝ) ^ (40 : ℕ)) < (smallPart : ℝ) := by
      rw [smallPart_value]; norm_num
    calc 40 * Real.log 10 = Real.log ((10 : ℝ) ^ (40 : ℕ)) := by rw [Real.log_pow]; push_cast; ring
      _ < Real.log smallPart := Real.log_lt_log (by positivity) h
  · have h : (smallPart : ℝ) < ((10 : ℝ) ^ (41 : ℕ)) := by
      rw [smallPart_value]; norm_num
    have hpos : (0 : ℝ) < (smallPart : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero smallPart_ne_zero
    calc Real.log smallPart < Real.log ((10 : ℝ) ^ (41 : ℕ)) := Real.log_lt_log hpos h
      _ = 41 * Real.log 10 := by rw [Real.log_pow]; push_cast; ring

/-! ## The six small primes against the Euler factors of `ζ` -/

/-- The product of the six Euler factors of `ζ` at `2, 3, 5, 7, 11, 13`. -/
noncomputable def smallEulerProduct (s : ℝ) : ℝ := ∏ p ∈ smallPrimes, eulerFactor p s

/-- The product of the four Euler factors of `ζ` at the new primes `5, 7, 11, 13`. -/
noncomputable def newEulerProduct (s : ℝ) : ℝ := ∏ p ∈ newPrimes, eulerFactor p s

/-- The Dirichlet mass of the divisors of the small part of `|M|`. -/
noncomputable def smallDivisorSum (s : ℝ) : ℝ := ∑ d ∈ smallPart.divisors, (d : ℝ) ^ (-s)

/-- The divisor sum of the small part is the product of the six truncated Euler factors. -/
theorem smallDivisorSum_eq_prod (s : ℝ) :
    smallDivisorSum s = ∏ p ∈ smallPrimes, truncFactor p (smallPart.factorization p) s := by
  rw [smallDivisorSum, sum_divisors_rpow_eq_prod s smallPart_ne_zero, smallPart,
    primeFactors_factProd _ wf_smallFactors]
  refine Finset.prod_congr (by decide) (fun p _ => rfl)

/-- The same, with the six exponents spelled out. -/
theorem smallDivisorSum_eq_explicit (s : ℝ) :
    smallDivisorSum s = truncFactor 2 46 s * (truncFactor 3 20 s * (truncFactor 5 9 s *
      (truncFactor 7 6 s * (truncFactor 11 2 s * truncFactor 13 3 s)))) := by
  rw [smallDivisorSum_eq_prod]
  have h : ∀ p ∈ smallPrimes,
      truncFactor p (smallPart.factorization p) s
        = truncFactor p ((smallFactors.filter fun pe => pe.1 = p).map Prod.snd).sum s :=
    fun p _ => by rw [factorization_smallPart]
  rw [Finset.prod_congr rfl h]
  norm_num [smallPrimes, smallFactors, Finset.prod_insert, Finset.mem_insert]

/-- Each of the six truncated factors is below the corresponding Euler factor of `ζ`. -/
theorem smallDivisorSum_le_smallEulerProduct (hs : 0 < s) :
    smallDivisorSum s ≤ smallEulerProduct s := by
  rw [smallDivisorSum_eq_prod, smallEulerProduct]
  refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
  · have hp2 : 2 ≤ p := by fin_cases hp <;> norm_num
    exact (truncFactor_pos hp2 hs _).le
  · have hp2 : 2 ≤ p := by fin_cases hp <;> norm_num
    exact truncFactor_le_eulerFactor hp2 hs _

/-- The six Euler factors have product at most `ζ(s)`. -/
theorem smallEulerProduct_le_zeta (hs : 1 < s) : smallEulerProduct s ≤ zetaR s :=
  prod_eulerFactor_le_zeta hs smallPrimes (by decide)

/-- **The comparison for the six small primes.** -/
theorem smallDivisorSum_le_zeta (hs : 1 < s) : smallDivisorSum s ≤ zetaR s :=
  le_trans (smallDivisorSum_le_smallEulerProduct (by linarith)) (smallEulerProduct_le_zeta hs)

/-! ### The numbers at `s = 2` -/

theorem eulerFactor_two_eq (p : ℕ) (hp : 2 ≤ p) :
    eulerFactor p 2 = (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1) := by
  have hp0 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hr : (p : ℝ) ^ (-(2 : ℝ)) = ((p : ℝ) ^ (2 : ℕ))⁻¹ := by
    rw [Real.rpow_neg (by linarith), ← Real.rpow_natCast (p : ℝ) 2]
    norm_num
  have h1 : (0 : ℝ) < (p : ℝ) ^ (2 : ℕ) - 1 := by nlinarith
  rw [eulerFactor, hr]
  rw [show ((p : ℝ) ^ 2) = (p : ℝ) ^ (2 : ℕ) by norm_num]
  field_simp

/-- The six Euler factors of `ζ` at `2, 3, 5, 7, 11, 13` multiply to `715715/442368`. -/
theorem smallEulerProduct_two : smallEulerProduct 2 = 715715 / 442368 := by
  have h : ∀ p ∈ smallPrimes, eulerFactor p 2 = (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1) := by
    intro p hp; fin_cases hp <;> exact eulerFactor_two_eq _ (by norm_num)
  rw [smallEulerProduct, Finset.prod_congr rfl h, smallPrimes]
  repeat rw [Finset.prod_insert (by decide)]
  rw [Finset.prod_singleton]
  norm_num

/-- The four new primes contribute the factor `715715/663552 = 1.0786`. -/
theorem newEulerProduct_two : newEulerProduct 2 = 715715 / 663552 := by
  have h : ∀ p ∈ newPrimes, eulerFactor p 2 = (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1) := by
    intro p hp; fin_cases hp <;> exact eulerFactor_two_eq _ (by norm_num)
  rw [newEulerProduct, Finset.prod_congr rfl h, newPrimes]
  repeat rw [Finset.prod_insert (by decide)]
  rw [Finset.prod_singleton]
  norm_num

/-- The six small primes account for at most all of `ζ(2)`. -/
theorem smallEulerProduct_two_le : smallEulerProduct 2 ≤ Real.pi ^ 2 / 6 := by
  rw [← zetaR_two]
  exact smallEulerProduct_le_zeta (by norm_num)

/-- **And for more than `98.3 %` of it.** -/
theorem smallEulerProduct_two_gt : 0.983 * (Real.pi ^ 2 / 6) < smallEulerProduct 2 := by
  rw [smallEulerProduct_two]
  nlinarith [Real.pi_lt_d4, Real.pi_pos]

end Sporadic

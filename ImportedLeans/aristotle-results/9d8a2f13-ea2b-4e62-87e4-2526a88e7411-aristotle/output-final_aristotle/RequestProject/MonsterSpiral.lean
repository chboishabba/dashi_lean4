/-
# Separating the spiral, and putting it back together

`visualization/moonshine-trajectories-zoom.svg` showed that the partial sum
`∑_{n ≤ N} n^{-1/2-it}` is a spiral whose turning telescopes to `t·log N`
(`MoonshineZoom.sum_turn`).  This file **separates** that one spiral in the two ways the
project's objects allow, and **recombines** the pieces:

* **multiplicatively, by primes** — for any `n ≠ 0`,
  `∑_{d ∣ n} d^{-s} = ∏_p ∑_{j ≤ v_p(n)} (p^j)^{-s}` (`divisorSumC_eq_prod`).  Each factor
  `factorSpiral p e s` is itself a polygon in `ℂ`: its steps have lengths `p^{-jσ}`
  (a geometric progression, `norm_factorTerm`) and it turns by the *same* angle
  `t·log p` at every vertex (`factorTerm_succ`) — an equiangular spiral, unlike the
  ζ-polygon whose turning `t·log((n+1)/n)` decays.  For the Monster this separates one
  sum of `424 488 960` terms (`card_divisors_monsterOrder`) into fifteen polygons with
  `95` steps in total (`sum_monster_exponents`), forty-six of them belonging to the prime `2`.
  Recombining: the fifteen turnings add up to
  `∑_p v_p(|M|)·t·log p = t·log|M|` (`monster_total_turning`), which is *exactly* the total
  turning of the ζ-spiral truncated at `N = |M|` (`monster_turning_eq_zeta_turning`).

* **additively, by residues mod 24** — the ζ-polygon splits into the 24 threads
  `∑_{n ≡ a (24)} n^{-s}` (`sum_thread` recombines them), and the separation is performed by
  the 24 McKay–Thompson twists through finite Fourier inversion (`thread_eq_fourier`).
  A thread turns by `t·log((n+24)/n)` per step, which is exactly the turning of the
  24 consecutive ζ-steps it skips over (`threadTurn_eq_sum_turn`): the threads are 24 slow
  copies of the same spiral, and superposing them gives back the fast one.

Finally the two separations meet: the Monster's divisor sum is literally a sub-sum of the
ζ-spiral truncated at `N = |M|` (`monsterSpiral_eq_filter_sum`).
-/
import Mathlib
import RequestProject.MonsterZeta
import RequestProject.MoonshineZoom
import RequestProject.ZetaExponentScale

open Complex Finset

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MonsterSpiral

open Sporadic

/-! ## Terms of a Dirichlet series in polar form -/

/-- `k^{-s} = e^{(log k)(−s)}` for `k ≠ 0`. -/
theorem natCast_cpow_neg_exp {k : ℕ} (hk : k ≠ 0) (s : ℂ) :
    (k : ℂ) ^ (-s) = Complex.exp ((Real.log k : ℂ) * (-s)) := by
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hk), Complex.natCast_log]

/-- `n ↦ n^{-s}` is completely multiplicative. -/
theorem natCast_cpow_neg_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (s : ℂ) :
    ((m * n : ℕ) : ℂ) ^ (-s) = (m : ℂ) ^ (-s) * (n : ℂ) ^ (-s) := by
  rw [natCast_cpow_neg_exp (Nat.mul_ne_zero hm hn), natCast_cpow_neg_exp hm,
    natCast_cpow_neg_exp hn, ← Complex.exp_add]
  congr 1
  have hm' : ((m : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hn' : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have : Real.log ((m * n : ℕ) : ℝ) = Real.log m + Real.log n := by
    push_cast
    exact Real.log_mul hm' hn'
  rw [this]
  push_cast
  ring

/-! ## One prime: the factor spiral -/

/-- The `j`-th vertex step of the spiral belonging to the prime `p`: the term `(p^j)^{-s}`. -/
noncomputable def factorTerm (p j : ℕ) (s : ℂ) : ℂ := ((p ^ j : ℕ) : ℂ) ^ (-s)

/-- The **factor spiral** of `p` truncated at the exponent `e`: the polygon
`∑_{j ≤ e} (p^j)^{-s}`.  For `p = 2`, `e = 46` this is the Monster's fiber of `2`, its
forty-six exponents drawn as forty-six steps. -/
noncomputable def factorSpiral (p e : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (e + 1), factorTerm p j s

/-- The steps of a factor spiral are the powers of the single complex number `p^{-s}`. -/
theorem factorTerm_eq_pow {p : ℕ} (hp : p ≠ 0) (j : ℕ) (s : ℂ) :
    factorTerm p j s = ((p : ℂ) ^ (-s)) ^ j := by
  induction j with
  | zero => simp [factorTerm]
  | succ k ih =>
      have : ((p ^ (k + 1) : ℕ) : ℂ) ^ (-s) = ((p ^ k : ℕ) : ℂ) ^ (-s) * (p : ℂ) ^ (-s) := by
        rw [show p ^ (k + 1) = p ^ k * p from pow_succ p k,
          natCast_cpow_neg_mul (pow_ne_zero _ hp) hp]
      rw [factorTerm, this, ← factorTerm, ih, pow_succ]

/-- **The step lengths of a factor spiral form a geometric progression**: the `j`-th step has
length `p^{-jσ}`, in contrast with the `n^{-σ}` of the ζ-polygon. -/
theorem norm_factorTerm {p : ℕ} (hp : 0 < p) (j : ℕ) (s : ℂ) :
    ‖factorTerm p j s‖ = ((p : ℝ) ^ (-s.re)) ^ j := by
  rw [factorTerm_eq_pow hp.ne', norm_pow, Complex.norm_natCast_cpow_of_pos hp]
  simp

/-- The angle by which a factor spiral turns at each of its vertices: `t·log p`, the **same at
every vertex** — the factor spirals are equiangular. -/
noncomputable def factorTurn (t : ℝ) (p : ℕ) : ℝ := t * Real.log p

/-- **A factor spiral is equiangular.**  Passing from the `j`-th step to the next scales by
`p^{-σ}` and rotates by the constant angle `factorTurn t p = t·log p`. -/
theorem factorTerm_succ {p : ℕ} (hp : 1 ≤ p) (j : ℕ) (sigma t : ℝ) :
    factorTerm p (j + 1) ((sigma : ℂ) + t * Complex.I)
      = (((p : ℝ) ^ (-sigma) : ℝ) : ℂ) * Complex.exp (-(factorTurn t p) * Complex.I) *
          factorTerm p j ((sigma : ℂ) + t * Complex.I) := by
  have hp0 : p ≠ 0 := by omega
  rw [factorTerm_eq_pow hp0, factorTerm_eq_pow hp0, pow_succ,
    MoonshineZoom.cpow_neg_eq_polar hp sigma t, factorTurn]
  push_cast
  ring

/-- The closed form of a factor spiral: a finite geometric sum. -/
theorem factorSpiral_eq_geom {p : ℕ} (hp : p ≠ 0) (e : ℕ) {s : ℂ} (h : (p : ℂ) ^ (-s) ≠ 1) :
    factorSpiral p e s = (((p : ℂ) ^ (-s)) ^ (e + 1) - 1) / ((p : ℂ) ^ (-s) - 1) := by
  rw [factorSpiral]
  simp only [factorTerm_eq_pow hp]
  exact geom_sum_eq h (e + 1)

/-- **The total turning of a factor spiral** is `t·log(p^e)`: `e` steps of `t·log p` each. -/
theorem sum_factorTurn (t : ℝ) (p e : ℕ) :
    ∑ _j ∈ Finset.range e, factorTurn t p = t * Real.log ((p : ℝ) ^ e) := by
  rw [Finset.sum_const, Real.log_pow, factorTurn]
  simp
  ring

/-! ## Each factor spiral converges to the corresponding Euler factor of ζ -/

/-- The Euler factor of `ζ` at `p`, `(1 − p^{-s})⁻¹`, on the complex plane: the limit the factor
spiral of `p` winds into. -/
noncomputable def eulerFactorC (p : ℕ) (s : ℂ) : ℂ := (1 - (p : ℂ) ^ (-s))⁻¹

/-- **The factor spiral is a logarithmic spiral about the Euler factor.**  The vertex
`∑_{j ≤ e}(p^j)^{-s}` misses the Euler factor `(1 − p^{-s})⁻¹` by exactly
`−(1 − p^{-s})⁻¹ (p^{-s})^{e+1}`: successive misses are the same complex number rotated by
`t·log p` and scaled by `p^{-σ}`, so the vertices spiral geometrically into the Euler factor. -/
theorem factorSpiral_sub_eulerFactorC {p : ℕ} (hp : p ≠ 0) (e : ℕ) {s : ℂ}
    (h : (p : ℂ) ^ (-s) ≠ 1) :
    factorSpiral p e s - eulerFactorC p s
      = -(eulerFactorC p s * ((p : ℂ) ^ (-s)) ^ (e + 1)) := by
  have hne : (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hne' : (p : ℂ) ^ (-s) - 1 ≠ 0 := sub_ne_zero.mpr h
  have hne'' : -1 + (p : ℂ) ^ (-s) ≠ 0 := by
    intro hc; exact hne' (by linear_combination hc)
  rw [factorSpiral_eq_geom hp e h, eulerFactorC]
  field_simp
  ring

/-- The distance from the `e`-th vertex to the Euler factor is `p^{-(e+1)σ}·|1 − p^{-s}|⁻¹`:
the truncation defect of the Monster's factor against ζ's, in complex form. -/
theorem norm_factorSpiral_sub_eulerFactorC {p : ℕ} (hp : 0 < p) (e : ℕ) {s : ℂ}
    (h : (p : ℂ) ^ (-s) ≠ 1) :
    ‖factorSpiral p e s - eulerFactorC p s‖
      = ((p : ℝ) ^ (-s.re)) ^ (e + 1) / ‖1 - (p : ℂ) ^ (-s)‖ := by
  rw [factorSpiral_sub_eulerFactorC hp.ne' e h, norm_neg, norm_mul, norm_pow, eulerFactorC,
    norm_inv, Complex.norm_natCast_cpow_of_pos hp]
  simp [div_eq_inv_mul]

/-- **The Monster's fifteen factors are truncations of ζ's fifteen Euler factors.**  Letting the
exponent grow, each factor spiral converges to the Euler factor of `ζ` at that prime, for every
`s` right of the imaginary axis. -/
theorem tendsto_factorSpiral {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun e : ℕ => factorSpiral p e s) Filter.atTop (nhds (eulerFactorC p s)) := by
  have hppos : 0 < p := by omega
  have hx : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hppos]
    have h2 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    simpa using Real.rpow_lt_one_of_one_lt_of_neg h2 (by simpa using hs)
  have hne : (p : ℂ) ^ (-s) ≠ 1 := fun hc => by simp [hc] at hx
  rw [← sub_zero (eulerFactorC p s)]
  have hgoal : Filter.Tendsto
      (fun e : ℕ => eulerFactorC p s - (eulerFactorC p s * ((p : ℂ) ^ (-s)) ^ (e + 1)))
      Filter.atTop (nhds (eulerFactorC p s - 0)) := by
    refine Filter.Tendsto.const_sub _ ?_
    have : Filter.Tendsto (fun e : ℕ => ((p : ℂ) ^ (-s)) ^ (e + 1)) Filter.atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx).comp (Filter.tendsto_add_atTop_nat 1)
    simpa using this.const_mul (eulerFactorC p s)
  refine hgoal.congr fun e => ?_
  have := factorSpiral_sub_eulerFactorC (by omega : p ≠ 0) e hne
  linear_combination -this

/-! ## Multiplicative separation: a divisor sum is a product of factor spirals -/

/-- The complex divisor sum `∑_{d ∣ n} d^{-s}`. -/
noncomputable def divisorSumC (n : ℕ) (s : ℂ) : ℂ := ∑ d ∈ n.divisors, (d : ℂ) ^ (-s)

/-- `n ↦ n^{-s}` as an arithmetic function with complex values. -/
noncomputable def cpowAF (s : ℂ) : ArithmeticFunction ℂ where
  toFun n := if n = 0 then 0 else (n : ℂ) ^ (-s)
  map_zero' := by simp

theorem cpowAF_apply (s : ℂ) {n : ℕ} (hn : n ≠ 0) : cpowAF s n = (n : ℂ) ^ (-s) := if_neg hn

theorem isMultiplicative_cpowAF (s : ℂ) : (cpowAF s).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [cpowAF], ?_⟩
  intro m n hm hn _
  rw [cpowAF_apply s (mul_ne_zero hm hn), cpowAF_apply s hm, cpowAF_apply s hn,
    natCast_cpow_neg_mul hm hn]

/-- **The separation.**  For any `n ≠ 0` the divisor-sum polygon is the product of the factor
spirals of the primes of `n`, each truncated at the exponent that prime carries. -/
theorem divisorSumC_eq_prod (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    divisorSumC n s = ∏ p ∈ n.primeFactors, factorSpiral p (n.factorization p) s := by
  have hmul : (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) *
      cpowAF s).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast.mul (isMultiplicative_cpowAF s)
  have key := ArithmeticFunction.IsMultiplicative.multiplicative_factorization _ hmul hn
  rw [ArithmeticFunction.coe_zeta_mul_apply] at key
  have hL : ∑ d ∈ n.divisors, cpowAF s d = divisorSumC n s :=
    Finset.sum_congr rfl fun d hd => cpowAF_apply s (Nat.pos_of_mem_divisors hd).ne'
  rw [hL] at key
  rw [key, Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hpp, factorSpiral]
  exact Finset.sum_congr rfl fun j _ => cpowAF_apply s (pow_ne_zero _ hpp.pos.ne')

/-- Norms separate too: the modulus of the divisor-sum polygon is the product of the moduli of
the factor spirals. -/
theorem norm_divisorSumC (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    ‖divisorSumC n s‖ = ∏ p ∈ n.primeFactors, ‖factorSpiral p (n.factorization p) s‖ := by
  rw [divisorSumC_eq_prod s hn, norm_prod]

/-! ## The Monster -/

/-- The Monster's divisor-sum polygon `∑_{d ∣ |M|} d^{-s}`, on the whole complex plane. -/
noncomputable def monsterSpiral (s : ℂ) : ℂ := divisorSumC monsterOrder s

/-- **The Monster separates into fifteen factor spirals** — one per supersingular prime,
truncated at `46, 20, 9, 6, 2, 3, 1, …, 1`. -/
theorem monsterSpiral_eq_prod (s : ℂ) :
    monsterSpiral s = ∏ p ∈ monsterPrimes, factorSpiral p (monsterOrder.factorization p) s := by
  rw [monsterSpiral, divisorSumC_eq_prod s monsterOrder_ne_zero, primeFactors_monsterOrder]

/-- The exponents of `|M|`, prime by prime. -/
theorem monster_factorization_eq (p : ℕ) : monsterOrder.factorization p = monster.exponent p := by
  rw [monsterOrder, exponent_eq_factorization monster_mem p]

/-- The same product, with the fifteen exponents written out. -/
theorem monsterSpiral_eq_explicit (s : ℂ) :
    monsterSpiral s =
      factorSpiral 2 46 s * (factorSpiral 3 20 s * (factorSpiral 5 9 s * (factorSpiral 7 6 s *
      (factorSpiral 11 2 s * (factorSpiral 13 3 s * (factorSpiral 17 1 s * (factorSpiral 19 1 s *
      (factorSpiral 23 1 s * (factorSpiral 29 1 s * (factorSpiral 31 1 s * (factorSpiral 41 1 s *
      (factorSpiral 47 1 s * (factorSpiral 59 1 s * factorSpiral 71 1 s))))))))))))) := by
  rw [monsterSpiral_eq_prod]
  have h : ∀ p ∈ monsterPrimes,
      factorSpiral p (monsterOrder.factorization p) s = factorSpiral p (monster.exponent p) s :=
    fun p _ => by rw [monster_factorization_eq]
  rw [Finset.prod_congr rfl h, monsterPrimes]
  repeat rw [Finset.prod_insert (by decide)]
  rw [Finset.prod_singleton]
  norm_num [monster, Group.exponent]

/-- **The forty-six steps of the prime 2**: the factor spiral of `2` inside `|M|` has the
exponents `2^0, 2^1, …, 2^46` as its vertices, its `j`-th step of length `2^{-jσ}`. -/
theorem monster_two_factorSpiral (s : ℂ) :
    factorSpiral 2 (monsterOrder.factorization 2) s = ∑ j ∈ Finset.range 47, factorTerm 2 j s := by
  rw [monster_factorization_two, factorSpiral]

/-- The number of steps of the fifteen separated spirals: `Ω(|M|) = 95`. -/
theorem sum_monster_exponents : ∑ p ∈ monsterPrimes, monsterOrder.factorization p = 95 := by
  have h : ∀ p ∈ monsterPrimes, monsterOrder.factorization p = monster.exponent p :=
    fun p _ => monster_factorization_eq p
  rw [Finset.sum_congr rfl h]
  decide

/-- The number of vertices, `95 + 15 = 110`. -/
theorem sum_monster_vertices : ∑ p ∈ monsterPrimes, (monsterOrder.factorization p + 1) = 110 := by
  rw [Finset.sum_add_distrib, sum_monster_exponents, Finset.sum_const, card_monsterPrimes]
  norm_num

/-- **The combined polygon has `424 488 960` vertices** — that is the number of terms in
`∑_{d ∣ |M|} d^{-s}`, against the `110` vertices of the fifteen separated spirals. -/
theorem card_divisors_monsterOrder : monsterOrder.divisors.card = 424488960 := by
  rw [Nat.card_divisors monsterOrder_ne_zero, primeFactors_monsterOrder]
  have h : ∀ p ∈ monsterPrimes, monsterOrder.factorization p + 1 = monster.exponent p + 1 :=
    fun p _ => by rw [monster_factorization_eq]
  rw [Finset.prod_congr rfl h]
  decide

/-- **Combining in polar form: the moduli multiply and the phases add.**  The Monster's divisor
sum is the product of the fifteen moduli `|F_p|` times `e^{i∑_p arg F_p}`. -/
theorem monsterSpiral_polar (s : ℂ) :
    monsterSpiral s
      = ((∏ p ∈ monsterPrimes, ‖factorSpiral p (monsterOrder.factorization p) s‖ : ℝ) : ℂ) *
          Complex.exp
            (((∑ p ∈ monsterPrimes,
              Complex.arg (factorSpiral p (monsterOrder.factorization p) s) : ℝ) : ℂ) *
              Complex.I) := by
  rw [monsterSpiral_eq_prod]
  have h : ∀ p ∈ monsterPrimes,
      factorSpiral p (monsterOrder.factorization p) s
        = ((‖factorSpiral p (monsterOrder.factorization p) s‖ : ℝ) : ℂ) *
            Complex.exp ((Complex.arg (factorSpiral p (monsterOrder.factorization p) s) : ℂ) *
              Complex.I) :=
    fun p _ => (Complex.norm_mul_exp_arg_mul_I _).symm
  rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib, ← Complex.exp_sum]
  push_cast
  rw [Finset.sum_mul]

/-! ## Recombining: the turning budget -/

/-- **The fifteen turnings add up to `t·log|M|`.**  Each factor spiral of `p` turns by
`t·log p` at each of its `v_p(|M|)` steps; summed over the fifteen supersingular primes this is
`46·t·log 2 + 20·t·log 3 + ⋯ + t·log 71 = t·log|M|`. -/
theorem monster_total_turning (t : ℝ) :
    ∑ p ∈ monsterPrimes, (monsterOrder.factorization p : ℝ) * factorTurn t p
      = t * Real.log monsterOrder := by
  rw [log_monsterOrder_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by rw [factorTurn]; ring

/-- **Separation and combination agree.**  The total turning of the Monster's fifteen factor
spirals equals the total turning of the ζ-spiral `∑_{n ≤ N} n^{-s}` truncated at `N = |M|`
(`MoonshineZoom.sum_turn`): the Monster's factorisation is a *repackaging* of the first
`|M|` steps of the zeta spiral into fifteen equiangular ones. -/
theorem monster_turning_eq_zeta_turning (t : ℝ) :
    ∑ p ∈ monsterPrimes, (monsterOrder.factorization p : ℝ) * factorTurn t p
      = ∑ n ∈ Finset.Ico 1 monsterOrder, MoonshineZoom.turn t n := by
  rw [monster_total_turning, MoonshineZoom.sum_turn t monsterOrder
    (Nat.one_le_iff_ne_zero.mpr monsterOrder_ne_zero)]

/-- **The Monster's polygon sits inside the zeta polygon**: its `424 488 960` steps are exactly
those steps `n ≤ |M|` of the zeta spiral whose index divides `|M|`. -/
theorem monsterSpiral_eq_filter_sum (s : ℂ) :
    monsterSpiral s
      = ∑ n ∈ (Finset.Icc 1 monsterOrder).filter (fun n => n ∣ monsterOrder), (n : ℂ) ^ (-s) := by
  have hset : monsterOrder.divisors
      = (Finset.Icc 1 monsterOrder).filter (fun n : ℕ => n ∣ monsterOrder) := by
    ext n
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdvd, -⟩
      have hpos : 0 < n := Nat.pos_of_dvd_of_pos hdvd
        (Nat.pos_of_ne_zero monsterOrder_ne_zero)
      exact ⟨⟨hpos, Nat.le_of_dvd (Nat.pos_of_ne_zero monsterOrder_ne_zero) hdvd⟩, hdvd⟩
    · rintro ⟨-, hdvd⟩
      exact ⟨hdvd, monsterOrder_ne_zero⟩
  rw [monsterSpiral, divisorSumC, hset]

/-! ## Additive separation: the twenty-four threads of the zeta polygon -/

/-- The `a`-th **thread** of the truncated zeta polygon: the steps whose index is `≡ a (mod 24)`,
`24` being the exponent in `Δ = η²⁴` and the order of the moonshine group of the project. -/
noncomputable def thread (a : ZMod 24) (K : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 K).filter (fun n : ℕ => ((n : ZMod 24) = a)), (n : ℂ) ^ (-s)

/-- The truncated McKay–Thompson polygon of the group element `j`, indexed by `ZMod 24`. -/
noncomputable def mtPartialZ (j : ZMod 24) (K : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 K, ZetaMoonshine.gradedTrace j n * (n : ℂ) ^ (-s)

/-- At `j = 0` this is the truncated zeta polygon. -/
theorem mtPartialZ_zero (K : ℕ) (s : ℂ) :
    mtPartialZ 0 K s = MoonshineBridge.zetaPartialC K s := by
  simp [mtPartialZ, MoonshineBridge.zetaPartialC]

/-- **Recombination.** The twenty-four threads add up to the whole zeta polygon. -/
theorem sum_thread (K : ℕ) (s : ℂ) :
    ∑ a : ZMod 24, thread a K s = MoonshineBridge.zetaPartialC K s := by
  rw [MoonshineBridge.zetaPartialC]
  simp only [thread]
  exact Finset.sum_fiberwise (Finset.Icc 1 K) (fun n : ℕ => ((n : ZMod 24)))
    (fun n : ℕ => (n : ℂ) ^ (-s))

/-- **Separation by finite Fourier inversion.**  The `a`-th thread is the average of the
twenty-four McKay–Thompson polygons against the conjugate character values: the twists
separate the zeta spiral into its threads exactly as characters separate a representation
into isotypic pieces. -/
theorem thread_eq_fourier (a : ZMod 24) (K : ℕ) (s : ℂ) :
    thread a K s
      = (24 : ℂ)⁻¹ * ∑ j : ZMod 24,
          (starRingEnd ℂ) (ZetaMoonshine.irrep a j) * mtPartialZ j K s := by
  have h1 : ∀ j : ZMod 24, (starRingEnd ℂ) (ZetaMoonshine.irrep a j) * mtPartialZ j K s
      = ∑ n ∈ Finset.Icc 1 K,
          ((starRingEnd ℂ) (ZetaMoonshine.irrep a j) * ZetaMoonshine.gradedTrace j n) *
            (n : ℂ) ^ (-s) := by
    intro j
    rw [mtPartialZ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_comm, Finset.mul_sum]
  rw [thread, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  have : (24 : ℂ)⁻¹ * ∑ j : ZMod 24,
      ((starRingEnd ℂ) (ZetaMoonshine.irrep a j) * ZetaMoonshine.gradedTrace j n) *
        (n : ℂ) ^ (-s)
      = ZetaMoonshine.mult a n * (n : ℂ) ^ (-s) := by
    rw [ZetaMoonshine.mult, ← Finset.sum_mul, mul_assoc]
    norm_num
  rw [this, ZetaMoonshine.mult_eq_ite]
  split <;> simp

/-! ## Where the two separations meet: the fiber of 2 inside the twenty-four threads -/

/-- The forty-six exponents of `2` in `|M|` meet only four of the twenty-four threads. -/
theorem two_pow_mod24_mem_four : ∀ k ∈ Finset.Icc 1 46, 2 ^ k % 24 ∈ ({2, 4, 8, 16} : Finset ℕ) := by
  decide

/-- How the forty-six steps of the factor spiral of `2` distribute over those four threads:
`2^1` alone lands in the class `2`, `2^2` alone in `4`, and the remaining forty-four alternate
twenty-two and twenty-two between the classes `8` and `16`. -/
theorem two_pow_thread_counts :
    ((Finset.Icc 1 46).filter (fun k => 2 ^ k % 24 = 2)).card = 1 ∧
    ((Finset.Icc 1 46).filter (fun k => 2 ^ k % 24 = 4)).card = 1 ∧
    ((Finset.Icc 1 46).filter (fun k => 2 ^ k % 24 = 8)).card = 22 ∧
    ((Finset.Icc 1 46).filter (fun k => 2 ^ k % 24 = 16)).card = 22 := by
  decide

/-- Consequently twenty of the twenty-four threads contain no power of `2` at all. -/
theorem thread_no_two_power {a : ℕ} (ha : a ∉ ({2, 4, 8, 16} : Finset ℕ)) (k : ℕ)
    (hk : 1 ≤ k) : 2 ^ k % 24 ≠ a := by
  intro hc
  have hmem : 2 ^ k % 24 ∈ ({2, 4, 8, 16} : Finset ℕ) := by
    have hcyc : ∀ m : ℕ, 2 ^ (m + 1) % 24 ∈ ({2, 4, 8, 16} : Finset ℕ) := by
      intro m
      induction m with
      | zero => decide
      | succ i ih =>
          have : 2 ^ (i + 2) % 24 = 2 * (2 ^ (i + 1) % 24) % 24 := by
            rw [pow_succ]
            omega
          rw [this]
          simp only [Finset.mem_insert, Finset.mem_singleton] at ih ⊢
          rcases ih with h | h | h | h <;> rw [h] <;> decide
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact hcyc m
  exact ha (hc ▸ hmem)

/-! ## The geometry of a thread -/

/-- The turning of the ζ-polygon accumulated between two indices. -/
theorem sum_turn_Ico (t : ℝ) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, MoonshineZoom.turn t n = t * Real.log ((b : ℝ) / a) := by
  have hsplit : ∑ n ∈ Finset.Ico 1 a, MoonshineZoom.turn t n +
      ∑ n ∈ Finset.Ico a b, MoonshineZoom.turn t n = ∑ n ∈ Finset.Ico 1 b, MoonshineZoom.turn t n :=
    Finset.sum_Ico_consecutive _ ha hab
  have h1 := MoonshineZoom.sum_turn t a ha
  have h2 := MoonshineZoom.sum_turn t b (le_trans ha hab)
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (le_trans ha hab)
  rw [h1, h2] at hsplit
  rw [Real.log_div hbpos.ne' hapos.ne']
  linarith

/-- The angle a thread turns at each of its vertices: it skips 24 indices at a time. -/
noncomputable def threadTurn (t : ℝ) (n : ℕ) : ℝ := t * Real.log ((n + 24 : ℝ) / n)

/-- **A thread step is twenty-four ζ-steps.**  The turning of one step of a thread equals the
total turning of the twenty-four consecutive steps of the full ζ-polygon that it spans — the
threads are the same spiral, taken twenty-four steps at a time. -/
theorem threadTurn_eq_sum_turn (t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    threadTurn t n = ∑ k ∈ Finset.Ico n (n + 24), MoonshineZoom.turn t k := by
  rw [sum_turn_Ico t hn (by omega), threadTurn]
  push_cast
  ring_nf

/-- **The total turning of a thread telescopes** as well: from its first vertex `a` to its
`M`-th, a thread turns by `t·log((a+24M)/a)`, i.e. `24` threads each turning `≈ t·log(N/24)`
recombine into the single `t·log N`. -/
theorem sum_threadTurn (t : ℝ) {a : ℕ} (ha : 1 ≤ a) (M : ℕ) :
    ∑ m ∈ Finset.range M, threadTurn t (a + 24 * m) = t * Real.log ((a + 24 * M : ℝ) / a) := by
  induction M with
  | zero => simp
  | succ K ih =>
      have hK : 1 ≤ a + 24 * K := by omega
      have hapos : (0 : ℝ) < a := by exact_mod_cast ha
      have h1 : (0 : ℝ) < (a : ℝ) + 24 * K := by positivity
      rw [Finset.sum_range_succ, ih, threadTurn]
      have hc : ((a + 24 * K : ℕ) : ℝ) = (a : ℝ) + 24 * K := by push_cast; ring
      rw [hc]
      rw [Real.log_div (by positivity) hapos.ne', Real.log_div (by positivity) h1.ne',
        Real.log_div (by positivity) hapos.ne']
      have : ((a : ℝ) + 24 * K + 24) = ((a : ℝ) + 24 * (K + 1)) := by ring
      rw [this]
      push_cast
      ring

end MonsterSpiral

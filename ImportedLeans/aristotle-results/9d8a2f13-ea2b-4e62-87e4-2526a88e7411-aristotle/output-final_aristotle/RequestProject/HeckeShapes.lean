/-
# The shape of a sporadic group in Hecke space

Every sporadic group `G` selects, for each prime `p ∣ |G|`, the first `e_p(G) = v_p(|G|)` points
of the Hecke fiber of `p`:

```
y_p(k) = τ(p^k) / p^{11k/2},    k = 1, …, e_p(G),
```

the Deligne-normalised coefficients already plotted in this project.  The list of these prime
powers is the group's **shape** in Hecke space, `visPoints`/`shapePoints`; the number of them is
its **dimension** `dim G = ∑_p e_p(G)`, and the total size of the coefficients it lights up is
its **mass**.

This file sets up that dictionary and proves the two structural facts behind it:

* **the pair bound** (`wave_pair_abs_ge`): consecutive points of a Hecke fiber can never both be
  small — `|y_p(k)| + |y_p(k+1)| ≥ 0.7` for every `p` and every `k`.  This is the Chebyshev
  identity `y_k² + y_{k+1}² - 2cos θ_p · y_k y_{k+1} = 1` for the Satake angle `θ_p`.  So a prime
  entering with a *large* exponent contributes mass — and shape — proportional to its exponent;
* **a prime entering with exponent one contributes a single point** — and in every one of the
  twenty-six sporadic groups every prime `≥ 17` does exactly that (`exponent_one_of_large`).

The numerical side (the mass of each of the twenty-six shapes and the resulting ranking) is in
`RequestProject/HeckeShapeTable.lean`.
-/
import RequestProject.TauWavesSix
import RequestProject.FiberSumTable

namespace HeckeShapes

open FiberSums PrimeFibers RamanujanTau

set_option autoImplicit false
set_option maxRecDepth 40000

/-! ## The Chebyshev pair bound

The wave `w_p(u) = sin((u+1)θ_p)/sin θ_p` of `RequestProject/TauWaves.lean` is the Satake model of
the fiber of `p`: it passes through the plotted points `τ(p^k)/p^{11k/2}` wherever the Hecke
recursion is available.  Two consecutive values of a wave satisfy a Chebyshev–Pythagoras identity,
which forbids them from both being small.
-/

/-- The algebraic core: with `A² + B² = 1` and `c² + s² = 1`, `s ≠ 0`, the pair
`(A/s, (Ac + Bs)/s)` lies on the conic `X² + Y² - 2cXY = 1`. -/
theorem chebyshev_conic {A B c s : ℝ} (hs : s ≠ 0) (h1 : A ^ 2 + B ^ 2 = 1)
    (h2 : c ^ 2 + s ^ 2 = 1) :
    (A / s) ^ 2 + ((A * c + B * s) / s) ^ 2 - 2 * c * ((A / s) * ((A * c + B * s) / s)) = 1 := by
  field_simp
  nlinarith [h1, h2, sq_nonneg A, sq_nonneg B]

/-- **The Chebyshev identity for a Hecke fiber.** Consecutive values of the wave of `p` lie on the
conic `X² + Y² - 2cos θ_p · XY = 1`. -/
theorem wave_pythagoras {p : ℕ} (h : |TauWaves.satakeCos p| < 1) (u : ℝ) :
    TauWaves.wave p u ^ 2 + TauWaves.wave p (u + 1) ^ 2
      - 2 * TauWaves.satakeCos p * (TauWaves.wave p u * TauWaves.wave p (u + 1)) = 1 := by
  have hs : 0 < Real.sin (TauWaves.theta p) := TauWaves.sin_theta_pos h
  have hc : Real.cos (TauWaves.theta p) = TauWaves.satakeCos p := TauWaves.cos_theta h.le
  have hadd : (u + 1 + 1) * TauWaves.theta p
      = (u + 1) * TauWaves.theta p + TauWaves.theta p := by ring
  have h1 : Real.sin ((u + 1) * TauWaves.theta p) ^ 2
      + Real.cos ((u + 1) * TauWaves.theta p) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have h2 : TauWaves.satakeCos p ^ 2 + Real.sin (TauWaves.theta p) ^ 2 = 1 := by
    rw [← hc]; rw [add_comm]; exact Real.sin_sq_add_cos_sq _
  rw [TauWaves.wave, TauWaves.wave, hadd, Real.sin_add, hc]
  exact chebyshev_conic hs.ne' h1 h2

/-- Consecutive points of a Hecke fiber have squares summing to at least `1/2`. -/
theorem wave_pair_sq_ge {p : ℕ} (h : |TauWaves.satakeCos p| < 1) (u : ℝ) :
    (1 : ℝ) / 2 ≤ TauWaves.wave p u ^ 2 + TauWaves.wave p (u + 1) ^ 2 := by
  have hid := wave_pythagoras h u
  have hc := abs_le.1 h.le
  nlinarith [sq_nonneg (TauWaves.wave p u + TauWaves.satakeCos p * TauWaves.wave p (u + 1)),
    mul_nonneg (by nlinarith [hc.1, hc.2] : (0 : ℝ) ≤ 1 - TauWaves.satakeCos p ^ 2)
      (sq_nonneg (TauWaves.wave p (u + 1)))]

/-- **The pair bound.** Two consecutive points of a Hecke fiber can never both be small:
`|y_p(k)| + |y_p(k+1)| ≥ 0.7` (indeed `≥ 1/√2`). -/
theorem wave_pair_abs_ge {p : ℕ} (h : |TauWaves.satakeCos p| < 1) (u : ℝ) :
    (0.7 : ℝ) ≤ |TauWaves.wave p u| + |TauWaves.wave p (u + 1)| := by
  have hsq := wave_pair_sq_ge h u
  have ha : |TauWaves.wave p u| ^ 2 = TauWaves.wave p u ^ 2 := sq_abs _
  have hb : |TauWaves.wave p (u + 1)| ^ 2 = TauWaves.wave p (u + 1) ^ 2 := sq_abs _
  nlinarith [abs_nonneg (TauWaves.wave p u), abs_nonneg (TauWaves.wave p (u + 1)),
    mul_nonneg (abs_nonneg (TauWaves.wave p u)) (abs_nonneg (TauWaves.wave p (u + 1)))]

/-! ## The mass of a fiber, with multiplicity -/

/-- The Hecke mass of the fiber of `p` truncated at exponent `e`: `∑_{k=1}^{e} |y_p(k)|`, in the
Satake (wave) model. -/
noncomputable def fiberWaveMass (p e : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 e, |TauWaves.wave p (k : ℝ)|

theorem fiberWaveMass_zero (p : ℕ) : fiberWaveMass p 0 = 0 := by simp [fiberWaveMass]

theorem fiberWaveMass_nonneg (p e : ℕ) : 0 ≤ fiberWaveMass p e :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem fiberWaveMass_succ (p e : ℕ) :
    fiberWaveMass p (e + 1) = fiberWaveMass p e + |TauWaves.wave p ((e : ℝ) + 1)| := by
  rw [fiberWaveMass, fiberWaveMass, Finset.sum_Icc_succ_top (by omega)]
  push_cast
  ring

theorem fiberWaveMass_mono {p e e' : ℕ} (h : e ≤ e') : fiberWaveMass p e ≤ fiberWaveMass p e' := by
  induction e' with
  | zero => simp [Nat.le_zero.1 h]
  | succ n ih =>
      rcases Nat.lt_or_ge e (n + 1) with hlt | hge
      · have := ih (by omega)
        rw [fiberWaveMass_succ]
        have := abs_nonneg (TauWaves.wave p ((n : ℝ) + 1))
        linarith [ih (by omega : e ≤ n)]
      · have : e = n + 1 := le_antisymm h hge
        subst this
        rfl

/-- Half the exponent's worth of pairs: `∑_{k=1}^{2m} |y_p(k)| ≥ 0.7 m`. -/
theorem fiberWaveMass_two_mul_ge {p : ℕ} (h : |TauWaves.satakeCos p| < 1) (m : ℕ) :
    (0.7 : ℝ) * m ≤ fiberWaveMass p (2 * m) := by
  induction m with
  | zero => simp [fiberWaveMass]
  | succ n ih =>
      have hstep : fiberWaveMass p (2 * (n + 1))
          = fiberWaveMass p (2 * n) + |TauWaves.wave p ((2 * n : ℕ) + 1)|
            + |TauWaves.wave p (((2 * n : ℕ) + 1) + 1)| := by
        have h1 : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
        rw [h1, fiberWaveMass_succ, fiberWaveMass_succ]
        push_cast
        ring_nf
      have hpair := wave_pair_abs_ge h ((2 * n : ℕ) + 1 : ℝ)
      rw [hstep]
      push_cast at hpair ⊢
      push_cast at ih
      linarith

/-! ## Deligne's bound at the Monster's nine large primes -/

/-- Deligne's bound in integer form: if `τ(p)² < 4p¹¹` then the Satake parameter of `p` is a
genuine cosine. -/
theorem abs_satakeCos_lt_one_of_intSq {p : ℕ} (hp : 0 < p)
    (h : (tau p) ^ 2 < 4 * (p : ℤ) ^ 11) : |TauWaves.satakeCos p| < 1 := by
  refine TauWavesSix.abs_satakeCos_lt_one_of_sq hp ?_
  exact_mod_cast h

theorem abs_satakeCos_seventeen : |TauWaves.satakeCos 17| < 1 :=
  abs_satakeCos_lt_one_of_intSq (by norm_num) (by native_decide)

theorem abs_satakeCos_nineteen : |TauWaves.satakeCos 19| < 1 :=
  abs_satakeCos_lt_one_of_intSq (by norm_num) (by native_decide)

theorem abs_satakeCos_twentythree : |TauWaves.satakeCos 23| < 1 :=
  abs_satakeCos_lt_one_of_intSq (by norm_num) (by native_decide)

theorem abs_satakeCos_twentynine : |TauWaves.satakeCos 29| < 1 :=
  abs_satakeCos_lt_one_of_intSq (by norm_num) (by native_decide)

theorem abs_satakeCos_thirtyone : |TauWaves.satakeCos 31| < 1 :=
  abs_satakeCos_lt_one_of_intSq (by norm_num) (by native_decide)

theorem abs_satakeCos_fortyone : |TauWaves.satakeCos 41| < 1 :=
  abs_satakeCos_lt_one_of_intSq (by norm_num) (by native_decide)

theorem abs_satakeCos_fortyseven : |TauWaves.satakeCos 47| < 1 :=
  abs_satakeCos_lt_one_of_intSq (by norm_num) (by native_decide)

theorem abs_satakeCos_fiftynine : |TauWaves.satakeCos 59| < 1 :=
  abs_satakeCos_lt_one_of_intSq (by norm_num) (by native_decide)

theorem abs_satakeCos_seventyone : |TauWaves.satakeCos 71| < 1 :=
  abs_satakeCos_lt_one_of_intSq (by norm_num) (by native_decide)

/-- The first point of a fiber is the plotted coefficient `τ(p)/p^{11/2}`. -/
theorem wave_one_eq_normTau {p : ℕ} (hp : 0 < p) (h : |TauWaves.satakeCos p| < 1) :
    TauWaves.wave p 1 = normTau p := by
  have hrt : TauWaves.rt p ≠ 0 := TauWaves.rt_ne_zero hp
  rw [TauWaves.wave_one h, TauWaves.satakeCos, normTau]
  rw [show Real.sqrt ((p : ℝ) ^ 11) = TauWaves.rt p from rfl]
  field_simp

theorem fiberWaveMass_one (p : ℕ) : fiberWaveMass p 1 = |TauWaves.wave p 1| := by
  simp [fiberWaveMass]

/-- A prime entering with exponent one contributes exactly one point of the picture, namely the
plotted coefficient `τ(p)/p^{11/2}`. -/
theorem fiberWaveMass_one_eq_abs_normTau {p : ℕ} (hp : 0 < p) (h : |TauWaves.satakeCos p| < 1) :
    fiberWaveMass p 1 = |normTau p| := by
  rw [fiberWaveMass_one, wave_one_eq_normTau hp h]

/-! ## Bounded amplitude at the large primes -/

/-- If `τ(p)² ≤ 3p¹¹` then the whole wave of `p` stays inside the band `|w| ≤ 2`. -/
theorem abs_wave_le_two {p : ℕ} (hp : 0 < p) (h : (tau p) ^ 2 ≤ 3 * (p : ℤ) ^ 11) (u : ℝ) :
    |TauWaves.wave p u| ≤ 2 := by
  have hR : ((tau p : ℤ) : ℝ) ^ 2 ≤ 3 * (p : ℝ) ^ 11 := by exact_mod_cast h
  have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hrt : 0 < TauWaves.rt p := TauWaves.rt_pos hp
  have hrt2 : TauWaves.rt p ^ 2 = (p : ℝ) ^ 11 := TauWaves.rt_sq p
  have hcos : TauWaves.satakeCos p ^ 2 ≤ 3 / 4 := by
    rw [TauWaves.satakeCos, div_pow]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hrt2, hR]
  have hlt : |TauWaves.satakeCos p| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith [hcos, sq_nonneg (TauWaves.satakeCos p - 1),
      sq_nonneg (TauWaves.satakeCos p + 1)]
  have hsin : Real.sin (TauWaves.theta p) = Real.sqrt (1 - TauWaves.satakeCos p ^ 2) := by
    rw [TauWaves.theta, Real.sin_arccos]
  have hhalf : (1 : ℝ) / 2 ≤ Real.sin (TauWaves.theta p) := by
    rw [hsin]
    have : Real.sqrt ((1 : ℝ) / 4) ≤ Real.sqrt (1 - TauWaves.satakeCos p ^ 2) :=
      Real.sqrt_le_sqrt (by linarith)
    have h4 : Real.sqrt ((1 : ℝ) / 4) = 1 / 2 := by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [h4 ▸ this]
  have hpos : 0 < Real.sin (TauWaves.theta p) := by linarith
  refine le_trans (TauWaves.abs_wave_le hlt u) ?_
  rw [div_le_iff₀ hpos]
  linarith

/-! ## The shape of a sporadic group -/

/-- The **dimension** of the shape of `G`: the number of Hecke coordinates it lights up,
`dim G = ∑_p v_p(|G|)`. -/
def dim (G : Sporadic.Group) : ℕ := (G.factors.map Prod.snd).sum

/-- The part of the dimension coming from the six small primes `2, 3, 5, 7, 11, 13`. -/
def smallDim (G : Sporadic.Group) : ℕ :=
  ((G.factors.filter fun pe => pe.1 ≤ 13).map Prod.snd).sum

/-- The part of the dimension coming from the primes `≥ 17`. -/
def largeDim (G : Sporadic.Group) : ℕ :=
  ((G.factors.filter fun pe => 17 ≤ pe.1).map Prod.snd).sum

theorem dim_eq_smallDim_add_largeDim : ∀ G ∈ Sporadic.groups, dim G = smallDim G + largeDim G := by
  decide

/-- The dimension of the shape is the number of prime factors of `|G|` counted with
multiplicity, `Ω(|G|)`. -/
theorem cardFactors_order : ∀ (l : List (ℕ × ℕ)), Sporadic.WF l →
    ArithmeticFunction.cardFactors (Sporadic.factProd l) = (l.map Prod.snd).sum := by
  intro l
  induction l with
  | nil => intro _; simp [Sporadic.factProd]
  | cons pe t ih =>
      intro h
      have hp : Nat.Prime pe.1 := (h.1 pe (List.mem_cons_self ..)).1
      have h0 : Sporadic.factProd t ≠ 0 := Sporadic.factProd_ne_zero t h.tail
      have hpow : (pe.1 ^ pe.2) ≠ 0 := pow_ne_zero _ hp.pos.ne'
      simp only [Sporadic.factProd, ArithmeticFunction.cardFactors_mul hpow h0,
        ArithmeticFunction.cardFactors_apply_prime_pow hp, ih h.tail, List.map_cons,
        List.sum_cons]

/-- `dim G = Ω(|G|)`: the shape of `G` has one coordinate for every prime factor of `|G|`,
counted with multiplicity. -/
theorem dim_eq_cardFactors {G : Sporadic.Group} (hG : G ∈ Sporadic.groups) :
    ArithmeticFunction.cardFactors G.order = dim G :=
  cardFactors_order G.factors (Sporadic.wf_groups G hG)

/-- **Every prime `≥ 17` enters every sporadic group with exponent exactly one**: it lights up a
single Hecke coordinate, and so cannot show any oscillation at all. -/
theorem exponent_one_of_large :
    ∀ G ∈ Sporadic.groups, ∀ pe ∈ G.factors, 17 ≤ pe.1 → pe.2 = 1 := by decide

/-- **Only small primes ever curve.** Three consecutive points are needed before the Hecke
recursion `y_{k+2} = y_1 y_{k+1} - y_k` binds anything, and every prime entering a sporadic
group with exponent `≥ 3` is one of `2, 3, 5, 7, 11, 13`. -/
theorem oscillating_primes_small :
    ∀ G ∈ Sporadic.groups, ∀ pe ∈ G.factors, 3 ≤ pe.2 → pe.1 ≤ 13 := by decide

/-- The twenty-six shapes are pairwise distinct: no two sporadic groups have the same
`(prime, exponent)` profile. -/
theorem factors_injective : ∀ G ∈ Sporadic.groups, ∀ H ∈ Sporadic.groups,
    G.factors = H.factors → G.name = H.name := by decide

/-- Consequently the large-prime dimension of a group is just its number of primes `≥ 17`. -/
theorem largeDim_eq_card : ∀ G ∈ Sporadic.groups,
    largeDim G = (G.factors.filter fun pe => 17 ≤ pe.1).length := by decide

theorem dim_monster : dim Sporadic.monster = 95 := by decide
theorem smallDim_monster : smallDim Sporadic.monster = 86 := by decide
theorem largeDim_monster : largeDim Sporadic.monster = 9 := by decide

/-- Ninety of the Monster's ninety-five Hecke coordinates — more than nine in ten — come from
its six small primes. -/
theorem monster_largeDim_lt_tenth : 10 * largeDim Sporadic.monster < dim Sporadic.monster := by
  decide

/-- The total dimension of all twenty-six shapes. -/
def totalDim : ℕ := (Sporadic.groups.map dim).sum
def totalSmallDim : ℕ := (Sporadic.groups.map smallDim).sum
def totalLargeDim : ℕ := (Sporadic.groups.map largeDim).sum

theorem totalDim_eq : totalDim = 712 := by decide
theorem totalSmallDim_eq : totalSmallDim = 670 := by decide
theorem totalLargeDim_eq : totalLargeDim = 42 := by decide

/-- Across all twenty-six sporadic groups, the primes `≥ 17` account for `42` of the `712` Hecke
coordinates: under six per cent. -/
theorem totalLargeDim_lt : 16 * totalLargeDim < totalDim := by decide

/-! ## The Hecke mass of a shape -/

/-- The Hecke mass of the shape of `G`: `∑_p ∑_{k ≤ v_p(|G|)} |τ(p^k)|/p^{11k/2}` in the Satake
model. -/
noncomputable def heckeMass (G : Sporadic.Group) : ℝ :=
  (G.factors.map fun pe => fiberWaveMass pe.1 pe.2).sum

/-- The part of the mass carried by the six small primes. -/
noncomputable def smallHeckeMass (G : Sporadic.Group) : ℝ :=
  ((G.factors.filter fun pe => pe.1 ≤ 13).map fun pe => fiberWaveMass pe.1 pe.2).sum

/-- The part of the mass carried by the primes `≥ 17`. -/
noncomputable def largeHeckeMass (G : Sporadic.Group) : ℝ :=
  ((G.factors.filter fun pe => 17 ≤ pe.1).map fun pe => fiberWaveMass pe.1 pe.2).sum

theorem smallHeckeMass_monster : smallHeckeMass Sporadic.monster
    = fiberWaveMass 2 46 + fiberWaveMass 3 20 + fiberWaveMass 5 9 + fiberWaveMass 7 6
      + fiberWaveMass 11 2 + fiberWaveMass 13 3 := by
  simp [smallHeckeMass, Sporadic.monster]
  ring

theorem largeHeckeMass_monster : largeHeckeMass Sporadic.monster
    = fiberWaveMass 17 1 + fiberWaveMass 19 1 + fiberWaveMass 23 1 + fiberWaveMass 29 1
      + fiberWaveMass 31 1 + fiberWaveMass 41 1 + fiberWaveMass 47 1 + fiberWaveMass 59 1
      + fiberWaveMass 71 1 := by
  simp [largeHeckeMass, Sporadic.monster]
  ring

theorem heckeMass_monster_split :
    heckeMass Sporadic.monster = smallHeckeMass Sporadic.monster + largeHeckeMass Sporadic.monster := by
  rw [smallHeckeMass_monster, largeHeckeMass_monster]
  simp [heckeMass, Sporadic.monster]
  ring

/-! ## The Monster: the small primes carry the mass -/

/-- The mass of the Monster's six small fibers is at least `29.4`: forty-two disjoint
consecutive pairs, each of mass at least `0.7`. -/
theorem monster_smallHeckeMass_ge : (29.4 : ℝ) ≤ smallHeckeMass Sporadic.monster := by
  have h2 : (16.1 : ℝ) ≤ fiberWaveMass 2 46 := by
    have h := fiberWaveMass_two_mul_ge TauWaves.abs_satakeCos_two_lt_one 23
    norm_num at h
    linarith
  have h3 : (7 : ℝ) ≤ fiberWaveMass 3 20 := by
    have h := fiberWaveMass_two_mul_ge TauWaves.abs_satakeCos_three_lt_one 10
    norm_num at h
    linarith
  have h5 : (2.8 : ℝ) ≤ fiberWaveMass 5 9 := by
    have h := fiberWaveMass_two_mul_ge TauWavesSix.abs_satakeCos_five_lt_one 4
    have hm : fiberWaveMass 5 8 ≤ fiberWaveMass 5 9 := fiberWaveMass_mono (by norm_num)
    norm_num at h
    linarith
  have h7 : (2.1 : ℝ) ≤ fiberWaveMass 7 6 := by
    have h := fiberWaveMass_two_mul_ge TauWavesSix.abs_satakeCos_seven_lt_one 3
    norm_num at h
    linarith
  have h11 : (0.7 : ℝ) ≤ fiberWaveMass 11 2 := by
    have h := fiberWaveMass_two_mul_ge TauWavesSix.abs_satakeCos_eleven_lt_one 1
    norm_num at h
    linarith
  have h13 : (0.7 : ℝ) ≤ fiberWaveMass 13 3 := by
    have h := fiberWaveMass_two_mul_ge TauWavesSix.abs_satakeCos_thirteen_lt_one 1
    have hm : fiberWaveMass 13 2 ≤ fiberWaveMass 13 3 := fiberWaveMass_mono (by norm_num)
    norm_num at h
    linarith
  rw [smallHeckeMass_monster]
  linarith

/-- The Monster's nine large primes carry a mass of less than `7.98`: each contributes the
single plotted point `τ(p)/p^{11/2}`. -/
theorem monster_largeHeckeMass_lt : largeHeckeMass Sporadic.monster < 7.98 := by
  have e17 : fiberWaveMass 17 1 = |normTau 17| :=
    fiberWaveMass_one_eq_abs_normTau (by norm_num) abs_satakeCos_seventeen
  have e19 : fiberWaveMass 19 1 = |normTau 19| :=
    fiberWaveMass_one_eq_abs_normTau (by norm_num) abs_satakeCos_nineteen
  have e23 : fiberWaveMass 23 1 = |normTau 23| :=
    fiberWaveMass_one_eq_abs_normTau (by norm_num) abs_satakeCos_twentythree
  have e29 : fiberWaveMass 29 1 = |normTau 29| :=
    fiberWaveMass_one_eq_abs_normTau (by norm_num) abs_satakeCos_twentynine
  have e31 : fiberWaveMass 31 1 = |normTau 31| :=
    fiberWaveMass_one_eq_abs_normTau (by norm_num) abs_satakeCos_thirtyone
  have e41 : fiberWaveMass 41 1 = |normTau 41| :=
    fiberWaveMass_one_eq_abs_normTau (by norm_num) abs_satakeCos_fortyone
  have e47 : fiberWaveMass 47 1 = |normTau 47| :=
    fiberWaveMass_one_eq_abs_normTau (by norm_num) abs_satakeCos_fortyseven
  have e59 : fiberWaveMass 59 1 = |normTau 59| :=
    fiberWaveMass_one_eq_abs_normTau (by norm_num) abs_satakeCos_fiftynine
  have e71 : fiberWaveMass 71 1 = |normTau 71| :=
    fiberWaveMass_one_eq_abs_normTau (by norm_num) abs_satakeCos_seventyone
  have b17 := (abs_le.1 absApprox_17).2
  have b19 := (abs_le.1 absApprox_19).2
  have b23 := (abs_le.1 absApprox_23).2
  have b29 := (abs_le.1 absApprox_29).2
  have b31 := (abs_le.1 absApprox_31).2
  have b41 := (abs_le.1 absApprox_41).2
  have b47 := (abs_le.1 absApprox_47).2
  have b59 := (abs_le.1 absApprox_59).2
  have b71 := (abs_le.1 absApprox_71).2
  rw [largeHeckeMass_monster, e17, e19, e23, e29, e31, e41, e47, e59, e71]
  norm_num at b17 b19 b23 b29 b31 b41 b47 b59 b71 ⊢
  linarith

/-- **The large primes add little.** The nine primes `17, …, 71` of the Monster carry less than a
third of the mass carried by its six small primes. -/
theorem monster_large_lt_third_small :
    3 * largeHeckeMass Sporadic.monster < smallHeckeMass Sporadic.monster := by
  have h1 := monster_largeHeckeMass_lt
  have h2 := monster_smallHeckeMass_ge
  linarith

/-- Equivalently: the nine large primes carry less than `22 %` of the Monster's Hecke mass. -/
theorem monster_largeHeckeMass_share :
    largeHeckeMass Sporadic.monster < 0.22 * heckeMass Sporadic.monster := by
  have h1 := monster_largeHeckeMass_lt
  have h2 := monster_smallHeckeMass_ge
  rw [heckeMass_monster_split]
  linarith

/-! ## The shape as a wave: the large primes barely move it

`groupWave G` superposes the fiber wave of each prime of `G`, counted with its exponent — the
construction of `RequestProject/TauWavesSix.lean` carried out for an arbitrary sporadic group.
-/

/-- The shape of `G` as a wave: `∑_p v_p(|G|) · w_p(u)`. -/
noncomputable def groupWave (G : Sporadic.Group) (u : ℝ) : ℝ :=
  (G.factors.map fun pe => (pe.2 : ℝ) * TauWaves.wave pe.1 u).sum

/-- For the Monster this is the six-prime stack of `TauWavesSix` plus one copy of each of the
nine large primes. -/
theorem groupWave_monster (u : ℝ) : groupWave Sporadic.monster u
    = TauWavesSix.stackWave u + (TauWaves.wave 17 u + TauWaves.wave 19 u + TauWaves.wave 23 u
        + TauWaves.wave 29 u + TauWaves.wave 31 u + TauWaves.wave 41 u + TauWaves.wave 47 u
        + TauWaves.wave 59 u + TauWaves.wave 71 u) := by
  simp [groupWave, Sporadic.monster, TauWavesSix.stackWave]
  ring

/-- At height `0` the shape stands at its dimension: `groupWave M 0 = 95`. -/
theorem groupWave_monster_zero : groupWave Sporadic.monster 0 = 95 := by
  rw [groupWave_monster, TauWavesSix.stackWave_zero,
    TauWaves.wave_zero abs_satakeCos_seventeen, TauWaves.wave_zero abs_satakeCos_nineteen,
    TauWaves.wave_zero abs_satakeCos_twentythree, TauWaves.wave_zero abs_satakeCos_twentynine,
    TauWaves.wave_zero abs_satakeCos_thirtyone, TauWaves.wave_zero abs_satakeCos_fortyone,
    TauWaves.wave_zero abs_satakeCos_fortyseven, TauWaves.wave_zero abs_satakeCos_fiftynine,
    TauWaves.wave_zero abs_satakeCos_seventyone]
  norm_num

/-- **The large primes barely move the shape.** The nine waves of `17, …, 71` shift the Monster's
shape by at most `18` at every height, while the six-prime stack stands at `86`. -/
theorem abs_groupWave_monster_sub_stackWave_le (u : ℝ) :
    |groupWave Sporadic.monster u - TauWavesSix.stackWave u| ≤ 18 := by
  have b17 := abs_wave_le_two (p := 17) (by norm_num) (by native_decide) u
  have b19 := abs_wave_le_two (p := 19) (by norm_num) (by native_decide) u
  have b23 := abs_wave_le_two (p := 23) (by norm_num) (by native_decide) u
  have b29 := abs_wave_le_two (p := 29) (by norm_num) (by native_decide) u
  have b31 := abs_wave_le_two (p := 31) (by norm_num) (by native_decide) u
  have b41 := abs_wave_le_two (p := 41) (by norm_num) (by native_decide) u
  have b47 := abs_wave_le_two (p := 47) (by norm_num) (by native_decide) u
  have b59 := abs_wave_le_two (p := 59) (by norm_num) (by native_decide) u
  have b71 := abs_wave_le_two (p := 71) (by norm_num) (by native_decide) u
  rw [groupWave_monster]
  have : TauWavesSix.stackWave u + (TauWaves.wave 17 u + TauWaves.wave 19 u + TauWaves.wave 23 u
      + TauWaves.wave 29 u + TauWaves.wave 31 u + TauWaves.wave 41 u + TauWaves.wave 47 u
      + TauWaves.wave 59 u + TauWaves.wave 71 u) - TauWavesSix.stackWave u
      = TauWaves.wave 17 u + TauWaves.wave 19 u + TauWaves.wave 23 u + TauWaves.wave 29 u
        + TauWaves.wave 31 u + TauWaves.wave 41 u + TauWaves.wave 47 u + TauWaves.wave 59 u
        + TauWaves.wave 71 u := by ring
  rw [this, abs_le]
  rw [abs_le] at b17 b19 b23 b29 b31 b41 b47 b59 b71
  constructor <;>
    linarith [b17.1, b17.2, b19.1, b19.2, b23.1, b23.2, b29.1, b29.2, b31.1, b31.2,
      b41.1, b41.2, b47.1, b47.2, b59.1, b59.2, b71.1, b71.2]

end HeckeShapes

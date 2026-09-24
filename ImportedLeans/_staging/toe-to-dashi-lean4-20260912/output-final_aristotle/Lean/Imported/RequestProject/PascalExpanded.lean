import Mathlib
import RequestProject.StudentPosters

/-!
# The expanded Pascal triangle, and the atlas indexed from it

`RequestProject/StudentPosters.lean` drew thirteen rows of Pascal's triangle mod `3` in order to
explain one line: the interior of row `p` is divisible by `p`.  This file expands that picture in
two directions.

**Mathematically.**  Instead of checking a handful of rows by hand we count, for every prime `p`
and every `n`, how many entries of row `n` survive mod `p`:

* `PascalAtlas.card_row_not_dvd` — the number of `k ≤ n` with `p ∤ C(n,k)` is
  `∏ᵢ (dᵢ + 1)`, the product over the base-`p` digits `dᵢ` of `n` of `dᵢ + 1`.  This is Lucas'
  theorem, turned into a count; it is the exact statement behind every visible feature of the
  coloured triangle.
* `PascalAtlas.row_interior_dvd_iff` — row `n` has a *vanishing interior* (the gold bands of the
  poster: `1 0 ⋯ 0 1`) exactly when that count equals `2`, and
  `PascalAtlas.row_interior_dvd_iff_pow` — exactly when `n` is a power of `p`.  So the gold bands
  of the triangle are precisely the rows `1, p, p², …`, which is precisely the list of iterates
  `x ↦ x^(pʲ)` of Frobenius.
* `PascalAtlas.card_triangle_not_dvd` — over the whole triangle of the first `pᵃ` rows the number
  of surviving entries is `(p(p+1)/2)ᵃ`; for the drawn triangle (`p = 3`, `a = 3`, 27 rows) that
  is `6³ = 216`.

**As a picture.**  27 rows is `3³` rows, and the project's gallery has exactly 27 pictures, so the
expanded triangle can be used as the index of the gallery: row `n` carries picture `n`, and the
base-`3` digits of `n` name an element of `GF(27) = 𝔽₃[t]/(t³ − t − 1)`, the field the project is
built around.  `PascalAtlas.atlas` is that index; `atlas_length`, `atlas_files_nodup` and
`atlas_labels_nodup` check that it really is one.
-/

namespace PascalAtlas

open Finset

/-! ## Base-`p` digits -/

/-- The base-`p` digits of `n`, least significant first, computed with an explicit fuel so that
the kernel can evaluate it inside `decide`. -/
def digitsOf (p : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, n => if n = 0 then [] else n % p :: digitsOf p fuel (n / p)

/-- With enough fuel, `digitsOf` is Mathlib's `Nat.digits`. -/
theorem digitsOf_eq_digits {p : Nat} (hp : 2 ≤ p) :
    ∀ (fuel n : Nat), n < p ^ fuel → digitsOf p fuel n = Nat.digits p n := by
  intro fuel
  induction fuel with
  | zero =>
      intro n hn
      have : n = 0 := by simpa using hn
      simp [digitsOf, this]
  | succ fuel ih =>
    intro n hn
    by_cases h0 : n = 0
    · simp [digitsOf, h0]
    · have hpos : 0 < n := Nat.pos_of_ne_zero h0
      have hdiv : n / p < p ^ fuel := by
        have hp0 : 0 < p := by omega
        exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; simpa [pow_succ] using hn)
      rw [digitsOf, if_neg h0, ih _ hdiv, Nat.digits_def' hp hpos]

/-- The width of row `n` of the triangle mod `p`: the number of entries that are not divisible
by `p`, read off Lucas' theorem as a product over the base-`p` digits. -/
def rowWidth (p n : Nat) : Nat := ((digitsOf p 64 n).map (· + 1)).prod

/-- The number of entries of row `n` that survive mod `p`, computed directly. -/
def rowSurvivors (p n : Nat) : Nat :=
  ((List.range (n + 1)).filter fun i => decide ¬ p ∣ Nat.choose n i).length

/-! ## The count: Lucas' theorem as a census of a row -/

/-- Below `p` there is no cancellation: `p ∤ C(m,k)` exactly when `k ≤ m`. -/
theorem not_dvd_choose_of_lt {p : Nat} (hp : p.Prime) {m k : Nat} (hm : m < p) :
    ¬ p ∣ Nat.choose m k ↔ k ≤ m := by
  constructor
  · intro h
    by_contra hk
    rw [Nat.choose_eq_zero_of_lt (by omega)] at h
    exact h (dvd_zero p)
  · intro hk hdvd
    have hmul := Nat.choose_mul_factorial_mul_factorial hk
    have : p ∣ Nat.factorial m := hmul ▸ Dvd.dvd.mul_right (Dvd.dvd.mul_right hdvd _) _
    exact absurd ((Nat.Prime.dvd_factorial hp).1 this) (by omega)

/-- The one-step Lucas congruence in the form used below. -/
theorem not_dvd_choose_iff {p : Nat} [Fact p.Prime] (n k : Nat) :
    ¬ p ∣ Nat.choose n k ↔ (¬ p ∣ Nat.choose (n % p) (k % p)) ∧ ¬ p ∣ Nat.choose (n / p) (k / p) := by
  have hp : p.Prime := Fact.out
  have h := (Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := k) (p := p))
  have hd : p ∣ Nat.choose n k ↔ p ∣ Nat.choose (n % p) (k % p) * Nat.choose (n / p) (k / p) := by
    constructor <;> intro hx
    · have := (Nat.modEq_zero_iff_dvd).2 hx
      exact (Nat.modEq_zero_iff_dvd).1 (h.symm.trans this)
    · have := (Nat.modEq_zero_iff_dvd).2 hx
      exact (Nat.modEq_zero_iff_dvd).1 (h.trans this)
  rw [hd, hp.dvd_mul]
  tauto

/-- **The census of a row.**  For a prime `p` and `n < pᵃ`, the number of `k < pᵃ` with
`p ∤ C(n,k)` is the product of `dᵢ + 1` over the base-`p` digits `dᵢ` of `n`. -/
theorem card_range_pow_filter (p : Nat) [Fact p.Prime] :
    ∀ (a n : Nat), n < p ^ a →
      ((range (p ^ a)).filter fun k => ¬ p ∣ Nat.choose n k).card
        = ∏ i ∈ range a, (n / p ^ i % p + 1) := by
  intro a
  induction a with
  | zero =>
    intro n hn
    have hn0 : n = 0 := by simpa using hn
    subst hn0
    have hp : p.Prime := Fact.out
    simp [Finset.filter_singleton, hp.ne_one]
  | succ a ih =>
    intro n hn
    classical
    have hp : p.Prime := Fact.out
    have hp0 : 0 < p := hp.pos
    have hdiv : n / p < p ^ a := by
      refine Nat.div_lt_of_lt_mul ?_
      calc n < p ^ (a + 1) := hn
        _ = p * p ^ a := by ring
    have hcard :
        ((range (p ^ (a + 1))).filter fun k => ¬ p ∣ Nat.choose n k).card
          = (((range p).filter fun r => r ≤ n % p) ×ˢ
              ((range (p ^ a)).filter fun q => ¬ p ∣ Nat.choose (n / p) q)).card := by
      refine Finset.card_nbij' (fun k => (k % p, k / p)) (fun x => x.1 + p * x.2) ?_ ?_ ?_ ?_
      · intro k hk
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range, Finset.mem_coe,
          Finset.mem_product, Finset.mem_filter] at hk ⊢
        obtain ⟨hk1, hk2⟩ := hk
        rw [not_dvd_choose_iff] at hk2
        refine ⟨⟨Nat.mod_lt _ hp0, (not_dvd_choose_of_lt hp (Nat.mod_lt _ hp0)).1 hk2.1⟩,
          ⟨?_, hk2.2⟩⟩
        refine Nat.div_lt_of_lt_mul ?_
        calc k < p ^ (a + 1) := hk1
          _ = p * p ^ a := by ring
      · rintro ⟨r, q⟩ hx
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range, Finset.mem_coe,
          Finset.mem_product, Finset.mem_filter] at hx ⊢
        obtain ⟨⟨hr, hrn⟩, ⟨hq, hqd⟩⟩ := hx
        have hlt : r + p * q < p ^ (a + 1) := by
          have : p * q + p ≤ p * p ^ a := by
            have : q + 1 ≤ p ^ a := hq
            calc p * q + p = p * (q + 1) := by ring
              _ ≤ p * p ^ a := Nat.mul_le_mul_left _ this
          have hpow : p ^ (a + 1) = p * p ^ a := by ring
          omega
        refine ⟨hlt, ?_⟩
        have hmod : (r + p * q) % p = r := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
        have hdvd' : (r + p * q) / p = q := by
          rw [Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hr]
          omega
        rw [not_dvd_choose_iff, hmod, hdvd']
        exact ⟨(not_dvd_choose_of_lt hp (Nat.mod_lt _ hp0)).2 hrn, hqd⟩
      · intro k _
        simpa using Nat.mod_add_div k p
      · rintro ⟨r, q⟩ hx
        simp only [Finset.mem_range, Finset.mem_coe,
          Finset.mem_product, Finset.mem_filter] at hx
        obtain ⟨⟨hr, -⟩, -⟩ := hx
        have hmod : (r + p * q) % p = r := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
        have hdvd' : (r + p * q) / p = q := by
          rw [Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hr]
          omega
        simp [hmod, hdvd']
    have hfil : ((range p).filter fun r => r ≤ n % p) = range (n % p + 1) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range]
      have : n % p < p := Nat.mod_lt _ hp0
      omega
    rw [hcard, Finset.card_product, hfil, Finset.card_range, ih (n / p) hdiv,
      Finset.prod_range_succ']
    have hshift : ∀ i ∈ range a, (n / p / p ^ i % p + 1) = (n / p ^ (i + 1) % p + 1) := by
      intro i _
      rw [Nat.div_div_eq_div_mul]
      congr 3
      ring
    rw [Finset.prod_congr rfl hshift]
    simp [Nat.mul_comm]

/-- **The census of a row**, in the form the picture uses: the number of entries of row `n`
that are not divisible by `p`. -/
theorem card_row_not_dvd (p : Nat) [Fact p.Prime] (a n : Nat) (hn : n < p ^ a) :
    ((range (n + 1)).filter fun k => ¬ p ∣ Nat.choose n k).card
      = ∏ i ∈ range a, (n / p ^ i % p + 1) := by
  classical
  have hset : ((range (p ^ a)).filter fun k => ¬ p ∣ Nat.choose n k)
      = ((range (n + 1)).filter fun k => ¬ p ∣ Nat.choose n k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, hk⟩
      refine ⟨?_, hk⟩
      by_contra hkn
      exact hk (by rw [Nat.choose_eq_zero_of_lt (by omega)]; exact dvd_zero p)
    · rintro ⟨hk, hk2⟩
      exact ⟨by omega, hk2⟩
  rw [← hset, card_range_pow_filter p a n hn]

/-- The interior of row `n` vanishes mod `p` exactly when only two of its entries survive. -/
theorem row_interior_dvd_iff (p : Nat) [Fact p.Prime] {n : Nat} (hn : 0 < n) :
    (∀ i, 0 < i → i < n → p ∣ Nat.choose n i) ↔
      ((range (n + 1)).filter fun k => ¬ p ∣ Nat.choose n k).card = 2 := by
  classical
  have hp : p.Prime := Fact.out
  have h1 : ¬ p ∣ (1 : Nat) := by simpa [Nat.dvd_one] using hp.ne_one
  have hmem0 : (0 : Nat) ∈ (range (n + 1)).filter fun k => ¬ p ∣ Nat.choose n k := by
    simp [h1]
  have hmemn : n ∈ (range (n + 1)).filter fun k => ¬ p ∣ Nat.choose n k := by
    simp [h1]
  have hsub : ({0, n} : Finset Nat) ⊆ (range (n + 1)).filter fun k => ¬ p ∣ Nat.choose n k := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hpair : ({0, n} : Finset Nat).card = 2 := Finset.card_pair (by omega)
  constructor
  · intro h
    have heq : ((range (n + 1)).filter fun k => ¬ p ∣ Nat.choose n k) = ({0, n} : Finset Nat) := by
      refine Finset.Subset.antisymm ?_ hsub
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hcon
      push_neg at hcon
      exact hk.2 (h k (Nat.pos_of_ne_zero hcon.1) (by omega))
    rw [heq, hpair]
  · intro hcard i hi hin
    have heq : ({0, n} : Finset Nat) = (range (n + 1)).filter fun k => ¬ p ∣ Nat.choose n k :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hpair])
    by_contra hdvd
    have hmem : i ∈ ((range (n + 1)).filter fun k => ¬ p ∣ Nat.choose n k) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hdvd⟩
    rw [← heq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega

/-- **The gold bands of the triangle are the powers of `p`.**  Row `n ≥ 1` has vanishing
interior exactly when `n` is a power of `p` — exactly the rows that make an iterate
`x ↦ x^(pʲ)` of Frobenius additive. -/
theorem not_dvd_choose_of_digits_le (p : Nat) [Fact p.Prime] :
    ∀ (a n k : Nat), k < p ^ a → (∀ i, k / p ^ i % p ≤ n / p ^ i % p) →
      ¬ p ∣ Nat.choose n k := by
  intro a
  induction a with
  | zero =>
    intro n k hk _
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    have hp : p.Prime := Fact.out
    simpa [Nat.dvd_one] using hp.ne_one
  | succ a ih =>
    intro n k hk hdig
    have hp : p.Prime := Fact.out
    have hp0 : 0 < p := hp.pos
    rw [not_dvd_choose_iff]
    refine ⟨(not_dvd_choose_of_lt hp (Nat.mod_lt _ hp0)).2 (by simpa using hdig 0), ?_⟩
    refine ih (n / p) (k / p) ?_ ?_
    · refine Nat.div_lt_of_lt_mul ?_
      calc k < p ^ (a + 1) := hk
        _ = p * p ^ a := by ring
    · intro i
      have h := hdig (i + 1)
      have hpow : p * p ^ i = p ^ (i + 1) := by ring
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, hpow]
      exact h

/-- **The gold bands of the triangle are the powers of `p`.**  Row `n ≥ 1` has vanishing
interior exactly when `n` is a power of `p` — exactly the rows that make an iterate
`x ↦ x^(pʲ)` of Frobenius additive. -/
theorem row_interior_dvd_iff_pow (p : Nat) [Fact p.Prime] {n : Nat} (hn : 0 < n) :
    (∀ i, 0 < i → i < n → p ∣ Nat.choose n i) ↔ ∃ j, n = p ^ j := by
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  have hp0 : 0 < p := hp.pos
  constructor
  · intro h
    refine ⟨Nat.log p n, ?_⟩
    set j := Nat.log p n with hj
    have hle : p ^ j ≤ n := Nat.pow_log_le_self p (by omega)
    have hlt : n < p ^ (j + 1) := Nat.lt_pow_succ_log_self hp1 n
    have htop : n / p ^ j < p := by
      refine Nat.div_lt_of_lt_mul ?_
      calc n < p ^ (j + 1) := hlt
        _ = p ^ j * p := by ring
    have htop1 : 1 ≤ n / p ^ j := (Nat.one_le_div_iff (Nat.pow_pos (a := p) (n := j) hp0)).2 hle
    have hkey : ¬ p ∣ Nat.choose n (p ^ j) := by
      refine not_dvd_choose_of_digits_le p (j + 1) n (p ^ j)
        (Nat.pow_lt_pow_right hp1 (Nat.lt_succ_self j)) ?_
      intro i
      rcases lt_trichotomy i j with hij | hij | hij
      · have : p ^ j / p ^ i = p ^ (j - i) := Nat.pow_div (le_of_lt hij) hp0
        rw [this]
        have hd : p ∣ p ^ (j - i) := dvd_pow_self p (by omega)
        simp [Nat.mod_eq_zero_of_dvd hd]
      · subst hij
        rw [Nat.div_self (Nat.pow_pos (a := p) (n := j) hp0), Nat.mod_eq_of_lt hp1,
          Nat.mod_eq_of_lt htop]
        exact htop1
      · rw [Nat.div_eq_of_lt (Nat.pow_lt_pow_right hp1 hij)]
        simp
    rcases eq_or_lt_of_le hle with heq | hlt2
    · exact heq.symm
    · exact absurd (h (p ^ j) (Nat.pow_pos (a := p) (n := j) hp0) hlt2) hkey
  · rintro ⟨j, rfl⟩ i h0 hi
    exact hp.dvd_choose_pow (by omega) (Nat.ne_of_lt hi)

/-- **The census of the whole triangle.**  Among the first `pᵃ` rows, the number of entries not
divisible by `p` is `(1 + 2 + ⋯ + p)ᵃ = (p(p+1)/2)ᵃ`. -/
theorem two_mul_sum_range_add_one (m : Nat) : 2 * ∑ r ∈ range m, (r + 1) = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring

theorem sum_range_add_one (m : Nat) : ∑ r ∈ range m, (r + 1) = m * (m + 1) / 2 := by
  have h := two_mul_sum_range_add_one m
  omega

/-- The digit-product count, summed over the first `pᵃ` rows. -/
theorem sum_digit_prod (p : Nat) [Fact p.Prime] :
    ∀ a : Nat, ∑ n ∈ range (p ^ a), ∏ i ∈ range a, (n / p ^ i % p + 1)
      = (∑ r ∈ range p, (r + 1)) ^ a := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
    have hp : p.Prime := Fact.out
    have hp0 : 0 < p := hp.pos
    have hbij : ∑ n ∈ range (p ^ (a + 1)), ∏ i ∈ range (a + 1), (n / p ^ i % p + 1)
        = ∑ x ∈ (range p) ×ˢ (range (p ^ a)),
            (x.1 + 1) * ∏ i ∈ range a, (x.2 / p ^ i % p + 1) := by
      refine Finset.sum_nbij' (fun k => (k % p, k / p)) (fun x => x.1 + p * x.2) ?_ ?_ ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_range] at hk
        simp only [Finset.mem_product, Finset.mem_range]
        refine ⟨Nat.mod_lt _ hp0, ?_⟩
        refine Nat.div_lt_of_lt_mul ?_
        calc k < p ^ (a + 1) := hk
          _ = p * p ^ a := by ring
      · rintro ⟨r, q⟩ hx
        simp only [Finset.mem_product, Finset.mem_range] at hx
        simp only [Finset.mem_range]
        obtain ⟨hr, hq⟩ := hx
        have hstep : p * q + p ≤ p * p ^ a := by
          calc p * q + p = p * (q + 1) := by ring
            _ ≤ p * p ^ a := Nat.mul_le_mul_left _ hq
        have hpow : p ^ (a + 1) = p * p ^ a := by ring
        omega
      · intro k _
        simpa using Nat.mod_add_div k p
      · rintro ⟨r, q⟩ hx
        simp only [Finset.mem_product, Finset.mem_range] at hx
        obtain ⟨hr, -⟩ := hx
        have hmod : (r + p * q) % p = r := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
        have hdiv : (r + p * q) / p = q := by
          rw [Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hr]
          omega
        simp [hmod, hdiv]
      · intro n _
        rw [Finset.prod_range_succ']
        have hshift : ∀ i ∈ range a, (n / p ^ (i + 1) % p + 1) = (n / p / p ^ i % p + 1) := by
          intro i _
          rw [Nat.div_div_eq_div_mul]
          congr 3
          ring
        rw [Finset.prod_congr rfl hshift]
        simp [Nat.mul_comm]
    rw [hbij, Finset.sum_product]
    have hinner : ∀ x ∈ range p,
        (∑ y ∈ range (p ^ a), (x + 1) * ∏ i ∈ range a, (y / p ^ i % p + 1))
          = (x + 1) * ∑ y ∈ range (p ^ a), ∏ i ∈ range a, (y / p ^ i % p + 1) :=
      fun x _ => (Finset.mul_sum _ _ _).symm
    rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul, ih, pow_succ, Nat.mul_comm]

/-- **The census of the whole triangle.**  Among the first `pᵃ` rows, the number of entries not
divisible by `p` is `(1 + 2 + ⋯ + p)ᵃ = (p(p+1)/2)ᵃ`. -/
theorem card_triangle_not_dvd (p : Nat) [Fact p.Prime] (a : Nat) :
    ∑ n ∈ range (p ^ a), ((range (n + 1)).filter fun k => ¬ p ∣ Nat.choose n k).card
      = (p * (p + 1) / 2) ^ a := by
  have hrow : ∀ n ∈ range (p ^ a),
      ((range (n + 1)).filter fun k => ¬ p ∣ Nat.choose n k).card
        = ∏ i ∈ range a, (n / p ^ i % p + 1) := by
    intro n hn
    exact card_row_not_dvd p a n (Finset.mem_range.1 hn)
  rw [Finset.sum_congr rfl hrow, sum_digit_prod p a, sum_range_add_one]

/-! ## The drawn triangle: 27 rows mod 3 -/

/-- The rows drawn on the expanded poster. -/
def drawnRows : Nat := 27

/-- Row `n` of the drawn triangle, reduced mod `3`. -/
def rowMod (p n : Nat) : List Nat := (List.range (n + 1)).map fun i => Nat.choose n i % p

/-- Row 27 mod 3 is `1 0 ⋯ 0 1`, the next gold band after rows 1, 3, 9. -/
theorem rowMod_27 : rowMod 3 27 =
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  decide

/-- Whether the interior of row `n` vanishes mod `p`: the test that paints a row gold. -/
def interiorVanishes (p n : Nat) : Bool :=
  (List.range (n + 1)).all fun i => decide (i = 0 ∨ i = n ∨ p ∣ Nat.choose n i)

/-- The Boolean test `interiorVanishes` says what it should. -/
theorem interiorVanishes_iff (p n : Nat) :
    interiorVanishes p n = true ↔ ∀ i, 0 < i → i < n → p ∣ Nat.choose n i := by
  simp only [interiorVanishes, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h i hi hin
    rcases h i (by omega) with h | h | h
    · omega
    · omega
    · exact h
  · intro h i hi
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · exact Or.inl h0
    · rcases Nat.lt_or_ge i n with hlt | hge
      · exact Or.inr (Or.inr (h i h0 hlt))
      · exact Or.inr (Or.inl (by omega))

/-- The gold rows below `N`: the rows `n ≥ 1` whose interior vanishes mod `p`. -/
def goldRows (p N : Nat) : List Nat :=
  (List.range N).filter fun n => decide (0 < n) && interiorVanishes p n

/-- The gold bands among the 27 drawn rows are exactly `1, 3, 9`. -/
theorem gold_rows_three : goldRows 3 27 = [1, 3, 9] := by decide

/-- Mod `2` the same rule gives `1, 2, 4, 8, 16` — the rows that make Sierpiński's triangle. -/
theorem gold_rows_two : goldRows 2 27 = [1, 2, 4, 8, 16] := by decide

/-- Mod `5`: rows `1, 5, 25`. -/
theorem gold_rows_five : goldRows 5 27 = [1, 5, 25] := by decide

/-- Mod `7`: rows `1, 7`. -/
theorem gold_rows_seven : goldRows 7 27 = [1, 7] := by decide

/-- The census, checked against the drawn triangle: every one of the 27 rows has exactly
`∏ (dᵢ + 1)` surviving entries, with the digits taken base `3`. -/
theorem rowSurvivors_eq_rowWidth_three : ∀ n ∈ List.range 27, rowSurvivors 3 n = rowWidth 3 n := by
  decide

/-- The drawn triangle has `216 = 6³` coloured cells and `378 − 216 = 162` pale ones. -/
theorem drawn_survivor_count :
    ((List.range 27).map (rowSurvivors 3)).sum = 216 ∧
      ((List.range 27).map (fun n => n + 1)).sum = 378 := by
  decide

/-! ## The atlas: 27 rows, 27 pictures

The expanded triangle has `27 = 3³` rows and the gallery has 27 pictures, so the triangle can be
used as the index of the gallery: row `n` carries picture `n`, and the three base-`3` digits of
`n` name an element `c₀ + c₁t + c₂t²` of `GF(27) = 𝔽₃[t]/(t³ − t − 1)`, the field this project is
built around.  `atlas` below is that index, and the pictures are drawn as links from the rows of
the triangle in `svg/student-0-atlas.svg`.
-/

/-- One line of the atlas: the file a row of the triangle points at, its title, and one line
saying what it shows. -/
structure Entry where
  /-- The file, relative to `svg/`. -/
  file : String
  /-- The title printed next to the row. -/
  title : String
  /-- One line of description. -/
  blurb : String
deriving DecidableEq, Repr

/-- The index: row `n` of the expanded triangle points at `atlas[n]`. -/
def atlas : List Entry :=
  [ ⟨"student-0-atlas.svg", "The atlas (this sheet)",
      "27 rows, 27 pictures; row n carries picture n and names the element of GF(27) with digits n"⟩,
    ⟨"student-1-freshmans-dream.svg", "Why xᵖ is a homomorphism",
      "Pascal's triangle mod 3, 27 rows; the interiors of rows 1, 3, 9 vanish"⟩,
    ⟨"student-2-cyclotomic-clocks.svg", "Frobenius orbits without a field",
      "on ℤ/(pᵏ−1) the map x ↦ xᵖ is j ↦ p·j: GF(8), GF(9), GF(16)"⟩,
    ⟨"student-3-subfield-tower.svg", "The subfields of GF(2¹²)",
      "one floor per divisor of 12, each the fixed field of an iterate of Frobenius"⟩,
    ⟨"student-4-dictionary.svg", "The dictionary",
      "centre ↔ prime subfield, transfer ↔ orbit product, index ↔ 1 + p + ⋯ + p^(k−1)"⟩,
    ⟨"student-5-orbit-spiral.svg", "Why the orbit product lands in 𝔽ₚ",
      "the four conjugates of x in GF(81) spiralling into the prime subfield"⟩,
    ⟨"student-6-exercise-ladder.svg", "Ten things to try",
      "exercises from x⁵ = x in 𝔽₅ up to the transfer homomorphism"⟩,
    ⟨"twist-1-dead-dial.svg", "The twist, Act I — the dial that dies",
      "on 𝔽ₚ the orbit sum is the scalar k, and p ∣ k kills it"⟩,
    ⟨"twist-2-still-onto.svg", "Act II — onto, but aimed wrongly",
      "GF(27) cut into the three level sets of the trace, nine elements each"⟩,
    ⟨"twist-3-the-twist.svg", "Act III — turn the field, not the value",
      "multiplication by c = 2t² carries 𝔽₃ across all three levels"⟩,
    ⟨"twist-4-repaired-map.svg", "Act IV — the repaired map",
      "R(x) = Tr(2t²·x) is additive, onto, idempotent and the identity on 𝔽₃"⟩,
    ⟨"twist-5-nine-twists.svg", "Act V — nine twists, nine repairs",
      "every c with Tr(c) = 1 works, and GF(27) has nine of them"⟩,
    ⟨"twist-6-census.svg", "Act VI — where it is indispensable",
      "310 field sizes q ≤ 1824; seven have a dead dial, only 729 fails both ways"⟩,
    ⟨"twist-7-pivot-ladder.svg", "Act VII — the pivot ladder",
      "dual failures up to 10¹²: 729, 531441, 9765625, … — seven of them"⟩,
    ⟨"repair-wheel-3d.svg", "The repair wheel",
      "GF(125)ˣ ≅ ℤ/124 turning: the orbit product is j ↦ 31j onto 𝔽₅ˣ"⟩,
    ⟨"repair-gears-3d.svg", "The two dials of a finite field",
      "gcd(k, p−1) = 1 multiplicatively, p ∤ k additively"⟩,
    ⟨"repair-atlas-3d.svg", "Every error of the scan, repaired",
      "the 18 sizes q ≤ 1824 whose orbit product is not a retraction"⟩,
    ⟨"retraction-analogy.svg", "The analogy",
      "A ↪ B → A with r ∘ ι = id, once for Z(G) ⊆ G and once for 𝔽ₚ ⊆ GF(q)"⟩,
    ⟨"frobenius-clock.svg", "The Frobenius clock of GF(27)",
      "GF(27)ˣ = ℤ/26 with Frobenius e ↦ 3e; fixed points 0 and 13 are 𝔽₃ˣ"⟩,
    ⟨"frobenius-orbits.svg", "Frobenius orbits in GF(27)",
      "three fixed points and eight 3-cycles"⟩,
    ⟨"frobenius-norm-retraction.svg", "The orbit product as a retraction",
      "N(x) = x·x³·x⁹ = x¹³ collapses GF(27) onto 𝔽₃"⟩,
    ⟨"gf9-error-repair.svg", "The smallest error, and its repair",
      "GF(9): N(2) = 1 is the whole error, and R(x) = 2(x + x³) repairs it"⟩,
    ⟨"frobenius-defect-heatmap.svg", "How far from a retraction?",
      "the error of GF(pᵏ) as a heat map in (p, k), green on k ≡ 1 mod p−1"⟩,
    ⟨"frobenius-defect-3d.svg", "The error surface",
      "the same error as a solid bar over each (p, k)"⟩,
    ⟨"field-size-scan.svg", "Every size q = 2 … 97, tested",
      "one column per candidate size: no field, retraction, or an error bar"⟩,
    ⟨"field-size-scan-degrees.svg", "The same scan by degree",
      "four panels, one per characteristic, error against the degree n"⟩,
    ⟨"center-retraction.svg", "The group-theoretic zoo",
      "which families of groups retract onto their centre"⟩ ]

/-- The atlas has exactly one entry per row of the expanded triangle. -/
theorem atlas_length : atlas.length = drawnRows := by decide

/-- No picture is indexed twice. -/
theorem atlas_files_nodup : (atlas.map Entry.file).Nodup := by decide

/-- The `GF(27)` label of row `n`: its three base-`3` digits, read as `c₀ + c₁t + c₂t²`. -/
def rowLabel (n : Nat) : Nat × Nat × Nat := (n % 3, n / 3 % 3, n / 9 % 3)

/-- The 27 rows carry the 27 distinct elements of `GF(27)`, so the index is a bijection between
the rows of the triangle and the elements of the field the project is built around. -/
theorem rowLabel_nodup : ((List.range drawnRows).map rowLabel).Nodup := by decide

/-- Reading the digits back gives the row again. -/
theorem rowLabel_reconstruct :
    ∀ n ∈ List.range drawnRows,
      (rowLabel n).1 + 3 * (rowLabel n).2.1 + 9 * (rowLabel n).2.2 = n := by decide

end PascalAtlas

import Mathlib
import RequestProject.Tesla369

/-!
# The trinity in an arbitrary base, and the vortex

Tesla's `3, 6, 9` is a statement about base ten, and the earlier files proved it there.  What
comes next is the obvious question: *what is the trinity of an arbitrary base?*

The answer is that nothing about ten matters except that `10 - 1 = 9` and `3 ∣ 9`.  In base `b`
the digital root is taken modulo `b - 1`, and for each divisor `d` of `b - 1` the digits
`d, 2d, …, b-1` form a "trinity" which detects divisibility by `d` exactly.  Base ten is
distinguished only in that its *three*-element such set detects an odd prime, and it is the
smallest base for which that happens.

Main results:

* `digitalRootBase`, `digitalRootBase_ten` : the base-`b` digital root, agreeing with
  `Tesla369.digitalRoot` at `b = 10`.
* `digitalRootBase_digitsSum` : casting out `(b-1)`s.
* `dvd_digitalRootBase_iff` : for `d ∣ b - 1`, `d ∣ dr_b n ↔ d ∣ n`.
* `mem_trinityBase_iff` : `dr_b n ∈ trinityBase b d ↔ d ∣ n`, the general form of
  `Tesla369.digitalRoot_mem_trinity_iff`.
* `card_trinityBase` : the base-`b` trinity of `d` has exactly `(b-1)/d` elements; so a
  three-element trinity exists iff `b ≡ 1 [MOD 3]` (`exists_trinity_card_three_iff`).
* `base_ten_least_odd_prime_trinity` : ten is the least base whose three-element trinity
  detects an odd prime.
* `digitalRootBase_pow_period`, `digitalRootBase_pow_notMem_trinityBase` : the general
  doubling circuit and the general reason it misses the trinity.
* `vortexOrbit_zero`, `vortexOrbit_three`, `vortexOrbit_one`, `vortex_orbits_partition` :
  the doubling map on `ZMod 9` has exactly three orbits, of sizes `1`, `2` and `6` — the
  fixed point `0`, the flip `3 ↔ 6`, and the circuit `1,2,4,8,7,5`.  This is the whole
  "vortex" picture, proved.
-/

namespace Tesla369

/-- The digital root of `n` in base `b`: `0` at `0`, and `1 + (n-1) % (b-1)` otherwise. -/
def digitalRootBase (b n : ℕ) : ℕ := if n = 0 then 0 else (n - 1) % (b - 1) + 1

/-- The base-`b` trinity attached to a divisor `d` of `b - 1`: the digits `d, 2d, …, b-1`. -/
def trinityBase (b d : ℕ) : Finset ℕ := (Finset.Icc 1 (b - 1)).filter (fun x => d ∣ x)

@[simp] lemma digitalRootBase_zero (b : ℕ) : digitalRootBase b 0 = 0 := rfl

lemma digitalRootBase_of_pos {b n : ℕ} (hn : 0 < n) :
    digitalRootBase b n = (n - 1) % (b - 1) + 1 := by
  simp [digitalRootBase, hn.ne']

/-- At `b = 10` this is Tesla's digital root. -/
@[simp] lemma digitalRootBase_ten (n : ℕ) : digitalRootBase 10 n = digitalRoot n := rfl

lemma digitalRootBase_pos {b n : ℕ} (hn : 0 < n) : 0 < digitalRootBase b n := by
  simp [digitalRootBase_of_pos hn]

lemma digitalRootBase_le {b n : ℕ} (hb : 2 ≤ b) : digitalRootBase b n ≤ b - 1 := by
  unfold digitalRootBase
  split
  · omega
  · have := Nat.mod_lt (n - 1) (show 0 < b - 1 by omega)
    omega

/-- The base-`b` digital root is congruent to `n` modulo `b - 1`. -/
lemma digitalRootBase_modEq (b n : ℕ) : digitalRootBase b n ≡ n [MOD b - 1] := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · rw [digitalRootBase_of_pos hn]
    have h := (Nat.mod_modEq (n - 1) (b - 1)).add_right 1
    have hn' : n - 1 + 1 = n := by omega
    rwa [hn'] at h

lemma sub_one_modEq {m x y : ℕ} (hx : 0 < x) (hy : 0 < y) (h : x ≡ y [MOD m]) :
    x - 1 ≡ y - 1 [MOD m] := by
  rw [Nat.modEq_iff_dvd] at h ⊢
  have hx' : ((x - 1 : ℕ) : ℤ) = (x : ℤ) - 1 := by push_cast [Nat.cast_sub hx]; ring
  have hy' : ((y - 1 : ℕ) : ℤ) = (y : ℤ) - 1 := by push_cast [Nat.cast_sub hy]; ring
  rw [hx', hy']
  simpa using h

/-- Two numbers congruent mod `b - 1`, simultaneously zero or not, have the same base-`b`
digital root. -/
lemma digitalRootBase_congr {b x y : ℕ} (h : x ≡ y [MOD b - 1]) (h0 : x = 0 ↔ y = 0) :
    digitalRootBase b x = digitalRootBase b y := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [h0.mp rfl]
  · have hy : 0 < y := Nat.pos_of_ne_zero (fun hy => by simp [hy] at h0; omega)
    rw [digitalRootBase_of_pos hx, digitalRootBase_of_pos hy]
    exact congrArg (· + 1) (sub_one_modEq hx hy h)

/-- **Casting out `(b-1)`s.** Summing the base-`b` digits does not change the base-`b`
digital root. -/
theorem digitalRootBase_digitsSum {b : ℕ} (hb : 3 ≤ b) (n : ℕ) :
    digitalRootBase b ((Nat.digits b n).sum) = digitalRootBase b n := by
  have hmod : b % (b - 1) = 1 := by
    have hbb : b = (b - 1) + 1 := by omega
    nth_rewrite 1 [hbb]
    rw [Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega)
  refine digitalRootBase_congr (Nat.modEq_digits_sum (b - 1) b hmod n).symm ?_
  constructor
  · intro h
    by_contra hn
    have hne : Nat.digits b n ≠ [] := (Nat.digits_ne_nil_iff_ne_zero (b := b)).mpr hn
    have hlast := Nat.getLast_digit_ne_zero b hn
    have hmem : (Nat.digits b n).getLast hne ∈ Nat.digits b n := List.getLast_mem hne
    have hsum : 0 < (Nat.digits b n).sum :=
      Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hlast)
        (List.single_le_sum (by intro x _; exact Nat.zero_le x) _ hmem)
    omega
  · rintro rfl; simp

/-- **The trinity of a base, in one line.** If `d` divides `b - 1` then the base-`b` digital
root detects divisibility by `d` exactly. -/
theorem dvd_digitalRootBase_iff {b d n : ℕ} (hd : d ∣ b - 1) :
    d ∣ digitalRootBase b n ↔ d ∣ n := by
  have h : digitalRootBase b n ≡ n [MOD d] := (digitalRootBase_modEq b n).of_dvd hd
  constructor
  · intro hdvd
    exact Nat.modEq_zero_iff_dvd.mp (h.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))
  · intro hdvd
    exact Nat.modEq_zero_iff_dvd.mp (h.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))

lemma mem_trinityBase_iff_of_pos {b d n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) :
    digitalRootBase b n ∈ trinityBase b d ↔ d ∣ digitalRootBase b n := by
  simp only [trinityBase, Finset.mem_filter, Finset.mem_Icc, and_iff_right_iff_imp]
  intro _
  exact ⟨digitalRootBase_pos hn, digitalRootBase_le hb⟩

/-- **The general trinity theorem.**  For `d ∣ b - 1` and `n > 0`, the base-`b` digital root of
`n` lies in the trinity `{d, 2d, …, b-1}` exactly when `d ∣ n`.  At `b = 10`, `d = 3` this is
`digitalRoot_mem_trinity_iff`. -/
theorem mem_trinityBase_iff {b d n : ℕ} (hb : 2 ≤ b) (hd : d ∣ b - 1) (hn : 0 < n) :
    digitalRootBase b n ∈ trinityBase b d ↔ d ∣ n := by
  rw [mem_trinityBase_iff_of_pos hb hn, dvd_digitalRootBase_iff hd]

/-- Base ten, `d = 3`: the trinity of the base really is `{3, 6, 9}`. -/
theorem trinityBase_ten : trinityBase 10 3 = trinity := by decide

/-- The base-`b` trinity attached to `d` has exactly `(b-1)/d` elements. -/
theorem card_trinityBase (b d : ℕ) : (trinityBase b d).card = (b - 1) / d := by
  have hIcc : Finset.Icc 1 (b - 1) = Finset.Ioc 0 (b - 1) := rfl
  rw [trinityBase, hIcc]
  exact Nat.Ioc_filter_dvd_card_eq_div _ _

/-- **A three-element trinity exists exactly in the bases `b ≡ 1 [MOD 3]`.**  Ten is such a
base; so are `4`, `7`, `13`, …. -/
theorem exists_trinity_card_three_iff {b : ℕ} (hb : 2 ≤ b) :
    (∃ d, d ∣ b - 1 ∧ (trinityBase b d).card = 3) ↔ 3 ∣ b - 1 := by
  constructor
  · rintro ⟨d, hd, hcard⟩
    rw [card_trinityBase] at hcard
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · simp at hcard
      · exact h
    rw [Nat.div_eq_iff_eq_mul_left hd0 hd] at hcard
    exact ⟨d, by omega⟩
  · intro h
    refine ⟨(b - 1) / 3, Nat.div_dvd_of_dvd h, ?_⟩
    obtain ⟨c, hc⟩ := h
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with rfl | h'
      · omega
      · exact h'
    rw [card_trinityBase, hc, Nat.mul_div_cancel_left c (by norm_num),
      Nat.mul_div_cancel _ hc0]

/-- **Why ten.**  Ten is the least base whose three-element trinity detects an *odd prime*:
for `b < 10` no divisor `d` of `b-1` is an odd prime with `(b-1)/d = 3`, while `b = 10`,
`d = 3` works.  (In base `4` the trinity is `{1,2,3}`, detecting nothing; in base `7` it is
`{2,4,6}`, detecting only parity.) -/
theorem base_ten_least_odd_prime_trinity :
    (∃ d, d ∣ 10 - 1 ∧ (trinityBase 10 d).card = 3 ∧ Nat.Prime d ∧ Odd d) ∧
      ∀ b < 10, ¬ ∃ d, d ∣ b - 1 ∧ (trinityBase b d).card = 3 ∧ Nat.Prime d ∧ Odd d := by
  refine ⟨⟨3, by norm_num, by decide, by norm_num, by decide⟩, ?_⟩
  rintro b hb ⟨d, hd, hcard, hp, hodd⟩
  rw [card_trinityBase] at hcard
  rw [Nat.div_eq_iff_eq_mul_left hp.pos hd] at hcard
  have h2 : 2 ≤ d := hp.two_le
  have hne : d ≠ 2 := by rintro rfl; exact (Nat.not_odd_iff_even.mpr (by decide)) hodd
  omega

/-! ### Digital-root arithmetic

The computational engine behind "vortex" calculations: digital roots may be taken before or
after adding and multiplying. -/

/-- Digital roots may be taken before adding. -/
theorem digitalRootBase_add {b x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
    digitalRootBase b (x + y) = digitalRootBase b (digitalRootBase b x + digitalRootBase b y) := by
  refine (digitalRootBase_congr ?_ ?_).symm
  · exact (digitalRootBase_modEq b x).add (digitalRootBase_modEq b y)
  · have h1 := digitalRootBase_pos (b := b) hx
    have h2 := digitalRootBase_pos (b := b) hy
    omega

/-- Digital roots may be taken before multiplying. -/
theorem digitalRootBase_mul {b x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
    digitalRootBase b (x * y) = digitalRootBase b (digitalRootBase b x * digitalRootBase b y) := by
  refine (digitalRootBase_congr ?_ ?_).symm
  · exact (digitalRootBase_modEq b x).mul (digitalRootBase_modEq b y)
  · have h1 := digitalRootBase_pos (b := b) hx
    have h2 := digitalRootBase_pos (b := b) hy
    have : 0 < x * y := Nat.mul_pos hx hy
    constructor
    · intro h; exact absurd h (Nat.mul_pos h1 h2).ne'
    · intro h; omega

/-- Decimal form: `dr (x + y) = dr (dr x + dr y)`. -/
theorem digitalRoot_add {x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
    digitalRoot (x + y) = digitalRoot (digitalRoot x + digitalRoot y) := by
  simpa using digitalRootBase_add (b := 10) hx hy

/-- Decimal form: `dr (x * y) = dr (dr x * dr y)`. -/
theorem digitalRoot_mul {x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
    digitalRoot (x * y) = digitalRoot (digitalRoot x * digitalRoot y) := by
  simpa using digitalRootBase_mul (b := 10) hx hy

/-- The digital root is the reduction mod `9`, read in `ZMod 9`: the map `n ↦ dr n` is compatible
with the ring homomorphism `ℕ → ZMod 9`. -/
theorem digitalRoot_cast (n : ℕ) : ((digitalRoot n : ℕ) : ZMod 9) = (n : ZMod 9) :=
  (ZMod.natCast_eq_natCast_iff _ _ _).mpr (digitalRoot_modEq n)

/-! ### The general doubling circuit -/

/-- **The general period theorem.**  If `a ^ t ≡ 1` modulo `b - 1`, the base-`b` digital roots
of the powers of `a` repeat with period `t`.  Base ten, `a = 2`, `t = 6` (since `64 ≡ 1 mod 9`)
is the vortex circuit `1, 2, 4, 8, 7, 5`. -/
theorem digitalRootBase_pow_period {b a t : ℕ} (ha : 0 < a) (ht : a ^ t ≡ 1 [MOD b - 1])
    (n : ℕ) : digitalRootBase b (a ^ (n + t)) = digitalRootBase b (a ^ n) := by
  refine digitalRootBase_congr ?_ ?_
  · rw [pow_add a n t]
    simpa using ht.mul_left (a ^ n)
  · have h1 : 0 < a ^ (n + t) := pow_pos ha _
    have h2 : 0 < a ^ n := pow_pos ha _
    omega

/-- **The general reason the circuit misses the trinity.**  If `a` is coprime to `d` and
`d > 1`, no power of `a` has base-`b` digital root in the trinity of `d`.  Base ten, `a = 2`,
`d = 3` is `digitalRoot_two_pow_notMem_trinity`. -/
theorem digitalRootBase_pow_notMem_trinityBase {b a d : ℕ} (hb : 2 ≤ b) (ha : 0 < a)
    (hd1 : 1 < d) (hd : d ∣ b - 1) (hcop : Nat.Coprime a d) (n : ℕ) :
    digitalRootBase b (a ^ n) ∉ trinityBase b d := by
  rw [mem_trinityBase_iff hb hd (pow_pos ha n)]
  intro hdvd
  have hcopn : Nat.Coprime (a ^ n) d := hcop.pow_left n
  have hg : d ∣ Nat.gcd (a ^ n) d := Nat.dvd_gcd hdvd dvd_rfl
  rw [hcopn] at hg
  exact absurd (Nat.le_of_dvd one_pos hg) (by omega)

/-! ### The vortex: orbits of doubling on `ZMod 9` -/

/-- The doubling orbit of `x` in `ZMod 9`. -/
def vortexOrbit (x : ZMod 9) : Finset (ZMod 9) := (Finset.range 6).image (fun k => 2 ^ k * x)

theorem vortexOrbit_zero : vortexOrbit 0 = {0} := by decide

theorem vortexOrbit_three : vortexOrbit 3 = {3, 6} := by decide

theorem vortexOrbit_one : vortexOrbit 1 = {1, 2, 4, 8, 7, 5} := by decide

/-- **The vortex diagram.**  Doubling on `ZMod 9` has exactly three orbits: the fixed point
`{0}`, the two-element trinity orbit `{3,6}`, and the six-element circuit `{1,2,4,8,7,5}`.
They are pairwise disjoint and cover everything. -/
theorem vortex_orbits_partition :
    (Disjoint (vortexOrbit 0) (vortexOrbit 3) ∧ Disjoint (vortexOrbit 0) (vortexOrbit 1) ∧
        Disjoint (vortexOrbit 3) (vortexOrbit 1)) ∧
      vortexOrbit 0 ∪ vortexOrbit 3 ∪ vortexOrbit 1 = Finset.univ := by
  decide

/-- Every element of `ZMod 9` has one of the three orbits as its orbit. -/
theorem vortexOrbit_eq (x : ZMod 9) :
    vortexOrbit x = vortexOrbit 0 ∨ vortexOrbit x = vortexOrbit 3 ∨
      vortexOrbit x = vortexOrbit 1 := by
  revert x; decide

/-- The orbits have sizes `1`, `2`, `6` — a partition of `9 = 1 + 2 + 6`. -/
theorem vortex_orbit_cards :
    (vortexOrbit 0).card = 1 ∧ (vortexOrbit 3).card = 2 ∧ (vortexOrbit 1).card = 6 := by
  decide

/-- The unit orbit is exactly the group of units: doubling acts transitively on `(ZMod 9)ˣ`,
so the six-step circuit is a full cycle through the invertible residues, and the trinity is
precisely what is left over. -/
theorem vortexOrbit_one_eq_units :
    vortexOrbit 1 = Finset.univ.filter (fun x : ZMod 9 => IsUnit x) := by decide

end Tesla369

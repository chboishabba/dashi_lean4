import Mathlib
import RequestProject.Hecke23

/-!
# From `{2, 3}` to all primes: multiplicative closure of a Hecke system

`RequestProject.Hecke23` shows that the two eigenvalues `a 2` and `a 3` determine `a n` for every
`3`-smooth `n`.  Here we close the obvious gap: the same argument, run over an arbitrary set of
primes `S`, shows that the eigenvalues `a p` for `p ∈ S` determine `a n` for every positive
`S`-smooth `n` (`Hecke23.eq_on_Smooth`).  Two corollaries are worth stating separately:

* **Full multiplicative closure** (`Hecke23.eq_of_eq_on_primes`): two Hecke systems of the same
  weight that agree at *every* prime agree at every positive integer.  (Nothing can be said at
  `n = 0`: the axioms say nothing about `a 0`, and `Hecke23.a_zero_undetermined` records this.)
* **Finite truncation** (`Hecke23.eq_on_le_of_eq_on_primes_le`): agreement at the primes `p ≤ N`
  already forces agreement at every `n ≤ N`.  This is the honest, purely algebraic shadow of
  multiplicity one: finitely many eigenvalues pin down an arbitrarily long initial segment of the
  sequence, with no analysis involved.  (The genuine multiplicity-one theorem — finitely many
  eigenvalues pin down *all* of them — is a theorem of analytic number theory and is not proved
  here.)
-/

namespace Hecke23

variable {R : Type*} [CommRing R] {k : ℕ} {a b : ℕ → R}

/-- The `S`-smooth numbers: the positive integers all of whose prime factors lie in `S`.  For
`S = {2, 3}` this is `Hecke23.Smooth3`. -/
def Smooth (S : Set ℕ) : Set ℕ := {n | n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p ∈ S}

/-- **Multiplicative closure.**  If two Hecke systems of the same weight agree at every prime of
`S`, they agree at every positive integer built out of the primes of `S`. -/
theorem eq_of_primeFactors_subset (ha : HeckeSystem k a) (hb : HeckeSystem k b) {S : Set ℕ}
    (hS : ∀ p : ℕ, p.Prime → p ∈ S → a p = b p) :
    ∀ n : ℕ, n ≠ 0 → (∀ p ∈ n.primeFactors, p ∈ S) → a n = b n := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p m hp hm =>
      intro _ hfac
      have hpS : p ∈ S := by
        refine hfac p ?_
        rw [Nat.primeFactors_prime_pow hm.ne' hp]
        simp
      exact eq_on_prime_pow ha hb hp (hS p hp hpS) m
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; simpa using ha.one.trans hb.one.symm
  | coprime x y hx hy hcop ihx ihy =>
      intro _ hfac
      have hx0 : x ≠ 0 := by omega
      have hy0 : y ≠ 0 := by omega
      have hunion : (x * y).primeFactors = x.primeFactors ∪ y.primeFactors :=
        Nat.primeFactors_mul hx0 hy0
      rw [ha.mul_coprime x y hcop, hb.mul_coprime x y hcop,
        ihx hx0 (fun p hp => hfac p (by rw [hunion]; exact Finset.mem_union_left _ hp)),
        ihy hy0 (fun p hp => hfac p (by rw [hunion]; exact Finset.mem_union_right _ hp))]

/-- The `S`-smooth version of `Hecke23.eq_on_Smooth3`. -/
theorem eq_on_Smooth (ha : HeckeSystem k a) (hb : HeckeSystem k b) {S : Set ℕ}
    (hS : ∀ p : ℕ, p.Prime → p ∈ S → a p = b p) : Set.EqOn a b (Smooth S) := by
  rintro n ⟨hn, hfac⟩
  exact eq_of_primeFactors_subset ha hb hS n hn hfac

/-- **Agreement at all primes is agreement everywhere.**  Two Hecke systems of the same weight
with the same eigenvalue at every prime have the same eigenvalue at every positive integer. -/
theorem eq_of_eq_on_primes (ha : HeckeSystem k a) (hb : HeckeSystem k b)
    (hS : ∀ p : ℕ, p.Prime → a p = b p) {n : ℕ} (hn : n ≠ 0) : a n = b n :=
  eq_of_primeFactors_subset ha hb (fun p hp _ => hS p hp) n hn (fun _ _ => trivial)

/-- **Finite truncation / baby multiplicity one.**  Agreement at the finitely many primes `p ≤ N`
forces agreement at every `n ≤ N`. -/
theorem eq_on_le_of_eq_on_primes_le (ha : HeckeSystem k a) (hb : HeckeSystem k b) {N : ℕ}
    (hS : ∀ p : ℕ, p.Prime → p ≤ N → a p = b p) {n : ℕ} (hn : n ≠ 0) (hnN : n ≤ N) :
    a n = b n := by
  refine eq_of_primeFactors_subset ha hb (S := {p | p ≤ N}) (fun p hp hpN => hS p hp hpN) n hn ?_
  intro p hp
  exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_primeFactors hp)) hnN

/-- **Weak multiplicity one for a finite family.**  Given finitely many Hecke systems of a fixed
weight, there is a single bound `N` such that agreement at the primes `p ≤ N` already forces two
members of the family to be equal at every positive integer.  This is a pigeonhole statement, not
an analytic one: the bound is extracted from the finitely many places where the members differ,
and nothing here gives an effective `N` in terms of the weight.  (The genuine multiplicity-one /
Sturm-bound theorems, which do give an effective `N`, are analytic and are not proved here.) -/
theorem exists_separating_bound {ι : Type*} [Fintype ι] (A : ι → ℕ → R)
    (hA : ∀ i, HeckeSystem k (A i)) :
    ∃ N : ℕ, ∀ i j : ι, (∀ p : ℕ, p.Prime → p ≤ N → A i p = A j p) →
      ∀ n : ℕ, n ≠ 0 → A i n = A j n := by
  classical
  set w : ι → ι → ℕ := fun i j =>
    if h : ∃ n : ℕ, n ≠ 0 ∧ A i n ≠ A j n then h.choose else 0 with hw
  refine ⟨Finset.univ.sup (fun q : ι × ι => w q.1 q.2), fun i j hij n hn => ?_⟩
  by_contra hne
  have hex : ∃ n : ℕ, n ≠ 0 ∧ A i n ≠ A j n := ⟨n, hn, hne⟩
  have hchoose := hex.choose_spec
  have hwij : w i j = hex.choose := by rw [hw]; simp [hex]
  have hle : w i j ≤ Finset.univ.sup (fun q : ι × ι => w q.1 q.2) :=
    Finset.le_sup (f := fun q : ι × ι => w q.1 q.2) (Finset.mem_univ (i, j))
  exact hchoose.2 (eq_on_le_of_eq_on_primes_le (hA i) (hA j) hij hchoose.1 (hwij ▸ hle))

/-- **`a 0` really is undetermined**, so the restriction to `n ≠ 0` above cannot be dropped:
changing the value of a Hecke system at `0` to an arbitrary `c` gives a Hecke system again. -/
theorem a_zero_undetermined (ha : HeckeSystem k a) (c : R) :
    HeckeSystem k (Function.update a 0 c) ∧
      ∀ n : ℕ, n ≠ 0 → Function.update a 0 c n = a n := by
  have hne : ∀ n : ℕ, n ≠ 0 → Function.update a 0 c n = a n := fun n hn =>
    Function.update_of_ne hn _ _
  refine ⟨⟨?_, ?_, ?_⟩, hne⟩
  · rw [hne 1 one_ne_zero]; exact ha.one
  · intro m n h
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hn : n = 1 := by simpa [Nat.Coprime] using h
      subst hn
      simp [ha.one]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hm1 : m = 1 := by simpa [Nat.Coprime] using h
      subst hm1
      simp [ha.one]
    rw [hne _ (by positivity), hne _ hm.ne', hne _ hn.ne']
    exact ha.mul_coprime m n h
  · intro p hp j
    have hp0 : 0 < p := hp.pos
    rw [hne _ (by positivity), hne _ (by positivity), hne _ (by positivity),
      hne _ (by positivity)]
    exact ha.prime_pow p hp j

/-- The `3`-smooth numbers are the `S`-smooth numbers for `S = {2, 3}`. -/
theorem Smooth3_eq : Smooth3 = Smooth {2, 3} := by
  ext n
  constructor
  · rintro ⟨i, j, rfl⟩
    refine ⟨by positivity, ?_⟩
    intro p hp
    have hpd : p ∣ 2 ^ i * 3 ^ j := Nat.dvd_of_mem_primeFactors hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    rcases (Nat.Prime.dvd_mul hpp).1 hpd with h | h
    · left; exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow h)
    · right; exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 (hpp.dvd_of_dvd_pow h)
  · rintro ⟨hn0, hfac⟩
    refine ⟨n.factorization 2, n.factorization 3, ?_⟩
    have : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
      (Nat.factorization_prod_pow_eq_self hn0).symm
    have hsub : n.primeFactors ⊆ ({2, 3} : Finset ℕ) := by
      intro p hp
      have := hfac p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      simpa using this
    calc n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := this
      _ = ∏ p ∈ ({2, 3} : Finset ℕ), p ^ n.factorization p :=
          Finset.prod_subset hsub (by
            intro p _ hp
            rw [← Nat.support_factorization] at hp
            rw [Finsupp.notMem_support_iff.mp hp, pow_zero])
      _ = 2 ^ n.factorization 2 * 3 ^ n.factorization 3 := by norm_num

end Hecke23

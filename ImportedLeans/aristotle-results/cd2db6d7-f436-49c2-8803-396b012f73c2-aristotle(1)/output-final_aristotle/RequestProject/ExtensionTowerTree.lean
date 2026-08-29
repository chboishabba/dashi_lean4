import Mathlib
import RequestProject.PascalTower

/-!
# Stage 2 of the tower: the degree tree, and the `GF` extension tower on top of it

`RequestProject/PascalTower.lean` built the triangle.  This file builds the other two objects of
the construction, again starting from the smallest one and growing:

**The tree.**  Its nodes are the *degrees* `1, 2, 3, 4, …`, its root is the degree `1`, and the
parent of a degree is obtained by deleting its largest prime factor
(`ExtensionTower.parent`, `ExtensionTower.parent_mul_topPrime`).  So the children of `n` are the
`n * q` with `q` a prime at least as large as every prime factor of `n`, each degree occurs at
depth `Ω n` — the number of prime factors of `n` counted with multiplicity
(`ExtensionTower.bigOmega_parent`) — and the tree is exhausted level by level, smallest first.

* `ExtensionTower.chain` — the path from the root down to `n`, e.g. `chain 12 = [1, 2, 4, 12]`.
* `ExtensionTower.chain_head`, `chain_getLast`, `chain_length`, `chain_isChain_dvd` — the path
  starts at `1`, ends at `n`, has `Ω n + 1` entries, and each entry divides the next.

**The field tower.**  Over a prime `p`, degree `n` carries the field `GF(pⁿ)` (Mathlib's
`GaloisField p n`), and the tree edges become field extensions:

* `ExtensionTower.card_galoisField` — `|GF(pⁿ)| = pⁿ`.
* `ExtensionTower.nonempty_algHom_iff_dvd` — `GF(pᵐ)` embeds into `GF(pⁿ)` exactly when `m ∣ n`,
  so the ancestors of `n` in the tree really are subfields of `GF(pⁿ)`
  (`ExtensionTower.nonempty_algHom_of_chain_le`).
* `ExtensionTower.floor` — the *factorial tower* `GF(p^{0!}) ⊆ GF(p^{1!}) ⊆ GF(p^{2!}) ⊆ ⋯`, a
  single increasing chain, starting at the prime field, which eventually contains every finite
  field of characteristic `p` (`ExtensionTower.nonempty_algHom_floor`,
  `ExtensionTower.exists_floor_containing`).

**Back to the triangle.**  The Gaussian triangle of `PascalTower` is the triangle of this tower:
`ExtensionTower.card_projectivization_eq_gauss` shows that `[n choose 1]_q` is the number of
lines in `GF(q)ⁿ`, for every field of the tower.
-/

namespace ExtensionTower

open Nat
open scoped LinearAlgebra.Projectivization

/-! ## The degree tree -/

/-- `Ω n`: the number of prime factors of `n`, with multiplicity.  This is the depth of `n` in the
degree tree. -/
def bigOmega (n : Nat) : Nat := n.primeFactorsList.length

@[simp] theorem bigOmega_one : bigOmega 1 = 0 := by simp [bigOmega]

theorem bigOmega_prime {q : Nat} (hq : q.Prime) : bigOmega q = 1 := by
  simp [bigOmega, Nat.primeFactorsList_prime hq]

/-- A sorted list of primes is the factor list of its product. -/
theorem sorted_prime_list_eq (l : List Nat) (hs : List.Pairwise (· ≤ ·) l)
    (hp : ∀ q ∈ l, Nat.Prime q) : l = (l.prod).primeFactorsList := by
  refine List.Perm.eq_of_pairwise ?_ hs
    (List.sortedLE_iff_pairwise.mp (Nat.primeFactorsList_sorted _))
    (Nat.primeFactorsList_unique rfl hp)
  intro a b _ _ hab hba
  exact le_antisymm hab hba

theorem primeFactorsList_ne_nil {n : Nat} (hn : 2 ≤ n) : n.primeFactorsList ≠ [] := by
  intro h
  have hp := Nat.prod_primeFactorsList (n := n) (by omega)
  rw [h] at hp
  simp at hp
  omega

/-- The largest prime factor of `n` (and `1` for `n ≤ 1`): the step from `n` up from its parent in
the degree tree. -/
def topPrime (n : Nat) : Nat := (n.primeFactorsList.getLast?).getD 1

/-- The parent of `n` in the degree tree: `n` with its largest prime factor deleted. -/
def parent (n : Nat) : Nat := n.primeFactorsList.dropLast.prod

@[simp] theorem parent_one : parent 1 = 1 := by simp [parent]

theorem topPrime_eq_getLast {n : Nat} (hn : n.primeFactorsList ≠ []) :
    topPrime n = n.primeFactorsList.getLast hn := by
  rw [topPrime, List.getLast?_eq_some_getLast (h := hn)]
  rfl

theorem topPrime_prime {n : Nat} (hn : 2 ≤ n) : (topPrime n).Prime := by
  have hne := primeFactorsList_ne_nil hn
  rw [topPrime_eq_getLast hne]
  exact Nat.prime_of_mem_primeFactorsList (List.getLast_mem hne)

/-- The defining equation of the tree edge: `parent n · topPrime n = n`. -/
theorem parent_mul_topPrime {n : Nat} (hn : 2 ≤ n) : parent n * topPrime n = n := by
  have hne := primeFactorsList_ne_nil hn
  have h : n.primeFactorsList.dropLast ++ [n.primeFactorsList.getLast hne] = n.primeFactorsList :=
    List.dropLast_append_getLast hne
  rw [parent, topPrime_eq_getLast hne]
  calc n.primeFactorsList.dropLast.prod * n.primeFactorsList.getLast hne
      = (n.primeFactorsList.dropLast ++ [n.primeFactorsList.getLast hne]).prod := by simp
    _ = n.primeFactorsList.prod := by rw [h]
    _ = n := Nat.prod_primeFactorsList (by omega)

theorem primeFactorsList_parent (n : Nat) :
    (parent n).primeFactorsList = n.primeFactorsList.dropLast := by
  refine (sorted_prime_list_eq _ ?_ ?_).symm
  · exact (List.sortedLE_iff_pairwise.mp (Nat.primeFactorsList_sorted n)).sublist
      (List.dropLast_sublist _)
  · intro q hq
    exact Nat.prime_of_mem_primeFactorsList (List.dropLast_subset _ hq)

/-- The parent sits one level closer to the root. -/
theorem bigOmega_parent {n : Nat} (hn : 2 ≤ n) : bigOmega (parent n) + 1 = bigOmega n := by
  have hne := primeFactorsList_ne_nil hn
  rw [bigOmega, bigOmega, primeFactorsList_parent, List.length_dropLast]
  have : 0 < n.primeFactorsList.length := List.length_pos_iff.mpr hne
  omega

theorem parent_dvd (n : Nat) : parent n ∣ n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp [parent]
  · exact ⟨topPrime n, (parent_mul_topPrime h).symm ▸ rfl⟩

theorem parent_pos {n : Nat} (hn : 0 < n) : 0 < parent n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    simp
  · have := parent_mul_topPrime h
    rcases Nat.eq_zero_or_pos (parent n) with h0 | h0
    · rw [h0] at this; simp at this; omega
    · exact h0

theorem parent_lt {n : Nat} (hn : 2 ≤ n) : parent n < n := by
  have hmul := parent_mul_topPrime hn
  have hq := topPrime_prime hn
  have h2 : 2 ≤ topPrime n := hq.two_le
  have hp : 0 < parent n := parent_pos (by omega)
  nlinarith [hmul, h2, hp]

/-- The path in the degree tree from the root `1` down to `n`, root first. -/
def chain : Nat → List Nat
  | 0 => [1]
  | 1 => [1]
  | n + 2 =>
      have : parent (n + 2) < n + 2 := parent_lt (by omega)
      chain (parent (n + 2)) ++ [n + 2]
  decreasing_by exact this

@[simp] theorem chain_zero : chain 0 = [1] := by rw [chain]
@[simp] theorem chain_one : chain 1 = [1] := by rw [chain]

theorem chain_succ_succ (n : Nat) : chain (n + 2) = chain (parent (n + 2)) ++ [n + 2] := by
  rw [chain]

theorem chain_of_two_le {n : Nat} (hn : 2 ≤ n) : chain n = chain (parent n) ++ [n] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact chain_succ_succ m

theorem chain_ne_nil (n : Nat) : chain n ≠ [] := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp
    | 1, _ => simp
    | (m + 2), ih => rw [chain_succ_succ]; simp

/-- The path starts at the root. -/
theorem chain_head (n : Nat) : (chain n).head? = some 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp
    | 1, _ => simp
    | (m + 2), ih =>
      rw [chain_succ_succ]
      obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil (chain_ne_nil (parent (m + 2)))
      have hh := ih (parent (m + 2)) (parent_lt (by omega))
      rw [hal] at hh ⊢
      simpa using hh

/-- The path ends at `n`. -/
theorem chain_getLast {n : Nat} (hn : 0 < n) :
    (chain n).getLast (chain_ne_nil n) = n := by
  match n, hn with
  | 1, _ => rw [List.getLast_congr (chain_ne_nil 1) (by simp) chain_one]; simp
  | (m + 2), _ =>
    rw [List.getLast_congr (chain_ne_nil _) (by simp) (chain_succ_succ m)]; simp

/-- The path has one entry per level: `Ω n + 1` of them. -/
theorem chain_length {n : Nat} (hn : 0 < n) : (chain n).length = bigOmega n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, hn, ih with
    | 1, _, _ => simp
    | (m + 2), _, ih =>
      have hp : 0 < parent (m + 2) := parent_pos (by omega)
      rw [chain_succ_succ, List.length_append, ih _ (parent_lt (by omega)) hp]
      have := bigOmega_parent (n := m + 2) (by omega)
      simp
      omega

/-- Consecutive nodes on the path: each divides the next. -/
theorem chain_isChain_dvd (n : Nat) : List.IsChain (· ∣ ·) (chain n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp
    | 1, _ => simp
    | (m + 2), ih =>
      have hlt : parent (m + 2) < m + 2 := parent_lt (by omega)
      have hp : 0 < parent (m + 2) := parent_pos (by omega)
      rw [chain_succ_succ]
      refine List.isChain_append.mpr ⟨ih _ hlt, by simp, ?_⟩
      intro x hx y hy
      rw [List.getLast?_eq_some_getLast (h := chain_ne_nil _)] at hx
      simp only [Option.mem_def, Option.some.injEq] at hx hy
      have hy' : y = m + 2 := by simpa using hy.symm
      subst hy'
      rw [← hx, chain_getLast hp]
      exact parent_dvd (m + 2)

/-- Every node of the path divides `n`. -/
theorem dvd_of_mem_chain {n m : Nat} (hn : 0 < n) (hm : m ∈ chain n) : m ∣ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, hn, hm, ih with
    | 1, _, hm, _ => simp at hm; simp [hm]
    | (k + 2), _, hm, ih =>
      rw [chain_succ_succ] at hm
      rcases List.mem_append.mp hm with h | h
      · exact dvd_trans (ih _ (parent_lt (by omega)) (parent_pos (by omega)) h)
          (parent_dvd (k + 2))
      · simp at h; simp [h]

example : chain 12 = [1, 2, 4, 12] := by
  rw [chain_of_two_le (by norm_num), show parent 12 = 4 by simp [parent],
    chain_of_two_le (by norm_num), show parent 4 = 2 by simp [parent],
    chain_of_two_le (by norm_num), show parent 2 = 1 by simp [parent], chain_one]
  rfl

example : chain 27 = [1, 3, 9, 27] := by
  rw [chain_of_two_le (by norm_num), show parent 27 = 9 by simp [parent],
    chain_of_two_le (by norm_num), show parent 9 = 3 by simp [parent],
    chain_of_two_le (by norm_num), show parent 3 = 1 by simp [parent], chain_one]
  rfl

example : chain 30 = [1, 2, 6, 30] := by
  rw [chain_of_two_le (by norm_num), show parent 30 = 6 by simp [parent],
    chain_of_two_le (by norm_num), show parent 6 = 2 by simp [parent],
    chain_of_two_le (by norm_num), show parent 2 = 1 by simp [parent], chain_one]
  rfl

/-! ## The field tower over the tree -/

variable (p : Nat) [Fact p.Prime]

/-- The field attached to a node of the degree tree: `GF(pⁿ)`. -/
abbrev field (n : Nat) := GaloisField p n

theorem card_galoisField {n : Nat} (hn : n ≠ 0) : Nat.card (GaloisField p n) = p ^ n :=
  GaloisField.card p n hn

theorem finrank_galoisField {n : Nat} (hn : n ≠ 0) :
    Module.finrank (ZMod p) (GaloisField p n) = n :=
  GaloisField.finrank p hn

/-- The tree edges are field extensions: `GF(pᵐ)` embeds into `GF(pⁿ)` exactly when `m ∣ n`. -/
theorem nonempty_algHom_iff_dvd {m n : Nat} (hm : m ≠ 0) (hn : n ≠ 0) :
    Nonempty (GaloisField p m →ₐ[ZMod p] GaloisField p n) ↔ m ∣ n := by
  rw [FiniteField.nonempty_algHom_iff_finrank_dvd, finrank_galoisField p hm,
    finrank_galoisField p hn]

/-- Ancestors in the degree tree are subfields: every node of the path to `n` gives a subfield of
`GF(pⁿ)`. -/
theorem nonempty_algHom_of_chain_le {n m : Nat} (hn : 0 < n) (hm : 0 < m) (h : m ∈ chain n) :
    Nonempty (GaloisField p m →ₐ[ZMod p] GaloisField p n) :=
  (nonempty_algHom_iff_dvd p (by omega) (by omega)).mpr (dvd_of_mem_chain hn h)

/-! ### The factorial tower: one increasing chain, smallest field first -/

/-- The degree of the `n`-th floor of the tower: `n !`.  The floors are
`GF(p) = GF(p^{0!}) ⊆ GF(p^{1!}) ⊆ GF(p^{2!}) ⊆ GF(p^{3!}) ⊆ ⋯`. -/
def floorDeg (n : Nat) : Nat := n !

/-- The `n`-th floor of the extension tower. -/
abbrev floor (n : Nat) := GaloisField p (floorDeg n)

theorem floorDeg_pos (n : Nat) : 0 < floorDeg n := Nat.factorial_pos n

theorem floorDeg_dvd {m n : Nat} (h : m ≤ n) : floorDeg m ∣ floorDeg n :=
  Nat.factorial_dvd_factorial h

theorem card_floor (n : Nat) : Nat.card (floor p n) = p ^ (n !) :=
  GaloisField.card p _ (Nat.factorial_ne_zero n)

/-- The floors really do form an increasing tower. -/
theorem nonempty_algHom_floor {m n : Nat} (h : m ≤ n) :
    Nonempty (floor p m →ₐ[ZMod p] floor p n) :=
  (nonempty_algHom_iff_dvd p (Nat.factorial_ne_zero m) (Nat.factorial_ne_zero n)).mpr
    (floorDeg_dvd h)

/-- Every finite field of characteristic `p` shows up inside the tower: `GF(p^k)` sits inside the
`k`-th floor. -/
theorem exists_floor_containing (k : Nat) (hk : k ≠ 0) :
    Nonempty (GaloisField p k →ₐ[ZMod p] floor p k) :=
  (nonempty_algHom_iff_dvd p hk (Nat.factorial_ne_zero k)).mpr (Nat.dvd_factorial
    (Nat.pos_of_ne_zero hk) le_rfl)

/-! ## The triangle of the tower -/

/-- The second column of the Gaussian triangle counts the lines of `Kⁿ` for `K` any finite field:
`[n choose 1]_q` is the number of points of the projective space `ℙ(Kⁿ)`, `q = |K|`. -/
theorem card_projectivization_eq_gauss (K : Type*) [Field K] [Finite K] (n : Nat) :
    Nat.card (ℙ K (Fin n → K)) = PascalTower.gauss (Nat.card K) n 1 := by
  have hK : 1 < Nat.card K := Finite.one_lt_card
  have hcard : Nat.card (Fin n → K) = (Nat.card K) ^ n := by
    simp [Nat.card_fun]
  have hmain := Projectivization.card' K (Fin n → K)
  rw [hcard] at hmain
  have hg : PascalTower.gauss (Nat.card K) n 1 * (Nat.card K - 1) + 1 = (Nat.card K) ^ n :=
    PascalTower.gauss_one_mul_pred (Nat.card K) n (by omega)
  have h2 : Nat.card (ℙ K (Fin n → K)) * (Nat.card K - 1) + 1
      = PascalTower.gauss (Nat.card K) n 1 * (Nat.card K - 1) + 1 := by rw [← hmain, hg]
  exact Nat.eq_of_mul_eq_mul_right (by omega) (Nat.add_right_cancel h2)

end ExtensionTower

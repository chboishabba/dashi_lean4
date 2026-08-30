import RequestProject.Holograms
import RequestProject.Moonshine

/-!
# MoonshineAddress: the three-stage moonshine address pipeline

This module formalises the complete pipeline from a hash (representing any
content-addressed object) to a point in the **20 176-dimensional moonshine
lattice** ℤ^(194×104):

```
  Object  ─(Stage 1)─▶  ℤ¹⁵          (15-prime Monster address)
          ─(Stage 2)─▶  ℤ¹⁹⁴         (projection into 194 irreps via T₁)
          ─(Stage 3)─▶  ℤ^(194×104)  (expand along 104 T₁ q-coefficients)
```

## Stage 1 — 15-prime Monster address

`primeAddress h j` is the residue `h mod pⱼ` for each of the fifteen Monster
primes `p₀=71, p₁=59, …, p₁₄=2`.  This gives the genuine ℤ¹⁵ coordinate vector
rather than a 2D projection.

## Stage 2 — T₁ diagonal projection into 194 irreps

Each irrep `i` is *tuned* to exactly one Monster prime: prime `mp (i % 15)`.
The weight is the (i % 15 + 2)-th j-coefficient:

  `irrepWeight h i  =  jCoeff (i % 15 + 2)  ·  (h mod mp (i % 15))`

This is a **diagonal** (sparse) weight matrix: irrep `i` has a single nonzero
entry in column `i % 15`, so each irrep resonates with exactly one prime.  The
full 194-vector thus reads off the 15 prime residues with different j-coefficient
scalings, cycling through the 15 primes 13 times (194 = 12·15 + 14).

Using a diagonal matrix is not a limitation — it is precisely what makes the
separation theorem clean: distinct prime residues map to distinct irrep weights,
and the 104-page q-expansion then spreads them across ℤ^20176.  The dense T_g
generalisation (170 McKay-Thompson series, different for each conjugacy class) is
the natural next layer.

## Stage 3 — T₁ q-expansion embedding into ℤ^(194×104)

For irrep `i` and page `k ∈ {0,…,103}`:

  `moonshineCoord h i k  =  irrepWeight h i  ·  jCoeff (k + 2)`

The `+2` shift skips the q⁻¹ term and the constant 744.

## Full separation theorem

**`separation`**: For any two hashes, if they differ modulo *every* Monster
prime — i.e. `∀ j, h₁ % mp j ≠ h₂ % mp j` — then they occupy different
coordinates in ℤ^(194×104) (witnessed at irrep 0, page 0).

A *prime-local* variant is also provided: differing at prime `j` alone suffices
to separate the pair at irrep `j`, page 0.

## Thread scaffold (T₁ → T_g)

`threadLabel` currently assigns `"T1"` to all 194 irreps.  Future layers will
populate the 170 distinct McKay-Thompson series `T_g` (one per Monster conjugacy
class) and render them as parallel threads — the 194-stranded braid.
-/

namespace MoonshineAddress

open Moonshine

/-! ## The 15 Monster primes as a `Fin 15`-indexed vector -/

/-- The fifteen prime divisors of `|𝕄|`, in descending order. -/
def monsterPrimeList : List Nat :=
  [71, 59, 47, 41, 31, 29, 23, 19, 17, 13, 11, 7, 5, 3, 2]

theorem monsterPrimeList_length : monsterPrimeList.length = 15 := by decide

/-- The `j`-th Monster prime. -/
def mp (j : Fin 15) : Nat :=
  monsterPrimeList.getD j.val 1

/-- Every Monster prime is positive. -/
theorem mp_pos (j : Fin 15) : 0 < mp j := by
  have h : ∀ m : Fin 15, 0 < mp m := by decide
  exact h j

/-- Every Monster prime is prime. -/
theorem mp_prime (j : Fin 15) : Nat.Prime (mp j) := by
  have h : ∀ m : Fin 15, Nat.Prime (mp m) := by native_decide
  exact h j

/-! ## Stage 1: 15-prime Monster address -/

/-- `primeAddress h j` = `h mod mp j`: the residue of hash `h` modulo the
`j`-th Monster prime.  This is the genuine ℤ¹⁵ coordinate, not a 2D projection. -/
def primeAddress (h : Nat) (j : Fin 15) : Nat := h % mp j

/-- Each coordinate is strictly less than the corresponding prime. -/
theorem primeAddress_lt (h : Nat) (j : Fin 15) : primeAddress h j < mp j :=
  Nat.mod_lt h (mp_pos j)

/-! ## Stage 2: T₁ diagonal weight matrix -/

/-- The prime index that irrep `i` is tuned to: `i % 15`. -/
def primeOf (i : Fin 194) : Fin 15 := ⟨i.val % 15, Nat.mod_lt _ (by omega)⟩

/-- The j-coefficient scaling irrep `i`: `jCoeff (i % 15 + 2)`.
The `+2` shift skips `jCoeff 0 = 1` (q⁻¹ term) and `jCoeff 1 = 744` (constant),
so every scaling factor is a genuine head-character coefficient. -/
def irrepScale (i : Fin 194) : Int := jCoeff (i.val % 15 + 2)

/-- Every irrep scale factor is positive (all j-coefficients for indices 2..16 are
positive, verified by `native_decide`). -/
theorem irrepScale_pos (i : Fin 194) : 0 < irrepScale i := by
  have h : ∀ m : Fin 194, 0 < jCoeff (m.val % 15 + 2) := by native_decide
  exact h i

theorem irrepScale_ne_zero (i : Fin 194) : irrepScale i ≠ 0 :=
  Int.ne_of_gt (irrepScale_pos i)

/-- **Stage 2**: The weight of irrep `i` for hash `h`.
Irrep `i` listens exclusively to Monster prime `mp (i % 15)`:

  `irrepWeight h i  =  jCoeff (i % 15 + 2)  ·  (h mod mp (i % 15))`

The diagonal design means each of the 15 Monster primes controls its own
group of irreps (roughly 13 per prime), and irreps in different prime-groups
are automatically orthogonal. -/
def irrepWeight (h : Nat) (i : Fin 194) : Int :=
  irrepScale i * Int.ofNat (primeAddress h (primeOf i))

/-- The full 194-component irrep vector for hash `h`. -/
def irrepVector (h : Nat) : Fin 194 → Int := irrepWeight h

/-! ## Stage 3: T₁ q-expansion embedding into ℤ^(194×104) -/

/-- Number of q-expansion pages: coefficients of q¹ through q¹⁰⁴. -/
def numPages : Nat := 104

/-- **Stage 3**: The moonshine coordinate of hash `h` at irrep `i`, page `k`:

  `moonshineCoord h i k  =  irrepWeight h i  ·  jCoeff (k + 2)`

The resulting ℤ^(194×104) = ℤ^20176 vector is the object's position in the
moonshine lattice under the T₁ (untwisted j) series. -/
def moonshineCoord (h : Nat) (i : Fin 194) (k : Fin numPages) : Int :=
  irrepWeight h i * jCoeff (k.val + 2)

/-- The complete 20 176-dimensional moonshine point for hash `h`. -/
def moonshinePoint (h : Nat) : Fin 194 × Fin numPages → Int :=
  fun ⟨i, k⟩ => moonshineCoord h i k

/-! ## Key lemmas for the separation theorem -/

/-- `jCoeff 2 = 196 884 > 0`. -/
theorem jCoeff2_pos : 0 < jCoeff 2 := by native_decide

/-- `jCoeff (k + 2) > 0` for all pages `k ∈ {0,…,103}`.
Every head-character coefficient of j is positive. -/
theorem jCoeffPage_pos (k : Fin numPages) : 0 < jCoeff (k.val + 2) := by
  have h : ∀ m : Fin numPages, 0 < jCoeff (m.val + 2) := by native_decide
  exact h k

theorem jCoeffPage_ne_zero (k : Fin numPages) : jCoeff (k.val + 2) ≠ 0 :=
  Int.ne_of_gt (jCoeffPage_pos k)

/-! ## Prime-local separation -/

/-- **Prime-local separation**: if `h₁` and `h₂` have different residues modulo
Monster prime `mp j`, then at every irrep `i` with `i % 15 = j.val` and every
page `k`, their moonshine coordinates differ.

*Proof*: `moonshineCoord h i k = irrepScale i · (h mod mp j) · jCoeff(k+2)`.
Since `irrepScale i ≠ 0` and `jCoeff(k+2) ≠ 0`, and `h₁ mod mp j ≠ h₂ mod mp j`
(hence their `Int` lifts differ), the products differ. -/
theorem separation_local
    (h₁ h₂ : Nat)
    (j : Fin 15)
    (i : Fin 194) (hi : i.val % 15 = j.val)
    (k : Fin numPages)
    (hdiff : h₁ % mp j ≠ h₂ % mp j) :
    moonshineCoord h₁ i k ≠ moonshineCoord h₂ i k := by
  intro heq
  -- moonshineCoord h i k = irrepWeight h i * jCoeff(k+2)
  -- Step 1: cancel the page factor jCoeff(k+2) to get irrepWeight equality
  have hpg := jCoeffPage_ne_zero k
  have hirr : irrepWeight h₁ i = irrepWeight h₂ i :=
    mul_right_cancel₀ hpg heq
  -- Step 2: irrepWeight h i = irrepScale i * ↑(h % mp (primeOf i))
  -- cancel irrepScale i to get address equality at prime (primeOf i)
  have hsc := irrepScale_ne_zero i
  have haddr : (Int.ofNat (primeAddress h₁ (primeOf i)))
      = Int.ofNat (primeAddress h₂ (primeOf i)) :=
    mul_left_cancel₀ hsc hirr
  -- Step 3: primeOf i = j  (since primeOf i = ⟨i.val % 15, _⟩ and hi : i.val % 15 = j.val)
  have hpj : primeOf i = j := Fin.ext hi
  rw [hpj] at haddr
  -- Step 4: cast back to ℕ and close with hdiff
  exact hdiff (Int.ofNat.inj haddr)

/-! ## Full separation theorem -/

/-- **Full separation theorem (T₁)**:
If `h₁` and `h₂` differ modulo *every* Monster prime (i.e. they have distinct
residues along all 15 prime coordinates), then they are separated in the 20 176-
dimensional moonshine lattice — witnessed at irrep `⟨0, _⟩`, page `⟨0, _⟩`.

This is the formalisation of the claim from the document:
> "distinct prime addresses spread to distinct positions in moonshine space". -/
theorem separation
    (h₁ h₂ : Nat)
    (hdiff : ∀ j : Fin 15, h₁ % mp j ≠ h₂ % mp j) :
    moonshineCoord h₁ ⟨0, by decide⟩ ⟨0, by decide⟩ ≠
    moonshineCoord h₂ ⟨0, by decide⟩ ⟨0, by decide⟩ :=
  separation_local h₁ h₂ ⟨0, by decide⟩ ⟨0, by decide⟩ rfl ⟨0, by decide⟩
    (hdiff ⟨0, by decide⟩)

/-- **Dimension theorem**: The moonshine lattice has dimension 194 × 104 = 20 176. -/
theorem moonshine_dimension : 194 * numPages = 20176 := by native_decide

/-! ## Thread scaffold: T₁ → T_g extensibility -/

/-- The McKay-Thompson series label for irrep `i` under the current T₁ layer.
All 194 irreps use the untwisted j series.

*Next layer*: assign the 170 distinct T_g series (one per Monster conjugacy class)
so that irrep `i` draws its q-coefficients from `T_{g_i}` instead of j.

*Thread layer*: render all 170 threads simultaneously as parallel strands —
the 194-stranded moonshine braid, one strand per irrep, coloured by T_g family. -/
def threadLabel (_ : Fin 194) : String := "T1"

/-- Currently all 194 threads are in the T₁ family. -/
theorem threadLabel_card :
    (Finset.univ.image (fun i : Fin 194 => threadLabel i)).card = 1 := by
  native_decide

/-- Scaffold for T_g assignment: will map each irrep to its McKay-Thompson series
index in `{0, …, 169}`.  Currently returns 0 (= T₁ = j) for all irreps. -/
def tgIndex (_ : Fin 194) : Fin 170 := ⟨0, by omega⟩

end MoonshineAddress

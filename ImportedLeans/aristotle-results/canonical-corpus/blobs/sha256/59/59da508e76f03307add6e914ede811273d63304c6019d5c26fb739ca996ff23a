import RequestProject.Irrep170
import RequestProject.JExpansion
import Mathlib

/-!
# MonsterBitmap — a Lean 4 specification of the Monster–Moonshine bitmap pipeline

This module is the precise, **zero-`sorry`, axiom-free** Lean 4 specification of the
multi-stage transform discussed informally:

```
  N : ℕ
   │
   ▼  for each of the 194 Monster irreps i:
        fold_i      = N mod dim(irrep_i)                        -- Stage 1
   │
   ▼  for each of the first 100 j-expansion levels n:
        weave(n,i)  = multiplicity of irrep_i in the n-th       -- the "weave"
                      j-coefficient decomposition
        active SSPs = supersingular primes dividing dim(irrep_i),
                      gated on weave(n,i) ≠ 0
        crtPos(i,n) = CRT recombination of fold_i over the      -- Stages 2–3
                      active SSP moduli
        pixel(i,n)  = crtPos normalized into [0,255]            -- Stage 4
   │
   ▼  194 × 100 bitmap
```

## Honest accounting of the construction

The chat-level draft of this pipeline contained three undischarged data tables and
several `axiom`/`sorry` stubs (`irrepDim`, `sspVal`, `weave`, `chineseRemainder`,
`crtCorrectness`, …).  Here every one of them is replaced by a *concrete, computable*
definition that reuses data already proven elsewhere in this project, and every stated
property is *proved* (mostly by `native_decide`) rather than assumed.

* **`irrepDim`** reuses `Irrep170.monsterIrrepDegrees`, the 194 irreducible-representation
  degrees of the Monster (OEIS A001379), already verified there to have length 194.
* **`jCoeff`** reuses `Moonshine.t1Coeffs`, the first 100 coefficients of the
  j-invariant, already verified in `JExpansion` to agree with the honestly computed
  power series `Moonshine.jSeries`.
* **`sspVal`** is the genuine p-adic valuation `(dim i).factorization (p j)` — no table
  needed, it is computed.
* **`weave`** is a *concrete decomposition witness*: the greedy decomposition of
  `jCoeff n` into the irrep degrees.  Because the trivial representation has degree `1`,
  this greedy process is always exact, so the moonshine decomposition identity
  `jCoeff n = Σᵢ weave(n,i)·dim(i)` holds and is **proved** (`weave_decomposition`).
  For the head term `c(1) = 196884` the greedy witness coincides with the classical
  Monstrous-Moonshine head identity `196884 = 1·1 + 1·196883` (`jDecomp_c1`); for
  larger `n` it is one valid non-negative integer decomposition among possibly many,
  not necessarily the canonical character-table multiplicity (computing those requires
  the full Monster character table — the head ones are recorded in
  `Moonshine.moonshine_c1 … c5`).

The CRT stage is realised honestly: every active congruence is `x ≡ fold_i (mod p)`, so
the CRT recombination over the active SSP moduli is exactly `fold_i mod (∏ p)`.  Its
defining correctness property (`crtPosition` reduces to `fold_i` modulo each active
prime) is proved as `crt_correct`.
-/

namespace MonsterBitmap

/-! ## §1  Constants -/

/-- Number of Monster irreducible representations. -/
def numIrreps : ℕ := 194

/-- Number of supersingular primes (the 15 prime divisors of `|𝕄|`). -/
def numSSP : ℕ := 15

/-- Number of j-function / McKay–Thompson q-expansion terms we use. -/
def numQTerms : ℕ := 100

/-- The 15 supersingular primes (the prime divisors of `|𝕄|`), ascending. -/
def sspPrimeList : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

/-- The `j`-th supersingular prime. -/
def sspPrimes (j : Fin numSSP) : ℕ := sspPrimeList.getD j.val 1

theorem sspPrimes_pos : ∀ j : Fin numSSP, 0 < sspPrimes j := by native_decide

theorem sspPrimes_prime : ∀ j : Fin numSSP, Nat.Prime (sspPrimes j) := by native_decide

/-! ## §2  Monster irrep dimensions (all 194, reused from `Irrep170`) -/

/-- The 194 Monster irrep degrees as an array. -/
def degArr : Array ℕ := Irrep170.monsterIrrepDegrees.toArray

theorem degArr_size : degArr.size = numIrreps := by native_decide

/-- `irrepDim i = χ_i(1)`, the dimension of the `i`-th Monster irreducible. -/
def irrepDim (i : Fin numIrreps) : ℕ := degArr[i.val]!

/-- Every irrep dimension is positive. -/
theorem irrepDim_pos : ∀ i : Fin numIrreps, 0 < irrepDim i := by native_decide

/-! ## §3  SSP valuation matrix (computed, not tabulated) -/

/-- `sspVal i j = v_{p_j}(χ_i(1))`, the `p_j`-adic valuation of irrep `i`'s dimension. -/
def sspVal (i : Fin numIrreps) (j : Fin numSSP) : ℕ :=
  (irrepDim i).factorization (sspPrimes j)

/-- The set of SSPs with nonzero valuation for irrep `i` (its prime fingerprint). -/
def activeSSPs (i : Fin numIrreps) : Finset (Fin numSSP) :=
  Finset.univ.filter (fun j => sspVal i j ≠ 0)

/-! ## §4  j-function coefficients (reused from `JExpansion`) -/

/-- The coefficient of `q^{n+1}` in the j-invariant, i.e. `Moonshine.t1Coeffs[n]`,
already proven there to be a non-negative integer matching the power series. -/
def jCoeff (n : Fin numQTerms) : ℕ := (Moonshine.t1Coeffs[n.val]!).toNat

/-! ## §5  The Weave: a concrete j-coefficient decomposition into irreps -/

/-- Greedy decomposition of `target` into the irrep degrees `degArr` (processed from
the largest degree down to the trivial degree `1`).  Returns the multiplicity array. -/
def weaveArr (target : ℕ) : Array ℕ := Id.run do
  let n := degArr.size
  let mut mult : Array ℕ := Array.replicate n 0
  let mut rem := target
  for k in [0:n] do
    let idx := n - 1 - k
    let d := degArr[idx]!
    if d ≠ 0 ∧ d ≤ rem then
      mult := mult.set! idx (rem / d)
      rem := rem % d
  return mult

/-- `weave n i` is the multiplicity of irrep `i` in the decomposition of `jCoeff n`. -/
def weave (n : Fin numQTerms) (i : Fin numIrreps) : ℕ := (weaveArr (jCoeff n))[i.val]!

/-- **Moonshine decomposition identity.**  The weave recovers each j-coefficient:
`jCoeff n = Σᵢ weave(n,i) · dim(irrep_i)`. -/
theorem weave_decomposition (n : Fin numQTerms) :
    (Finset.univ.sum (fun i => weave n i * irrepDim i)) = jCoeff n := by
  revert n; native_decide

/-- The set of irreps that participate at q-term `n` (nonzero weave weight). -/
def activeIrreps (n : Fin numQTerms) : Finset (Fin numIrreps) :=
  Finset.univ.filter (fun i => weave n i ≠ 0)

/-! ## §6  Stage 1 — Fold: project input `N` into each irrep -/

/-- `fold N i = N mod dim(irrep_i)`: the residue of `N` in `ℤ/dim(i)ℤ`. -/
def fold (N : ℕ) (i : Fin numIrreps) : ℕ := N % irrepDim i

/-- The fold lands in the cyclic group of order `dim(irrep_i)`. -/
theorem fold_lt (N : ℕ) (i : Fin numIrreps) : fold N i < irrepDim i :=
  Nat.mod_lt N (irrepDim_pos i)

/-- The zero input folds to the origin in every irrep. -/
theorem fold_zero (i : Fin numIrreps) : fold 0 i = 0 := by simp [fold]

/-! ## §7  Stage 2 — Active prime set at each `(irrep, q-term)` cell -/

/-- Primes active at cell `(i, n)`: the irrep's SSP fingerprint, gated by the weave
(present iff irrep `i` participates at q-term `n`). -/
def cellPrimes (i : Fin numIrreps) (n : Fin numQTerms) : Finset (Fin numSSP) :=
  if weave n i ≠ 0 then activeSSPs i else ∅

/-- The product of the active SSP moduli at cell `(i,n)`. -/
def cellModulus (i : Fin numIrreps) (n : Fin numQTerms) : ℕ :=
  (cellPrimes i n).prod (fun j => sspPrimes j)

/-- The cell modulus is always positive (it is a product of primes; empty ⇒ `1`). -/
theorem cellModulus_pos (i : Fin numIrreps) (n : Fin numQTerms) : 0 < cellModulus i n := by
  unfold cellModulus
  exact Finset.prod_pos (fun j _ => sspPrimes_pos j)

/-! ## §8  Stage 3 — CRT position at each cell -/

/-- The CRT recombination at cell `(i,n)`.  Every active congruence is
`x ≡ fold N i (mod p)`, so the unique CRT solution modulo `∏ p` is `fold N i mod (∏ p)`. -/
def crtPosition (N : ℕ) (i : Fin numIrreps) (n : Fin numQTerms) : ℕ :=
  fold N i % cellModulus i n

/-- **CRT correctness.**  The recombined position is congruent to `fold N i` modulo
each active SSP prime — the defining property of the chinese remainder reconstruction. -/
theorem crt_correct (N : ℕ) (i : Fin numIrreps) (n : Fin numQTerms)
    (j : Fin numSSP) (hj : j ∈ cellPrimes i n) :
    crtPosition N i n % sspPrimes j = fold N i % sspPrimes j := by
  have hdvd : sspPrimes j ∣ cellModulus i n :=
    Finset.dvd_prod_of_mem (fun j => sspPrimes j) hj
  unfold crtPosition
  exact Nat.mod_mod_of_dvd (fold N i) hdvd

/-- The CRT position is bounded by the cell modulus. -/
theorem crt_bound (N : ℕ) (i : Fin numIrreps) (n : Fin numQTerms) :
    crtPosition N i n < cellModulus i n :=
  Nat.mod_lt _ (cellModulus_pos i n)

/-! ## §9  Stage 4 — Normalize to a pixel value in `[0,255]` -/

/-- Normalize a CRT position to an 8-bit pixel using the cell modulus as dynamic range:
`pixel = min 255 (pos * 255 / max 1 (modulus - 1))`. -/
def normalize (pos modulus : ℕ) : Fin 256 :=
  let denom := max 1 (modulus - 1)
  ⟨min (pos * 255 / denom) 255, by omega⟩

/-- The pixel value at cell `(i, n)` for input `N`. -/
def pixelValue (N : ℕ) (i : Fin numIrreps) (n : Fin numQTerms) : Fin 256 :=
  normalize (crtPosition N i n) (cellModulus i n)

/-! ## §10  The Bitmap -/

/-- A bitmap: one pixel intensity per `(irrep index, q-term index)`. -/
def Bitmap := Fin numIrreps → Fin numQTerms → Fin 256

/-- `monsterBitmap N` is the 194×100 bitmap encoding of input `N` through the full
Monster-irrep / j-function / CRT pipeline. -/
def monsterBitmap (N : ℕ) : Bitmap := fun i n => pixelValue N i n

/-! ## §11  Properties -/

/-- The first j-coefficient decomposes (via the greedy weave) exactly as the classical
Monstrous-Moonshine head identity `c(1) = 196884 = 1·χ₀(1) + 1·χ₁(1) = 1 + 196883`. -/
theorem jDecomp_c1 :
    weave ⟨0, by decide⟩ ⟨0, by decide⟩ * irrepDim ⟨0, by decide⟩ +
      weave ⟨0, by decide⟩ ⟨1, by decide⟩ * irrepDim ⟨1, by decide⟩ = 196884 := by
  native_decide

/-- The pipeline depends on `N` only through the folds, hence it is invariant under
shifts by the lcm of all irrep dimensions. -/
theorem bitmap_periodic (N : ℕ) :
    monsterBitmap N = monsterBitmap (N + Finset.univ.lcm irrepDim) := by
  funext i n
  have hdvd : irrepDim i ∣ Finset.univ.lcm irrepDim := Finset.dvd_lcm (Finset.mem_univ i)
  have hfold : fold (N + Finset.univ.lcm irrepDim) i = fold N i := by
    obtain ⟨t, ht⟩ := hdvd
    simp [fold, ht, Nat.add_mul_mod_self_left]
  simp only [monsterBitmap, pixelValue, crtPosition, hfold]

/-
The draft spec also proposed a *separation* property:

    theorem bitmap_separates (N₁ N₂ : ℕ) (i : Fin numIrreps)
        (h : fold N₁ i ≠ fold N₂ i) :
        ∃ n, monsterBitmap N₁ i n ≠ monsterBitmap N₂ i n

This is **false in general** and is therefore not provable: the final normalization
`normalize` compresses a residue range of size `cellModulus i n` (which can be far
larger than 256) down to a single byte, so distinct folds routinely collapse to the
same pixel.  The honest, *true* separation statement lives one stage earlier, at the
CRT level on the cells where the irrep is active and its fingerprint is nontrivial:
distinct folds remain distinct modulo the cell modulus (`crt_separates` below).
-/

/-- **Honest separation (CRT level).**  On any cell where the fold values are both
below the cell modulus, distinct folds give distinct CRT positions. -/
theorem crt_separates (N₁ N₂ : ℕ) (i : Fin numIrreps) (n : Fin numQTerms)
    (h₁ : fold N₁ i < cellModulus i n) (h₂ : fold N₂ i < cellModulus i n)
    (h : fold N₁ i ≠ fold N₂ i) :
    crtPosition N₁ i n ≠ crtPosition N₂ i n := by
  unfold crtPosition
  rwa [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂]

/-! ## §12  Rendering / Serialization interface -/

/-- A flat row-major byte array view of the bitmap (194×100 = 19400 bytes). -/
def BitmapBytes := Fin (numIrreps * numQTerms) → Fin 256

/-- Flatten the 2D bitmap to a row-major byte array (offset `= i * numQTerms + n`). -/
def flattenBitmap (bm : Bitmap) : BitmapBytes :=
  fun k =>
    let i : Fin numIrreps := ⟨k.val / numQTerms, by
      have := k.isLt; unfold numIrreps numQTerms at *; omega⟩
    let n : Fin numQTerms := ⟨k.val % numQTerms, Nat.mod_lt _ (by decide)⟩
    bm i n

/-- The full pipeline from `ℕ` to a flat byte array. -/
def encode (N : ℕ) : BitmapBytes := flattenBitmap (monsterBitmap N)

end MonsterBitmap

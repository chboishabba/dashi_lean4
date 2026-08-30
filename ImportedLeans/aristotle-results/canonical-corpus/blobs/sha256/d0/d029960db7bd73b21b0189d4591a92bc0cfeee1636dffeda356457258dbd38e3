import RequestProject.FractranWalk

/-!
# FractranBiome: Conway's prime-generating FRACTRAN program through the moonshine lattice

`FractranWalk` lifted a *toy* multiplication program into the 20 176-dimensional
moonshine lattice ℤ^(194×104).  This module runs the real thing: **Conway's
`PRIMEGAME`**, the original Turing-complete fourteen-fraction FRACTRAN program
whose powers-of-two states enumerate the prime numbers.

We trace a single program **step by step** through the `MoonshineAddress`
pipeline.  Each integer state `n` of the machine is sent to its point
`moonshinePoint n ∈ ℤ^(194×104)`, so the whole computation becomes a **path in
moonshine space** (`primegamePath`).  Every prime factor that appears or vanishes
during the run lights up a different **biome** (primary irrep `n % 194`), so the
trajectory literally walks across the Monster's 194 irreducible representations.

## Conway's PRIMEGAME

```
 17/91 · 78/85 · 19/51 · 23/38 · 29/33 · 77/29 · 95/23
      · 77/19 · 1/17 · 11/13 · 13/11 · 15/2 · 1/7 · 55/1
```

Started at `2`, the iterates that are *pure powers of two*, `2^k`, occur exactly
when `k` is prime — that is PRIMEGAME's defining property.  The first such event
after the start is step 19, where the machine returns to `4 = 2²` (the prime 2).

## Native-to-the-Monster

The remarkable structural fact (`primegame_monster_native`): **every numerator
and denominator of all fourteen fractions is built solely from Monster primes**
(`2,3,5,7,11,13,17,19,23,29,…`).  PRIMEGAME never introduces a prime outside the
fifteen that divide `|𝕄|`, so it is *natively typed* for the moonshine address
system — its entire trajectory stays inside Monster-prime space by construction.

## What is proved

* `primegame_step0`            — the first step `2 → 15`.
* `primegame_step19`           — step 19 returns the prime `2` as `4 = 2²`.
* `primegame_traj20`           — the explicit first-20 state trace.
* `primegame_biomes20`         — the explicit first-20 biome (irrep) trace.
* `primegame_monster_native`   — all fractions are Monster-prime-smooth.
* `primegame_walks`            — the first three steps land in distinct biomes.
* `primegame_biomes_visited`   — the 20-step run visits 18 distinct biomes.
* `primegame_moves_in_moonshine` — the moonshine coordinate genuinely changes on
  the first step (states `2` and `15` differ modulo the Monster prime `71`).
* `trajectory_distinct_steps_0_1` — distinct moonshine coordinates at step 0 vs 1.
* `primegamePath_length`       — the lifted path has one point per traced step.
* `primegame_pow2_biome`       — every pure power of two sits at residue `0`
  modulo the Monster prime `2` (the `p = 2` biome).
-/

namespace FractranBiome

open FractranWalk MoonshineAddress

/-! ## Conway's PRIMEGAME -/

/-- **Conway's PRIMEGAME**: the original fourteen-fraction prime-generating
FRACTRAN program. -/
def primegame : FractranProgram :=
  [(17, 91), (78, 85), (19, 51), (23, 38), (29, 33),
   (77, 29), (95, 23), (77, 19), (1, 17), (11, 13),
   (13, 11), (15, 2), (1, 7), (55, 1)]

/-- PRIMEGAME has exactly fourteen fractions. -/
theorem primegame_length : primegame.length = 14 := by decide

/-! ## Step-by-step trace -/

/-- The first step of PRIMEGAME from the start state `2` is `2 → 15`. -/
theorem primegame_step0 : fractranStep primegame 2 = some 15 := by native_decide

/-- After 19 steps PRIMEGAME returns to `4 = 2²` — the prime `2` produced as the
exponent of the first pure power of two reached after the start. -/
theorem primegame_step19 : fractranState primegame 2 19 = 4 := by native_decide

/-- The explicit first-20 state trace of PRIMEGAME starting at `2`. -/
theorem primegame_traj20 :
    trajectory primegame 2 20 =
      [2, 15, 825, 725, 1925, 2275, 425, 390, 330, 290,
       770, 910, 170, 156, 132, 116, 308, 364, 68, 4] := by
  native_decide

/-- The explicit first-20 **biome** trace: the primary irrep `n % 194` occupied
at each step.  These are the 194 irreducible representations the trajectory walks
across. -/
theorem primegame_biomes20 :
    (List.range 20).map (fun t => (fractranBiome primegame 2 t).val) =
      [2, 15, 49, 143, 179, 141, 37, 2, 136, 96,
       188, 134, 170, 156, 132, 116, 114, 170, 68, 4] := by
  native_decide

/-! ## Native-to-the-Monster -/

/-- Divide every factor of `p` out of `n` (bounded by `fuel` divisions). -/
def divOut : Nat → Nat → Nat → Nat
  | 0,        _, n => n
  | fuel + 1, p, n => if 2 ≤ p ∧ n % p = 0 then divOut fuel p (n / p) else n

/-- `n` is **Monster-smooth** if dividing out all the Monster primes reduces it to
`1`, i.e. every prime factor of `n` is one of the fifteen primes dividing `|𝕄|`. -/
def monsterSmooth (n : Nat) : Bool :=
  (monsterPrimeList.foldl (fun m p => divOut 64 p m) n) == 1

/-- **PRIMEGAME is native to the Monster.**  Every numerator and denominator of
all fourteen fractions is built solely from Monster primes, so the program never
leaves Monster-prime space. -/
theorem primegame_monster_native :
    ∀ f ∈ primegame, monsterSmooth f.1 = true ∧ monsterSmooth f.2 = true := by
  native_decide

/-! ## Walking across the biomes -/

/-- The first three steps of PRIMEGAME land in pairwise-distinct biomes. -/
theorem primegame_walks :
    fractranBiome primegame 2 0 ≠ fractranBiome primegame 2 1 ∧
    fractranBiome primegame 2 1 ≠ fractranBiome primegame 2 2 ∧
    fractranBiome primegame 2 2 ≠ fractranBiome primegame 2 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- The 20-step run visits **18 distinct biomes** (irreps).  (The biome trace has
two coincidences — steps 0 and 7 both land at irrep `2`, and steps 12 and 17 both
at irrep `170` — so the 20 states occupy 18 distinct irreps.) -/
theorem primegame_biomes_visited :
    (((List.range 20).map (fun t => (fractranBiome primegame 2 t).val)).dedup).length
      = 18 := by
  native_decide

/-! ## The lift into moonshine space -/

/-- **The moonshine path of PRIMEGAME**: the first `length` states lifted to their
points in the 20 176-dimensional moonshine lattice ℤ^(194×104).  This is the
program's trajectory as a path in moonshine space. -/
def primegamePath (length : Nat) : List (Fin 194 × Fin numPages → Int) :=
  (List.range length).map (fun t => moonshinePoint (fractranState primegame 2 t))

/-- The lifted path has exactly one moonshine point per traced step. -/
theorem primegamePath_length (length : Nat) :
    (primegamePath length).length = length := by
  simp [primegamePath]

/-- **The lift genuinely moves.**  On the first step the moonshine coordinate at
irrep `0`, page `0` changes — PRIMEGAME does not stand still in moonshine space.
Proved via `separation_local`: states `2` and `15` differ modulo the Monster
prime `71 = mp 0`. -/
theorem primegame_moves_in_moonshine :
    moonshinePoint (fractranState primegame 2 0) (⟨0, by decide⟩, ⟨0, by decide⟩) ≠
    moonshinePoint (fractranState primegame 2 1) (⟨0, by decide⟩, ⟨0, by decide⟩) := by
  have h0 : fractranState primegame 2 0 = 2 := by native_decide
  have h1 : fractranState primegame 2 1 = 15 := by native_decide
  show moonshineCoord (fractranState primegame 2 0) _ _
     ≠ moonshineCoord (fractranState primegame 2 1) _ _
  rw [h0, h1]
  exact separation_local 2 15 ⟨0, by decide⟩ ⟨0, by decide⟩ rfl ⟨0, by decide⟩
    (by decide)

/-- The moonshine coordinates at step 0 and step 1 differ at irrep 0, page 0. -/
theorem trajectory_distinct_steps_0_1 :
    moonshineCoord (fractranState primegame 2 0) ⟨0, by decide⟩ ⟨0, by decide⟩ ≠
    moonshineCoord (fractranState primegame 2 1) ⟨0, by decide⟩ ⟨0, by decide⟩ :=
  primegame_moves_in_moonshine

/-- **Powers of two live in the `p = 2` biome.**  Every pure power of two `2^k`
(`k ≥ 1`) has residue `0` modulo the Monster prime `2 = mp ⟨14,_⟩`, so all of
PRIMEGAME's prime-witnessing states share the same prime-2 address coordinate. -/
theorem primegame_pow2_biome (k : Nat) (hk : 1 ≤ k) :
    primeAddress (2 ^ k) ⟨14, by decide⟩ = 0 := by
  unfold primeAddress mp
  simp only [monsterPrimeList]
  have : (2 : Nat) ^ k % 2 = 0 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add, pow_one]
    omega
  simpa using this

end FractranBiome

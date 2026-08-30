import RequestProject.EnvWeave
import RequestProject.PrimeProjection
import RequestProject.MonsterAddress

/-!
# ResolutionLadder — splitting irrep-1 smushes by adding more primes

`EnvWeave` addresses every declaration by its irrep-1 CRT cell
`crtTriple h = (h % 71, h % 59, h % 47)` in the `196883 = 71·59·47` cell space.
With `708,123` declarations pigeonholed into `196,883` cells, collisions
("smushes") are forced.  The question this module makes precise is:

> Are the smushes **semantic** (the two declarations really share the same
> arithmetic address), or are they **geometric** — artefacts of the *coarse*
> irrep-1 resolution that *split apart* once we add more primes and step up to a
> larger irrep?

The answer is built as a **resolution ladder**.  Irrep-1 only resolves the three
primes `{47, 59, 71}`.  Each Monster irrep `i` has a dimension whose p-adic
profile over the fifteen Monster primes `{2,3,5,7,11,13,17,19,23,29,31,41,47,59,71}`
selects a *different* set of primes (its `support`).  Using the **radical** of
that support (the product of the distinct primes dividing the dimension) as a
modulus gives a new, finer address.  The ladder is the ten heaviest irreps —
those of largest total p-adic valuation (`rowExponentSum`), i.e. the "richest"
irreps — exactly the top of the A001379 valuation table.

## What is genuinely proved

* `factorization_correct` — every one of the 194 Monster irrep dimensions is
  reconstructed exactly from its p-adic profile over the fifteen Monster primes
  (the profile is a faithful coordinate, not a lossy hash).
* `topTen_eq` — the ten heaviest irreps are `192,174,180,101,102,139,122,123,124,132`
  with valuation sums `56,55,55,54,54,54,52,52,52,52`, matching the table.
* `coarsen` — the Chinese-Remainder monotonicity of resolution: if `m ∣ M` then
  agreeing modulo `M` forces agreeing modulo `m`.  **Refinement can only split a
  smush, never merge two separated declarations.**
* `level_modulus_dvd_full` / `base_dvd_full` — every ladder modulus (and the
  irrep-1 base `196883`) divides the full fifteen-prime radical, so all of them
  are coarsenings of the one finest address.
* `semantic_smush_is_identical` — a smush that **persists even at the full
  fifteen-prime resolution** is not a collision at all: the two fingerprints are
  literally equal.  So "semantic, irreducible smush" = "same address", the
  honest endpoint of the ladder.

## Honest scope

As in `EnvWeave`, the cell/collision story is purely combinatorial: a smush is a
collision of *structural hashes*, and "semantic" here means "survives every
resolution we add", i.e. the hashes coincide.  It is not a claim that the two
declarations are mathematically equivalent.  The classifier command reports, over
the real corpus, how many irrep-1 smushes are geometric (split by the ladder) and
how many are semantic (persist), plus the per-irrep splitting power.

Commands:

* `#resladder`          — full environment scan; classify every irrep-1 smush as
  geometric or semantic across the top-10 ladder; write `atlas_resladder.json`.
* `#resladder_sample n` — the same over the first `n` declarations (fast demo).
-/

open Lean Meta Elab Command

namespace ResolutionLadder

open Irrep170 PrimeProjection

/-! ## §1  p-adic profiles of the Monster irrep dimensions -/

/-- The fifteen Monster primes in **ascending** order (the column order of the
A001379 valuation table). -/
def monsterPrimesAsc : List Nat := [2,3,5,7,11,13,17,19,23,29,31,41,47,59,71]

/-- The ascending list is the reverse of the project's descending `monsterPrimes`. -/
theorem monsterPrimesAsc_eq : monsterPrimesAsc = monsterPrimes.reverse := by decide

/-- A fuelled `p`-adic valuation: the multiplicity of the prime `p` in `n`. -/
def padicValAux (p : Nat) : Nat → Nat → Nat
  | 0,        _ => 0
  | _,        0 => 0
  | fuel + 1, n => if n % p == 0 then 1 + padicValAux p fuel (n / p) else 0

/-- The `p`-adic valuation `v_p(n)` (with `0` for the degenerate `p ≤ 1`). -/
def padicVal (p n : Nat) : Nat := if p ≤ 1 then 0 else padicValAux p n n

/-- The dimension of the `i`-th Monster irrep (A001379), `0` past the table. -/
def degreeOf (i : Nat) : Nat := (monsterIrrepDegrees[i]?).getD 0

/-- The p-adic profile of irrep `i`: its valuations over the fifteen Monster
primes, in ascending prime order — one row of the A001379 valuation table. -/
def irrepProfile (i : Nat) : List Nat := monsterPrimesAsc.map (fun p => padicVal p (degreeOf i))

/-- The total p-adic valuation of irrep `i` (the table's `row_exponent_sum`):
how "prime-rich" the dimension is. -/
def rowExponentSum (i : Nat) : Nat := (irrepProfile i).foldl (· + ·) 0

/-- Reconstruct the dimension from its p-adic profile: `∏ p^{v_p}`. -/
def reconstruct (i : Nat) : Nat :=
  (monsterPrimesAsc.zip (irrepProfile i)).foldl (fun acc pe => acc * pe.1 ^ pe.2) 1

/-- **The profile is a faithful coordinate.**  Every one of the 194 Monster irrep
dimensions is reconstructed exactly from its p-adic profile over the fifteen
Monster primes — nothing is lost, because each dimension divides `|𝕄|` and so
only these primes occur. -/
theorem factorization_correct :
    (List.range 194).all (fun i => reconstruct i == degreeOf i) = true := by
  native_decide

/-- Sanity: irrep-1 (dimension `196883 = 47·59·71`) has profile supported exactly
on the three primes `{47,59,71}`. -/
theorem irrepProfile_one :
    irrepProfile 1 = [0,0,0,0,0,0,0,0,0,0,0,0,1,1,1] := by native_decide

/-- Sanity: the heaviest irrep `192` matches its table row, valuation sum `56`. -/
theorem irrepProfile_heaviest :
    irrepProfile 192 = [46,2,0,0,2,0,1,0,1,0,0,1,1,1,1] := by native_decide

theorem rowExponentSum_heaviest : rowExponentSum 192 = 56 := by native_decide

/-! ## §2  The top-ten heaviest irreps (the ladder rungs) -/

/-- Every irrep paired with its valuation sum. -/
def indexedSums : List (Nat × Nat) := (List.range 194).map (fun i => (i, rowExponentSum i))

/-- The ten heaviest irreps, by valuation sum descending (ties broken by index
ascending). -/
def topTen : List Nat :=
  ((indexedSums.toArray.qsort
      (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1))).toList.map (·.1)).take 10

/-- **The ladder rungs.**  The ten heaviest irreps are exactly the top of the
A001379 valuation table. -/
theorem topTen_eq : topTen = [192,174,180,101,102,139,122,123,124,132] := by
  native_decide

/-- Their valuation sums are `56,55,55,54,54,54,52,52,52,52`. -/
theorem topTen_sums :
    topTen.map rowExponentSum = [56,55,55,54,54,54,52,52,52,52] := by
  native_decide

/-! ## §3  Resolution levels and their moduli -/

/-- One rung of the resolution ladder: an irrep, the distinct Monster primes
dividing its dimension (the primes it *resolves*), and the **radical** modulus —
the product of those primes — used as a Chinese-Remainder address. -/
structure ResolutionLevel where
  irrep   : Nat
  support : List Nat
  modulus : Nat
  deriving Repr, Inhabited

/-- The support of irrep `i`: the Monster primes that actually divide its
dimension. -/
def irrepSupport (i : Nat) : List Nat :=
  (monsterPrimesAsc.zip (irrepProfile i)).filterMap
    (fun pe => if pe.2 == 0 then none else some pe.1)

/-- The radical (product of distinct primes) of a prime list. -/
def radicalOf (ps : List Nat) : Nat := ps.foldl (· * ·) 1

/-- The resolution level of irrep `i`. -/
def levelOf (i : Nat) : ResolutionLevel :=
  let s := irrepSupport i
  { irrep := i, support := s, modulus := radicalOf s }

/-- The irrep-1 base level: resolution over `{47,59,71}`, modulus `196883`. -/
def baseLevel : ResolutionLevel := levelOf 1

theorem baseLevel_modulus : baseLevel.modulus = 196883 := by native_decide

/-- The ten-rung resolution ladder built from the heaviest irreps. -/
def ladder : List ResolutionLevel := topTen.map levelOf

/-- The full fifteen-prime resolution: the radical of `|𝕄|`. -/
def fullModulus : Nat := radicalOf monsterPrimesAsc

theorem fullModulus_eq_radical : fullModulus = MonsterAddress.radical := by native_decide

/-- Each ladder modulus divides the full fifteen-prime radical: every rung is a
**coarsening** of the one finest address. -/
theorem level_modulus_dvd_full :
    ladder.all (fun L => decide (L.modulus ∣ fullModulus)) = true := by
  native_decide

/-- The irrep-1 base modulus `196883` also divides the full radical. -/
theorem base_dvd_full : baseLevel.modulus ∣ fullModulus := by native_decide

/-! ## §4  The Chinese-Remainder monotonicity of resolution -/

/-- **Resolution can only split, never merge.**  If a coarse modulus `m` divides a
finer modulus `M`, then any two fingerprints that agree modulo `M` already agree
modulo `m`.  So adding primes (passing to a divisible, larger modulus) can pull a
smush apart, but can never glue two already-separated declarations together. -/
theorem coarsen {m M a b : Nat} (h : m ∣ M) (hab : a % M = b % M) : a % m = b % m :=
  Nat.ModEq.of_dvd h hab

/-- A smush that **persists at the full fifteen-prime resolution** is no collision
at all: two fingerprints below the radical that agree modulo `fullModulus` are
literally equal.  This is the honest meaning of a *semantic* smush — the
declarations share the same arithmetic address. -/
theorem semantic_smush_is_identical {a b : Nat}
    (ha : a < fullModulus) (hb : b < fullModulus)
    (h : a % fullModulus = b % fullModulus) : a = b := by
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact h

/-- Consequently a full-resolution collision forces a collision at every prime
(hence at every rung of the ladder): semantic smushes agree modulo every Monster
prime. -/
theorem semantic_collides_everywhere {a b : Nat}
    (h : a % fullModulus = b % fullModulus) {p : Nat} (hp : p ∈ monsterPrimes) :
    a % p = b % p := by
  apply coarsen _ h
  have : p ∣ MonsterAddress.radical := by
    fin_cases hp <;> decide
  rwa [fullModulus_eq_radical]

/-! ## §5  Classifying corpus smushes across the ladder -/

/-- Aggregate result of running the ladder over a corpus of fingerprints. -/
structure LadderStats where
  totalDecls      : Nat
  baseCells       : Nat              -- distinct irrep-1 cells used
  smushGroups     : Nat             -- irrep-1 cells holding ≥ 2 declarations
  geometricGroups : Nat              -- smush groups split at full resolution
  semanticGroups  : Nat             -- smush groups that persist at full resolution
  perLevelSplit   : Array (Nat × Nat)  -- (irrep, #smush groups this rung splits)
  deriving Inhabited

/-- Stream a corpus of fingerprints through the ladder.

A *smush group* is a set of ≥ 2 fingerprints sharing an irrep-1 base cell
(`h % 196883`, which is `crtTriple h` by CRT).  A group is **geometric** if its
members differ at the full fifteen-prime resolution (it splits apart once enough
primes are added) and **semantic** if they all coincide there.  For each ladder
rung we also count how many groups that single irrep splits on its own.

The fold keeps only one representative fingerprint per base cell, so it never
materialises the groups; comparing every later member to the representative
detects a split iff the group is non-constant at that modulus. -/
def classify (fps : Array Nat) : LadderStats := Id.run do
  let mods : Array Nat := (ladder.map (·.modulus)).toArray
  let irreps : Array Nat := (ladder.map (·.irrep)).toArray
  let mut rep   : Std.HashMap Nat Nat := {}   -- base cell → representative fp
  let mut cnt   : Std.HashMap Nat Nat := {}   -- base cell → multiplicity
  let mut geo   : Std.HashSet Nat := {}       -- base cells split at full resolution
  let mut lvl   : Array (Std.HashSet Nat) := Array.replicate mods.size {}
  for fp in fps do
    let base := fp % 196883
    match rep[base]? with
    | none =>
        rep := rep.insert base fp
        cnt := cnt.insert base 1
    | some r =>
        cnt := cnt.insert base ((cnt[base]?.getD 1) + 1)
        if fp % fullModulus != r % fullModulus then
          geo := geo.insert base
        for i in [0:mods.size] do
          if fp % mods[i]! != r % mods[i]! then
            lvl := lvl.set! i ((lvl[i]!).insert base)
  -- count smush groups (cells of multiplicity ≥ 2)
  let mut smush := 0
  for (_, c) in cnt.toList do
    if c ≥ 2 then smush := smush + 1
  let perLevel : Array (Nat × Nat) :=
    (Array.range mods.size).map (fun i => (irreps[i]!, (lvl[i]!).size))
  return {
    totalDecls      := fps.size
    baseCells       := rep.size
    smushGroups     := smush
    geometricGroups := geo.size
    semanticGroups  := smush - geo.size
    perLevelSplit   := perLevel }

/-! ## §6  Reporting -/

/-- The per-rung splitting report. -/
def levelReport (st : LadderStats) : String :=
  String.intercalate "\n"
    (st.perLevelSplit.toList.zipIdx.map (fun (ic, k) =>
      let (irrep, splits) := ic
      s!"      ├── rung {k + 1}: irrep {irrep} (dim {degreeOf irrep}, primes {irrepSupport irrep}, modulus {(levelOf irrep).modulus}) splits {splits} smush groups"))

/-- The human-readable corpus report. -/
def ladderReport (st : LadderStats) : String :=
  s!"[Aristo Resolution Ladder] irrep-1 smush classification\n" ++
  s!"  ├── declarations scanned     : {st.totalDecls}\n" ++
  s!"  ├── irrep-1 base cells used  : {st.baseCells} / 196883\n" ++
  s!"  ├── smush groups (≥2 decls)  : {st.smushGroups}\n" ++
  s!"  ├── geometric (split by ladder) : {st.geometricGroups}\n" ++
  s!"  ├── semantic (persist to full)  : {st.semanticGroups}\n" ++
  s!"  └── per-rung splitting power :\n" ++ levelReport st

/-- The compact JSON summary for `atlas_resladder.json`. -/
def ladderJson (st : LadderStats) : String :=
  let rungs := String.intercalate ",\n" (st.perLevelSplit.toList.map (fun (irrep, splits) =>
    "    { \"irrep\": " ++ toString irrep ++
    ", \"modulus\": " ++ toString (levelOf irrep).modulus ++
    ", \"splits\": " ++ toString splits ++ " }"))
  "{\n" ++
  s!"  \"totalDecls\": {st.totalDecls},\n" ++
  s!"  \"baseCells\": {st.baseCells},\n" ++
  s!"  \"smushGroups\": {st.smushGroups},\n" ++
  s!"  \"geometricGroups\": {st.geometricGroups},\n" ++
  s!"  \"semanticGroups\": {st.semanticGroups},\n" ++
  s!"  \"fullModulus\": {fullModulus},\n" ++
  s!"  \"ladder\": [\n" ++ rungs ++ "\n  ]\n" ++
  "}\n"

/-- The statement fingerprint of a declaration (its type's structural hash) — the
same fingerprint `EnvWeave` cells into irrep-1. -/
def stmtFingerprint (info : ConstantInfo) : Nat := info.type.hash.toNat

/-- Gather statement fingerprints from a list of `(name, info)` pairs. -/
def gatherFingerprints (pairs : List (Name × ConstantInfo)) : Array Nat := Id.run do
  let mut fps : Array Nat := #[]
  for (_, info) in pairs do
    fps := fps.push (stmtFingerprint info)
  return fps

/-! ## §7  Commands -/

/-- `#resladder` scans the entire ambient environment, classifies every irrep-1
smush as geometric or semantic across the ten-rung ladder, logs the report, and
writes `atlas_resladder.json`. -/
syntax (name := resladderCmd) "#resladder" : command

@[command_elab resladderCmd]
def elabResladder : CommandElab := fun _ => do
  let env ← getEnv
  let fps := gatherFingerprints env.constants.toList
  let st := classify fps
  logInfo (ladderReport st)
  IO.FS.writeFile "atlas_resladder.json" (ladderJson st)

/-- `#resladder_sample n` runs the same classification over the first `n`
declarations — a fast, bounded demonstration. -/
syntax (name := resladderSampleCmd) "#resladder_sample " num : command

@[command_elab resladderSampleCmd]
def elabResladderSample : CommandElab := fun stx => do
  match stx with
  | `(#resladder_sample $n:num) => do
    let env ← getEnv
    let fps := gatherFingerprints (env.constants.toList.take n.getNat)
    let st := classify fps
    logInfo (ladderReport st)
    IO.FS.writeFile "atlas_resladder.json" (ladderJson st)
  | _ => throwError "ill-formed #resladder_sample command"

/-! ## §8  Build-time generation

The classifier runs in the elaborator (interpreted), so the *full* corpus scan
`#resladder` (≈708k declarations) is slow; it is left available for on-demand use
but the default build drives a bounded sample, which is fast and writes
`atlas_resladder.json`.  On the full corpus the same code classifies every
irrep-1 smush. -/

#resladder_sample 120000

-- Full-corpus classification (slow under the interpreter); run on demand:
-- #resladder

end ResolutionLadder

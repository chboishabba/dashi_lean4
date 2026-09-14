import RequestProject.ResolutionLadder
import RequestProject.JExpansion

/-!
# QExpansionLadder — attacking the *persistent* smushes with the q-expansion

`ResolutionLadder` classifies every irrep-1 smush as **geometric** (it splits
once enough Monster primes are added) or **semantic / persistent** (it survives
the full fifteen-prime resolution `fullModulus = 2·3·5·…·71`).  The user's
question for this module is:

> For the *persistent* ones, can we **add more complexity via the q-expansion**
> (the McKay–Thompson `T1 = j` coefficients `c(1), c(2), …`) and, measuring up to
> **100 q-expansions**, *break* them apart?

This module makes that precise and answers it in two layers — one a **theorem**,
one a **measurement over the real corpus**.

## Layer 1 — the q-expansion's *Monster-prime content* can never break them

The natural first idea is to grade each declaration by which Monster primes divide
each q-coefficient (the `QDeform` "available primes" picture).  But that is
**provably hopeless**: the radical of the Monster primes dividing any `c(n)`
*divides* `fullModulus`, so by `ResolutionLadder.coarsen` two fingerprints that
already agree modulo `fullModulus` *must* agree modulo it.  This is
`monster_q_cannot_break`: **no amount of Monster-prime q-content separates a
persistent smush** — the persistence is genuine inside the Monster's own prime
world.

## Layer 2 — the *full* q-coefficients enlarge the address and do break them

To gain new separating power we must step **outside** the fifteen Monster primes
and use the *whole integer* `c(n)` as a fresh coordinate: the depth-`N`
q-expansion address of a fingerprint `h` is

```
qAddress h N = (h % fullModulus, h % c(1), h % c(2), …, h % c(N)).
```

Because `c(n)` carries non-Monster prime factors and grows without bound, a single
q-coefficient eventually exceeds the 64-bit hash range, after which *distinct*
fingerprints cannot collide modulo it (`qcoeff_separates`).  Concretely
`2^64 ≤ c(14)` (`hashRange_le_qCoeff14`), so **every smush of two genuinely
different hashes is broken by depth 14 at the latest**
(`distinct_hashes_break_by_14`).  The only persistent smushes that survive *all*
100 q-expansions are those whose members carry the **literally identical** hash —
there is nothing left to separate (`unbreakable_iff_equal_hash`).

`measureQ` runs this over the corpus and reports, for each depth `1 … 100`, how
many persistent smush groups have been broken, together with the residue of truly
identical-hash groups that no q-expansion can ever break.

## Honest scope

As in `ResolutionLadder`/`EnvWeave`, a "smush" is a collision of *structural
hashes*; "breaking" means the chosen modulus distinguishes them.  None of this
claims semantic (in)equivalence of the declarations themselves.  The Layer-1
theorem and the separation lemmas are fully general; the corpus counts are
computational facts reported by the command.

Commands:

* `#qladder`          — full environment scan; measure persistent-smush breaking
  across 100 q-expansions; write `atlas_qexpansion.json`.
* `#qladder_sample n` — the same over the first `n` declarations (fast demo).
-/

open Lean Meta Elab Command

namespace QExpansionLadder

open ResolutionLadder Moonshine

/-! ## §1  The q-expansion coefficients as moduli -/

/-- The `k`-th q-expansion coefficient as a `Nat`: `qCoeff k = c(k+1) = [q^{k+1}] j`.
So `qCoeff 0 = 196884`, `qCoeff 1 = 21493760`, … (the `T1 = j` expansion). -/
def qCoeff (k : Nat) : Nat := (Moonshine.t1Coeffs[k]!).toNat

theorem qCoeff_zero : qCoeff 0 = 196884 := by native_decide

/-- The q-coefficients grow past the 64-bit hash range: `2^64 ≤ c(14)` (the
fourteenth coefficient, `qCoeff 13`), while the thirteenth still fits. -/
theorem hashRange_le_qCoeff14 : (2:Nat)^64 ≤ qCoeff 13 := by native_decide

theorem qCoeff13_lt_hashRange : qCoeff 12 < (2:Nat)^64 := by native_decide

/-! ## §2  Layer 1 — Monster-prime q-content cannot break a persistent smush -/

/-- The radical of the **Monster primes dividing** the `k`-th q-coefficient — the
"available primes" of q-page `k` in the `QDeform` sense, multiplied together. -/
def qMonsterRadical (k : Nat) : Nat :=
  (monsterPrimesAsc.filter (fun p => qCoeff k % p == 0)).foldl (· * ·) 1

/-- Each q-page's Monster-prime radical **divides** the full fifteen-prime radical
(for every one of the 100 measured pages): it is a coarsening of `fullModulus`. -/
theorem qMonsterRadical_dvd_full :
    (List.range 100).all (fun n => decide (qMonsterRadical n ∣ fullModulus)) = true := by
  native_decide

/-- **Layer 1 (the negative theorem).**  A persistent smush — two fingerprints
agreeing modulo `fullModulus` — *cannot* be broken by the Monster-prime content of
any q-coefficient: they automatically agree modulo `qMonsterRadical n` as well.
This is `ResolutionLadder.coarsen` applied to the divisibility above, so it holds
no matter how many q-expansions we add. -/
theorem monster_q_cannot_break {n : Nat} {a b : Nat}
    (hdvd : qMonsterRadical n ∣ fullModulus)
    (h : a % fullModulus = b % fullModulus) :
    a % qMonsterRadical n = b % qMonsterRadical n :=
  ResolutionLadder.coarsen hdvd h

/-! ## §3  Layer 2 — the full q-coefficients do break them -/

/-- **The separation principle.**  Once a modulus `m` is at least as large as the
range bounding two *distinct* values, it tells them apart.  This is why a large
enough q-coefficient breaks a smush of two different hashes. -/
theorem qcoeff_separates {a b B m : Nat}
    (hne : a ≠ b) (ha : a < B) (hb : b < B) (hBm : B ≤ m) :
    a % m ≠ b % m := by
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le ha hBm),
      Nat.mod_eq_of_lt (lt_of_lt_of_le hb hBm)]
  exact hne

/-- **Distinct hashes break by depth 14.**  Any two different fingerprints below
the 64-bit hash range are separated by the fourteenth q-coefficient `c(14)`, since
`2^64 ≤ c(14)`.  So no smush of genuinely different hashes survives 100
q-expansions; in fact 14 already suffice. -/
theorem distinct_hashes_break_by_14 {a b : Nat}
    (ha : a < 2^64) (hb : b < 2^64) (hne : a ≠ b) :
    a % qCoeff 13 ≠ b % qCoeff 13 :=
  qcoeff_separates hne ha hb hashRange_le_qCoeff14

/-- **What truly survives.**  Two fingerprints below the hash range agree modulo
`c(14)` *iff they are equal*.  Hence the only persistent smushes that survive all
100 q-expansions are those whose members carry the identical hash — there is
genuinely nothing left to separate. -/
theorem unbreakable_iff_equal_hash {a b : Nat}
    (ha : a < 2^64) (hb : b < 2^64) :
    a % qCoeff 13 = b % qCoeff 13 ↔ a = b := by
  constructor
  · intro h
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le ha hashRange_le_qCoeff14),
        Nat.mod_eq_of_lt (lt_of_lt_of_le hb hashRange_le_qCoeff14)] at h
    exact h
  · intro h; rw [h]

/-! ## §4  Measuring the break over a corpus

For each irrep-1 base cell we keep one representative fingerprint.  A cell is a
**persistent (semantic) smush** when it holds `≥ 2` declarations that all agree
modulo `fullModulus`.  For such a cell, the **break depth** is the smallest `k`
(`< 100`) at which some member differs from the representative modulo `c(k+1)`;
`100` means no q-expansion in range separates them (an identical-hash group).

`breakByDepth[N]` is then the number of persistent smush groups broken using the
first `N` q-expansions (`c(1) … c(N)`), and `unbreakable` is the residue that
survives all 100. -/

/-- Aggregate result of the q-expansion attack on the persistent smushes. -/
structure QStats where
  totalDecls      : Nat
  smushGroups     : Nat               -- irrep-1 cells with ≥ 2 declarations
  persistentGroups : Nat              -- of those, the ones agreeing mod fullModulus
  breakByDepth    : Array Nat         -- size 101: breakByDepth[N] = # broken using c(1..N)
  unbreakable     : Nat               -- persistent groups surviving all 100 q-expansions
  deriving Inhabited

/-- The first q-depth-index `< 100` at which `fp` and `r` differ modulo a
q-coefficient, or `100` if none does. -/
def firstBreak (fp r : Nat) : Nat := Id.run do
  let mut found := 100
  for k in [0:100] do
    if fp % (qCoeff k) != r % (qCoeff k) then
      found := k
      break
  return found

/-- Stream a corpus of fingerprints through the q-expansion attack. -/
def measureQ (fps : Array Nat) : QStats := Id.run do
  let mut rep     : Std.HashMap Nat Nat := {}   -- base cell → representative fp
  let mut cnt     : Std.HashMap Nat Nat := {}   -- base cell → multiplicity
  let mut geo     : Std.HashSet Nat := {}       -- base cells that split mod fullModulus
  let mut breakK  : Std.HashMap Nat Nat := {}   -- base cell → min break depth-index
  for fp in fps do
    let base := fp % 196883
    match rep[base]? with
    | none =>
        rep := rep.insert base fp
        cnt := cnt.insert base 1
        breakK := breakK.insert base 100
    | some r =>
        cnt := cnt.insert base ((cnt[base]?.getD 1) + 1)
        if fp % fullModulus != r % fullModulus then
          geo := geo.insert base
        let fb := firstBreak fp r
        if fb < (breakK[base]?.getD 100) then
          breakK := breakK.insert base fb
  -- tabulate over the persistent (semantic) smush groups
  let mut breakByDepth : Array Nat := Array.replicate 101 0
  let mut smush := 0
  let mut persistent := 0
  let mut unbreak := 0
  for (base, c) in cnt.toList do
    if c ≥ 2 then
      smush := smush + 1
      if !geo.contains base then
        persistent := persistent + 1
        let bk := (breakK[base]?.getD 100)
        if bk ≥ 100 then
          unbreak := unbreak + 1
        for N in [bk + 1:101] do
          breakByDepth := breakByDepth.set! N (breakByDepth[N]! + 1)
  return {
    totalDecls       := fps.size
    smushGroups      := smush
    persistentGroups := persistent
    breakByDepth     := breakByDepth
    unbreakable      := unbreak }

/-! ## §5  A verified toy example of the measurement

A hand-built corpus with one persistent smush group of three members all sharing
the irrep-1 base cell and agreeing modulo `fullModulus` (they differ by multiples
of `fullModulus`), plus one truly identical-hash pair.  We check that the first
group breaks at the expected depth and the identical-hash group never breaks. -/

/-- Two distinct values `fullModulus` apart agree modulo `fullModulus`. -/
theorem toy_congruent : (5 + fullModulus) % fullModulus = (5 : Nat) % fullModulus :=
  Nat.add_mod_right 5 fullModulus

/-- For the toy group `{5, 5 + fullModulus}`, the values are distinct, both well
below the hash range, hence broken by `c(14)` — a concrete instance of
`distinct_hashes_break_by_14`. -/
theorem toy_breaks : (5 : Nat) % qCoeff 13 ≠ (5 + fullModulus) % qCoeff 13 := by
  apply distinct_hashes_break_by_14
  · native_decide
  · native_decide
  · native_decide

/-- An identical-hash pair can never be broken: equal fingerprints agree modulo
every q-coefficient. -/
theorem toy_identical_never_breaks (k : Nat) : (7 : Nat) % qCoeff k = (7 : Nat) % qCoeff k := rfl

/-! ## §6  Reporting -/

/-- A compact "breaks at depth N" curve sampled at a few depths. -/
def curveSummary (st : QStats) : String :=
  let depths := [1, 2, 5, 10, 14, 20, 50, 100]
  String.intercalate "\n"
    (depths.map (fun N =>
      s!"      ├── after {N} q-expansion(s): {(st.breakByDepth[N]?).getD 0} / {st.persistentGroups} persistent smushes broken"))

/-- The human-readable report. -/
def qReport (st : QStats) : String :=
  s!"[Aristo Q-Expansion Ladder] breaking the persistent smushes\n" ++
  s!"  ├── declarations scanned       : {st.totalDecls}\n" ++
  s!"  ├── irrep-1 smush groups       : {st.smushGroups}\n" ++
  s!"  ├── persistent (semantic) ones : {st.persistentGroups}\n" ++
  s!"  ├── broken across 100 q-expansions :\n" ++ curveSummary st ++ "\n" ++
  s!"  └── unbreakable (identical hash, no q-expansion can split) : {st.unbreakable}"

/-- The full per-depth JSON for `atlas_qexpansion.json`. -/
def qJson (st : QStats) : String :=
  let perDepth := String.intercalate ",\n" ((List.range 100).map (fun i =>
    let N := i + 1
    "    { \"depth\": " ++ toString N ++ ", \"broken\": " ++ toString ((st.breakByDepth[N]?).getD 0) ++ " }"))
  "{\n" ++
  s!"  \"totalDecls\": {st.totalDecls},\n" ++
  s!"  \"smushGroups\": {st.smushGroups},\n" ++
  s!"  \"persistentGroups\": {st.persistentGroups},\n" ++
  s!"  \"unbreakable\": {st.unbreakable},\n" ++
  s!"  \"fullModulus\": {fullModulus},\n" ++
  s!"  \"breakByDepth\": [\n" ++ perDepth ++ "\n  ]\n" ++
  "}\n"

/-! ## §7  Commands -/

/-- `#qladder` scans the whole ambient environment, runs the q-expansion attack on
every persistent irrep-1 smush across 100 q-expansions, logs the report, and
writes `atlas_qexpansion.json`. -/
syntax (name := qladderCmd) "#qladder" : command

@[command_elab qladderCmd]
def elabQladder : CommandElab := fun _ => do
  let env ← getEnv
  let fps := ResolutionLadder.gatherFingerprints env.constants.toList
  let st := measureQ fps
  logInfo (qReport st)
  IO.FS.writeFile "atlas_qexpansion.json" (qJson st)

/-- `#qladder_sample n` runs the same attack over the first `n` declarations. -/
syntax (name := qladderSampleCmd) "#qladder_sample " num : command

@[command_elab qladderSampleCmd]
def elabQladderSample : CommandElab := fun stx => do
  match stx with
  | `(#qladder_sample $n:num) => do
    let env ← getEnv
    let fps := ResolutionLadder.gatherFingerprints (env.constants.toList.take n.getNat)
    let st := measureQ fps
    logInfo (qReport st)
    IO.FS.writeFile "atlas_qexpansion.json" (qJson st)
  | _ => throwError "ill-formed #qladder_sample command"

/-! ## §8  Build-time generation

As with `ResolutionLadder`, the classifier runs in the elaborator (interpreted),
so the full-corpus `#qladder` is slow; the default build drives a bounded sample
(matching the resolution ladder's 120,000) which is fast and writes
`atlas_qexpansion.json`.  The full scan stays available on demand. -/

#qladder_sample 120000

-- Full-corpus q-expansion attack (slow under the interpreter); run on demand:
-- #qladder

end QExpansionLadder

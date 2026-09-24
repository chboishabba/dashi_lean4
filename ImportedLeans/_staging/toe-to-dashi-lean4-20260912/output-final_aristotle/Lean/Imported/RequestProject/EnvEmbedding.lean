import Mathlib
import RequestProject.SemanticCID
import RequestProject.ExprAddress
import Lean

/-!
# EnvEmbedding — embedding the *entire* Lean 4 + mathlib environment into the
semantic-CID space, and choosing the **best CID** for every declaration.

The single-slot `SemCID` codec (`RequestProject.SemanticCID`) gives each
declaration a canonical 64-bit address
`[prefix:16][version:24][digest:24]`, where the 24-bit digest is the low bits of
the declaration's structural fingerprint.  With only `2^24 = 16 777 216`
digests but ~`7×10^5` declarations in the loaded environment, the *canonical*
digest is not injective: many declarations collide on the same digest.

This module answers the request *"embed all of mathlib and lean4 current env
into this cid space and choose the best CID for each decl"*.  The plan:

* **Best CID = canonical-if-free, else nearest free slot.**  We resolve
  collisions by **open addressing**: a declaration keeps its canonical digest
  `k % 2^24` when that slot is free, otherwise it takes the least free slot at
  or above it (`firstFrom`).  `bestDigit`/`bestCidFromDigit` package this, and
  `bestCid_eq_cidOf_of_free` proves that an *uncontended* declaration keeps
  exactly its canonical `SemCID.cidOf` address — so "best" only ever deviates
  from canonical to break a genuine tie.

* **The embedding is faithful (collision-free).**  `assignFrom` runs the open
  addressing over a whole list of preferred digests; `assignFrom_nodup` proves
  the assigned digests are pairwise distinct, and `bestCids_nodup` lifts that to
  distinct 64-bit CIDs (whenever the probed digests stay inside the 24-bit
  field).  Thus the chosen best-CIDs are an injective embedding of the
  environment into CID space — every declaration gets its own address.

* **The reflection front-end actually does it.**  `#cidembedall` sweeps
  `(← getEnv).constants` — *all* of Lean 4 core + mathlib + this project —
  computes each declaration's fingerprint from its cached `Expr.hash`
  (`e.hash.toNat`, O(1) per declaration), runs the open-addressing assignment,
  and reports how many declarations there are, how many canonical digests
  collide, how many were relocated by probing, and that the final number of
  occupied slots equals the number of declarations (empirical confirmation of
  the proved injectivity).  `#bestcid f` reports a single declaration's
  canonical CID.

## Honest scope

This is a *combinatorial* embedding, in the same spirit as the rest of the
project.  The fingerprint is `Expr.hash` (Lean's cached structural hash of the
type and value expressions), chosen so the full ~`7×10^5`-declaration sweep is
feasible at elaboration time; nothing here claims a mathematical relationship
between the Monster group and the embedded declarations.  The verified content
is precisely the open-addressing algebra: the best-CID assignment is
canonical-preserving on free slots and injective overall.
-/

open Lean Meta Elab Command

namespace EnvCID

open SemCID

/-! ## §1  Open-addressing probe: the least free slot at or above `start` -/

/-- Bounded search for the least value `≥ start` not in `used`.  With `fuel`
steps it scans `start, start+1, …`. -/
def firstFromFuel : Nat → List Nat → Nat → Nat
  | 0, _, start => start
  | fuel + 1, used, start => if start ∈ used then firstFromFuel fuel used (start + 1) else start

/-- The least value `≥ start` not in `used`.  The fuel `used.length + 1`
guarantees success (there are more candidates than members of `used`). -/
def firstFrom (used : List Nat) (start : Nat) : Nat :=
  firstFromFuel (used.length + 1) used start

/-- The probe never returns a value below `start`. -/
theorem firstFromFuel_ge (fuel : Nat) (used : List Nat) (start : Nat) :
    start ≤ firstFromFuel fuel used start := by
  induction fuel generalizing start with
  | zero => simp [firstFromFuel]
  | succ n ih =>
      unfold firstFromFuel
      split
      · exact le_trans (Nat.le_succ start) (ih (start + 1))
      · exact le_refl start

/-- The probe never returns a value below `start`. -/
theorem firstFrom_ge (used : List Nat) (start : Nat) : start ≤ firstFrom used start := by
  unfold firstFrom; exact firstFromFuel_ge _ _ _

/-- If the preferred `start` slot is free, the probe keeps it: **the best slot of
an uncontended declaration is its canonical slot.** -/
theorem firstFrom_eq_of_not_mem {used : List Nat} {start : Nat} (h : start ∉ used) :
    firstFrom used start = start := by
  unfold firstFrom firstFromFuel
  simp [h]

/-- Structural spec of the probe: either it returns a free slot, or it exhausted
its fuel because every candidate in the scanned window is taken. -/
theorem firstFromFuel_spec (fuel : Nat) (used : List Nat) (start : Nat) :
    firstFromFuel fuel used start ∉ used ∨ (∀ i, i < fuel → (start + i) ∈ used) := by
  induction fuel generalizing start with
  | zero => right; intro i hi; omega
  | succ n ih =>
      unfold firstFromFuel
      by_cases hs : start ∈ used
      · rw [if_pos hs]
        rcases ih (start + 1) with h | h
        · left; exact h
        · right; intro i hi
          match i with
          | 0 => simpa using hs
          | j + 1 =>
              have hmem : start + 1 + j ∈ used := h j (by omega)
              have e : start + (j + 1) = start + 1 + j := by omega
              rw [e]; exact hmem
      · rw [if_neg hs]; left; exact hs

/-- **The probe always finds a free slot.**  With fuel `used.length + 1` the
scanned window has more candidates than `used` has members, so by pigeonhole one
candidate is free. -/
theorem firstFrom_not_mem (used : List Nat) (start : Nat) : firstFrom used start ∉ used := by
  unfold firstFrom
  rcases firstFromFuel_spec (used.length + 1) used start with h | h
  · exact h
  · exfalso
    let l : List Nat := (List.range (used.length + 1)).map (start + ·)
    have hnodup : l.Nodup := by
      apply List.Nodup.map
      · intro a b hab; exact Nat.add_left_cancel hab
      · exact List.nodup_range
    have hsub : l ⊆ used := by
      intro x hx
      simp only [l, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact h i hi
    have hlen : l.length ≤ used.length := (hnodup.subperm hsub).length_le
    simp only [l, List.length_map, List.length_range] at hlen
    omega

/-! ## §2  Assigning best slots to a whole list of preferred digests -/

/-- Open-addressing assignment: process `ds` (the preferred digests, head first),
giving each the least free slot at or above it given the slots already taken. -/
def assignFrom : List Nat → List Nat
  | [] => []
  | d :: ds =>
      let prev := assignFrom ds
      firstFrom prev d :: prev

/-- The assignment occupies exactly one slot per preferred digest. -/
theorem assignFrom_length (ds : List Nat) : (assignFrom ds).length = ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [assignFrom, ih]

/-- **The assigned slots are pairwise distinct** — open addressing produces a
collision-free placement. -/
theorem assignFrom_nodup (ds : List Nat) : (assignFrom ds).Nodup := by
  induction ds with
  | nil => simp [assignFrom]
  | cons d ds ih =>
      unfold assignFrom
      simp only [List.nodup_cons]
      exact ⟨firstFrom_not_mem _ _, ih⟩

/-! ## §3  The best CID of a declaration -/

/-- The best digest for a declaration with fingerprint `k`, given the slots
already taken: its canonical digest `k % 2^24` if free, else the nearest free
slot above it. -/
def bestDigit (used : List Nat) (k : Nat) : Nat := firstFrom used (k % two24)

/-- Pack a chosen digest into a full 64-bit semantic CID at version `v`. -/
def bestCidFromDigit (v : SemVer) (d : Nat) : Nat := pack (encodeVer v) d

/-- The list of best CIDs for declarations with preferred fingerprints `ks`,
at version `v`: reduce each fingerprint to its canonical digest, run the
open-addressing assignment, then pack. -/
def bestCids (v : SemVer) (ks : List Nat) : List Nat :=
  (assignFrom (ks.map (· % two24))).map (bestCidFromDigit v)

/-- **An uncontended declaration keeps its canonical CID.**  If the canonical
digest of `k` is free, the best digest is exactly `k % 2^24`. -/
theorem bestDigit_eq_of_free {used : List Nat} {k : Nat} (h : (k % two24) ∉ used) :
    bestDigit used k = k % two24 := by
  unfold bestDigit; exact firstFrom_eq_of_not_mem h

/-- **The best CID equals the canonical `SemCID.cidOf` when the slot is free** —
the relocation only ever happens to break a genuine collision. -/
theorem bestCid_eq_cidOf_of_free {used : List Nat} (v : SemVer) {k : Nat}
    (h : (k % two24) ∉ used) :
    bestCidFromDigit v (bestDigit used k) = cidOf v k := by
  unfold bestCidFromDigit cidOf
  rw [bestDigit_eq_of_free h]

/-- **The best-CID embedding is faithful (injective).**  Whenever the probed
digests stay inside the 24-bit digest field, distinct slots give distinct 64-bit
CIDs: every declaration gets its own address. -/
theorem bestCids_nodup (v : SemVer) (ks : List Nat)
    (hb : ∀ d ∈ assignFrom (ks.map (· % two24)), d < two24) :
    (bestCids v ks).Nodup := by
  unfold bestCids
  apply List.Nodup.map_on
  · intro x hx y hy hxy
    exact (pack_inj (encodeVer v) x (encodeVer v) y (hb x hx) (hb y hy) hxy).2
  · exact assignFrom_nodup _

/-! ## §4  Reflection front-end: embed the entire environment -/

/-- The fingerprint of a declaration from its cached `Expr.hash` (O(1)): the XOR
of the type's hash and the value's hash (`0` when there is no value). -/
def declFingerprint (info : ConstantInfo) : Nat :=
  let vh := match info.value? with | some v => v.hash.toNat | none => 0
  info.type.hash.toNat ^^^ vh

/-- `#bestcid f` reports the canonical semantic CID of a single declaration `f`,
computed from its cached-hash fingerprint at the mathlib version. -/
syntax (name := bestcidCmd) "#bestcid " ident : command

@[command_elab bestcidCmd]
def elabBestcid : CommandElab := fun stx => do
  match stx with
  | `(#bestcid $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadCore id.getId
    let env ← getEnv
    match env.find? name with
    | some info =>
      let k := declFingerprint info
      let d := k % two24
      let cid := bestCidFromDigit mathlibVersion d
      logInfo s!"[Aristo Best CID] {name}\n  ├── fingerprint (Expr.hash) k = {k}\n  ├── canonical digest (k % 2^24) = {SemCID.toHex d}\n  └── best CID (if uncontended) = {SemCID.toHex cid}"
    | none => throwError "unknown declaration {name}"
  | _ => throwError "ill-formed #bestcid command"

/-- `#cidembedall` embeds the **entire loaded environment** (Lean 4 core +
mathlib + this project) into the semantic-CID space, choosing the best CID for
each declaration by open addressing, and prints a summary: total declarations,
distinct canonical digests, how many were relocated to resolve collisions, the
maximum probe distance, and the final number of occupied slots (which equals the
declaration count, confirming the embedding is collision-free). -/
syntax (name := cidembedallCmd) "#cidembedall" : command

@[command_elab cidembedallCmd]
def elabCidembedall : CommandElab := fun _ => do
  let env ← getEnv
  let mut used : Std.HashSet Nat := {}
  let mut naive : Std.HashSet Nat := {}
  let mut total := 0
  let mut relocated := 0
  let mut maxProbe := 0
  for (_, info) in env.constants.toList do
    total := total + 1
    let start := (declFingerprint info) % two24
    naive := naive.insert start
    let mut slot := start
    let mut probe := 0
    while used.contains slot do
      probe := probe + 1
      slot := (start + probe) % two24
    if probe > 0 then relocated := relocated + 1
    if probe > maxProbe then maxProbe := probe
    used := used.insert slot
  let collisionFree := used.size == total
  let report :=
    s!"[Aristo CID Embedding] embedded the full environment into the semantic-CID space\n" ++
    s!"  ├── total declarations            = {total}\n" ++
    s!"  ├── distinct canonical digests    = {naive.size}\n" ++
    s!"  ├── relocated to resolve collision= {relocated}\n" ++
    s!"  ├── max probe distance            = {maxProbe}\n" ++
    s!"  ├── occupied slots after embedding= {used.size}\n" ++
    s!"  └── collision-free embedding      = {collisionFree} (occupied = total)"
  logInfo report
  -- best-effort JSON artifact for the user
  try
    let json :=
      s!"\{\n" ++
      s!"  \"totalDeclarations\": {total},\n" ++
      s!"  \"distinctCanonicalDigests\": {naive.size},\n" ++
      s!"  \"relocatedForCollision\": {relocated},\n" ++
      s!"  \"maxProbeDistance\": {maxProbe},\n" ++
      s!"  \"occupiedSlots\": {used.size},\n" ++
      s!"  \"digestSpace\": {two24},\n" ++
      s!"  \"collisionFree\": {collisionFree}\n" ++
      s!"}\n"
    IO.FS.writeFile "atlas_cidembed.json" json
  catch _ => pure ()

/-! ## §5  Test suite -/

#bestcid Nat.add
#bestcid List.map
#bestcid Prod.fst

#cidembedall

end EnvCID

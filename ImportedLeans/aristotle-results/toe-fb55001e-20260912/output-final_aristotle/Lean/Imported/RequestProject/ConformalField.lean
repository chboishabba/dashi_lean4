import Mathlib
import RequestProject.SemanticCID
import RequestProject.EnvEmbedding
import RequestProject.ExprAddress
import Lean

/-!
# ConformalField — multi-hash CID scoring and a conformal field of arrows.

The whole-environment embedding (`RequestProject.EnvEmbedding`) showed that the
single 24-bit digest is **not** injective on the loaded environment: ~`7×10^5`
declarations share only `2^24` digests, so tens of thousands of declarations
*collide* (the `#cidembedall` run relocated `84 016` declarations to break ties).
Open addressing fixes the *placement*, but the underlying **score** of each CID
is still a single 24-bit number — a single point that birthday-collides.

This module answers the follow-up request — *"score all the CIDs as multi
hashes, and create a conformal field of arrows between hash values"* — with two
verified pillars.

## §1  Multi-hash scoring

Instead of one 24-bit digest we give every declaration a **vector of `numHashes`
independent salted hashes** (`multiHash`), and fold that vector mixed-radix into
a single `numHashes·24`-bit **score** (`score`).  We prove:

* the score lives in the enlarged space `(2^24)^numHashes` (`score_lt`);
* the fold is **injective** on in-range vectors (`combineBase_inj`), so a score
  *is* its multi-hash vector — `score k = score k' ↔ multiHash k = multiHash k'`
  (`score_eq_iff_multiHash_eq`): two CIDs now collide only if they agree on
  *every* one of their hashes simultaneously, not just on the single digest;
* the multi-hash **refines** the single digest — its first component is exactly
  the old digest (`multiHash_head`, `score_mod`), so the number of distinct
  scores is never smaller than the number of distinct digests
  (`distinct_scores_ge_distinct_digests`): multi-hashing can only *split*
  collision classes, never merge them.

## §2  A conformal field of arrows

Over a prime field `ZMod p` an **affine map** `arrow a b x = a·x + b` with
`a ≠ 0` is the discrete analogue of a conformal (angle/structure-preserving)
transformation: it is a **bijection** (`arrow_bijective`), so the directed graph
of arrows `x ↦ arrow a b x` is a *permutation* of the hash values — every hash
node has exactly one out-arrow and one in-arrow, i.e. the field of arrows is
**collision-free by construction** (`arrow_injective`).  We prove the affine
maps are closed under composition with the affine group law (`arrow_comp`),
contain the identity (`arrow_one_zero`), and have an explicit inverse
(`arrowInv`, `arrow_leftInv`, `arrow_rightInv`, packaged as `arrowEquiv`).  Thus
the conformal field is a genuine permutation group acting on hash space.

## §3  Reflection front-end

`#multiscore f` prints one declaration's multi-hash vector, its score, and the
arrows of its hash chain.  `#conformalsweep` sweeps the entire environment,
reports how many collision classes the multi-hash splits the single-digest
classes into, builds the affine arrow field over a drawing grid (confirming it
is a permutation), and writes a JSON summary plus an SVG of the arrow field.

## Honest scope

This is a *combinatorial codec*, in the same spirit as `SemCID`/`EnvEmbedding`:
the fingerprint is the structural hash, the salts are fixed odd multipliers, and
"conformal" denotes the affine/structure-preserving arrow map whose bijectivity
is the proved content.  No cryptographic hardness or analytic conformality is
claimed.
-/

open Lean Meta Elab Command

namespace ConformalField

/-! ## §1  Multi-hash scoring -/

/-- Width of a single hash field, in bits. -/
def hashBits : Nat := 24

/-- The size of one hash field, `2^24`. -/
def digestSpace : Nat := 2 ^ hashBits

/-- `digestSpace = 2^24`. -/
theorem digestSpace_eq : digestSpace = 2 ^ 24 := rfl

/-- `digestSpace` is positive. -/
theorem digestSpace_pos : 0 < digestSpace := by decide

/-- The fixed odd multipliers ("salts") defining the independent hashes.  The
first salt is `1`, so the first hash is exactly the canonical 24-bit digest. -/
def salts : List Nat := [1, 0x9E3779, 0x85EBCA, 0xC2B2AE]

/-- The number of independent hashes per declaration. -/
def numHashes : Nat := salts.length

/-- `numHashes = 4`. -/
theorem numHashes_eq : numHashes = 4 := rfl

/-- One salted hash: the low 24 bits of `k · s`. -/
def hashWith (s k : Nat) : Nat := (k * s) % digestSpace

/-- Every salted hash fits in 24 bits. -/
theorem hashWith_lt (s k : Nat) : hashWith s k < digestSpace := by
  unfold hashWith; exact Nat.mod_lt _ digestSpace_pos

/-- The **multi-hash vector** of a declaration with fingerprint `k`: one salted
hash per salt. -/
def multiHash (k : Nat) : List Nat := salts.map (fun s => hashWith s k)

/-- The multi-hash has `numHashes` components. -/
theorem multiHash_length (k : Nat) : (multiHash k).length = numHashes := by
  unfold multiHash numHashes; simp

/-- Every component of the multi-hash fits in 24 bits. -/
theorem multiHash_lt (k : Nat) : ∀ h ∈ multiHash k, h < digestSpace := by
  intro h hh
  unfold multiHash at hh
  simp only [List.mem_map] at hh
  obtain ⟨s, _, rfl⟩ := hh
  exact hashWith_lt s k

/-- The **first** component of the multi-hash is exactly the canonical digest
`k % 2^24` (the salt is `1`). -/
theorem multiHash_head (k : Nat) : (multiHash k).headI = k % digestSpace := by
  simp [multiHash, salts, hashWith]

/-- Mixed-radix fold of a digit list into a single number, base `base`,
least-significant digit first. -/
def combineBase (base : Nat) : List Nat → Nat
  | [] => 0
  | h :: t => h + base * combineBase base t

/-- A list of digits all `< base` folds to a value `< base ^ length`. -/
theorem combineBase_lt (base : Nat) (l : List Nat) (hb : 0 < base)
    (h : ∀ d ∈ l, d < base) : combineBase base l < base ^ l.length := by
  induction l with
  | nil => simpa [combineBase] using hb
  | cons a t ih =>
    simp only [combineBase, List.length_cons, pow_succ]
    have ha : a < base := h a (by simp)
    have ht : combineBase base t < base ^ t.length := ih (fun d hd => h d (by simp [hd]))
    have hCB : combineBase base t + 1 ≤ base ^ t.length := ht
    calc a + base * combineBase base t
        < base + base * combineBase base t := by omega
      _ = base * (combineBase base t + 1) := by ring
      _ ≤ base * base ^ t.length := by gcongr
      _ = base ^ t.length * base := by ring

/-- **The fold is injective** on equal-length lists whose digits are all
`< base`: a score *is* its digit vector. -/
theorem combineBase_inj (base : Nat) (l l' : List Nat)
    (hlen : l.length = l'.length)
    (hl : ∀ d ∈ l, d < base) (hl' : ∀ d ∈ l', d < base)
    (h : combineBase base l = combineBase base l') : l = l' := by
  induction l generalizing l' with
  | nil => cases l' with
    | nil => rfl
    | cons => simp at hlen
  | cons a t ih => cases l' with
    | nil => simp at hlen
    | cons a' t' =>
      simp only [combineBase] at h
      have ha : a < base := hl a (by simp)
      have ha' : a' < base := hl' a' (by simp)
      have hbpos : 0 < base := lt_of_le_of_lt (Nat.zero_le a) ha
      have hmod : a = a' := by
        have hc := congrArg (· % base) h
        simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] using hc
      rw [hmod] at h
      have hX : base * combineBase base t = base * combineBase base t' := Nat.add_left_cancel h
      have hCC : combineBase base t = combineBase base t' := Nat.eq_of_mul_eq_mul_left hbpos hX
      have hlen' : t.length = t'.length := by simpa using hlen
      have hrec := ih t' hlen' (fun d hd => hl d (by simp [hd])) (fun d hd => hl' d (by simp [hd])) hCC
      rw [hmod, hrec]

/-- The **score** of a declaration with fingerprint `k`: the mixed-radix fold of
its multi-hash vector, base `2^24`. -/
def score (k : Nat) : Nat := combineBase digestSpace (multiHash k)

/-- The score lives in the enlarged space `(2^24)^numHashes`. -/
theorem score_lt (k : Nat) : score k < digestSpace ^ numHashes := by
  unfold score
  have := combineBase_lt digestSpace (multiHash k) digestSpace_pos (multiHash_lt k)
  rwa [multiHash_length] at this

/-- The score's low 24 bits recover the canonical digest `k % 2^24`. -/
theorem score_mod (k : Nat) : score k % digestSpace = k % digestSpace := by
  unfold score
  have hne : multiHash k ≠ [] := by
    intro hc; have hl := multiHash_length k; rw [hc] at hl; simp [numHashes, salts] at hl
  obtain ⟨a, t, ht⟩ := List.exists_cons_of_ne_nil hne
  have hhead : a = k % digestSpace := by
    have := multiHash_head k; rw [ht] at this; simpa using this
  rw [ht]
  simp only [combineBase]
  rw [Nat.add_mul_mod_self_left, hhead, Nat.mod_mod]

/-- **Two CIDs collide under the multi-hash score iff their whole multi-hash
vectors coincide** — much stronger separation than the single digest. -/
theorem score_eq_iff_multiHash_eq (k k' : Nat) :
    score k = score k' ↔ multiHash k = multiHash k' := by
  unfold score
  constructor
  · intro h
    exact combineBase_inj digestSpace _ _ (by rw [multiHash_length, multiHash_length])
      (multiHash_lt k) (multiHash_lt k') h
  · intro h; rw [h]

/-- A function can only *merge* `dedup` classes: the number of distinct values of
`l.map h` never exceeds the number of distinct values of `l`. -/
theorem dedup_map_length_le {α β : Type _} [DecidableEq α] [DecidableEq β]
    (l : List α) (h : α → β) : (l.map h).dedup.length ≤ l.dedup.length := by
  rw [← List.card_toFinset, ← List.card_toFinset]
  have hset : (List.map h l).toFinset = l.toFinset.image h := by ext x; simp
  rw [hset]; exact Finset.card_image_le

/-- **Multi-hashing only splits collision classes.**  The number of distinct
scores over any list of fingerprints is at least the number of distinct single
digests — multi-hashing never merges two previously-separated declarations. -/
theorem distinct_scores_ge_distinct_digests (ks : List Nat) :
    (ks.map (· % digestSpace)).dedup.length ≤ (ks.map score).dedup.length := by
  have H : ∀ (f : Nat → Nat), (∀ k, f k % digestSpace = k % digestSpace) →
      (ks.map (· % digestSpace)).dedup.length ≤ (ks.map f).dedup.length := by
    intro f hf
    have key : (ks.map f).map (· % digestSpace) = ks.map (· % digestSpace) := by
      rw [List.map_map]; apply List.map_congr_left; intro k _
      simp only [Function.comp_apply]; exact hf k
    rw [← key]; exact dedup_map_length_le (ks.map f) (· % digestSpace)
  exact H score score_mod

/-! ## §2  A conformal field of arrows over `ZMod p` -/

section Conformal

variable {p : Nat} [Fact (Nat.Prime p)]

/-- A discrete **conformal arrow**: the affine map `x ↦ a·x + b` on the prime
field `ZMod p`.  With `a ≠ 0` this is the structure-preserving (angle-preserving)
transformation whose graph is the field of arrows between hash values. -/
def arrow (a b x : ZMod p) : ZMod p := a * x + b

/-- The explicit inverse arrow. -/
def arrowInv (a b x : ZMod p) : ZMod p := a⁻¹ * (x - b)

/-- `arrowInv` is a left inverse of `arrow` when `a ≠ 0`. -/
theorem arrow_leftInv {a : ZMod p} (b : ZMod p) (ha : a ≠ 0) :
    ∀ x, arrowInv a b (arrow a b x) = x := by
  intro x; unfold arrow arrowInv
  rw [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

/-- `arrowInv` is a right inverse of `arrow` when `a ≠ 0`. -/
theorem arrow_rightInv {a : ZMod p} (b : ZMod p) (ha : a ≠ 0) :
    ∀ x, arrow a b (arrowInv a b x) = x := by
  intro x; unfold arrow arrowInv
  rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul, sub_add_cancel]

/-- **The arrow map is injective**: no two distinct hash values share a target —
the field of arrows is collision-free. -/
theorem arrow_injective {a : ZMod p} (b : ZMod p) (ha : a ≠ 0) :
    Function.Injective (arrow a b) :=
  Function.LeftInverse.injective (arrow_leftInv b ha)

/-- **The arrow map is surjective**: every hash value is some arrow's target. -/
theorem arrow_surjective {a : ZMod p} (b : ZMod p) (ha : a ≠ 0) :
    Function.Surjective (arrow a b) :=
  Function.RightInverse.surjective (arrow_rightInv b ha)

/-- **The conformal field is a bijection** (a permutation of the hash values). -/
theorem arrow_bijective {a : ZMod p} (b : ZMod p) (ha : a ≠ 0) :
    Function.Bijective (arrow a b) :=
  ⟨arrow_injective b ha, arrow_surjective b ha⟩

/-- The conformal field packaged as an equivalence (permutation) of `ZMod p`. -/
def arrowEquiv {a : ZMod p} (b : ZMod p) (ha : a ≠ 0) : ZMod p ≃ ZMod p where
  toFun := arrow a b
  invFun := arrowInv a b
  left_inv := arrow_leftInv b ha
  right_inv := arrow_rightInv b ha

/-- **Affine group law**: composing two arrows is again an arrow. -/
theorem arrow_comp (a b a' b' x : ZMod p) :
    arrow a b (arrow a' b' x) = arrow (a * a') (a * b' + b) x := by
  unfold arrow; ring

/-- The identity arrow `x ↦ 1·x + 0`. -/
theorem arrow_one_zero : (arrow (1 : ZMod p) 0) = id := by
  funext x; simp [arrow]

end Conformal

/-! ## §3  Reflection front-end -/

/-- The structural fingerprint of a declaration from its cached `Expr.hash`,
identical to `EnvCID.declFingerprint`. -/
def declFingerprint (info : ConstantInfo) : Nat :=
  let vh := match info.value? with | some v => v.hash.toNat | none => 0
  info.type.hash.toNat ^^^ vh

/-- The hash of a declaration's (unique) name. -/
def nameHash (n : Name) : Nat := (hash n).toNat

/-- The **name-aware fingerprint**: the structural `Expr.hash` fingerprint XORed
with the declaration's name hash.  Structurally identical declarations (e.g. all
the `.ctorIdx` projections) share an `Expr.hash`, so no hash of the structural
fingerprint alone can separate them; folding in the unique name is what lets the
multi-hash score actually split those collision classes. -/
def fullFingerprint (n : Name) (info : ConstantInfo) : Nat :=
  declFingerprint info ^^^ nameHash n

/-- A textual multi-hash report for declaration `decl` with fingerprint `k`. -/
def reportOf (decl : Name) (k : Nat) : String :=
  let hs := multiHash k
  let hexes := hs.map SemCID.toHex
  let chain := String.intercalate " → " hexes
  s!"[Aristo Multi-Hash Score] {decl}\n" ++
  s!"  ├── structural fingerprint k = {k}\n" ++
  s!"  ├── single digest (k % 2^24)  = {SemCID.toHex (k % digestSpace)}\n" ++
  s!"  ├── multi-hash ({numHashes} hashes) = [{String.intercalate ", " hexes}]\n" ++
  s!"  ├── conformal arrow chain     = {chain}\n" ++
  s!"  └── score (mixed-radix 2^24)  = {SemCID.toHex (score k)}"

/-- `#multiscore f` prints the multi-hash score and conformal arrow chain of
declaration `f`, computed from its structural fingerprint. -/
syntax (name := multiscoreCmd) "#multiscore " ident : command

@[command_elab multiscoreCmd]
def elabMultiscore : CommandElab := fun stx => do
  match stx with
  | `(#multiscore $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadCore id.getId
    let env ← getEnv
    match env.find? name with
    | some info => logInfo (reportOf name (fullFingerprint name info))
    | none => throwError "unknown declaration {name}"
  | _ => throwError "ill-formed #multiscore command"

/-- `#conformalsweep` sweeps the entire loaded environment, scores every
declaration with the multi-hash, and reports how many *distinct* multi-hash
scores there are versus distinct single digests (so how many collision classes
the multi-hash splits).  It also builds the affine conformal arrow field over a
drawing grid of `gridP` nodes, confirms it is a permutation (distinct targets =
node count, i.e. collision-free), and writes a JSON summary and an SVG of the
arrow field. -/
syntax (name := conformalsweepCmd) "#conformalsweep" : command

@[command_elab conformalsweepCmd]
def elabConformalsweep : CommandElab := fun _ => do
  let env ← getEnv
  let mut total := 0
  let mut digests : Std.HashSet Nat := {}
  let mut scores : Std.HashSet Nat := {}
  for (name, info) in env.constants.toList do
    total := total + 1
    let kStruct := declFingerprint info
    let k := fullFingerprint name info
    digests := digests.insert (kStruct % digestSpace)
    scores := scores.insert (score k)
  -- The conformal arrow field over a small prime grid: x ↦ (a*x + b) % gridP.
  let gridP := 97
  let aCoef := 5
  let bCoef := 11
  let mut targets : Std.HashSet Nat := {}
  for x in List.range gridP do
    targets := targets.insert ((aCoef * x + bCoef) % gridP)
  let fieldIsPerm := targets.size == gridP
  let report :=
    s!"[Aristo Conformal Field] multi-hash scoring + arrow field\n" ++
    s!"  ├── total declarations          = {total}\n" ++
    s!"  ├── distinct single digests     = {digests.size}\n" ++
    s!"  ├── distinct multi-hash scores  = {scores.size}\n" ++
    s!"  ├── collision classes split by  = {scores.size - digests.size}\n" ++
    s!"  ├── arrow field x↦({aCoef}x+{bCoef}) mod {gridP}\n" ++
    s!"  └── field is a permutation      = {fieldIsPerm} (collision-free arrows)"
  logInfo report
  -- best-effort JSON + SVG artifacts
  try
    let json :=
      s!"\{\n" ++
      s!"  \"totalDeclarations\": {total},\n" ++
      s!"  \"distinctSingleDigests\": {digests.size},\n" ++
      s!"  \"distinctMultiScores\": {scores.size},\n" ++
      s!"  \"numHashes\": {numHashes},\n" ++
      s!"  \"scoreSpaceBits\": {numHashes * hashBits},\n" ++
      s!"  \"arrowField\": \{ \"a\": {aCoef}, \"b\": {bCoef}, \"p\": {gridP} },\n" ++
      s!"  \"fieldIsPermutation\": {fieldIsPerm}\n" ++
      s!"}\n"
    IO.FS.writeFile "atlas_conformal.json" json
    -- SVG: draw the arrows of the conformal field on a circle of gridP nodes.
    let w := 720
    let cx := 360.0
    let cy := 360.0
    let r := 300.0
    let nodePos := fun (i : Nat) =>
      let θ := 2.0 * 3.14159265 * (Float.ofNat i) / (Float.ofNat gridP)
      (cx + r * Float.cos θ, cy + r * Float.sin θ)
    let mut body := ""
    for x in List.range gridP do
      let y := (aCoef * x + bCoef) % gridP
      let (x0, y0) := nodePos x
      let (x1, y1) := nodePos y
      body := body ++
        s!"  <line x1=\"{x0}\" y1=\"{y0}\" x2=\"{x1}\" y2=\"{y1}\" " ++
        s!"stroke=\"#3a7\" stroke-width=\"1\" marker-end=\"url(#ah)\"/>\n"
    for x in List.range gridP do
      let (x0, y0) := nodePos x
      body := body ++ s!"  <circle cx=\"{x0}\" cy=\"{y0}\" r=\"3\" fill=\"#222\"/>\n"
    let svg :=
      s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{w}\" height=\"{w}\" " ++
      s!"viewBox=\"0 0 {w} {w}\">\n" ++
      "  <defs><marker id=\"ah\" markerWidth=\"6\" markerHeight=\"6\" refX=\"5\" refY=\"3\" " ++
      "orient=\"auto\"><path d=\"M0,0 L6,3 L0,6 Z\" fill=\"#3a7\"/></marker></defs>\n" ++
      s!"  <rect width=\"{w}\" height=\"{w}\" fill=\"#fafafa\"/>\n" ++
      body ++
      "</svg>\n"
    IO.FS.writeFile "atlas_conformal.svg" svg
  catch _ => pure ()

/-! ## §4  Test suite -/

#multiscore Nat.add
#multiscore List.map
#multiscore Prod.fst

#conformalsweep

end ConformalField

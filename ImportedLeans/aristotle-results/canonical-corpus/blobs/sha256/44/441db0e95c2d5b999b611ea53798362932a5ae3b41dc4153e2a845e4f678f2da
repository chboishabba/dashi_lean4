import Mathlib
import RequestProject.ExprAddress
import RequestProject.SemanticCID
import Lean

/-!
# MultiCID — a multi-slot semantic CID for the 56-bit irrep addresses and the
104 `q`-expansion participation profile.

The single-slot `SemCID` codec packs one declaration into one 64-bit address
`[prefix:16][version:24][digest:24]`.  That is enough to index a *point*, but a
declaration's Moonshine footprint is not a point: each of the 104 `q`-expansions
decomposes its coefficients over the 194 Monster irreps, so a declaration touches
a *pattern* of irreps across many series.  Indexing that pattern needs **several
64-bit slots** — a *multi-CID*.

This module formalises the two pieces requested:

1. **56-bit irrep slots.**  Each irrep address is a 64-bit slot laid out as
   `[irrepTag:8][digest:56]`: an 8-bit tag (the irrep index `0..193 < 256`) and a
   *56-bit* semantic digest (the low 56 bits of the declaration's structural
   fingerprint).  `packIrrep`, `decTag`, `decDigest56` with their round-trip and
   injectivity proofs, and `irrepCidOf` building the canonical slot, are the
   irrep-level codec — the "56-bit versions of the irreps".

2. **The multi-CID and the 104 `q`-expansion participation.**  `MultiCID` is the
   vector of irrep slots for one declaration; `multiCidOf` builds it and we prove
   the tags and digests it stores are exactly recoverable.  The participation
   profile across the 104 expansions is a 104-bit mask (`encodeBits`), and we
   prove the key fact that **one 64-bit slot is not enough** — a 104-bit profile
   exceeds `2^64`, so it must be split across `⌈104/64⌉ = 2` slots, which we prove
   round-trips losslessly (`split_recombine`, `participation_hi_lt`).  This is the
   formal content of "we need multiple times 64 bits".

Everything is a combinatorial codec in the same grounded spirit as `SemCID`:
every claim below is an actually-proved Lean theorem.
-/

open Lean Meta Elab Command

namespace MultiCID

/-! ## §1  The 56-bit irrep slot `[irrepTag:8][digest:56]` -/

/-- Width of the irrep-tag field, in bits. -/
def irrepTagBits : Nat := 8
/-- Width of the irrep digest, in bits — the "56-bit version" of the irrep. -/
def irrepDigestBits : Nat := 56

/-- The irrep slot layout fills exactly 64 bits. -/
theorem irrep_layout_bits : irrepTagBits + irrepDigestBits = 64 := by decide

/-- The number of Monster irreps, re-exported from `Moonshine`. -/
def numIrreps : Nat := Moonshine.numIrreps

/-- `numIrreps = 194`. -/
theorem numIrreps_eq : numIrreps = 194 := rfl

/-- Every irrep index fits in the 8-bit tag field. -/
theorem numIrreps_fits : numIrreps < 2 ^ 8 := by decide

/-- `2^56`, the size of the irrep digest field. -/
def two56 : Nat := 2 ^ 56

/-- **Pack** an 8-bit irrep tag and a 56-bit digest into a 64-bit slot. -/
def packIrrep (tag digest : Nat) : Nat := tag * two56 + digest

/-- Decode the irrep tag (high 8 bits). -/
def decTag (a : Nat) : Nat := a / two56
/-- Decode the 56-bit digest (low 56 bits). -/
def decDigest56 (a : Nat) : Nat := a % two56

/-- Decoding the digest of a packed slot recovers it. -/
theorem decDigest56_pack (t d : Nat) (hd : d < two56) :
    decDigest56 (packIrrep t d) = d := by
  unfold decDigest56 packIrrep two56 at *; omega

/-- Decoding the tag of a packed slot recovers it. -/
theorem decTag_pack (t d : Nat) (hd : d < two56) :
    decTag (packIrrep t d) = t := by
  unfold decTag packIrrep two56 at *; omega

/-- **Content is the address.**  Packing is injective on in-range
`(tag, digest)` pairs. -/
theorem packIrrep_inj (t d t' d' : Nat) (hd : d < two56) (hd' : d' < two56)
    (h : packIrrep t d = packIrrep t' d') : t = t' ∧ d = d' := by
  unfold packIrrep two56 at *; omega

/-- A packed slot with a byte-sized tag fits in 64 bits. -/
theorem packIrrep_lt (t d : Nat) (ht : t < 2 ^ 8) (hd : d < two56) :
    packIrrep t d < 2 ^ 64 := by
  unfold packIrrep two56 at *; omega

/-- The canonical 56-bit irrep slot for fingerprint `k` at irrep index `i`:
tag is `i` clamped to a byte, digest is the low 56 bits of `k`. -/
def irrepCidOf (i k : Nat) : Nat := packIrrep (i % 2 ^ 8) (k % two56)

/-- The canonical slot carries the (clamped) irrep tag. -/
theorem irrepCidOf_tag (i k : Nat) (hi : i < 2 ^ 8) :
    decTag (irrepCidOf i k) = i := by
  unfold irrepCidOf
  have hd : k % two56 < two56 := Nat.mod_lt _ (by unfold two56; positivity)
  rw [decTag_pack _ _ hd, Nat.mod_eq_of_lt hi]

/-- The canonical slot carries the 56-bit digest `k % 2^56`. -/
theorem irrepCidOf_digest (i k : Nat) : decDigest56 (irrepCidOf i k) = k % two56 := by
  unfold irrepCidOf
  have hd : k % two56 < two56 := Nat.mod_lt _ (by unfold two56; positivity)
  exact decDigest56_pack _ _ hd

/-- The canonical slot always fits in 64 bits. -/
theorem irrepCidOf_lt (i k : Nat) : irrepCidOf i k < 2 ^ 64 := by
  unfold irrepCidOf
  exact packIrrep_lt _ _ (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by unfold two56; positivity))

/-! ## §2  The multi-CID: a vector of irrep slots -/

/-- A **multi-CID**: the vector of 64-bit irrep slots a declaration occupies. -/
structure MultiAddr where
  slots : List Nat
deriving Repr, DecidableEq

/-- The number of slots in a multi-CID (`k × 64` bits total). -/
def MultiAddr.numSlots (m : MultiAddr) : Nat := m.slots.length

/-- Build the multi-CID for fingerprint `k` across the irrep indices `irreps`:
one 56-bit irrep slot per index. -/
def multiCidOf (k : Nat) (irreps : List Nat) : MultiAddr :=
  ⟨irreps.map (fun i => irrepCidOf i k)⟩

/-- The multi-CID has one slot per irrep index. -/
theorem multiCidOf_numSlots (k : Nat) (irreps : List Nat) :
    (multiCidOf k irreps).numSlots = irreps.length := by
  unfold MultiAddr.numSlots multiCidOf; simp

/-- Every slot of a multi-CID fits in 64 bits. -/
theorem multiCidOf_slots_lt (k : Nat) (irreps : List Nat) :
    ∀ a ∈ (multiCidOf k irreps).slots, a < 2 ^ 64 := by
  intro a ha
  unfold multiCidOf at ha
  simp only [List.mem_map] at ha
  obtain ⟨i, _, rfl⟩ := ha
  exact irrepCidOf_lt i k

/-- The tags stored in a multi-CID recover the (byte-clamped) irrep list. -/
theorem multiCidOf_tags (k : Nat) (irreps : List Nat) (h : ∀ i ∈ irreps, i < 2 ^ 8) :
    (multiCidOf k irreps).slots.map decTag = irreps := by
  show (irreps.map (fun i => irrepCidOf i k)).map decTag = irreps
  revert h
  induction irreps with
  | nil => intro _; rfl
  | cons a as ih =>
    intro h
    rw [List.map_cons, List.map_cons,
        irrepCidOf_tag a k (h a (by simp)),
        ih (fun i hi => h i (by simp [hi]))]

/-- Every slot of a multi-CID stores the same 56-bit digest `k % 2^56`. -/
theorem multiCidOf_digests (k : Nat) (irreps : List Nat) :
    (multiCidOf k irreps).slots.map decDigest56 = irreps.map (fun _ => k % two56) := by
  show (irreps.map (fun i => irrepCidOf i k)).map decDigest56 = irreps.map (fun _ => k % two56)
  induction irreps with
  | nil => rfl
  | cons a as ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, irrepCidOf_digest a k, ih]

/-! ## §3  The 104 `q`-expansion participation profile -/

/-- The number of `q`-expansions combined in the Moonshine sheaf. -/
def numExpansions : Nat := 104

/-- `numExpansions = 104`. -/
theorem numExpansions_eq : numExpansions = 104 := rfl

/-- Encode a bit list as a natural number, least-significant bit first. -/
def encodeBits : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * encodeBits bs

/-- A length-`n` bit list encodes to a value `< 2^n`. -/
theorem encodeBits_lt (bs : List Bool) : encodeBits bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [encodeBits]
  | cons b bs ih =>
    simp only [encodeBits, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

/-- A 104-bit participation profile is `< 2^104`. -/
theorem participation_lt (bs : List Bool) (h : bs.length = 104) :
    encodeBits bs < 2 ^ 104 := by
  have := encodeBits_lt bs; rw [h] at this; exact this

/-! ## §4  Why one 64-bit slot is not enough -/

/-- **One 64-bit slot cannot hold a 104-bit profile.**  `2^64 < 2^104`. -/
theorem one_slot_insufficient : 2 ^ 64 < 2 ^ 104 := by
  exact Nat.pow_lt_pow_right (by decide) (by decide)

/-- Split a value into its low 64 bits and the remaining high bits. -/
def splitHL (n : Nat) : Nat × Nat := (n % 2 ^ 64, n / 2 ^ 64)

/-- Recombine a low/high pair into a single value. -/
def recombine (lo hi : Nat) : Nat := hi * 2 ^ 64 + lo

/-- The low/high split round-trips: recombining recovers the value. -/
theorem split_recombine (n : Nat) : recombine (splitHL n).1 (splitHL n).2 = n := by
  unfold recombine splitHL; simp; omega

/-- The low half of any split fits in 64 bits. -/
theorem splitHL_lo_lt (n : Nat) : (splitHL n).1 < 2 ^ 64 := by
  unfold splitHL; exact Nat.mod_lt _ (by positivity)

/-- For a 104-bit profile the **high half fits in 40 bits**, so the whole profile
fits in exactly two 64-bit slots (`104 = 64 + 40`). -/
theorem participation_hi_lt (bs : List Bool) (h : bs.length = 104) :
    (splitHL (encodeBits bs)).2 < 2 ^ 40 := by
  unfold splitHL
  have hlt : encodeBits bs < 2 ^ 104 := participation_lt bs h
  have : encodeBits bs / 2 ^ 64 < 2 ^ 104 / 2 ^ 64 := by
    apply Nat.div_lt_of_lt_mul
    calc encodeBits bs < 2 ^ 104 := hlt
      _ = 2 ^ 104 / 2 ^ 64 * 2 ^ 64 := by norm_num
  simpa using this

/-! ## §5  The combined Monster footprint -/

/-- A declaration's **Monster footprint**: its structural fingerprint, the
multi-CID of 56-bit irrep slots it occupies, and its 104-bit `q`-expansion
participation profile (stored as a single natural number). -/
structure MonsterFootprint where
  /-- The declaration's structural fingerprint. -/
  fingerprint : Nat
  /-- The multi-CID of 56-bit irrep slots. -/
  irrepSlots : MultiAddr
  /-- The 104-bit `q`-expansion participation profile. -/
  qParticipation : Nat
deriving Repr

/-- Build a Monster footprint for fingerprint `k`, irrep indices `irreps`, and
participation bit list `part`. -/
def footprintOf (k : Nat) (irreps : List Nat) (part : List Bool) : MonsterFootprint :=
  { fingerprint := k
    irrepSlots := multiCidOf k irreps
    qParticipation := encodeBits part }

/-- The footprint's slot count is the number of irreps it touches. -/
theorem footprintOf_numSlots (k : Nat) (irreps : List Nat) (part : List Bool) :
    (footprintOf k irreps part).irrepSlots.numSlots = irreps.length := by
  unfold footprintOf; exact multiCidOf_numSlots k irreps

/-- The footprint's participation profile is `< 2^104` when built from 104 bits. -/
theorem footprintOf_participation_lt (k : Nat) (irreps : List Nat) (part : List Bool)
    (h : part.length = 104) :
    (footprintOf k irreps part).qParticipation < 2 ^ 104 := by
  unfold footprintOf; exact participation_lt part h

/-! ## §6  The reflection front-end -/

/-- Derive a small deterministic list of irrep indices a fingerprint occupies:
its primary irrep `k mod 194` together with two rotated companions. -/
def irrepsOf (k : Nat) : List Nat :=
  [k % numIrreps, (k + 1) % numIrreps, (k * 7 + 3) % numIrreps]

/-- Every derived irrep index is `< 194 < 256`. -/
theorem irrepsOf_lt (k : Nat) : ∀ i ∈ irrepsOf k, i < 2 ^ 8 := by
  intro i hi
  unfold irrepsOf at hi
  fin_cases hi <;>
    exact lt_trans (Nat.mod_lt _ (by decide)) (by decide)

/-- A textual multi-CID report for declaration `decl` with fingerprint `k`. -/
def reportOf (decl : Name) (k : Nat) : String :=
  let irreps := irrepsOf k
  let m := multiCidOf k irreps
  let slotStr := String.intercalate ", " (m.slots.map SemCID.toHex)
  s!"[Aristo Multi-CID] {decl}\n" ++
  s!"  ├── structural fingerprint k = {k}\n" ++
  s!"  ├── 56-bit digest (k % 2^56) = {SemCID.toHex (k % two56)}\n" ++
  s!"  ├── irrep tags = {irreps}\n" ++
  s!"  ├── {m.numSlots} irrep slots (64 bits each) = [{slotStr}]\n" ++
  s!"  └── 104-q profile needs 2 slots (104 = 64 + 40)"

/-- `#multicid f` prints the multi-slot 56-bit irrep CID of declaration `f`,
computed from its structural fingerprint. -/
syntax (name := multicidCmd) "#multicid " ident : command

@[command_elab multicidCmd]
def elabMulticid : CommandElab := fun stx => do
  match stx with
  | `(#multicid $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadCore id.getId
    let k ← liftTermElabM <| Meta.MetaM.run' (ExprAddress.declStructuralSum name)
    logInfo (reportOf name k)
  | _ => throwError "ill-formed #multicid command"

/-! ## §7  Test suite -/

#multicid Nat.add
#multicid List.map
#multicid Prod.fst

end MultiCID

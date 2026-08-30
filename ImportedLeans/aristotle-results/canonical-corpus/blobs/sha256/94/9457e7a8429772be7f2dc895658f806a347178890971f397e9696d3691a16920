import Mathlib
import RequestProject.ExprAddress
import Lean

/-!
# Dasl — the 0xDA51 (DASL) prefix address scheme, formalised

This module turns the informal **0xDA51 Prefix Classification** specification
into an executable, *provable* Lean development.  The "DASL" (Data-Addressed
Structures & Links) scheme packs a 64-bit content address as

```
[prefix:16][type:4][data:44]      (16 + 4 + 44 = 64 bits)
```

with the constant prefix `0xDA51` in the top 16 bits, a 4-bit `type` field, and a
44-bit type-specific payload.  We model addresses as natural numbers and use
*arithmetic* (base-2 positional) packing rather than raw bitwise operators, which
makes every layout/roundtrip fact a clean `omega` goal.

## What is actually proved

* **Layout** (`layout_bits`, `*_widths_sum`): the prefix/type/data widths sum to
  64, and every per-type field layout sums to exactly 44 bits.
* **Roundtrip** (`decPrefix_pack`, `decType_pack`, `decData_pack`): packing then
  decoding recovers the prefix `0xDA51`, the type field, and the payload.
* **Injectivity** (`pack_inj`): distinct `(type, data)` pairs (within range) give
  distinct addresses — *"the content is the address, so no collision is
  possible"*.  This is the formal core of the document's claim that a full
  content address has no hash collisions.
* **Per-type encoders** (`encMonsterWalk`, `encAstNode`, …, `encHauptmodul`) for
  all eight documented types, each proved to carry the right prefix and type
  nibble, with field-level roundtrips for representative types.
* **Composition** (`mergeCID`, `slide`): the XOR-merge preserves the `0xDA51`
  prefix (`mergeCID_prefix`); harmonic sliding lands in `[0,40)` (`slide_lt`).
* **Number facts** from the document: `0x51 = 81`, `196883 = 47·59·71`, the
  trivector gluing congruence `196884 ≡ 1 (mod 47,59,71)`, `gcd(10,8)=2`,
  `lcm(10,8)=40`, the E₈ nibble identity `240 = 16·15`, and the list of 15
  supersingular Monster primes (all prime).

## Honest scope

This is a *combinatorial coordinate system*.  The surrounding narrative (moonshine
sheaves, umbral shadows, Niemeier lattices, the "Monster couch theorem") is **not**
formalised and is not asserted here: nothing below claims a mathematical link
between the Monster group and the addressed declarations beyond the explicit
arithmetic identities.  Two source-document examples are internally inconsistent
and are flagged where they appear (`astNode_example_type`, and the Type-2 example
whose printed prefix is `0xDA52`, not `0xDA51`).

A reflection command `#daslstratify f` assigns any declaration its canonical
Type-3 (Nested CID) DASL address from its structural fingerprint.
-/

open Lean Meta Elab Command

namespace Dasl

/-! ## §1  The address layout -/

/-- Width of the constant prefix field, in bits. -/
def prefixBits : Nat := 16
/-- Width of the type field, in bits. -/
def typeBits : Nat := 4
/-- Width of the type-specific data payload, in bits. -/
def dataBits : Nat := 44

/-- The DASL address layout fills exactly 64 bits. -/
theorem layout_bits : prefixBits + typeBits + dataBits = 64 := by decide

/-- The constant DASL prefix `0xDA51` (= 55889 decimal). -/
def daPrefix : Nat := 0xDA51

/-- `0x51 = 81` — the low byte of the prefix in decimal (DASL etymology). -/
theorem hex51 : (0x51 : Nat) = 81 := by decide

/-- `0xDA51 = 55889`. -/
theorem daPrefix_val : daPrefix = 55889 := by decide

/-- The binary expansion of the prefix is `1101 1010 0101 0001`. -/
theorem daPrefix_bits :
    Nat.testBit daPrefix 15 = true  ∧ Nat.testBit daPrefix 14 = true  ∧
    Nat.testBit daPrefix 13 = false ∧ Nat.testBit daPrefix 12 = true  ∧
    Nat.testBit daPrefix 11 = true  ∧ Nat.testBit daPrefix 10 = false ∧
    Nat.testBit daPrefix 9  = true  ∧ Nat.testBit daPrefix 8  = false ∧
    Nat.testBit daPrefix 7  = false ∧ Nat.testBit daPrefix 6  = true  ∧
    Nat.testBit daPrefix 5  = false ∧ Nat.testBit daPrefix 4  = true  ∧
    Nat.testBit daPrefix 3  = false ∧ Nat.testBit daPrefix 2  = false ∧
    Nat.testBit daPrefix 1  = false ∧ Nat.testBit daPrefix 0  = true := by
  decide

/-- `2^44`, the size of the data field. -/
def two44 : Nat := 2 ^ 44
/-- `2^48`, the size of the type+data region (positioned below the prefix). -/
def two48 : Nat := 2 ^ 48

/-- **Pack** a type field and a payload into a 64-bit DASL address. -/
def pack (type data : Nat) : Nat := daPrefix * two48 + type * two44 + data

/-- Decode the 16-bit prefix field. -/
def decPrefix (a : Nat) : Nat := a / two48
/-- Decode the 4-bit type field. -/
def decType (a : Nat) : Nat := a / two44 % 16
/-- Decode the 44-bit data payload. -/
def decData (a : Nat) : Nat := a % two44

/-! ## §2  Roundtrip and injectivity -/

/-- Decoding the payload of a packed address recovers it. -/
theorem decData_pack (t d : Nat) (hd : d < two44) : decData (pack t d) = d := by
  unfold decData pack two44 two48 daPrefix at *; omega

/-- Decoding the type field of a packed address recovers it. -/
theorem decType_pack (t d : Nat) (ht : t < 16) (hd : d < two44) :
    decType (pack t d) = t := by
  unfold decType pack two44 two48 daPrefix at *; omega

/-- Decoding the prefix of any packed address yields the constant `0xDA51`. -/
theorem decPrefix_pack (t d : Nat) (ht : t < 16) (hd : d < two44) :
    decPrefix (pack t d) = 0xDA51 := by
  unfold decPrefix pack two44 two48 daPrefix at *; omega

/-- **The content is the address.**  Packing is injective on in-range
`(type, data)` pairs: distinct payloads yield distinct addresses, so a full
content address admits no collisions. -/
theorem pack_inj (t d t' d' : Nat) (hd : d < two44)
    (hd' : d' < two44) (h : pack t d = pack t' d') :
    t = t' ∧ d = d' := by
  unfold pack two44 two48 daPrefix at *; omega

/-! ## §3  Per-type field layouts

Every type uses a 44-bit payload.  The field widths are recorded as lists, and
each is proved to sum to exactly 44. -/

/-- Type 0 (Monster Walk): `[group:4][position:8][sequence:16][factors:4][pad:12]`. -/
def type0Widths : List Nat := [4, 8, 16, 4, 12]
/-- Type 1 (AST Node): `[selector:3][bott:3][tenfold:11][hecke:7][hash:20]`. -/
def type1Widths : List Nat := [3, 3, 11, 7, 20]
/-- Type 2 (Protocol): `[protocol_id:8][version:8][capabilities:28]`. -/
def type2Widths : List Nat := [8, 8, 28]
/-- Type 3 (Nested CID): `[shard:8][hecke:8][bott:8][hash:20]`. -/
def type3Widths : List Nat := [8, 8, 8, 20]
/-- Type 4 (Harmonic Path): `[source:4][dest:4][harmonic:8][transition:28]`. -/
def type4Widths : List Nat := [4, 4, 8, 28]
/-- Type 5 (Shard ID): `[prime_idx:4][replica:4][zone:8][node:28]`. -/
def type5Widths : List Nat := [4, 4, 8, 28]
/-- Type 6 (Eigenspace): `[eigenspace:2][prime_idx:4][mckay:6][hub_proj:4][hash:28]`. -/
def type6Widths : List Nat := [2, 4, 6, 4, 28]
/-- Type 7 (Hauptmodul): `[prime_idx:4][genus:4][coeff_idx:8][coeff_val:28]`. -/
def type7Widths : List Nat := [4, 4, 8, 28]

theorem type0_widths_sum : type0Widths.sum = 44 := by decide
theorem type1_widths_sum : type1Widths.sum = 44 := by decide
theorem type2_widths_sum : type2Widths.sum = 44 := by decide
theorem type3_widths_sum : type3Widths.sum = 44 := by decide
theorem type4_widths_sum : type4Widths.sum = 44 := by decide
theorem type5_widths_sum : type5Widths.sum = 44 := by decide
theorem type6_widths_sum : type6Widths.sum = 44 := by decide
theorem type7_widths_sum : type7Widths.sum = 44 := by decide

/-! ## §4  Per-type encoders

Each encoder clamps every field to its bit width (via `% 2^width`), so the
resulting payload is always `< 2^44` and the address is always well-formed. -/

/-- Type 0 — Monster Walk block. -/
def encMonsterWalk (group position sequence factors pad : Nat) : Nat :=
  pack 0 ((group % 16) * 2^40 + (position % 256) * 2^32 + (sequence % 65536) * 2^16
          + (factors % 16) * 2^12 + (pad % 4096))

/-- Type 1 — AST node (triple view). -/
def encAstNode (selector bott tenfold hecke hash : Nat) : Nat :=
  pack 1 ((selector % 8) * 2^41 + (bott % 8) * 2^38 + (tenfold % 2048) * 2^27
          + (hecke % 128) * 2^20 + (hash % 2^20))

/-- Type 2 — Monster protocol. -/
def encProtocol (protocol_id version capabilities : Nat) : Nat :=
  pack 2 ((protocol_id % 256) * 2^36 + (version % 256) * 2^28 + (capabilities % 2^28))

/-- Type 3 — Nested CID (content-addressed). -/
def encNestedCID (shard hecke bott hash : Nat) : Nat :=
  pack 3 ((shard % 256) * 2^36 + (hecke % 256) * 2^28 + (bott % 256) * 2^20
          + (hash % 2^20))

/-- Type 4 — Harmonic path. -/
def encHarmonicPath (source dest harmonic transition : Nat) : Nat :=
  pack 4 ((source % 16) * 2^40 + (dest % 16) * 2^36 + (harmonic % 256) * 2^28
          + (transition % 2^28))

/-- Type 5 — Shard ID. -/
def encShardID (prime_idx replica zone node : Nat) : Nat :=
  pack 5 ((prime_idx % 16) * 2^40 + (replica % 16) * 2^36 + (zone % 256) * 2^28
          + (node % 2^28))

/-- Type 6 — Eigenspace address. -/
def encEigenspace (eigenspace prime_idx mckay hub_proj hash : Nat) : Nat :=
  pack 6 ((eigenspace % 4) * 2^42 + (prime_idx % 16) * 2^38 + (mckay % 64) * 2^32
          + (hub_proj % 16) * 2^28 + (hash % 2^28))

/-- Type 7 — Hauptmodul reference. -/
def encHauptmodul (prime_idx genus coeff_idx coeff_val : Nat) : Nat :=
  pack 7 ((prime_idx % 16) * 2^40 + (genus % 16) * 2^36 + (coeff_idx % 256) * 2^28
          + (coeff_val % 2^28))

/-! Each encoder produces a well-formed address: prefix `0xDA51`, correct type. -/

theorem encMonsterWalk_prefix (a b c d e : Nat) :
    decPrefix (encMonsterWalk a b c d e) = 0xDA51 := by
  unfold decPrefix encMonsterWalk pack two44 two48 daPrefix; omega
theorem encMonsterWalk_type (a b c d e : Nat) :
    decType (encMonsterWalk a b c d e) = 0 := by
  unfold decType encMonsterWalk pack two44 two48 daPrefix; omega

theorem encAstNode_prefix (a b c d e : Nat) :
    decPrefix (encAstNode a b c d e) = 0xDA51 := by
  unfold decPrefix encAstNode pack two44 two48 daPrefix; omega
theorem encAstNode_type (a b c d e : Nat) :
    decType (encAstNode a b c d e) = 1 := by
  unfold decType encAstNode pack two44 two48 daPrefix; omega

theorem encProtocol_prefix (a b c : Nat) :
    decPrefix (encProtocol a b c) = 0xDA51 := by
  unfold decPrefix encProtocol pack two44 two48 daPrefix; omega
theorem encProtocol_type (a b c : Nat) :
    decType (encProtocol a b c) = 2 := by
  unfold decType encProtocol pack two44 two48 daPrefix; omega

theorem encNestedCID_prefix (a b c d : Nat) :
    decPrefix (encNestedCID a b c d) = 0xDA51 := by
  unfold decPrefix encNestedCID pack two44 two48 daPrefix; omega
theorem encNestedCID_type (a b c d : Nat) :
    decType (encNestedCID a b c d) = 3 := by
  unfold decType encNestedCID pack two44 two48 daPrefix; omega

theorem encHarmonicPath_prefix (a b c d : Nat) :
    decPrefix (encHarmonicPath a b c d) = 0xDA51 := by
  unfold decPrefix encHarmonicPath pack two44 two48 daPrefix; omega
theorem encHarmonicPath_type (a b c d : Nat) :
    decType (encHarmonicPath a b c d) = 4 := by
  unfold decType encHarmonicPath pack two44 two48 daPrefix; omega

theorem encShardID_prefix (a b c d : Nat) :
    decPrefix (encShardID a b c d) = 0xDA51 := by
  unfold decPrefix encShardID pack two44 two48 daPrefix; omega
theorem encShardID_type (a b c d : Nat) :
    decType (encShardID a b c d) = 5 := by
  unfold decType encShardID pack two44 two48 daPrefix; omega

theorem encEigenspace_prefix (a b c d e : Nat) :
    decPrefix (encEigenspace a b c d e) = 0xDA51 := by
  unfold decPrefix encEigenspace pack two44 two48 daPrefix; omega
theorem encEigenspace_type (a b c d e : Nat) :
    decType (encEigenspace a b c d e) = 6 := by
  unfold decType encEigenspace pack two44 two48 daPrefix; omega

theorem encHauptmodul_prefix (a b c d : Nat) :
    decPrefix (encHauptmodul a b c d) = 0xDA51 := by
  unfold decPrefix encHauptmodul pack two44 two48 daPrefix; omega
theorem encHauptmodul_type (a b c d : Nat) :
    decType (encHauptmodul a b c d) = 7 := by
  unfold decType encHauptmodul pack two44 two48 daPrefix; omega

/-! ## §5  Field-level roundtrips (representative types)

A field is read from the payload by `field shift width = data / 2^shift % 2^width`.
We verify the full roundtrip for the Eigenspace (Type 6) and AST (Type 1)
encoders, demonstrating that every sub-field is recovered exactly. -/

/-- Read a sub-field of width `2^width` starting at bit `shift` of the payload. -/
def field (data shift width : Nat) : Nat := data / 2^shift % 2^width

/-- Type-6 eigenspace field roundtrips. -/
theorem encEigenspace_roundtrip (es pi mk hp ha : Nat) :
    field (decData (encEigenspace es pi mk hp ha)) 42 2 = es % 4 ∧
    field (decData (encEigenspace es pi mk hp ha)) 38 4 = pi % 16 ∧
    field (decData (encEigenspace es pi mk hp ha)) 32 6 = mk % 64 ∧
    field (decData (encEigenspace es pi mk hp ha)) 28 4 = hp % 16 ∧
    field (decData (encEigenspace es pi mk hp ha)) 0 28 = ha % 2^28 := by
  unfold field decData encEigenspace pack two44 two48 daPrefix
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Type-1 AST-node field roundtrips. -/
theorem encAstNode_roundtrip (sel bo tf he ha : Nat) :
    field (decData (encAstNode sel bo tf he ha)) 41 3 = sel % 8 ∧
    field (decData (encAstNode sel bo tf he ha)) 38 3 = bo % 8 ∧
    field (decData (encAstNode sel bo tf he ha)) 27 11 = tf % 2048 ∧
    field (decData (encAstNode sel bo tf he ha)) 20 7 = he % 128 ∧
    field (decData (encAstNode sel bo tf he ha)) 0 20 = ha % 2^20 := by
  unfold field decData encAstNode pack two44 two48 daPrefix
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-! ## §6  Composition rules -/

/-- **XOR merge** (`merge_cids`): keep the `0xDA51` prefix, XOR the low 48 bits. -/
def mergeCID (c1 c2 : Nat) : Nat :=
  daPrefix * two48 + ((c1 % two48) ^^^ (c2 % two48))

/-- The XOR merge preserves the common prefix `0xDA51`. -/
theorem mergeCID_prefix (c1 c2 : Nat) : decPrefix (mergeCID c1 c2) = 0xDA51 := by
  have hpos : 0 < two48 := by unfold two48; positivity
  have hx : (c1 % two48) ^^^ (c2 % two48) < two48 :=
    Nat.xor_lt_two_pow (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos)
  unfold decPrefix mergeCID two48 daPrefix at *; omega

/-- **Harmonic sliding**: bridge the 10-fold and 8-fold ways via `LCM(10,8)=40`. -/
def slide (c1 c2 : Nat) : Nat := (c1 + c2) % 40

/-- A harmonic slide always lands in `[0, 40)`. -/
theorem slide_lt (c1 c2 : Nat) : slide c1 c2 < 40 := by
  unfold slide; omega

/-! ## §7  Number facts from the specification -/

/-- The smallest non-trivial Monster irrep dimension factors as `47·59·71`. -/
theorem trivector_factor : 47 * 59 * 71 = 196883 := by decide

/-- **Trivector gluing.**  The first non-trivial `j`-coefficient `196884` is
congruent to `1` modulo each of the three "pillar" primes — the CRT gluing
condition for the `47·59·71` trivector stalk. -/
theorem trivector_gluing :
    196884 % 47 = 1 ∧ 196884 % 59 = 1 ∧ 196884 % 71 = 1 := by decide

/-- `gcd(10,8) = 2` — the harmonic number bridging the 10-fold and 8-fold ways. -/
theorem harmonic_gcd : Nat.gcd 10 8 = 2 := by decide

/-- `lcm(10,8) = 40` — the harmonic sliding modulus. -/
theorem harmonic_lcm : Nat.lcm 10 8 = 40 := by decide

/-- The E₈ identity: `240 = 16 · 15` (hex nibble sum of `|𝕄|` = roots of E₈). -/
theorem e8_nibble : 240 = 16 * 15 := by decide

/-- The 15 supersingular primes dividing `|𝕄|` (OEIS A002267). -/
def supersingularPrimes : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

/-- There are exactly 15 supersingular Monster primes. -/
theorem supersingularPrimes_length : supersingularPrimes.length = 15 := by decide

/-- Every supersingular Monster prime is prime. -/
theorem supersingularPrimes_prime :
    ∀ p ∈ supersingularPrimes, Nat.Prime p := by decide

/-- Bott periodicity has period 8. -/
def bottSequence : List String :=
  ["R", "C", "H", "H⊕H", "H(2)", "C(4)", "R(8)", "R(8)⊕R(8)"]

theorem bottSequence_length : bottSequence.length = 8 := by decide

/-! ## §8  Example addresses from the specification

The internally-consistent examples are verified by `decide`.  Two source
examples are inconsistent and are documented rather than "proved correct". -/

/-- Type-0 Monster Walk example `0xDA510001F9080000` carries prefix `0xDA51`,
type `0`. -/
theorem monsterWalk_example :
    decPrefix 0xDA510001F9080000 = 0xDA51 ∧ decType 0xDA510001F9080000 = 0 := by
  decide

/-- Type-3 Nested CID example `0xDA513AE3392F2B7F`: prefix `0xDA51`, type `3`. -/
theorem nestedCID_example :
    decPrefix 0xDA513AE3392F2B7F = 0xDA51 ∧ decType 0xDA513AE3392F2B7F = 3 := by
  decide

/-- Type-5 Shard example `0xDA515E2A00000001`: prefix `0xDA51`, type `5`. -/
theorem shard_example :
    decPrefix 0xDA515E2A00000001 = 0xDA51 ∧ decType 0xDA515E2A00000001 = 5 := by
  decide

/-- Type-6 Eigenspace example `0xDA5160750A000000`: prefix `0xDA51`, type `6`. -/
theorem eigenspace_example :
    decPrefix 0xDA5160750A000000 = 0xDA51 ∧ decType 0xDA5160750A000000 = 6 := by
  decide

/-- Type-7 Hauptmodul example `0xDA5170060000030E`: prefix `0xDA51`, type `7`. -/
theorem hauptmodul_example :
    decPrefix 0xDA5170060000030E = 0xDA51 ∧ decType 0xDA5170060000030E = 7 := by
  decide

/-- **Documented inconsistency (Type-1 example).**  The source lists
`0xDA51E0000011C000` as a Type-1 (AST Node) address, but its 4-bit type nibble is
`1110₂ = 14`, not `1`: the example overlaps the 3-bit `selector = 0b111` field
into the type field.  We record the true decoded type. -/
theorem astNode_example_type : decType 0xDA51E0000011C000 = 14 := by decide

-- NOTE (Type-2 example): the source prints the Type-2 protocol example as
-- `0xDA52010000000001`, whose top 16 bits are `0xDA52`, not the DASL prefix
-- `0xDA51`.  It is therefore not a valid DASL address as written; the intended
-- value is `0xDA52000000000001` only if the prefix is changed, so we do not
-- assert it.  (`decPrefix 0xDA52010000000001 = 0xDA52`.)
theorem protocol_example_prefix_is_DA52 : decPrefix 0xDA52010000000001 = 0xDA52 := by
  decide

/-! ## §9  Canonical content address of a declaration

`#daslstratify f` gives declaration `f` its canonical **Type-3 Nested CID** DASL
address, derived from its structural fingerprint `k` (`ExprAddress.declStructuralSum`):

* `shard = k % 71`   (71 supersingular primes),
* `hecke = k % 59`   (Hecke error-correction index),
* `bott  = k % 47`   (Bott periodicity phase),
* `hash  = k % 2^20` (low structural bits).

This realises the document's claim that "every well-typed computation has a
canonical Monster address" — purely combinatorially. -/

/-- The canonical Type-3 DASL address of structural fingerprint `k`. -/
def addrOfFingerprint (k : Nat) : Nat := encNestedCID (k % 71) (k % 59) (k % 47) k

/-- The canonical address always carries the DASL prefix. -/
theorem addrOfFingerprint_prefix (k : Nat) : decPrefix (addrOfFingerprint k) = 0xDA51 := by
  unfold addrOfFingerprint; exact encNestedCID_prefix _ _ _ _

/-- The canonical address always has Nested-CID type `3`. -/
theorem addrOfFingerprint_type (k : Nat) : decType (addrOfFingerprint k) = 3 := by
  unfold addrOfFingerprint; exact encNestedCID_type _ _ _ _

/-- A hex character for a single nibble. -/
def hexDigit (d : Nat) : Char := "0123456789ABCDEF".toList.getD d '0'

/-- Render `n` as an uppercase hex string (helper, fuel = recursion on `n / 16`). -/
partial def toHexAux (n : Nat) (acc : String) : String :=
  if n == 0 then acc else toHexAux (n / 16) (String.singleton (hexDigit (n % 16)) ++ acc)

/-- Render `n` as `0x…` uppercase hex. -/
def toHex (n : Nat) : String := if n == 0 then "0x0" else "0x" ++ toHexAux n ""

/-- A textual DASL report for declaration `decl` with fingerprint `k`. -/
def reportOf (decl : Name) (k : Nat) : String :=
  let a := addrOfFingerprint k
  s!"[Aristo DASL Address] {decl}\n  ├── Structural fingerprint k = {k}\n  ├── DASL address = {toHex a}\n  ├── prefix = {toHex (decPrefix a)} · type = {decType a} (Nested CID)\n  ├── shard (mod 71)  = {k % 71}\n  ├── hecke (mod 59)  = {k % 59}\n  ├── bott  (mod 47)  = {k % 47}\n  └── hash  (k % 2^20) = {k % 2^20}"

/-- `#daslstratify f` prints the canonical Type-3 DASL address of declaration `f`. -/
syntax (name := daslstratifyCmd) "#daslstratify " ident : command

@[command_elab daslstratifyCmd]
def elabDaslstratify : CommandElab := fun stx => do
  match stx with
  | `(#daslstratify $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadCore id.getId
    let k ← liftTermElabM <| Meta.MetaM.run' (ExprAddress.declStructuralSum name)
    logInfo (reportOf name k)
  | _ => throwError "ill-formed #daslstratify command"

/-! ## §10  Test suite -/

#daslstratify Nat.add
#daslstratify List.map
#daslstratify Prod.fst

end Dasl

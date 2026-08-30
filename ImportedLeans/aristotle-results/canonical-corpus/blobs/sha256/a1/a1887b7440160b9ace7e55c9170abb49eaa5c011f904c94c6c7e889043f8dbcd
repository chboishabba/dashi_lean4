import Mathlib
import RequestProject.ExprAddress
import RequestProject.Dasl
import Lean

/-!
# SemanticCID — a semantic-version content identifier (CID) codec with a Lean 4
reflection front-end.

This module answers the request for *"a custom semantic version, a CID for
mathlib, and a quick Lean 4 reflection → CID codec"* supporting five capabilities:

1. **Proof that a statement has a CID.**  `cidOf v k` is the canonical CID of a
   declaration whose structural fingerprint is `k` under semantic version `v`;
   `HasSemCID` is the (decidable) proposition that an address *is* that CID, and
   `verifyCID` is its Boolean decision procedure, proved sound and complete.
2. **Enforcement.**  `enforce` is a gate that admits a fingerprint only when its
   CID matches a target; `enforce_sound`/`enforce_complete` and the `Conforming`
   subtype prove the gate accepts exactly the conforming fingerprints.
3. **FFI to compatible types.**  `FFICompatible` (and its Boolean form
   `ffiCompatibleB`) is the ABI-compatibility relation — *same prefix and same
   major version* — proved to be an equivalence relation; `ffiCall` is a transport
   gate that only fires across compatible boundaries.
4. **ZKP-style proofs of conformity.**  A binding commitment `commit` lets a
   prover commit to a fingerprint and later prove its CID without changing it:
   `verifyConformity` is complete (`conformity_complete`) and *binding*
   (`conformity_binding`) — a commitment determines a unique CID, so conformity
   cannot be equivocated.
5. **Linking along CID boundaries.**  `link` merges two module CIDs (XOR of
   digests, common version), proved prefix-preserving, version-preserving on
   compatible inputs, commutative and associative — the algebra of a module
   linker that respects the semantic boundary.

## Honest scope

This is a *combinatorial codec*, in the same spirit as `Dasl`/`ExprAddress`.
The CID is `[prefix:16][version:24][digest:24]` packed positionally into a 64-bit
natural number; the digest is the low 24 bits of the declaration's structural
fingerprint (`ExprAddress.declStructuralSum`).  We do **not** formalise the
*hiding* (zero-knowledge) property of a real ZKP — only completeness and the
binding/soundness direction, which is what makes the conformity proof
non-forgeable.  No cryptographic hardness is claimed; "ZKP" here means a
commit-and-open conformity protocol whose binding property is proved.
-/

open Lean Meta Elab Command

namespace SemCID

/-! ## §1  Custom semantic version -/

/-- A semantic version `major.minor.patch`, each field a byte (`< 256`). -/
structure SemVer where
  major : Nat
  minor : Nat
  patch : Nat
deriving DecidableEq, Repr

/-- The semantic version this codec targets for mathlib (toolchain `v4.28.0`). -/
def mathlibVersion : SemVer := ⟨4, 28, 0⟩

/-- Two versions are **compatible** iff they share a major version (SemVer rule:
no breaking changes within a major series). -/
def Compatible (v w : SemVer) : Prop := v.major = w.major

instance : DecidablePred (fun p : SemVer × SemVer => Compatible p.1 p.2) :=
  fun p => decEq p.1.major p.2.major

/-- Compatibility is reflexive. -/
theorem Compatible.refl (v : SemVer) : Compatible v v := rfl

/-- Compatibility is symmetric. -/
theorem Compatible.symm {v w : SemVer} (h : Compatible v w) : Compatible w v := Eq.symm h

/-- Compatibility is transitive. -/
theorem Compatible.trans {u v w : SemVer} (h1 : Compatible u v) (h2 : Compatible v w) :
    Compatible u w := Eq.trans h1 h2

/-- Encode a semantic version into a 24-bit field `[major:8][minor:8][patch:8]`,
clamping each field to a byte. -/
def encodeVer (v : SemVer) : Nat :=
  (v.major % 256) * 2 ^ 16 + (v.minor % 256) * 2 ^ 8 + (v.patch % 256)

/-- An encoded version always fits in 24 bits. -/
theorem encodeVer_lt (v : SemVer) : encodeVer v < 2 ^ 24 := by
  unfold encodeVer
  have h1 : v.major % 256 < 256 := Nat.mod_lt _ (by decide)
  have h2 : v.minor % 256 < 256 := Nat.mod_lt _ (by decide)
  have h3 : v.patch % 256 < 256 := Nat.mod_lt _ (by decide)
  omega

/-- Read the major byte back from an encoded version. -/
def decMajor (e : Nat) : Nat := e / 2 ^ 16 % 256
/-- Read the minor byte back from an encoded version. -/
def decMinor (e : Nat) : Nat := e / 2 ^ 8 % 256
/-- Read the patch byte back from an encoded version. -/
def decPatch (e : Nat) : Nat := e % 256

/-- The version encoding round-trips on byte-sized fields. -/
theorem encodeVer_roundtrip (v : SemVer)
    (hM : v.major < 256) (hm : v.minor < 256) (hp : v.patch < 256) :
    decMajor (encodeVer v) = v.major ∧
    decMinor (encodeVer v) = v.minor ∧
    decPatch (encodeVer v) = v.patch := by
  unfold decMajor decMinor decPatch encodeVer
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-! ## §2  The semantic CID layout -/

/-- Width of the constant semantic prefix, in bits. -/
def prefixBits : Nat := 16
/-- Width of the semantic-version field, in bits. -/
def verBits : Nat := 24
/-- Width of the semantic digest, in bits. -/
def digestBits : Nat := 24

/-- The CID layout fills exactly 64 bits. -/
theorem layout_bits : prefixBits + verBits + digestBits = 64 := by decide

/-- The constant semantic-CID prefix `0x5EC1` ("SEC1"/"SemCID"). -/
def semPrefix : Nat := 0x5EC1

/-- `0x5EC1 = 24257`. -/
theorem semPrefix_val : semPrefix = 24257 := by decide

/-- The prefix fits in 16 bits. -/
theorem semPrefix_lt : semPrefix < 2 ^ 16 := by decide

/-- `2^24`, the size of the version and digest fields. -/
def two24 : Nat := 2 ^ 24
/-- `2^48`, the size of the version+digest region. -/
def two48 : Nat := 2 ^ 48

/-- **Pack** a 24-bit version and 24-bit digest into a 64-bit semantic CID. -/
def pack (ver digest : Nat) : Nat := semPrefix * two48 + ver * two24 + digest

/-- Decode the 16-bit prefix field. -/
def decPrefix (a : Nat) : Nat := a / two48
/-- Decode the 24-bit version field. -/
def decVer (a : Nat) : Nat := a / two24 % two24
/-- Decode the 24-bit digest field. -/
def decDigest (a : Nat) : Nat := a % two24

/-- Decoding the digest of a packed CID recovers it. -/
theorem decDigest_pack (v d : Nat) (hd : d < two24) : decDigest (pack v d) = d := by
  unfold decDigest pack two24 two48 semPrefix at *; omega

/-- Decoding the version field of a packed CID recovers it. -/
theorem decVer_pack (v d : Nat) (hv : v < two24) (hd : d < two24) :
    decVer (pack v d) = v := by
  unfold decVer pack two24 two48 semPrefix at *; omega

/-- Decoding the prefix of any packed CID yields the constant `0x5EC1`. -/
theorem decPrefix_pack (v d : Nat) (hv : v < two24) (hd : d < two24) :
    decPrefix (pack v d) = 0x5EC1 := by
  unfold decPrefix pack two24 two48 semPrefix at *; omega

/-- **The content is the CID.**  Packing is injective on in-range
`(version, digest)` pairs. -/
theorem pack_inj (v d v' d' : Nat) (hd : d < two24) (hd' : d' < two24)
    (h : pack v d = pack v' d') : v = v' ∧ d = d' := by
  unfold pack two24 two48 semPrefix at *; omega

/-! ## §3  Feature 1 — the canonical CID and its proof of membership -/

/-- The canonical semantic CID of a declaration with structural fingerprint `k`
under semantic version `v`: digest is the low 24 bits of `k`. -/
def cidOf (v : SemVer) (k : Nat) : Nat := pack (encodeVer v) (k % two24)

/-- The canonical CID always carries the semantic prefix `0x5EC1`. -/
theorem cidOf_prefix (v : SemVer) (k : Nat) : decPrefix (cidOf v k) = 0x5EC1 := by
  unfold cidOf
  have hv := encodeVer_lt v
  have hd : k % two24 < two24 := Nat.mod_lt _ (by unfold two24; positivity)
  exact decPrefix_pack _ _ (by unfold two24; exact hv) hd

/-- The canonical CID carries the encoded version. -/
theorem cidOf_ver (v : SemVer) (k : Nat) : decVer (cidOf v k) = encodeVer v := by
  unfold cidOf
  have hv := encodeVer_lt v
  have hd : k % two24 < two24 := Nat.mod_lt _ (by unfold two24; positivity)
  exact decVer_pack _ _ (by unfold two24; exact hv) hd

/-- The canonical CID carries the digest `k % 2^24`. -/
theorem cidOf_digest (v : SemVer) (k : Nat) : decDigest (cidOf v k) = k % two24 := by
  unfold cidOf
  have hd : k % two24 < two24 := Nat.mod_lt _ (by unfold two24; positivity)
  exact decDigest_pack _ _ hd

/-- **Membership proposition**: address `a` is the CID of fingerprint `k` at
version `v`. -/
def HasSemCID (v : SemVer) (k : Nat) (a : Nat) : Prop := cidOf v k = a

instance (v : SemVer) (k a : Nat) : Decidable (HasSemCID v k a) := by
  unfold HasSemCID; infer_instance

/-- The Boolean CID checker. -/
def verifyCID (v : SemVer) (k a : Nat) : Bool := cidOf v k == a

/-- `verifyCID` is **sound**: if it accepts, the address really is the CID. -/
theorem verifyCID_sound (v : SemVer) (k a : Nat) (h : verifyCID v k a = true) :
    HasSemCID v k a := by
  unfold verifyCID at h; unfold HasSemCID; exact (beq_iff_eq).mp h

/-- `verifyCID` is **complete**: the canonical CID is always accepted. -/
theorem verifyCID_complete (v : SemVer) (k : Nat) : verifyCID v k (cidOf v k) = true := by
  unfold verifyCID; simp

/-! ## §4  Feature 2 — enforcement -/

/-- The **enforcement gate**: admit fingerprint `k` only if its CID at version `v`
equals the target `cid`. -/
def enforce (cid : Nat) (v : SemVer) (k : Nat) : Option Nat :=
  if cidOf v k = cid then some k else none

/-- Enforcement is **sound**: anything it admits has the demanded CID. -/
theorem enforce_sound (cid : Nat) (v : SemVer) (k k' : Nat)
    (h : enforce cid v k = some k') : cidOf v k' = cid := by
  unfold enforce at h
  by_cases hc : cidOf v k = cid
  · simp [hc] at h; subst h; exact hc
  · simp [hc] at h

/-- Enforcement is **complete**: a conforming fingerprint is admitted unchanged. -/
theorem enforce_complete (v : SemVer) (k : Nat) : enforce (cidOf v k) v k = some k := by
  unfold enforce; simp

/-- Enforcement **rejects a version mismatch**: if the target's version field is
not the encoded `v`, nothing is admitted. -/
theorem enforce_reject_version (cid : Nat) (v : SemVer) (k : Nat)
    (h : decVer cid ≠ encodeVer v) : enforce cid v k = none := by
  unfold enforce
  by_cases hc : cidOf v k = cid
  · exfalso; apply h; rw [← hc]; exact cidOf_ver v k
  · simp [hc]

/-- The subtype of fingerprints **conforming** to a target CID at version `v`. -/
def Conforming (cid : Nat) (v : SemVer) : Type := {k : Nat // cidOf v k = cid}

/-! ## §5  Feature 3 — FFI across compatible type boundaries -/

/-- **ABI/FFI compatibility** of two CIDs: same prefix and same *major* version.
Two declarations whose CIDs are FFI-compatible may be linked across an FFI call. -/
def FFICompatible (a b : Nat) : Prop :=
  decPrefix a = decPrefix b ∧ decMajor (decVer a) = decMajor (decVer b)

/-- FFI compatibility is reflexive. -/
theorem FFICompatible.refl (a : Nat) : FFICompatible a a := ⟨rfl, rfl⟩

/-- FFI compatibility is symmetric. -/
theorem FFICompatible.symm {a b : Nat} (h : FFICompatible a b) : FFICompatible b a :=
  ⟨h.1.symm, h.2.symm⟩

/-- FFI compatibility is transitive. -/
theorem FFICompatible.trans {a b c : Nat}
    (h1 : FFICompatible a b) (h2 : FFICompatible b c) : FFICompatible a c :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

/-- Boolean FFI-compatibility gate. -/
def ffiCompatibleB (a b : Nat) : Bool :=
  (decPrefix a == decPrefix b) && (decMajor (decVer a) == decMajor (decVer b))

/-- The Boolean gate agrees with the proposition. -/
theorem ffiCompatibleB_iff (a b : Nat) : ffiCompatibleB a b = true ↔ FFICompatible a b := by
  unfold ffiCompatibleB FFICompatible
  simp [Bool.and_eq_true, beq_iff_eq]

/-- Two CIDs at **compatible** versions are FFI-compatible. -/
theorem ffiCompatible_of_compatible (v w : SemVer) (k j : Nat)
    (hM : v.major < 256) (hw : w.major < 256) (h : Compatible v w) :
    FFICompatible (cidOf v k) (cidOf w j) := by
  refine ⟨?_, ?_⟩
  · rw [cidOf_prefix, cidOf_prefix]
  · rw [cidOf_ver, cidOf_ver]
    unfold decMajor encodeVer
    have hvm : v.major % 256 = v.major := Nat.mod_eq_of_lt hM
    have hwm : w.major % 256 = w.major := Nat.mod_eq_of_lt hw
    unfold Compatible at h
    omega

/-- An **FFI transport gate**: a payload `x : α` crosses from `caller` to `callee`
only when their CIDs are FFI-compatible. -/
def ffiCall {α : Type} (caller callee : Nat) (x : α) : Option α :=
  if ffiCompatibleB caller callee then some x else none

/-- The FFI gate is **sound**: a payload only crosses a genuinely compatible
boundary. -/
theorem ffiCall_sound {α : Type} (caller callee : Nat) (x y : α)
    (h : ffiCall caller callee x = some y) : FFICompatible caller callee := by
  unfold ffiCall at h
  by_cases hc : ffiCompatibleB caller callee
  · exact (ffiCompatibleB_iff _ _).mp hc
  · simp [hc] at h

/-- Across a compatible boundary, the payload is transported unchanged. -/
theorem ffiCall_compatible {α : Type} (caller callee : Nat) (x : α)
    (h : FFICompatible caller callee) : ffiCall caller callee x = some x := by
  unfold ffiCall
  rw [(ffiCompatibleB_iff _ _).mpr h]; rfl

/-! ## §6  Feature 4 — ZKP-style proofs of conformity

A prover commits to a fingerprint `k` with salt `r` via a *binding* commitment.
Later it can open the commitment and prove the CID is `cid` at version `v`.  We
prove **completeness** (an honest opening verifies) and **binding** (a commitment
determines a unique fingerprint, hence a unique CID — conformity cannot be
equivocated).  The *hiding* property of a real ZKP is not formalised. -/

/-- `2^32`, the salt space. -/
def two32 : Nat := 2 ^ 32

/-- A binding commitment to fingerprint `k` with salt `r` (`r < 2^32`). -/
def commit (k r : Nat) : Nat := k * two32 + r

/-- The commitment is **binding**: equal commitments with in-range salts have
equal fingerprints and equal salts. -/
theorem commit_inj (k r k' r' : Nat) (hr : r < two32) (hr' : r' < two32)
    (h : commit k r = commit k' r') : k = k' ∧ r = r' := by
  unfold commit two32 at *; omega

/-- The conformity **verifier**: check the opening `(k, r)` matches commitment `c`
and that `k`'s CID at version `v` is `cid`. -/
def verifyConformity (c cid : Nat) (v : SemVer) (k r : Nat) : Bool :=
  (commit k r == c) && (cidOf v k == cid)

/-- **Completeness**: an honest prover's opening always verifies. -/
theorem conformity_complete (v : SemVer) (k r : Nat) :
    verifyConformity (commit k r) (cidOf v k) v k r = true := by
  unfold verifyConformity; simp

/-- **Binding/soundness of conformity**: a single commitment cannot be opened to
two different CIDs.  If two openings (with in-range salts) both verify against the
same commitment `c` and the same version `v`, the claimed CIDs coincide. -/
theorem conformity_binding (c cid cid' : Nat) (v : SemVer) (k r k' r' : Nat)
    (hr : r < two32) (hr' : r' < two32)
    (h1 : verifyConformity c cid v k r = true)
    (h2 : verifyConformity c cid' v k' r' = true) : cid = cid' := by
  unfold verifyConformity at h1 h2
  simp only [Bool.and_eq_true, beq_iff_eq] at h1 h2
  obtain ⟨hc1, hd1⟩ := h1
  obtain ⟨hc2, hd2⟩ := h2
  have hcommit : commit k r = commit k' r' := by rw [hc1, hc2]
  obtain ⟨hk, _⟩ := commit_inj k r k' r' hr hr' hcommit
  rw [← hd1, ← hd2, hk]

/-! ## §7  Feature 5 — linking modules along CID boundaries

A linker combines two module CIDs into one.  We XOR the digests (so order does
not matter) and keep the version field; the result is again a well-formed CID. -/

/-- **Link** two module CIDs: keep `a`'s version, XOR the digests. -/
def link (a b : Nat) : Nat := pack (decVer a) ((decDigest a) ^^^ (decDigest b))

/-- A digest field is always `< 2^24`. -/
theorem decDigest_lt (a : Nat) : decDigest a < two24 := by
  unfold decDigest two24; exact Nat.mod_lt _ (by positivity)

/-- A version field is always `< 2^24`. -/
theorem decVer_lt (a : Nat) : decVer a < two24 := by
  unfold decVer two24; exact Nat.mod_lt _ (by positivity)

/-- The XOR of two digests stays in 24 bits. -/
theorem digest_xor_lt (a b : Nat) : (decDigest a) ^^^ (decDigest b) < two24 := by
  unfold two24
  exact Nat.xor_lt_two_pow (by have := decDigest_lt a; unfold two24 at this; exact this)
    (by have := decDigest_lt b; unfold two24 at this; exact this)

/-- Linking preserves the semantic prefix `0x5EC1`. -/
theorem link_prefix (a b : Nat) : decPrefix (link a b) = 0x5EC1 := by
  unfold link
  exact decPrefix_pack _ _ (decVer_lt a) (digest_xor_lt a b)

/-- Linking keeps the first module's version field. -/
theorem link_ver (a b : Nat) : decVer (link a b) = decVer a := by
  unfold link
  exact decVer_pack _ _ (decVer_lt a) (digest_xor_lt a b)

/-- Linking XORs the two digests. -/
theorem link_digest (a b : Nat) : decDigest (link a b) = (decDigest a) ^^^ (decDigest b) := by
  unfold link
  exact decDigest_pack _ _ (digest_xor_lt a b)

/-- Linking is **commutative on the digest** (the linked digest does not depend on
link order). -/
theorem link_digest_comm (a b : Nat) : decDigest (link a b) = decDigest (link b a) := by
  rw [link_digest, link_digest, Nat.xor_comm]

/-- Linking is **associative on the digest**. -/
theorem link_digest_assoc (a b c : Nat) :
    decDigest (link (link a b) c) = decDigest (link a (link b c)) := by
  simp only [link_digest, Nat.xor_assoc]

/-- **Linking respects the FFI boundary.**  Linking onto any well-formed CID `a`
(one carrying the semantic prefix) yields a CID FFI-compatible with `a`: the
linked module sits on the same boundary. -/
theorem link_compatible (a b : Nat) (ha : decPrefix a = 0x5EC1) :
    FFICompatible (link a b) a := by
  refine ⟨?_, ?_⟩
  · rw [link_prefix, ha]
  · rw [link_ver]

/-! ## §8  A CID for mathlib, and the reflection front-end -/

/-- The semantic CID of declaration with fingerprint `k`, at the mathlib version. -/
def mathlibCidOf (k : Nat) : Nat := cidOf mathlibVersion k

/-- The mathlib CID always carries the semantic prefix. -/
theorem mathlibCidOf_prefix (k : Nat) : decPrefix (mathlibCidOf k) = 0x5EC1 := by
  unfold mathlibCidOf; exact cidOf_prefix _ _

/-- A hex character for a single nibble. -/
def hexDigit (d : Nat) : Char := "0123456789ABCDEF".toList.getD d '0'

/-- Render `n` as uppercase hex (recursion on `n / 16`). -/
partial def toHexAux (n : Nat) (acc : String) : String :=
  if n == 0 then acc else toHexAux (n / 16) (String.singleton (hexDigit (n % 16)) ++ acc)

/-- Render `n` as `0x…` uppercase hex. -/
def toHex (n : Nat) : String := if n == 0 then "0x0" else "0x" ++ toHexAux n ""

/-- A textual semantic-CID report for declaration `decl` with fingerprint `k`. -/
def reportOf (decl : Name) (k : Nat) : String :=
  let a := mathlibCidOf k
  let v := mathlibVersion
  s!"[Aristo Semantic CID] {decl}\n" ++
  s!"  ├── structural fingerprint k = {k}\n" ++
  s!"  ├── semantic version = {v.major}.{v.minor}.{v.patch}\n" ++
  s!"  ├── semantic CID = {toHex a}\n" ++
  s!"  ├── prefix = {toHex (decPrefix a)} · version = {toHex (decVer a)}\n" ++
  s!"  └── digest (k % 2^24) = {toHex (decDigest a)}"

/-- `#semanticcid f` prints the semantic CID of declaration `f` at the mathlib
version, computed from its structural fingerprint. -/
syntax (name := semanticcidCmd) "#semanticcid " ident : command

@[command_elab semanticcidCmd]
def elabSemanticcid : CommandElab := fun stx => do
  match stx with
  | `(#semanticcid $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadCore id.getId
    let k ← liftTermElabM <| Meta.MetaM.run' (ExprAddress.declStructuralSum name)
    logInfo (reportOf name k)
  | _ => throwError "ill-formed #semanticcid command"

/-! ## §9  Test suite -/

#semanticcid Nat.add
#semanticcid List.map
#semanticcid Prod.fst

end SemCID

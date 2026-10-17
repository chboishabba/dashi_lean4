import Mathlib

/-!
# Canonical 0xDA51 address core

The wire ABI is frozen as

```
[prefix:16][type:4][data:44]
```

with prefix `0xDA51`.  Historical type codes `0`–`7` keep their original
meanings; code `8` is reserved for theory-atlas entries.
-/

namespace DA51

/-- The canonical DA51 prefix, `0xDA51 = 55889`. -/
def prefixVal : ℕ := 0xDA51

theorem prefixVal_eq : prefixVal = 55889 := rfl

/-- The frozen DA51 type registry. -/
inductive AddrType
  | monsterWalk
  | astNode
  | monsterProtocol
  | nestedCID
  | harmonicPath
  | shardID
  | eigenspaceAddr
  | hauptmodul
  | atlasEntry
  deriving DecidableEq, Repr

/-- The 4-bit type code.  Codes `0`–`7` are historical; `8` is additive. -/
def AddrType.code : AddrType → ℕ
  | .monsterWalk => 0
  | .astNode => 1
  | .monsterProtocol => 2
  | .nestedCID => 3
  | .harmonicPath => 4
  | .shardID => 5
  | .eigenspaceAddr => 6
  | .hauptmodul => 7
  | .atlasEntry => 8

/-- Decode a known DA51 type code.  Codes `9`–`15` remain unassigned. -/
def AddrType.ofCode : ℕ → Option AddrType
  | 0 => some .monsterWalk
  | 1 => some .astNode
  | 2 => some .monsterProtocol
  | 3 => some .nestedCID
  | 4 => some .harmonicPath
  | 5 => some .shardID
  | 6 => some .eigenspaceAddr
  | 7 => some .hauptmodul
  | 8 => some .atlasEntry
  | _ => none

theorem AddrType.ofCode_code (t : AddrType) : AddrType.ofCode t.code = some t := by
  cases t <;> rfl

theorem AddrType.code_lt (t : AddrType) : t.code < 16 := by
  cases t <;> decide

theorem AddrType.code_injective : Function.Injective AddrType.code := by
  intro a b h
  cases a <;> cases b <;> simp_all [AddrType.code]

/-- Assemble an address from a type code and a data word. -/
def mkAddr (t d : ℕ) : ℕ :=
  prefixVal * 2 ^ 48 + (t % 16) * 2 ^ 44 + d % 2 ^ 44

/-- The prefix field, bits 63–48. -/
def prefixOf (a : ℕ) : ℕ := a / 2 ^ 48

/-- The type field, bits 47–44. -/
def typeOf (a : ℕ) : ℕ := a / 2 ^ 44 % 16

/-- The data field, bits 43–0. -/
def dataOf (a : ℕ) : ℕ := a % 2 ^ 44

/-- A valid DA51 envelope fits in 64 bits and carries the canonical prefix. -/
def IsValid (a : ℕ) : Prop := a < 2 ^ 64 ∧ prefixOf a = prefixVal

theorem prefixOf_mk (t d : ℕ) : prefixOf (mkAddr t d) = prefixVal := by
  unfold prefixOf mkAddr prefixVal
  omega

theorem typeOf_mk (t d : ℕ) : typeOf (mkAddr t d) = t % 16 := by
  unfold typeOf mkAddr prefixVal
  omega

theorem dataOf_mk (t d : ℕ) : dataOf (mkAddr t d) = d % 2 ^ 44 := by
  unfold dataOf mkAddr prefixVal
  omega

theorem mk_lt_two_pow_64 (t d : ℕ) : mkAddr t d < 2 ^ 64 := by
  unfold mkAddr prefixVal
  omega

theorem mk_isValid (t d : ℕ) : IsValid (mkAddr t d) :=
  ⟨mk_lt_two_pow_64 t d, prefixOf_mk t d⟩

/-- Type and data are recovered whenever they fit their fields. -/
theorem mk_injective {t t' d d' : ℕ}
    (ht : t < 16) (ht' : t' < 16) (hd : d < 2 ^ 44) (hd' : d' < 2 ^ 44)
    (h : mkAddr t d = mkAddr t' d') : t = t' ∧ d = d' := by
  have h1 := typeOf_mk t d
  have h2 := dataOf_mk t d
  rw [h, typeOf_mk] at h1
  rw [h, dataOf_mk] at h2
  constructor <;> omega

/-! ## Agreement with the historical UInt64 extraction -/

/-- `a >>> 48` on `UInt64` is the prefix field. -/
theorem prefixOf_eq_shift {a : ℕ} (h : a < 2 ^ 64) :
    (a.toUInt64 >>> 48).toNat = prefixOf a := by
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.toUInt64_eq,
    UInt64.toNat_ofNat', prefixOf]
  omega

/-- `(a >>> 44) &&& 0xF` on `UInt64` is the type field. -/
theorem typeOf_eq_shift {a : ℕ} (h : a < 2 ^ 64) :
    ((a.toUInt64 >>> 44) &&& 0xF).toNat = typeOf a := by
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.toUInt64_eq,
    UInt64.toNat_ofNat', UInt64.toNat_and, typeOf]
  rw [show (15 : ℕ) = 2 ^ 4 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- `a &&& 0x00000FFFFFFFFFFF` on `UInt64` is the data field. -/
theorem dataOf_eq_mask {a : ℕ} :
    (a.toUInt64 &&& 0x00000FFFFFFFFFFF).toNat = dataOf a := by
  simp [Nat.toUInt64_eq, UInt64.toNat_ofNat', UInt64.toNat_and, dataOf]
  rw [show (17592186044415 : ℕ) = 2 ^ 44 - 1 by rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- Recognize a canonical, currently assigned DA51 envelope. -/
def decodeType (a : ℕ) : Option AddrType :=
  if IsValid a then AddrType.ofCode (typeOf a) else none

end DA51

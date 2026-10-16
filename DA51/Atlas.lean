import DA51.Core

/-!
# DA51 type-8 theory-atlas coordinates

Type `8` data is laid out as

```
[level:4][biome:4][status:4][serial:12][reserved:20]
```

Canonical atlas encodings require the reserved low 20 bits to be zero.
This module is deliberately wire-semantic only: a decoded status nibble is not
itself a theorem proof or a security authorization.
-/

namespace DA51.Atlas

inductive Level
  | delta0 | pi1 | sigma1 | pi2 | sigma2 | lean
  deriving DecidableEq, Repr

namespace Level

def code : Level → ℕ
  | .delta0 => 0
  | .pi1 => 1
  | .sigma1 => 2
  | .pi2 => 3
  | .sigma2 => 4
  | .lean => 5

def ofCode : ℕ → Option Level
  | 0 => some .delta0
  | 1 => some .pi1
  | 2 => some .sigma1
  | 3 => some .pi2
  | 4 => some .sigma2
  | 5 => some .lean
  | _ => none

def rank : Level → ℕ := code

def selfHosted : Level → Bool
  | .delta0 | .pi1 | .sigma1 => true
  | .pi2 | .sigma2 | .lean => false

theorem ofCode_code (l : Level) : ofCode l.code = some l := by cases l <;> rfl

theorem code_lt (l : Level) : l.code < 8 := by cases l <;> decide

theorem code_lt_of_rank_lt {l l' : Level} (h : l.rank < l'.rank) : l.code < l'.code := h

end Level

inductive Biome
  | moonshineHighlands
  | eisensteinPlains
  | spectralSea
  | bridgeMarsh
  | oggArchipelago
  | scaffoldFoothills
  | galleryPeaks
  | machineWorks
  | haltingPens
  deriving DecidableEq, Repr

namespace Biome

def code : Biome → ℕ
  | .moonshineHighlands => 0
  | .eisensteinPlains => 1
  | .spectralSea => 2
  | .bridgeMarsh => 3
  | .oggArchipelago => 4
  | .scaffoldFoothills => 5
  | .galleryPeaks => 6
  | .machineWorks => 7
  | .haltingPens => 8

def ofCode : ℕ → Option Biome
  | 0 => some .moonshineHighlands
  | 1 => some .eisensteinPlains
  | 2 => some .spectralSea
  | 3 => some .bridgeMarsh
  | 4 => some .oggArchipelago
  | 5 => some .scaffoldFoothills
  | 6 => some .galleryPeaks
  | 7 => some .machineWorks
  | 8 => some .haltingPens
  | _ => none

theorem ofCode_code (b : Biome) : ofCode b.code = some b := by cases b <;> rfl

theorem code_lt (b : Biome) : b.code < 16 := by cases b <;> decide

end Biome

inductive Status
  | open_
  | provedTrue
  | provedFalse
  | trueInLiterature
  | falseInLiterature
  deriving DecidableEq, Repr

namespace Status

def code : Status → ℕ
  | .open_ => 0
  | .provedTrue => 1
  | .provedFalse => 2
  | .trueInLiterature => 3
  | .falseInLiterature => 4

def ofCode : ℕ → Option Status
  | 0 => some .open_
  | 1 => some .provedTrue
  | 2 => some .provedFalse
  | 3 => some .trueInLiterature
  | 4 => some .falseInLiterature
  | _ => none

theorem ofCode_code (s : Status) : ofCode s.code = some s := by cases s <;> rfl

theorem code_lt (s : Status) : s.code < 8 := by cases s <;> decide

/-- Proof obligation used by typed catalogue owners.  Raw wire decoding never manufactures it. -/
def Sound (P : Prop) : Status → Prop
  | .provedTrue => P
  | .provedFalse => ¬ P
  | _ => True

end Status

/-- A canonical atlas coordinate. -/
structure Coord where
  level : Level
  biome : Biome
  status : Status
  serial : Fin 4096
  deriving DecidableEq, Repr

namespace Coord

/-- The 44-bit atlas data word. -/
def data (c : Coord) : ℕ :=
  (((c.level.code * 16 + c.biome.code) * 16 + c.status.code) * 4096 + c.serial.val) * 2 ^ 20

/-- The complete type-8 DA51 address. -/
def address (c : Coord) : ℕ := DA51.mkAddr DA51.AddrType.atlasEntry.code c.data

theorem data_lt (c : Coord) : c.data < 2 ^ 44 := by
  have hl := c.level.code_lt
  have hb := c.biome.code_lt
  have hs := c.status.code_lt
  have hn := c.serial.isLt
  unfold data
  omega

/-- Field extraction from a 44-bit data word. -/
def levelField (d : ℕ) : ℕ := d / 2 ^ 40 % 16
def biomeField (d : ℕ) : ℕ := d / 2 ^ 36 % 16
def statusField (d : ℕ) : ℕ := d / 2 ^ 32 % 16
def serialField (d : ℕ) : ℕ := d / 2 ^ 20 % 4096
def reservedField (d : ℕ) : ℕ := d % 2 ^ 20

/-- Decode a canonical atlas data word.  Nonzero reserved bits are rejected. -/
def decodeData (d : ℕ) : Option Coord :=
  if reservedField d = 0 then
    match Level.ofCode (levelField d), Biome.ofCode (biomeField d),
      Status.ofCode (statusField d) with
    | some l, some b, some s => some ⟨l, b, s, Fin.ofNat 4096 (serialField d)⟩
    | _, _, _ => none
  else none

/-- Decode a canonical atlas address. -/
def decode (a : ℕ) : Option Coord :=
  if a < 2 ^ 64 ∧ DA51.prefixOf a = DA51.prefixVal ∧
      DA51.typeOf a = DA51.AddrType.atlasEntry.code then
    decodeData (DA51.dataOf a)
  else none

theorem fields_data (c : Coord) :
    levelField c.data = c.level.code ∧
    biomeField c.data = c.biome.code ∧
    statusField c.data = c.status.code ∧
    serialField c.data = c.serial.val ∧
    reservedField c.data = 0 := by
  have hl := c.level.code_lt
  have hb := c.biome.code_lt
  have hs := c.status.code_lt
  have hn := c.serial.isLt
  unfold levelField biomeField statusField serialField reservedField data
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Encoding followed by decoding returns the original coordinate. -/
theorem decode_address (c : Coord) : decode c.address = some c := by
  have hd : DA51.dataOf c.address = c.data := by
    rw [address, DA51.dataOf_mk, Nat.mod_eq_of_lt c.data_lt]
  obtain ⟨h1, h2, h3, h4, h5⟩ := fields_data c
  have hv : c.address < 2 ^ 64 ∧ DA51.prefixOf c.address = DA51.prefixVal ∧
      DA51.typeOf c.address = DA51.AddrType.atlasEntry.code :=
    ⟨DA51.mk_lt_two_pow_64 _ _, DA51.prefixOf_mk _ _, by
      rw [address, DA51.typeOf_mk]
      rfl⟩
  rw [decode, if_pos hv, hd, decodeData, h5, if_pos rfl, h1, h2, h3,
    Level.ofCode_code, Biome.ofCode_code, Status.ofCode_code, h4]
  simp only [Fin.ofNat_val_eq_self]

theorem address_injective : Function.Injective address := fun c c' h => by
  have hc := decode_address c
  rw [h, decode_address] at hc
  exact (Option.some.inj hc).symm

theorem address_isValid (c : Coord) : DA51.IsValid c.address := DA51.mk_isValid _ _

theorem typeOf_address (c : Coord) : DA51.typeOf c.address = DA51.AddrType.atlasEntry.code := by
  rw [address, DA51.typeOf_mk]
  rfl

/-- Addresses sort first by atlas level rank because level occupies the top data nibble. -/
theorem address_lt_of_rank_lt {c c' : Coord} (h : c.level.rank < c'.level.rank) :
    c.address < c'.address := by
  have hl := Level.code_lt_of_rank_lt h
  have hb := c.biome.code_lt
  have hb' := c'.biome.code_lt
  have hs := c.status.code_lt
  have hs' := c'.status.code_lt
  have hn := c.serial.isLt
  have hn' := c'.serial.isLt
  have hd := c.data_lt
  have hd' := c'.data_lt
  unfold address DA51.mkAddr
  rw [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hd']
  unfold data
  omega

/-- Self-hosted levels (`delta0`, `pi1`, `sigma1`) form an initial address segment. -/
theorem selfHosted_iff_address_lt (c : Coord) :
    c.level.selfHosted = true ↔ c.address < 0xDA51830000000000 := by
  have hb := c.biome.code_lt
  have hs := c.status.code_lt
  have hn := c.serial.isLt
  have hd := c.data_lt
  unfold address DA51.mkAddr DA51.prefixVal
  rw [Nat.mod_eq_of_lt hd]
  unfold data
  cases h : c.level <;>
    simp [Level.selfHosted, Level.code, DA51.AddrType.code] <;> omega

end Coord

/-- A typed proof-carrying placement.  This is intentionally stronger than wire decoding. -/
structure Placed (P : Prop) where
  coord : Coord
  sound : coord.status.Sound P

namespace Placed

variable {P : Prop}

/-- A status-1 typed placement exposes its stored proof. -/
theorem holds_of_status (x : Placed P) (h : x.coord.status = .provedTrue) : P := by
  have hs := x.sound
  rw [h] at hs
  exact hs

end Placed

end DA51.Atlas

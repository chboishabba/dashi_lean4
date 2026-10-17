import DA51.Atlas

/-!
# DA51 golden fixtures

These literals are the cross-language compatibility contract for atlas type 8.
-/

namespace DA51.Fixtures

open DA51.Atlas

/-- The 23 atlas coordinates in catalogue serial order. -/
def catalogueCoords : List Coord :=
  [⟨.delta0, .moonshineHighlands, .provedTrue, 0⟩,
   ⟨.delta0, .moonshineHighlands, .provedTrue, 1⟩,
   ⟨.delta0, .moonshineHighlands, .provedTrue, 2⟩,
   ⟨.delta0, .haltingPens, .provedTrue, 3⟩,
   ⟨.pi1, .haltingPens, .open_, 4⟩,
   ⟨.pi1, .eisensteinPlains, .provedTrue, 5⟩,
   ⟨.pi1, .bridgeMarsh, .open_, 6⟩,
   ⟨.pi1, .bridgeMarsh, .falseInLiterature, 7⟩,
   ⟨.pi2, .eisensteinPlains, .provedTrue, 8⟩,
   ⟨.pi2, .haltingPens, .open_, 9⟩,
   ⟨.lean, .bridgeMarsh, .open_, 10⟩,
   ⟨.lean, .bridgeMarsh, .open_, 11⟩,
   ⟨.lean, .spectralSea, .open_, 12⟩,
   ⟨.lean, .eisensteinPlains, .provedTrue, 13⟩,
   ⟨.lean, .eisensteinPlains, .provedTrue, 14⟩,
   ⟨.lean, .spectralSea, .provedTrue, 15⟩,
   ⟨.lean, .spectralSea, .provedTrue, 16⟩,
   ⟨.lean, .spectralSea, .provedTrue, 17⟩,
   ⟨.lean, .moonshineHighlands, .provedTrue, 18⟩,
   ⟨.lean, .moonshineHighlands, .provedTrue, 19⟩,
   ⟨.lean, .moonshineHighlands, .provedTrue, 20⟩,
   ⟨.lean, .moonshineHighlands, .trueInLiterature, 21⟩,
   ⟨.lean, .moonshineHighlands, .trueInLiterature, 22⟩]

def catalogueAddresses : List ℕ := catalogueCoords.map Coord.address

/-- Exact 64-bit fixture literals. -/
theorem catalogue_addresses : catalogueAddresses =
    [0xDA51800100000000, 0xDA51800100100000, 0xDA51800100200000, 0xDA51808100300000,
     0xDA51818000400000, 0xDA51811100500000, 0xDA51813000600000, 0xDA51813400700000,
     0xDA51831100800000, 0xDA51838000900000, 0xDA51853000A00000, 0xDA51853000B00000,
     0xDA51852000C00000, 0xDA51851100D00000, 0xDA51851100E00000, 0xDA51852100F00000,
     0xDA51852101000000, 0xDA51852101100000, 0xDA51850101200000, 0xDA51850101300000,
     0xDA51850101400000, 0xDA51850301500000, 0xDA51850301600000] := rfl

/-- All catalogue fixture addresses are distinct. -/
theorem catalogue_addresses_nodup : catalogueAddresses.Nodup := by
  rw [catalogue_addresses]
  decide

/-- Every fixture is a valid DA51 envelope and round-trips through the atlas decoder. -/
theorem catalogue_decode :
    ∀ c ∈ catalogueCoords, DA51.IsValid c.address ∧ Coord.decode c.address = some c :=
  fun c _ => ⟨c.address_isValid, c.decode_address⟩

/-- Reserved low bits make a type-8 payload non-canonical. -/
example : Coord.decode 0xDA51800100000001 = none := by decide

/-- Unknown type code 9 is not a recognized DA51 semantic type. -/
example : DA51.decodeType 0xDA51900000000000 = none := by decide

/-- Maximum serial is representable and round-trips. -/
example :
    let c : Coord := ⟨.lean, .haltingPens, .falseInLiterature, 4095⟩
    Coord.decode c.address = some c := by
  simp [Coord.decode_address]

end DA51.Fixtures

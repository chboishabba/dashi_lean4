/-!
A deliberately small WrongType/McNamara adapter to the generic B^k owner.
Original McNamara XY cell = violated frame × imposed logic. Any additional
coordinate or normative reading needs its own source- and query-specific
meaning. The adapter claims no automatic legal wrongdoing or culpability.
-/
import AgdaMirror.Core.IndexedRelationalHyperfabric
import AgdaMirror.Law.WrongTypeGrid

namespace AgdaMirror.Law.WrongTypeGrid.GenericHyperfabricAdapter

open AgdaMirror.Core.IndexedRelationalHyperfabric

abbrev ModeAddress (k : Nat) := Address Mode k

def sourceGridProjection {k : Nat} (address : ModeAddress (k + 2)) : Cell :=
  ⟨address ⟨0, by omega⟩, address ⟨1, by omega⟩⟩

structure SituatedWrongContext (k : Nat) where
  address : ModeAddress k
  wrongTypeId : String
  actorInterestReference : String
  eventReference : String
  normAndJurisdictionReference : String
  authorityReference : String
  evidenceReference : String

structure GroundedConsumer {State View Answer : Type}
    (observe : State → View) (query : State → Answer) where
  sufficient : FactorsThrough observe query
  Authority : Prop
  authorityReceipt : Authority
  Source : Prop
  sourceReceipt : Source

theorem no_automatic_query_promotion
    {State View Answer : Type}
    (observe : State → View) (query : State → Answer)
    (witness : Collision observe query) :
    ¬ FactorsThrough observe query :=
  collision_blocks_factorisation witness

theorem grid_has_nine_sites : sites 3 2 = 9 := three_two
theorem cube_has_twenty_seven_sites : sites 3 3 = 27 := three_three
theorem four_axes_have_eighty_one_sites : sites 3 4 = 81 := three_four

end AgdaMirror.Law.WrongTypeGrid.GenericHyperfabricAdapter

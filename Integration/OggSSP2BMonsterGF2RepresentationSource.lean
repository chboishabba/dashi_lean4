import Integration.OggSSP2BActualStableCompletionSubquotient

/-!
# Explicit Monster representation over GF(2): source boundary

Wilson and collaborators constructed the Monster on a 196882-dimensional vector space
over GF(2), with standard generators and vector-action routines in the 3-local computer
construction.  This is the right characteristic for the remaining post-Brauer extension
problem, but the sparse action programs/restriction matrices are not currently part of
this repository.

Accordingly this owner records source authority and the exact acquisition boundary; it
does not promote existence of the huge representation into an actual 2B Tate quotient.
-/

namespace Integration.OggSSP2BMonsterGF2RepresentationSource

abbrev monsterGF2Dimension : Nat := 196882

theorem monster_gf2_dimension_exact : monsterGF2Dimension = 196882 := rfl

structure SourceStatus where
  explicitMonsterGF2RepresentationSourced : Bool
  standardGeneratorsComputedExternally : Bool
  vectorActionProgramsKnownExternally : Bool
  actionProgramsPresentInRepository : Bool
  twoBLocalRestrictionMatricesPresent : Bool
  actualTate276IdentificationPaid : Bool
  stableQ10SubquotientPaid : Bool
  outerJ2x5OnSameQPaid : Bool

def canonicalStatus : SourceStatus where
  explicitMonsterGF2RepresentationSourced := true
  standardGeneratorsComputedExternally := true
  vectorActionProgramsKnownExternally := true
  actionProgramsPresentInRepository := false
  twoBLocalRestrictionMatricesPresent := false
  actualTate276IdentificationPaid := false
  stableQ10SubquotientPaid := false
  outerJ2x5OnSameQPaid := false

inductive ExternalGF2MonsterRepresentationIsTwoBTateHead : Prop

theorem external_representation_does_not_identify_tate_head :
    ¬ ExternalGF2MonsterRepresentationIsTwoBTateHead := by
  intro h
  cases h

end Integration.OggSSP2BMonsterGF2RepresentationSource

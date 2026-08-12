/-!
Lean mirror of `DASHI.Physics.YangMills.YMSourceAuthoritySurface`.
This is inventory metadata only.  It neither imports a theorem nor promotes the
Yang–Mills claim.  The Agda promotion invariant is represented directly by the
constant `clayYangMillsPromoted = false`.
-/
namespace AgdaMirror.Physics.YangMills.YMSourceAuthoritySurface

/-- Lane-local mirror of the global Clay promotion flag.  It remains false. -/
def clayYangMillsPromoted : Bool := false

theorem clayYangMillsPromoted_false : clayYangMillsPromoted = false := rfl

inductive SourceAuthorityId where
  | eriksson26020041 | eriksson26020052 | eriksson26020056
  | eriksson26020069 | eriksson26020072 | eriksson26020087
  | eriksson26020088 | eriksson26020089 | eriksson26020091
  | eriksson26020092 | eriksson26020096
  | balabanCmp095 | balabanCmp099 | balabanCmp109 | balabanCmp116
  | balabanCmp119 | balabanCmp122 | zenodo18799942 | zenodo18800920
  | diestelGraphTheory | dashiInternalProof | unknownAuthority
  deriving DecidableEq, Repr

inductive VerificationStatus where
  | proved | standardWrapper | paperImport | auditTested | openTarget
  | mixedReducer | provedConditionalReducer
  deriving DecidableEq, Repr

inductive ClaimRole where
  | postulateImport | consequenceProof | conventionDefinition
  deriving DecidableEq, Repr

/-- Authority metadata.  The final field preserves the non-promotion boundary. -/
structure SourceAuthorityDetails where
  sourceAuthorityId : SourceAuthorityId
  theoremLocator : String
  claimRole : ClaimRole
  verificationStatus : VerificationStatus
  noClayPromotion : clayYangMillsPromoted = false

end AgdaMirror.Physics.YangMills.YMSourceAuthoritySurface

module DASHI.Core.AristotleReliableSourceConsumerAdequacyBidiExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- ARISTOTLE / WIKIDATA RETURN 3
--   full ⊇ sourced ⊇ reliable  ×  PROVENANCE-SENSITIVE CONSUMER ADEQUACY
--
-- Reverse extraction of the Lean owner
--   Integration.Kernel.Aristotle.ReliableSourceConsumerAdequacy,
-- which instantiates the independent-support and quorum owners on the
-- reference semantics of the archive module RequestProject.Provenance
-- (where `imported from Wikimedia project` is explicitly not a source).
--
-- STATUS.  Agda source; no Agda kernel receipt is claimed here.
------------------------------------------------------------------------

-- The three reference kinds of the archive.

data RefKind : Set where
  statedIn      : RefKind
  referenceURL  : RefKind
  importedFrom  : RefKind

-- Whether a reference counts as a source at all.

isSource : RefKind → Bool
isSource statedIn     = true
isSource referenceURL = true
isSource importedFrom = false

-- The provenance root a reference rests on.  An `imported from` note has
-- none, which is why it can never pay an independent-support obligation.

data Root : Set where
  gnd     : Root
  someURL : Root

data MaybeRoot : Set where
  noRoot   : MaybeRoot
  hasRoot  : Root → MaybeRoot

------------------------------------------------------------------------
-- THE FIXTURE: THREE VISIBLE ROWS, TWO SOURCE-BEARING, ONE ROOT
------------------------------------------------------------------------

data Row : Set where
  rowImported : Row
  rowStated₁  : Row
  rowStated₂  : Row

kindOf : Row → RefKind
kindOf rowImported = importedFrom
kindOf rowStated₁  = statedIn
kindOf rowStated₂  = statedIn

rootOf : Row → MaybeRoot
rootOf rowImported = noRoot
rootOf rowStated₁  = hasRoot gnd
rootOf rowStated₂  = hasRoot gnd

-- Two source-bearing rows.

bothRowsAreSources : (isSource (kindOf rowStated₁) ≡ true)
                   × (isSource (kindOf rowStated₂) ≡ true)
bothRowsAreSources = refl , refl

-- Resting on the same root: they are not independent.

Independent : Row → Row → Set
Independent r s = ¬ (rootOf r ≡ rootOf s)

sourceRowsAreNotIndependent : ¬ (Independent rowStated₁ rowStated₂)
sourceRowsAreNotIndependent ind = ind refl

-- The `imported from` row contributes no root.

importedContributesNoRoot : rootOf rowImported ≡ noRoot
importedContributesNoRoot = refl

------------------------------------------------------------------------
-- ADEQUACY TIERS
------------------------------------------------------------------------

data Tier : Set where
  full     : Tier
  sourced  : Tier
  reliable : Tier

-- Whether a row is admitted at a tier.

admits : Tier → Row → Bool
admits full     _           = true
admits sourced  _           = true
admits reliable rowImported = false
admits reliable rowStated₁  = true
admits reliable rowStated₂  = true

-- A statement whose only support is an `imported from` note is admitted in
-- the full and sourced tiers and refused in the reliable tier.

importedAdmittedInFull : admits full rowImported ≡ true
importedAdmittedInFull = refl

importedRefusedInReliable : ¬ (admits reliable rowImported ≡ true)
importedRefusedInReliable ()

patternInFullAbsentInReliable :
  (admits full rowImported ≡ true) × (¬ (admits reliable rowImported ≡ true))
patternInFullAbsentInReliable =
  importedAdmittedInFull , importedRefusedInReliable

------------------------------------------------------------------------
-- THE ADEQUACY BOUNDARY
------------------------------------------------------------------------

-- The admissibility shape of the donor owner, with the independence
-- obligation made explicit.

record IndependentSupport : Set₁ where
  constructor independent-support
  field
    Claim : Set
    claim : Claim
    left right : Row
    leftSupports  : isSource (kindOf left) ≡ true
    rightSupports : isSource (kindOf right) ≡ true
    independentRoots : Independent left right

open IndependentSupport public

-- The fixture cannot inhabit it: two visible source-bearing reports, one
-- root, therefore no two-fold independent support.
--
--   #VisibleSupport = 2   does not give   #IndependentSupport = 2.

twoVisibleReportsAreNotTwoIndependentRoots :
  (isSource (kindOf rowStated₁) ≡ true)
  × (isSource (kindOf rowStated₂) ≡ true)
  × (¬ (Independent rowStated₁ rowStated₂))
twoVisibleReportsAreNotTwoIndependentRoots =
  refl , refl , sourceRowsAreNotIndependent

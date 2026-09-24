module DASHI.Core.AristotleWikibaseZelphBraidedPromotionBidiExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- ARISTOTLE / WIKIDATA RETURN 5  (CAPSTONE)
--   BRAIDED PROMOTION TRANSPORT OVER THE NATIVE ⨝ GRAPH EVIDENCE PLANES
--
-- Reverse extraction of the Lean owner
--   Integration.Kernel.Aristotle.WikibaseZelphBraidedPromotion.
--
-- STATUS.  Agda source; no Agda kernel receipt is claimed here.  The four
-- firewalls and the compilation are discharged by the Agda terms below,
-- but nothing in this file has been machine-checked in this environment.
------------------------------------------------------------------------

-- The four evidentiary strands.

data Strand : Set where
  native : Strand
  graph  : Strand
  review : Strand
  policy : Strand

-- The four promotion obligations.

data Obligation : Set where
  artifactObl       : Obligation
  correspondenceObl : Obligation
  transportObl      : Obligation
  inhabitanceObl    : Obligation

-- Which strand can pay which obligation.  Note that the last obligation
-- admits two payers: this is what makes the assignment underdetermined by
-- the receipt.

canPay : Strand → Obligation → Bool
canPay native artifactObl       = true
canPay native correspondenceObl = true
canPay graph  transportObl      = true
canPay review inhabitanceObl    = true
canPay policy inhabitanceObl    = true
canPay native transportObl      = false
canPay native inhabitanceObl    = false
canPay graph  artifactObl       = false
canPay graph  correspondenceObl = false
canPay graph  inhabitanceObl    = false
canPay review artifactObl       = false
canPay review correspondenceObl = false
canPay review transportObl      = false
canPay policy artifactObl       = false
canPay policy correspondenceObl = false
canPay policy transportObl      = false

Assignment : Set
Assignment = Obligation → Strand

Discharges : Assignment → Set
Discharges A = (o : Obligation) → canPay (A o) o ≡ true

reviewAssignment : Assignment
reviewAssignment artifactObl       = native
reviewAssignment correspondenceObl = native
reviewAssignment transportObl      = graph
reviewAssignment inhabitanceObl    = review

policyAssignment : Assignment
policyAssignment artifactObl       = native
policyAssignment correspondenceObl = native
policyAssignment transportObl      = graph
policyAssignment inhabitanceObl    = policy

reviewDischarges : Discharges reviewAssignment
reviewDischarges artifactObl       = refl
reviewDischarges correspondenceObl = refl
reviewDischarges transportObl      = refl
reviewDischarges inhabitanceObl    = refl

policyDischarges : Discharges policyAssignment
policyDischarges artifactObl       = refl
policyDischarges correspondenceObl = refl
policyDischarges transportObl      = refl
policyDischarges inhabitanceObl    = refl

reviewIsNotPolicy : ¬ (review ≡ policy)
reviewIsNotPolicy ()

assignmentsDiffer : ¬ (reviewAssignment ≡ policyAssignment)
assignmentsDiffer eq = reviewIsNotPolicy (cong (λ f → f inhabitanceObl) eq)

------------------------------------------------------------------------
-- COMPILATION INTO AN ORDINARY RECEIPT
------------------------------------------------------------------------

-- The receipt records that all four obligations are paid; it does not
-- record who paid them.

data Receipt : Set where
  fullPromotionReceipt : Receipt

compile : (A : Assignment) → Discharges A → Receipt
compile _ _ = fullPromotionReceipt

strandAssignmentCompiles : Receipt
strandAssignmentCompiles = compile reviewAssignment reviewDischarges

-- Compilation forgets the assignment.

compileForgetsAssignment :
  compile reviewAssignment reviewDischarges
    ≡ compile policyAssignment policyDischarges
compileForgetsAssignment = refl

-- FullPromotionReceipt does not give ProvenanceAssignment: no function
-- from receipts to assignments is a left inverse of compilation.

fullReceiptDoesNotDetermineProvenance :
  ¬ (Σ (Receipt → Assignment)
       (λ f → (A : Assignment) (d : Discharges A) → f (compile A d) ≡ A))
fullReceiptDoesNotDetermineProvenance (f , law) =
  assignmentsDiffer
    (trans (sym (law reviewAssignment reviewDischarges))
           (law policyAssignment policyDischarges))

------------------------------------------------------------------------
-- THE FOUR FIREWALLS
------------------------------------------------------------------------

-- 1. A native statement receipt does not give graph completeness.

data Question : Set where
  subjectIsHuman : Question
  subjectIsAgent : Question

nativeTruthy : Question → Bool
nativeTruthy subjectIsHuman = true
nativeTruthy subjectIsAgent = false

graphDerives : Question → Bool
graphDerives subjectIsHuman = true
graphDerives subjectIsAgent = false

nativeReceiptIsNotGraphCompleteness :
  (nativeTruthy subjectIsHuman ≡ true) × (graphDerives subjectIsAgent ≡ false)
nativeReceiptIsNotGraphCompleteness = refl , refl

-- 2. Graph soundness does not give native statement semantics: the graph
--    derives a typing for which the only native statement is deprecated,
--    hence not truthy.

data NativeRank : Set where
  preferredRank  : NativeRank
  normalRank     : NativeRank
  deprecatedRank : NativeRank

rankOfPersonStatement : NativeRank
rankOfPersonStatement = deprecatedRank

graphDerivesPerson : Bool
graphDerivesPerson = true

deprecatedIsNotNormal : ¬ (deprecatedRank ≡ normalRank)
deprecatedIsNotNormal ()

graphSoundnessIsNotNativeSemantics :
  (graphDerivesPerson ≡ true) × (¬ (rankOfPersonStatement ≡ normalRank))
graphSoundnessIsNotNativeSemantics = refl , deprecatedIsNotNormal

-- 3. A peer-exact assessment is not policy authority.

data PeerAssessment : Set where
  exactMatch : PeerAssessment

PolicyAuthority : Set
PolicyAuthority = ⊥

peerExactIsNotPolicyAuthority : PeerAssessment × (¬ PolicyAuthority)
peerExactIsNotPolicyAuthority = exactMatch , (λ z → z)

-- 4. Already proved above: the logical receipt does not reconstruct the
--    provenance strands.

braidedPromotionWithoutCollapse :
  Receipt
  × (graphDerives subjectIsAgent ≡ false)
  × (¬ (rankOfPersonStatement ≡ normalRank))
  × (¬ PolicyAuthority)
  × (¬ (Σ (Receipt → Assignment)
          (λ f → (A : Assignment) (d : Discharges A) → f (compile A d) ≡ A)))
braidedPromotionWithoutCollapse =
  strandAssignmentCompiles
  , refl
  , deprecatedIsNotNormal
  , (λ z → z)
  , fullReceiptDoesNotDetermineProvenance

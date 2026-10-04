import Mathlib
import Integration.OggSSPP2OrientedInertiaTenStateRecognition

/-!
# Gaussian-CM ramified embedding source surface at p=2

External source context:
Noam Elkies, Ken Ono, Tonghai Yang,
"Reduction of CM elliptic curves and modular function congruences",
IMRN 2005(44), 2695--2707.

For a CM elliptic curve with CM order O_D and a prime p inert or ramified in
the CM field, Deuring reduction is supersingular and gives a normalized optimal
embedding O_D -> End(E_0).  Embeddings occur in conjugate pairs.  In the
ramified case every embedding in the pair is normalized.

For Gaussian CM K = Q(i), p = 2 is ramified.  Thus the two conjugate/oriented
Gaussian-CM markings are legitimate source-side marking candidates on the
supersingular endomorphism ring.

Goren--Love supplies the oriented-order language: for each imaginary quadratic
discriminant there are exactly two oriented orders up to oriented isomorphism,
exchanged by the nontrivial Galois action.

This file records those source facts and exposes the exact realization contract.
It does not manufacture an actual ring embedding into the particular Banerjee
curve endomorphism ring.
-/

namespace Integration.OggSSPP2GaussianCMRamifiedEmbeddingSource

namespace Ten := Integration.OggSSPP2OrientedInertiaTenStateRecognition

abbrev Orientation := Ten.ClassicalQuadraticOrientation

def conjugateOrientation : Orientation → Orientation
  | .lower => .upper
  | .upper => .lower

theorem conjugate_orientation_involutive
    (o : Orientation) :
    conjugateOrientation (conjugateOrientation o) = o := by
  cases o <;> rfl

theorem orientation_cardinality :
    Fintype.card Orientation = 2 := by decide

structure SourceReceipt where
  gaussianCMFieldIsQGaussian : Bool
  primeTwoRamifiedInGaussianCMField : Bool
  nonSplitCMReductionIsSupersingular : Bool
  reductionProducesOptimalEmbedding : Bool
  ramifiedCaseEveryConjugateEmbeddingNormalized : Bool
  exactlyTwoOrientedOrders : Bool
  sourceTitle : String
  sourceLocator : String
  deriving Repr

def canonicalSourceReceipt : SourceReceipt where
  gaussianCMFieldIsQGaussian := true
  primeTwoRamifiedInGaussianCMField := true
  nonSplitCMReductionIsSupersingular := true
  reductionProducesOptimalEmbedding := true
  ramifiedCaseEveryConjugateEmbeddingNormalized := true
  exactlyTwoOrientedOrders := true
  sourceTitle :=
    "Elkies--Ono--Yang (2005) + Goren--Love (2025)"
  sourceLocator :=
    "EOY Section 3 / Deuring normalized optimal embeddings; Goren--Love Proposition 3.7 and oriented-order discussion"

/--
Formal same-object realization still required by the repo.

The two orientation labels are fixed.  The implementation must supply actual
embedding objects into one chosen supersingular endomorphism object and prove
optimality/normalization for both.
-/
structure Realization (EndomorphismObject : Type) where
  Embedding : Type

  embeddingOfOrientation :
    Orientation → Embedding

  targetEndomorphismObject :
    Embedding → EndomorphismObject

  selectedEndomorphismObject :
    EndomorphismObject

  everyEmbeddingTargetsSelectedObject :
    ∀ o,
      targetEndomorphismObject (embeddingOfOrientation o) =
        selectedEndomorphismObject

  optimal :
    Embedding → Prop

  optimalProof :
    ∀ o, optimal (embeddingOfOrientation o)

  normalized :
    Embedding → Prop

  normalizedProof :
    ∀ o, normalized (embeddingOfOrientation o)

  conjugatePair :
    Prop

  conjugatePairProof :
    conjugatePair

  orientationsDistinct :
    embeddingOfOrientation .lower ≠ embeddingOfOrientation .upper

structure Boundary where
  ramifiedGaussianCMSourceRecorded : Bool
  conjugatePairSourceRecorded : Bool
  bothEmbeddingsNormalizedInRamifiedCaseRecorded : Bool
  twoOrientedOrdersSourceRecorded : Bool
  sameBanerjeeEndomorphismRealizationConstructed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  ramifiedGaussianCMSourceRecorded := true
  conjugatePairSourceRecorded := true
  bothEmbeddingsNormalizedInRamifiedCaseRecorded := true
  twoOrientedOrdersSourceRecorded := true
  sameBanerjeeEndomorphismRealizationConstructed := false

end Integration.OggSSPP2GaussianCMRamifiedEmbeddingSource

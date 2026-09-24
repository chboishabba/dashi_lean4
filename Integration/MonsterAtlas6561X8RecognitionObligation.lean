import Mathlib
import Integration.MoonshineC6TenRankWeightTwelveCrossPollination

/-!
# ATLAS 6561-point action recognition obligation

This mirror does not fabricate ATLAS permutation data.  It states exactly the
extra data needed to promote the numerical 3^8 = 6561 match to an equivariant
identification with a DASHI eight-trit carrier.
-/

namespace Integration.MonsterAtlas6561X8RecognitionObligation

abbrev AtlasPoint6561 := Fin 6561
abbrev CandidateBlock9 := Fin 9
abbrev CandidateWithinBlock729 := Fin 729
abbrev X8 := Fin 8 → Fin 3

theorem nine_times_729 : 9 * 729 = 6561 := by norm_num
theorem three_squared_times_three_sixth :
    (3*3) * 729 = 6561 := by norm_num
theorem three_power_eight : 3^8 = 6561 := by norm_num

structure Atlas6561PermutationData where
  Generator : Type
  act : Generator → AtlasPoint6561 → AtlasPoint6561
  sourceIdentifier : String
  firstGeneratorFile : String
  secondGeneratorFile : String
  generatorFilesAcquired : Bool
  actionDecodedFromGeneratorFiles : Bool

structure NineBy729BlockRecognition (P : Atlas6561PermutationData) where
  encode : AtlasPoint6561 → CandidateBlock9 × CandidateWithinBlock729
  decode : CandidateBlock9 × CandidateWithinBlock729 → AtlasPoint6561
  decodeEncode : ∀ p, decode (encode p) = p
  encodeDecode : ∀ q, encode (decode q) = q

  blockAct : P.Generator → CandidateBlock9 → CandidateBlock9
  withinBlockAct :
    P.Generator → CandidateBlock9 → CandidateWithinBlock729 →
      CandidateWithinBlock729

  actionIntertwines :
    ∀ g p,
      encode (P.act g p)
        =
      let q := encode p
      (blockAct g q.1, withinBlockAct g q.1 q.2)

structure Atlas6561X8Recognition (P : Atlas6561PermutationData) where
  toX8 : AtlasPoint6561 → X8
  fromX8 : X8 → AtlasPoint6561
  fromAfterTo : ∀ p, fromX8 (toX8 p) = p
  toAfterFrom : ∀ x, toX8 (fromX8 x) = x

  x8Act : P.Generator → X8 → X8
  sameAction : ∀ g p, toX8 (P.act g p) = x8Act g (toX8 p)

structure Atlas6561FullRecognition where
  permutationData : Atlas6561PermutationData
  blockRecognition : NineBy729BlockRecognition permutationData
  x8Recognition : Atlas6561X8Recognition permutationData

inductive CardinalityCreatesX8Action : Prop
inductive ImprimitiveMeansNineBy729 : Prop
inductive ExponentTwoPlusSixCreatesBlockSystem : Prop

theorem cardinality_does_not_create_x8_action :
    ¬ CardinalityCreatesX8Action := by
  intro h; cases h

theorem imprimitive_does_not_mean_nine_by_729 :
    ¬ ImprimitiveMeansNineBy729 := by
  intro h; cases h

theorem exponent_split_does_not_create_blocks :
    ¬ ExponentTwoPlusSixCreatesBlockSystem := by
  intro h; cases h

structure Frontier where
  sourceDegree6561Recorded : Bool
  sourceTransitiveRecorded : Bool
  sourceImprimitiveRecorded : Bool
  candidateNineBy729ArithmeticPaid : Bool
  generatorFileIdentifiersLocated : Bool
  generatorBytesAcquiredHere : Bool
  actualPermutationActionDecodedHere : Bool
  actualBlockSystemComputedHere : Bool
  canonicalNineBy729BlockChartProvedHere : Bool
  x8EquivariantRecognitionInhabitedHere : Bool
  deriving Repr

def canonicalFrontier : Frontier where
  sourceDegree6561Recorded := true
  sourceTransitiveRecorded := true
  sourceImprimitiveRecorded := true
  candidateNineBy729ArithmeticPaid := true
  generatorFileIdentifiersLocated := true
  generatorBytesAcquiredHere := false
  actualPermutationActionDecodedHere := false
  actualBlockSystemComputedHere := false
  canonicalNineBy729BlockChartProvedHere := false
  x8EquivariantRecognitionInhabitedHere := false

end Integration.MonsterAtlas6561X8RecognitionObligation

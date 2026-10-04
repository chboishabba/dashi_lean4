import Mathlib
import CondensedMatter.MajoranaB4BraidExact
import CondensedMatter.MajoranaParityQubitExact
import CondensedMatter.MajoranaOperatorKernelExact
import CondensedMatter.MajoranaLogicalBraidGateExact
import CondensedMatter.IsingMajoranaUniversalityBoundaryExact

namespace CondensedMatter
namespace YbSb2

/-!
MAX-CUT STATUS

Mathematical closures:
* exact B4 Majorana braid group action, inverses and braid words;
* Yang-Baxter relations + far commutativity + noncommutativity;
* exact four-Majorana even-parity logical qubit;
* concrete complex Majorana operator kernel, CAR and number projector;
* exact logical braid matrices on the even-parity code space;
* source-scoped Ising/Majorana braiding-alone non-universality boundary.

Open physical residuals are explicitly typed below.
-/

structure MajoranaMathematicsClosed where
  b4YB12 :
    ∀ x : SignedMajorana4,
      sigma1_4 (sigma2_4 (sigma1_4 x)) =
      sigma2_4 (sigma1_4 (sigma2_4 x))
  b4YB23 :
    ∀ x : SignedMajorana4,
      sigma2_4 (sigma3_4 (sigma2_4 x)) =
      sigma3_4 (sigma2_4 (sigma3_4 x))
  far13 :
    ∀ x : SignedMajorana4,
      sigma1_4 (sigma3_4 x) = sigma3_4 (sigma1_4 x)
  adjacentNoncommuting :
    ¬ ∀ x : SignedMajorana4,
      sigma1_4 (sigma2_4 x) = sigma2_4 (sigma1_4 x)
  gamma1Square : CMatrix2.mul gamma1 gamma1 = CMatrix2.one
  gamma2Square : CMatrix2.mul gamma2 gamma2 = CMatrix2.one
  gamma12Anticommute :
    CMatrix2.add (CMatrix2.mul gamma1 gamma2)
      (CMatrix2.mul gamma2 gamma1) = CMatrix2.zero
  numberProjector :
    CMatrix2.mul fermionNumber fermionNumber = fermionNumber
  logicalBraidGates : ExactMajoranaLogicalBraidGates

def canonicalMajoranaMathematicsClosed : MajoranaMathematicsClosed where
  b4YB12 := yangBaxter12_4
  b4YB23 := yangBaxter23_4
  far13 := farCommutation13_4
  adjacentNoncommuting := adjacent12_noncommuting_4
  gamma1Square := gamma1_square
  gamma2Square := gamma2_square
  gamma12Anticommute := gamma12_anticommute
  numberProjector := fermionNumber_projector
  logicalBraidGates := canonicalExactMajoranaLogicalBraidGates

theorem ising_braiding_alone_still_not_universal :
    ¬ canonicalIsingMajoranaUniversalitySourceClaim.braidingAloneUniversal :=
  canonical_ising_braiding_not_universal

structure YbSb2MajoranaPhysicalResiduals where
  isolatedManipulableMajoranas : Prop
  physicalExchangeRealizesExactB4 : Prop
  parityProtectedReadout : Prop
  universalityCompletionResource : Prop
  experimentalDeviceComputation : Prop

end YbSb2
end CondensedMatter

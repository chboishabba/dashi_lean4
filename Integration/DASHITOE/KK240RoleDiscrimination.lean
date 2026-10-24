import Integration.DASHITOE.PrimitiveMaxCut

/-!
TOE x KK/Casimir/QCD 240/243 consumer-role audit.

The three occurrences of numeral 240 are NOT equal physical quantities:
* 240 classical E8 roots (candidate from Agda #1094 243=3+240);
* 240 ideal-plate Casimir pressure denominator (Agda #701);
* about 240 units in selected 5D KK QCD stationarity residual (Agda #1241).

Arithmetical coincidences do not supply action, stress, operator or
representation-intertwining proofs. Literature and upstream math own
original mechanisms; this is an explicitly finite Lean role-check only.
No local import of sibling Agda theorem, no physical E8 identification.
-/

namespace DASHITOE

inductive TwoFortyPhysicalRole where
  | e8RootCardinality
  | parallelPlatePressureDenominator
  | kKQCDStationarityCoefficient
  deriving DecidableEq, Repr

def numberOnly (_ : TwoFortyPhysicalRole) : Nat := 240

theorem numberOnlyCannotDeterminePhysicalRole
    (readout : Nat → TwoFortyPhysicalRole)
    (adequate : ∀ role, readout (numberOnly role) = role) : False := by
  have e8 : readout 240 = .e8RootCardinality := by
    simpa [numberOnly] using adequate .e8RootCardinality
  have plate : readout 240 = .parallelPlatePressureDenominator := by
    simpa [numberOnly] using adequate .parallelPlatePressureDenominator
  have impossible :
      TwoFortyPhysicalRole.e8RootCardinality =
        TwoFortyPhysicalRole.parallelPlatePressureDenominator :=
    e8.symm.trans plate
  cases impossible

theorem ternaryKernelCountArithmetic : 243 = 3 + 240 := by decide

theorem plateDerivativeCountArithmetic : 720 = 3 * 240 := by decide

-- Count of periodic free five-dimensional polarization units,
-- not a claim that the corresponding full QCD action exists.
def selectedQCDNetFreeUnits : Nat := 6 * 3 * 4 - 8 * 3

theorem selectedQCDNetFreeUnitsEq : selectedQCDNetFreeUnits = 48 := by decide

theorem restrictedFreeBosonFortySevenShort : 47 * 5 = 235 := by decide

theorem restrictedFreeBosonFortyEightMax : 48 * 5 = 240 := by decide

-- Any physical scalar-portal/no-go beyond these finite identities
-- depends on the selected 5D free periodic spectrum, radius,
-- real-field polarizations, mass function, and same-action variation.
-- It belongs to Agda KK #1241 rather than being invented in Lean.


/-! Source-attributed Lie-algebra branching DIMENSION arithmetic:
E8|E6×SU3: 248=(78+8)+(27×3)+(27×3).
E6|SU3³: 78=3×8+2×27.
A physically selected 5D SU3³ free vector sector would have
three physical polarizations per adjoint generator. NONE of these
arithmetic equalities implies unbroken gauge fields, 5D action,
physical symmetry breaking, massless spin-1 modes or observed QCD. -/

theorem classicalE8E6SU3AdjointDimension :
    248 = 78 + 8 + 2 * (27 * 3) := by decide

theorem classicalE6TrinificationAdjointDimension :
    78 = 3 * 8 + 2 * 27 := by decide

theorem twoAdditionalSU3FiveDimVectorUnits :
    (2 * 8) * 3 = 48 := by decide

theorem sixDiracQuarksAndThreeVectorOctetsCount :
    6 * 3 * 4 = 3 * 8 * 3 := by decide



/-! 2026-10-24 physical-source BACKWARD consumer.
These Bool values LABEL calculated results in Agda KK #1241's
`check_kk_soft_split_su3_holonomy_maxcut.py`. They do NOT prove
the 5D periodic quantum determinant inside Lean or construct SUSY.
-/

inductive KKPairedColourModel where
  | sixQuarkHyperlikePairs
  | eightWithTwoHeavyFundamentals
  deriving DecidableEq, Repr

def localRadionAndWilsonHessianPositive (_ : KKPairedColourModel) : Bool :=
  true

def fixedRadiusGlobalColourIdentityPreferred : KKPairedColourModel → Bool
  | .sixQuarkHyperlikePairs => false
  | .eightWithTwoHeavyFundamentals => true

theorem localHessianDoesNotDetermineGlobalColourIdentity
    (f : Bool → Bool)
    (h : ∀ model, f (localRadionAndWilsonHessianPositive model) =
      fixedRadiusGlobalColourIdentityPreferred model) : False := by
  have a : f true = false := by
    simpa [localRadionAndWilsonHessianPositive,
      fixedRadiusGlobalColourIdentityPreferred] using
      h KKPairedColourModel.sixQuarkHyperlikePairs
  have b : f true = true := by
    simpa [localRadionAndWilsonHessianPositive,
      fixedRadiusGlobalColourIdentityPreferred] using
      h KKPairedColourModel.eightWithTwoHeavyFundamentals
  cases a.symm.trans b

theorem eightFundamentalFlavoursEven : (6 + 2) % 2 = 0 := by decide

theorem vectorMultipletCasimirCancellation : 3 + 1 = 4 := by decide

theorem hyperMultipletCasimirCancellation : 4 = 2 * 2 := by decide

/-!
External SUSY field-content prior art; eight flavours is necessary for
one simple parity-CS counting condition, not a proof of full 5D
SU3×U1 gauge invariance, chiral EW, full action, or experiment.
-/

end DASHITOE

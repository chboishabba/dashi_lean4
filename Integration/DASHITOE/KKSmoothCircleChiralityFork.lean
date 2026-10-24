import Integration.DASHITOE.KK240RoleDiscrimination

/-!
KK/TOE physical model-selection fork, 2026-10-24.

ORIGINAL EXTERNAL scientific source roots: 5D S1 chirality/index is
standard periodic Dirac physics; original orbifold-anomaly analyses
Arkani-Hamed/Cohen/Georgi 2001 and Scrucca et al. 2002.
Repo source: Agda KK #1241 KKCircleQEDChiralityConsumerExact and
KKSmoothCircleChiralityModelForkExact.

THIS Lean code proves FINITE world/observer non-descents and a finite
truth table. It does NOT formalise the continuum Fredholm index,
orbifold anomaly inflow, an interacting E6 action, or any experiment.
-/

namespace DASHITOE

inductive KKMassAverage where
  | zero | nonzero
  deriving DecidableEq, Repr

inductive KKWilsonTwist where
  | trivial | nontrivial
  deriving DecidableEq, Repr

def smoothS1LeftZero (m : KKMassAverage) (θ : KKWilsonTwist) : Bool :=
  m == .zero && θ == .trivial

def smoothS1RightZero (m : KKMassAverage) (θ : KKWilsonTwist) : Bool :=
  m == .zero && θ == .trivial

theorem finiteS1ZeroModeParity (m : KKMassAverage) (θ : KKWilsonTwist) :
    smoothS1LeftZero m θ = smoothS1RightZero m θ := rfl

inductive KKPhysicalModel where
  | smoothBulk
  | orbifoldBulk
  | chiralFourDBrane
  deriving DecidableEq, Repr

def canSelectUnpairedChiralZero : KKPhysicalModel → Bool
  | .smoothBulk => false
  | .orbifoldBulk => true
  | .chiralFourDBrane => true

def originalSmoothCircleCasimirStillSameObject : KKPhysicalModel → Bool
  | .smoothBulk => true
  | .orbifoldBulk => false
  | .chiralFourDBrane => false

def exactPhysicalStandardModelConstructed : KKPhysicalModel → Bool
  | _ => false

def reusedFull27RepresentationDimension (_ : KKPhysicalModel) : Nat := 27

theorem same27CountCannotDetermineChiralZero
    (readout : Nat → Bool)
    (h : ∀ model, readout (reusedFull27RepresentationDimension model) =
      canSelectUnpairedChiralZero model) : False := by
  have a : readout 27 = false := by
    simpa [reusedFull27RepresentationDimension, canSelectUnpairedChiralZero]
      using h KKPhysicalModel.smoothBulk
  have b : readout 27 = true := by
    simpa [reusedFull27RepresentationDimension, canSelectUnpairedChiralZero]
      using h KKPhysicalModel.orbifoldBulk
  cases a.symm.trans b

theorem same27CountCannotDetermineOriginalCircleCasimir
    (readout : Nat → Bool)
    (h : ∀ model, readout (reusedFull27RepresentationDimension model) =
      originalSmoothCircleCasimirStillSameObject model) : False := by
  have a : readout 27 = true := by
    simpa [reusedFull27RepresentationDimension,
      originalSmoothCircleCasimirStillSameObject]
      using h KKPhysicalModel.smoothBulk
  have b : readout 27 = false := by
    simpa [reusedFull27RepresentationDimension,
      originalSmoothCircleCasimirStillSameObject]
      using h KKPhysicalModel.orbifoldBulk
  cases a.symm.trans b

theorem branchSelectionDoesNotCertifyStandardModel
    (model : KKPhysicalModel) :
    exactPhysicalStandardModelConstructed model = false := by
  cases model <;> rfl


/-! Later source-specific E6-derived SU3^3 orbifold candidate:
P_L=(-,-,+) fixes the original SU2L. The four diagonal SU3R
involutions exhaust the determinant-one order-two choices.
Original loop-anomaly computations are in Agda KK #1241's exact
rational Python. The Boolean outcomes below are FINITE LABELS
of those calculations, not native Lean proofs of QFT anomalies.
-/

inductive KKRightDiagonalParity where
  | identity | minusMinusPlus | minusPlusMinus | plusMinusMinus
  deriving DecidableEq, Repr

def colourCubicAnomalyZero : KKRightDiagonalParity → Bool
  | .identity => false
  | .minusMinusPlus => true
  | .minusPlusMinus => true
  | .plusMinusMinus => true

def uvAbelianCubicAnomalyZero : KKRightDiagonalParity → Bool
  | .identity => true
  | .minusMinusPlus => false
  | .minusPlusMinus => false
  | .plusMinusMinus => false

theorem noDiagonalRightParityRemovesBothSourceAnomalies
    (choice : KKRightDiagonalParity) :
    ¬ (colourCubicAnomalyZero choice = true ∧
       uvAbelianCubicAnomalyZero choice = true) := by
  cases choice <;> decide

theorem firstTitsOrbifoldMatterZeroModes : 6 + 6 + 4 = 16 := by decide

theorem firstTitsOrbifoldVectorlikeAndSinglet :
    3 + 3 + 2 + 2 + 1 = 11 := by decide

theorem fullE6GaugeEvenHasThirtyMoreThanTrinification :
    16 + 30 = 46 := by decide

/-!
Source results: one candidate has IR chiral16 and vectorlike10+1
with vanishing tested SM subgroup anomalies and E32/E33 source
parity, yet BEFORE the VEVs nonzero UV U1L/U1R anomalies. A
constant 5D bulk Dirac mass is odd under gamma5 orbifold reflection.
No full quantum orbifold, global spin CS, SM mass source, one photon,
orbifold Casimir, or physical full-E6 gauge field is certified.
-/


/-!
2026-10-25 GREEN-SCHWARZ physical-source PARITY-GATE follow-on.
The actual original anomaly calculation is in Agda KK #1241's
check_kk_e6_orbifold_gs_anomaly_factor.py. These are FINITE NUMERIC
COEFFICIENT checks and source-outcome labels, not a Lean formal
continuum chiral determinant or a globally quantized WZ functional.
-/
theorem uvCubicFactorLeft : 8 * 5 = 40 := by decide
theorem uvCubicFactorMixed : 8 * 8 = 64 := by decide
theorem uvCubicExpansionMixed : 3 * 8 = 24 := by decide
theorem uvGravFactor : 2 * 8 = 16 := by decide
theorem uvMixedEachFixedPlane : 2 * 1 = 2 := by decide

inductive KKOrbifoldInflowSource where
  | oppositeEndpointBulkCSOnly
  | twoLocalWessZuminoVariations
  deriving DecidableEq, Repr

def localFactorisedAnomalyVariationRepair : KKOrbifoldInflowSource → Bool
  | .oppositeEndpointBulkCSOnly => false
  | .twoLocalWessZuminoVariations => true

def globalSpinQuotientWZCertified (_ : KKOrbifoldInflowSource) : Bool :=
  false

theorem bulkCSOnlyFailsIntegratedAnomaly :
    localFactorisedAnomalyVariationRepair
      .oppositeEndpointBulkCSOnly = false := rfl

theorem localWZAnsatzDoesNotCertifyQuantumGaugeTheory :
    globalSpinQuotientWZCertified
      .twoLocalWessZuminoVariations = false := rfl

-- The SOURCE-SPECIFIC 4x4 neutral Cartan Gram calculation using
-- Phi E32, Chi E33, anomalous GS direction and even Chi E21
-- finds rank 2,2,3, leaving one massless generator Q=T3L+Y.
-- This is a labelled computational consumer, not a mathematical
-- derivation of a scalar E21 VEV from the old E6 positive Hessian.
theorem selectedNeutralMassRanks : (2 : Nat) = 2 ∧
    (2 : Nat) = 2 ∧ (4 : Nat) - 3 = 1 := by decide

-- Existing Chi E33 has charges (+2,-2), so argChi/2 shifts in
-- the required infinitesimal direction but is not clearly
-- 2pi-periodic; conditional mod-2 WZ obstruction remains.
theorem sourceChiAnomalousChargeTwo : (2 : Nat) * 2 = 4 := by decide


/-!
The physically selected S1/Z2 parity allows Phi 4 complex and Chi
5 complex scalar constant modes = 18 real (not full 36 bulk).
Source Hessian from Agda KK #1241 PyTorch: local 18-real even
zero-mode Hessian has 7 gauge zeros + 11 strictly positive values;
the unrestricted 36-real Hessian has two NEGATIVE odd directions.
These numeric signs are SOURCE LABELS only, not Lean real-analysis
eigenvalue proofs. Actual odd 5D KK tower and global gauge/WZ remain OPEN.
-/
theorem orbifoldEvenPhiAndChiRealComponents :
    2 * (4 + 5) = 18 := by decide

theorem sourceSevenGoldstonesElevenPositive :
    7 + 11 = 18 := by decide

theorem parityEvenGaugeBrokenToOnePhoton :
    7 + 1 = 8 := by decide

inductive KKScalarHessianConsumer where
  | full36BulkAtHomogeneousPoint
  | even18FourDimensionalZeroModes
  deriving DecidableEq, Repr

def selectedSourceHasNegativeHessianEigenvalue :
    KKScalarHessianConsumer → Bool
  | .full36BulkAtHomogeneousPoint => true
  | .even18FourDimensionalZeroModes => false

theorem physicalEvenZeroModeHessianSourceHasNoNegative :
    selectedSourceHasNegativeHessianEigenvalue
      .even18FourDimensionalZeroModes = false := rfl

end DASHITOE

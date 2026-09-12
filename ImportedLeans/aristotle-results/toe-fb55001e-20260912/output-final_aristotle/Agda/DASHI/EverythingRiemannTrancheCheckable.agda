module DASHI.EverythingRiemannTrancheCheckable where

-- Toolchain-portable aggregate for the 2026 zeta reflection/Hermitian-defect
-- tranche.  It is exactly `DASHI.EverythingRiemannReflectionOrbitDefect2026`
-- minus `DASHI.Analysis.ZetaTheoremSurface`, whose transitive import
-- `DASHI.Analysis.RiemannPrimePowerArithmetic` needs `Ontology.GodelLattice`,
-- a module that is not present in this source snapshot.  Every module listed
-- here has been machine-checked with a stock Agda + standard library.

-- Focused aggregate root for the 2026 zeta reflection/Hermitian-defect tranche.
-- Analytic calibration: Alpöge--Furman, arXiv:2608.13637 (2026),
-- DOI: 10.48550/arXiv.2608.13637.

import DASHI.Analysis.RiemannReflectionOrbitDefectExact
import DASHI.Analysis.RiemannReflectionPairBlockExact
import DASHI.Analysis.RiemannWeilOffLineHyperbolicBlockExact
import DASHI.Analysis.RiemannComplexPoissonChannelSplitExact
import DASHI.Analysis.RiemannComplexPoissonHermitianReductionExact
import DASHI.Analysis.RiemannComplexPoissonPairEnergyExact
import DASHI.Analysis.RiemannComplexPoissonFiniteRetentionExact
import DASHI.Analysis.RiemannWeilPairKernelFrobeniusExact
import DASHI.Analysis.RiemannMixedKernelEnvelopeExact
import DASHI.Analysis.RiemannMixedChannelAlmostOrthogonalityExact
import DASHI.Analysis.RiemannPrimeSideExcessNormalizationExact
import DASHI.Analysis.RiemannHermitianDefectAssemblyExact
import DASHI.Analysis.RiemannHermitianDetectabilityGapExact
import DASHI.Analysis.RiemannHermitianExcessDetectabilityAssemblyExact
import DASHI.Analysis.RiemannHermitianPowerAmplificationExact
import DASHI.Analysis.RiemannHermitianLocalizationAmplificationExact
import DASHI.Analysis.RiemannArithmeticUnitarityRigidityBoundary
import DASHI.Analysis.RiemannHermitianEndgameTrichotomyExact
import DASHI.Analysis.RiemannHermitianDreamRouteExact
import DASHI.Analysis.RiemannHermitianTopDownAssemblyExact
import DASHI.Analysis.RiemannHermitianSourceGapMapExact
import DASHI.Analysis.RiemannCenteredGridRetentionExact
import DASHI.Analysis.RiemannG3SourceTransportExact
import DASHI.Analysis.RiemannReflectionC3OrbitShapeBridgeExact
import DASHI.Analysis.RiemannReflectionOrbitDefectRegression

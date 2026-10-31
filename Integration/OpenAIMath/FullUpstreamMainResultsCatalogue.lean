import Integration.OpenAIMath.UpstreamPin

/-! # Full upstream declaration inventory (NOT theorem ports)
Generated from openai/math lean/formalization.yaml, blob 372bcd714cd3a186a9139ac8e0f3318961fb2df1.
An upstream `main_results` entry is a declaration reference; it does not
certify an accepted DASHI Lean proof, comparable mathematical statement,
or a same-object Agda bridge. Keep original OpenAI and earlier authors' credit.
No alteration of the original pinned vendor tree. This catalogue may be NEWER
than upstreamCommit, and an audit must flag divergence rather than conflating them.
-/
namespace Integration.OpenAIMath

structure CatalogueDeclaration where
  comparator : String
  declaration : String
  file : String
  deriving Repr, DecidableEq

def fullCatalogueUpstreamBlob : String := "372bcd714cd3a186a9139ac8e0f3318961fb2df1"
def mainResultDeclarations : List CatalogueDeclaration :=
  [
    { comparator := "ComparatorChallenges/AbhyankarSathaye.json", declaration := "OAI.AbhyankarSathaye.exists_noncoordinate_polynomial", file := "OAI/AlgebraicGeometry/AbhyankarSathaye/Counterexample.lean" }
    , { comparator := "ComparatorChallenges/AmplitudeDamping.json", declaration := "OAI.GAD.main", file := "OAI/InformationTheory/AmplitudeDamping/Main.lean" }
    , { comparator := "ComparatorChallenges/ArnoldCounterexample.json", declaration := "OAI.ArnoldCounterexample.main", file := "OAI/Geometry/Arnold/Main.lean" }
    , { comparator := "ComparatorChallenges/ArtinCAT0.json", declaration := "OAI.ArtinCAT0.main", file := "OAI/GroupTheory/ArtinCAT0/Main.lean" }
    , { comparator := "ComparatorChallenges/AsymptoticallyMinimalLittlewood.json", declaration := "OAI.AsymptoticallyMinimalLittlewood.main", file := "OAI/Analysis/Littlewood/Main.lean" }
    , { comparator := "ComparatorChallenges/AuslanderReiten.json", declaration := "OAI.ArExplicit.Statement.main", file := "OAI/Algebra/AuslanderReiten/All.lean" }
    , { comparator := "ComparatorChallenges/BackwardIntertwiners.json", declaration := "OAI.BackwardIntertwiners.direct_algebra_corollary", file := "OAI/Analysis/BackwardIntertwiners/AlgebraCorollary.lean" }
    , { comparator := "ComparatorChallenges/BassTrace.json", declaration := "OAI.BassTrace.RightProjective.bassTraceModules_vanishing_and_support", file := "OAI/RingTheory/BassTrace/Main.lean" }
    , { comparator := "ComparatorChallenges/BiholderTransport.json", declaration := "OAI.WeakMTWTransport.uniform_biHolder_transport", file := "OAI/Analysis/BiholderTransport/Main.lean" }
    , { comparator := "ComparatorChallenges/BinPackingGap.json", declaration := "OAI.BinPackingGap.main_results", file := "OAI/Computability/BinPacking/Main.lean" }
    , { comparator := "ComparatorChallenges/BinaryMatching.json", declaration := "OAI.BinaryMatching.deterministic_approximate_counting", file := "OAI/Computability/MatchingCount/BinarySolve.lean" }
    , { comparator := "ComparatorChallenges/BinarySweep.json", declaration := "OAI.binary_sweep_contraction_and_mixing", file := "OAI/Probability/BinarySweep/Main.lean" }
    , { comparator := "ComparatorChallenges/BipartiteCrossing.json", declaration := "OAI.Zarankiewicz.mainTarget_proof", file := "OAI/Combinatorics/Crossing/Main.lean" }
    , { comparator := "ComparatorChallenges/BorsukNine.json", declaration := "OAI.BorsukNine.main_theorem", file := "OAI/Geometry/Borsuk/Counterexample.lean" }
    , { comparator := "ComparatorChallenges/BoundedRecovery.json", declaration := "OAI.BoundedRecovery.bounded_recovery", file := "OAI/Analysis/ModularRecovery/Recovery.lean" }
    , { comparator := "ComparatorChallenges/BoundedTreePotentials.json", declaration := "OAI.BoundedTreePotentials.TreeCalculus.main_counterexample", file := "OAI/Analysis/TreePotential/Main.lean" }
    , { comparator := "ComparatorChallenges/BoundedTreewidthL1.json", declaration := "OAI.BoundedTreewidthL1.main_theorem", file := "OAI/Combinatorics/TreewidthL1/Main.lean" }
    , { comparator := "ComparatorChallenges/Brennan.json", declaration := "OAI.Brennan.main_theorem", file := "OAI/Analysis/IntegralMeans/Main.lean" }
    , { comparator := "ComparatorChallenges/BrennanSharp.json", declaration := "OAI.Brennan.Sharp.sharp_endpoints", file := "OAI/Analysis/IntegralMeans/SharpEndpoints.lean" }
    , { comparator := "ComparatorChallenges/C0Absorption.json", declaration := "OAI.C0Absorption.main_result", file := "OAI/Analysis/C0Absorption/Main.lean" }
    , { comparator := "ComparatorChallenges/CHObstruction.json", declaration := "OAI.CHObstruction.main", file := "OAI/ModelTheory/Categoricity/Main.lean" }
    , { comparator := "ComparatorChallenges/CartierChartCompactnessSupport.json", declaration := "OAI.CartierSections.isCompact_closedChartFieldRetraction_cone", file := "OAI/AlgebraicGeometry/CartierSections/ChartCompactness.lean" }
    , { comparator := "ComparatorChallenges/CharacterCriterion.json", declaration := "OAI.KirchbergRordam.character_criterion", file := "OAI/Analysis/CharacterCriterion/Main.lean" }
    , { comparator := "ComparatorChallenges/CharacterVarietiesAllSeamsSupport.json", declaration := "OAI.IntegralCharacterVarieties.SurfacePresentation.Diagram.producedMarkedValues_allSeams", file := "OAI/AlgebraicGeometry/CharacterVarieties/Seams/ProducedSolution.lean" }
    , { comparator := "ComparatorChallenges/ChoicelessPolynomialTime.json", declaration := "OAI.CPTSeparation.main", file := "OAI/ModelTheory/Choiceless/Separation.lean" }
    , { comparator := "ComparatorChallenges/CirculantHadamard.json", declaration := "OAI.CirculantHadamard.exists_iff_order_one_or_four", file := "OAI/LinearAlgebra/CirculantHadamard/Main.lean" }
    , { comparator := "ComparatorChallenges/ClassicalON.json", declaration := "OAI.ClassicalON.main", file := "OAI/Probability/ClassicalON/Main.lean" }
    , { comparator := "ComparatorChallenges/CliqueFreeLog.json", declaration := "OAI.CliqueFreeLog.logarithmic_independence_bound", file := "OAI/Combinatorics/CliqueFree/Main.lean" }
    , { comparator := "ComparatorChallenges/CommonBasesFPRAS.json", declaration := "OAI.common_bases_fpras", file := "OAI/Combinatorics/MatroidCounting/CommonBases.lean" }
    , { comparator := "ComparatorChallenges/CommutingDerivations.json", declaration := "OAI.AbhyankarSathaye.CommutingDerivations.commuting_derivations_with_ordinary_extras", file := "OAI/AlgebraicGeometry/CommutingDerivations/OrdinaryExtraMain.lean" }
    , { comparator := "ComparatorChallenges/CompactBanach.json", declaration := "OAI.CompactBanach.main", file := "OAI/Geometry/DoublingHilbert/CompactBanach.lean" }
    , { comparator := "ComparatorChallenges/CompleteCrossing.json", declaration := "OAI.Paper170.complete_graph_crossing_number", file := "OAI/Combinatorics/CompleteCrossing/Main.lean" }
    , { comparator := "ComparatorChallenges/CompleteCrouzeix.json", declaration := "OAI.CompleteCrouzeix.main", file := "OAI/Analysis/NumericalRange/Main.lean" }
    , { comparator := "ComparatorChallenges/ComplexCancellation.json", declaration := "OAI.ComplexCancellation.main", file := "OAI/Algebra/AffineCancellation/Main.lean" }
    , { comparator := "ComparatorChallenges/Conductivity.json", declaration := "OAI.ScalarConductivity.main_nonuniqueness", file := "OAI/Analysis/Conductivity/Main.lean" }
    , { comparator := "ComparatorChallenges/ConjugatePoints.json", declaration := "OAI.ThreeManifold.main_theorem", file := "OAI/Geometry/ConjugatePoints/ThreeManifold.lean" }
    , { comparator := "ComparatorChallenges/ContinuumTransition.json", declaration := "OAI.ContinuumTemperature.main_theorem", file := "OAI/Probability/ContinuumTransition/Main.lean" }
    , { comparator := "ComparatorChallenges/CoordinateSweeps.json", declaration := "OAI.CoordinateSweeps.conditional_main", file := "OAI/Probability/CoordinateSweeps/Main.lean" }
    , { comparator := "ComparatorChallenges/Cotype.json", declaration := "OAI.Cotype.mainTarget_proved", file := "OAI/Analysis/Cotype/Main.lean" }
    , { comparator := "ComparatorChallenges/CoulombIonization.json", declaration := "OAI.CoulombAtom.generalized_ionization", file := "OAI/Analysis/CoulombIonization/Main.lean" }
    , { comparator := "ComparatorChallenges/CourtadeKumar.json", declaration := "OAI.LeanBlast.CourtadeKumar.courtadeKumarAndAttainment", file := "OAI/InformationTheory/BooleanNoise/Main.lean" }
    , { comparator := "ComparatorChallenges/CriticalSK.json", declaration := "OAI.CriticalSK.covariance_and_linear_tests", file := "OAI/MathematicalPhysics/CriticalSK/Rayleigh.lean" }
    , { comparator := "ComparatorChallenges/CriticalSKMixing.json", declaration := "OAI.CriticalSK.critical_mixing_bounds", file := "OAI/MathematicalPhysics/CriticalMixing/Main.lean" }
    , { comparator := "ComparatorChallenges/CriticalZ3.json", declaration := "OAI.CriticalZ3.critical_no_infinite", file := "OAI/Probability/CriticalZ3/Main.lean" }
    , { comparator := "ComparatorChallenges/CycleDecomposition.json", declaration := "OAI.ErdosGallai.erdos_gallai", file := "OAI/Combinatorics/CycleDecomposition/Main.lean" }
    , { comparator := "ComparatorChallenges/DaugavetModuli.json", declaration := "OAI.ExactModuli.exact_example", file := "OAI/Analysis/Daugavet/Main.lean" }
    , { comparator := "ComparatorChallenges/DegreeRigidity.json", declaration := "OAI.TuringRigidity.ManuscriptMain.rigidity", file := "OAI/Computability/DegreeRigidity/Main.lean" }
    , { comparator := "ComparatorChallenges/DeligneDrinfeld.json", declaration := "OAI.DeligneDrinfeld.main", file := "OAI/Algebra/Drinfeld/Completion.lean" }
    , { comparator := "ComparatorChallenges/DepthThree.json", declaration := "OAI.DepthThreeLowerBound.exists_polynomial_time_language_depth_three_lower_bound", file := "OAI/Computability/DepthThree/Main.lean" }
    , { comparator := "ComparatorChallenges/DiamondDistortion.json", declaration := "OAI.DiamondDistortion.headline_all_pairs", file := "OAI/Analysis/DiamondDistortion/Descent.lean" }
    , { comparator := "ComparatorChallenges/DirectCrouzeix.json", declaration := "OAI.DirectCrouzeix.complete_crouzeix", file := "OAI/Analysis/DirectCrouzeix/CompleteBound.lean" }
    , { comparator := "ComparatorChallenges/DirectionalBallisticity.json", declaration := "OAI.DirectionalTransience.directional_transience_implies_ballisticity", file := "OAI/Probability/Ballisticity/Main.lean" }
    , { comparator := "ComparatorChallenges/DirichletSevenEighths.json", declaration := "OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re", file := "OAI/NumberTheory/DirichletL/Nonvanishing.lean" }
    , { comparator := "ComparatorChallenges/DixmierAllDiscrete.json", declaration := "OAI.Dixmier.current_main_theorem", file := "OAI/Analysis/Unitarizability/AllDiscrete.lean" }
    , { comparator := "ComparatorChallenges/DoublingHilbert.json", declaration := "OAI.DoublingHilbert.main", file := "OAI/Geometry/DoublingHilbert/Main.lean" }
    , { comparator := "ComparatorChallenges/EgyptianFractions.json", declaration := "OAI.Problem337.main_double_log_order", file := "OAI/NumberTheory/EgyptianFractions/Main.lean" }
    , { comparator := "ComparatorChallenges/EgyptianFractions.json", declaration := "OAI.Problem337.counting_double_log_order", file := "OAI/NumberTheory/EgyptianFractions/Main.lean" }
    , { comparator := "ComparatorChallenges/EgyptianFractions.json", declaration := "OAI.Problem337.prescribed_denominator_corollary", file := "OAI/NumberTheory/EgyptianFractions/Main.lean" }
    , { comparator := "ComparatorChallenges/EntangledGames.json", declaration := "OAI.ThresholdParallelRepetition.threshold_parallel_repetition", file := "OAI/Probability/EntangledGames/Main.lean" }
    , { comparator := "ComparatorChallenges/EuclideanFiveColor.json", declaration := "OAI.EuclideanFiveColor.no_proper_five_coloring", file := "OAI/Geometry/PlaneColoring/Five.lean" }
    , { comparator := "ComparatorChallenges/EuclideanRamsey.json", declaration := "OAI.EuclideanRamsey.classification", file := "OAI/Combinatorics/EuclideanRamsey/Main.lean" }
    , { comparator := "ComparatorChallenges/ExactFourier.json", declaration := "OAI.ExactFourier.main_theorem", file := "OAI/Computability/FourierCircuit/Main.lean" }
    , { comparator := "ComparatorChallenges/FactorGeneration.json", declaration := "OAI.Generator.single_generation_of_II1_separable_predual", file := "OAI/Analysis/FactorGeneration/Main.lean" }
    , { comparator := "ComparatorChallenges/FinitisticAsymmetry.json", declaration := "OAI.LittleFinitistic.extreme_left_right_asymmetry", file := "OAI/Algebra/FinitisticAsymmetry/Main.lean" }
    , { comparator := "ComparatorChallenges/ForestSpace.json", declaration := "OAI.ForestSpace.main_theorem", file := "OAI/Analysis/ForestSpace/Main.lean" }
    , { comparator := "ComparatorChallenges/FoulkesHowe.json", declaration := "OAI.Problem346.canonical_foulkes_howe_surjective", file := "OAI/RepresentationTheory/FoulkesHowe/Stabilization.lean" }
    , { comparator := "ComparatorChallenges/FourierLLogL.json", declaration := "OAI.FourierLLogL.paperMain", file := "OAI/Analysis/FourierLLogL/PaperMain.lean" }
    , { comparator := "ComparatorChallenges/FreeIsing.json", declaration := "OAI.Problem367.free_ising_factor_iff_threshold", file := "OAI/Probability/FreeIsing/Main.lean" }
    , { comparator := "ComparatorChallenges/GaussianMoat.json", declaration := "OAI.GaussianMoat.fullMain", file := "OAI/NumberTheory/GaussianMoat/Main.lean" }
    , { comparator := "ComparatorChallenges/GaussianPropeller.json", declaration := "OAI.GaussianPropeller.all_partitions", file := "OAI/Probability/GaussianPropeller/Main.lean" }
    , { comparator := "ComparatorChallenges/GaussianReplacement.json", declaration := "OAI.CurrentProjection.hybridBlockMain", file := "OAI/Probability/GaussianReplacement/Hybrid.lean" }
    , { comparator := "ComparatorChallenges/GaussianReplacement.json", declaration := "OAI.CurrentProjection.fiberBlockMain", file := "OAI/Probability/GaussianReplacement/FiberBlock.lean" }
    , { comparator := "ComparatorChallenges/GotsmanLinial.json", declaration := "OAI.LeanBlast.GotsmanLinial.gotsmanLinialStatement", file := "OAI/Combinatorics/GotsmanLinial/Main.lean" }
    , { comparator := "ComparatorChallenges/GrahamSpherical.json", declaration := "OAI.GrahamSpherical.full_main", file := "OAI/Combinatorics/SphericalRamsey/Main.lean" }
    , { comparator := "ComparatorChallenges/GrothendieckElementaryExpansion.json", declaration := "OAI.Grothendieck.elementary_expansion", file := "OAI/CategoryTheory/Globular/ElementaryExpansion.lean" }
    , { comparator := "ComparatorChallenges/GroupRingDeterminant.json", declaration := "OAI.GroupRingDeterminant.main", file := "OAI/Analysis/GroupDeterminants/Main.lean" }
    , { comparator := "ComparatorChallenges/HadwigerCounterexample.json", declaration := "OAI.HadwigerCounterexample.not_hadwiger_conjecture", file := "OAI/Combinatorics/HadwigerCounterexample/Main.lean" }
    , { comparator := "ComparatorChallenges/HarmonicArtin.json", declaration := "OAI.HarmonicArtin.salvetti_cover_contractible", file := "OAI/Topology/ArtinGroups/Realizations/SalvettiCoverContractible.lean" }
    , { comparator := "ComparatorChallenges/HarmonicGrowth.json", declaration := "OAI.HarmonicCounterexample.main", file := "OAI/Geometry/HarmonicGrowth/Main.lean" }
    , { comparator := "ComparatorChallenges/HeckeSevenEighths.json", declaration := "OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re", file := "OAI/NumberTheory/DirichletL/Hecke/Nonvanishing.lean" }
    , { comparator := "ComparatorChallenges/HenonEmden.json", declaration := "OAI.HenonLaneEmden.main_nonexistence", file := "OAI/Analysis/HenonEmden/Main.lean" }
    , { comparator := "ComparatorChallenges/HodgeConjectureCMAbelianVarieties/main.json", declaration := "HodgeCM.hodge_conjecture_for_cm_abelian_varieties", file := "ComparatorChallenges/HodgeConjectureCMAbelianVarieties/Solution.lean" }
    , { comparator := "ComparatorChallenges/HoneycombBridgeMassSupport.json", declaration := "OAI.CriticalHoneycomb.finiteBridgeMassEstimate", file := "OAI/Combinatorics/HoneycombChords/BridgeMass.lean" }
    , { comparator := "ComparatorChallenges/HyperbolicCones.json", declaration := "OAI.Paper256.main_result", file := "OAI/Analysis/HyperbolicCones/Main.lean" }
    , { comparator := "ComparatorChallenges/HyperbolicObstruction.json", declaration := "OAI.HyperbolicObstruction.main", file := "OAI/Geometry/HyperbolicGroups/Main.lean" }
    , { comparator := "ComparatorChallenges/IndependentProducts.json", declaration := "OAI.IndependentProducts.main_general", file := "OAI/Analysis/ProductSpaces/WeakNullity.lean" }
    , { comparator := "ComparatorChallenges/IndependentProducts.json", declaration := "OAI.IndependentProducts.main_exponential", file := "OAI/Analysis/ProductSpaces/Main.lean" }
    , { comparator := "ComparatorChallenges/IndependentSets.json", declaration := "OAI.LargeIndependentSets.mainTheoremReal", file := "OAI/Combinatorics/IndependentSets/Main.lean" }
    , { comparator := "ComparatorChallenges/InfiniteMatroid.json", declaration := "OAI.InfiniteMatroidCounterexample.main", file := "OAI/Combinatorics/InfiniteMatroid/Main.lean" }
    , { comparator := "ComparatorChallenges/IsometricImmersion.json", declaration := "OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion", file := "OAI/Geometry/IsometricImmersion/Main.lean" }
    , { comparator := "ComparatorChallenges/Jacobsthal.json", declaration := "OAI.Erdos970.Erdos970Final.erdos_970_quadratic", file := "OAI/NumberTheory/Jacobsthal/Conclusions/QuadraticBound.lean" }
    , { comparator := "ComparatorChallenges/KMedianRecovery.json", declaration := "OAI.MetricKMedianRecovery.global_application", file := "OAI/Combinatorics/KMedianRecovery/Main.lean" }
    , { comparator := "ComparatorChallenges/KahlerSplitting.json", declaration := "OAI.UniversalCoverSplitting.main", file := "OAI/Geometry/KahlerSplitting/Main.lean" }
    , { comparator := "ComparatorChallenges/KaplanskyFinitelyPresented.json", declaration := "OAI.KaplanskyCounterexample.finitelyPresented_counterexample", file := "OAI/RingTheory/DirectFiniteness/FinitelyPresented.lean" }
    , { comparator := "ComparatorChallenges/KaplanskyQuasitrace.json", declaration := "OAI.Kaplansky.kaplansky_quasitrace_counterexample", file := "OAI/Analysis/Kaplansky/Main.lean" }
    , { comparator := "ComparatorChallenges/LocalSmoothing.json", declaration := "OAI.Analysis.Fourier.LocalSmoothing.Comparator.euclidean_local_smoothing", file := "OAI/Analysis/Fourier/LocalSmoothing/Comparator.lean" }
    , { comparator := "ComparatorChallenges/LocalSmoothing.json", declaration := "OAI.Analysis.Fourier.LocalSmoothing.Comparator.bochner_riesz", file := "OAI/Analysis/Fourier/LocalSmoothing/Comparator.lean" }
    , { comparator := "ComparatorChallenges/LocalSmoothing.json", declaration := "OAI.Analysis.Fourier.LocalSmoothing.Comparator.spherical_restriction", file := "OAI/Analysis/Fourier/LocalSmoothing/Comparator.lean" }
    , { comparator := "ComparatorChallenges/LocalSmoothing.json", declaration := "OAI.Analysis.Fourier.LocalSmoothing.Comparator.kakeya_maximal", file := "OAI/Analysis/Fourier/LocalSmoothing/Comparator.lean" }
    , { comparator := "ComparatorChallenges/LocalSmoothing.json", declaration := "OAI.Analysis.Fourier.LocalSmoothing.Comparator.kakeya", file := "OAI/Analysis/Fourier/LocalSmoothing/Comparator.lean" }
    , { comparator := "ComparatorChallenges/LocalSmoothing.json", declaration := "OAI.Analysis.Fourier.LocalSmoothing.Comparator.stein_square", file := "OAI/Analysis/Fourier/LocalSmoothing/Comparator.lean" }
    , { comparator := "ComparatorChallenges/Laughlin.json", declaration := "OAI.Laughlin.mainTarget_proved", file := "OAI/Analysis/Laughlin/Main.lean" }
    , { comparator := "ComparatorChallenges/LiebThirring.json", declaration := "OAI.SharpLiebThirring.sharp_lieb_thirring", file := "OAI/Analysis/LiebThirring/Main.lean" }
    , { comparator := "ComparatorChallenges/LipschitzEquivalence.json", declaration := "OAI.LipschitzCounterexample.main", file := "OAI/Analysis/LipschitzEquivalence/Main.lean" }
    , { comparator := "ComparatorChallenges/LittleFinitistic.json", declaration := "OAI.LittleFinitistic.Main.exists_counterexample", file := "OAI/Algebra/Finitistic/Main.lean" }
    , { comparator := "ComparatorChallenges/LogBrunnMinkowski.json", declaration := "OAI.LogBrunnMinkowski.main", file := "OAI/Geometry/LogVolume/BrunnMinkowski.lean" }
    , { comparator := "ComparatorChallenges/LogConcaveQuery.json", declaration := "OAI.LogConcaveSampling.exact_source_main", file := "OAI/Probability/LogConcave/Main.lean" }
    , { comparator := "ComparatorChallenges/LogspaceEquality.json", declaration := "OAI.ExactDerandomization.exact_logarithmic_space_derandomization", file := "OAI/Computability/Logspace/Equality.lean" }
    , { comparator := "ComparatorChallenges/MahlerConjecture.json", declaration := "OAI.SymmetricMahler.symmetric_mahler", file := "OAI/Analysis/Mahler/MainTheorem.lean" }
    , { comparator := "ComparatorChallenges/MarkovType.json", declaration := "OAI.MarkovSuperreflexivity.hasNontrivialMarkovType_iff_hasEquivalentUCNorm", file := "OAI/Analysis/MarkovType/Main.lean" }
    , { comparator := "ComparatorChallenges/MatchingEntropy.json", declaration := "OAI.MatchingEntropy.entropy_main", file := "OAI/Combinatorics/PerfectMatching/Main.lean" }
    , { comparator := "ComparatorChallenges/MatrixFields.json", declaration := "OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant", file := "OAI/LinearAlgebra/MatrixFields/Conclusions/AllFieldsBound.lean" }
    , { comparator := "ComparatorChallenges/MatrixMultiplication.json", declaration := "OAI.MatrixMultiplication.complex_omega_le_nine_quarters", file := "OAI/LinearAlgebra/MatrixMultiplication/Main.lean" }
    , { comparator := "ComparatorChallenges/MatrixMultiplication.json", declaration := "OAI.MatrixMultiplication.complex_alpha_gt_93_div_200", file := "OAI/LinearAlgebra/MatrixMultiplication/Main.lean" }
    , { comparator := "ComparatorChallenges/MatrixMultiplication.json", declaration := "OAI.MatrixMultiplication.complex_rectangular_omega_lt_523_div_250", file := "OAI/LinearAlgebra/MatrixMultiplication/Main.lean" }
    , { comparator := "ComparatorChallenges/MatrixRemoval.json", declaration := "OAI.Problem348.no_polynomial_removal_bound", file := "OAI/Combinatorics/MatrixRemoval/Main.lean" }
    , { comparator := "ComparatorChallenges/MaximalSeshadriConstants.json", declaration := "OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants", file := "OAI/AlgebraicGeometry/Seshadri/Main.lean" }
    , { comparator := "ComparatorChallenges/MemoryPrecision.json", declaration := "OAI.MemoryPrecision.main", file := "OAI/Probability/MemoryPrecision/Main.lean" }
    , { comparator := "ComparatorChallenges/MetricEntropyDuality.json", declaration := "OAI.MetricEntropyDuality.exists_entropy_duality_counterexample_with_covers", file := "OAI/Analysis/MetricEntropy/Main.lean" }
    , { comparator := "ComparatorChallenges/MidpointLenses.json", declaration := "OAI.SegmentLenses.midpoint_lens_main", file := "OAI/Analysis/SegmentLenses/Main.lean" }
    , { comparator := "ComparatorChallenges/Nagata.json", declaration := "OAI.Nagata.nagata_conjecture", file := "OAI/AlgebraicGeometry/PlaneCurves/Nagata.lean" }
    , { comparator := "ComparatorChallenges/OddKaplansky.json", declaration := "OAI.OddKaplansky.main_theorem", file := "OAI/Algebra/OddKaplansky/Main.lean" }
    , { comparator := "ComparatorChallenges/OneTapeSpace.json", declaration := "OAI.Fifths.Single.capped", file := "OAI/Computability/SpaceSimulation/Main.lean" }
    , { comparator := "ComparatorChallenges/OneTapeSpace.json", declaration := "OAI.Fifths.Single.unknown", file := "OAI/Computability/SpaceSimulation/Main.lean" }
    , { comparator := "ComparatorChallenges/OneWayLiveness.json", declaration := "OAI.OneWayLiveness.main_theorem", file := "OAI/Combinatorics/Automata/Main.lean" }
    , { comparator := "ComparatorChallenges/OptimalMaxCut.json", declaration := "OAI.OptimalMaxCut.main", file := "OAI/Computability/MaxCut/Main.lean" }
    , { comparator := "ComparatorChallenges/PartitionPrinciple.json", declaration := "OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice", file := "OAI/SetTheory/PartitionPrinciple/Models/Separation.lean" }
    , { comparator := "ComparatorChallenges/PerfectCompleteness.json", declaration := "OAI.PerfectCompleteness.Theorem11.exists_reduction", file := "OAI/Computability/PerfectCompleteness/Theorem11.lean" }
    , { comparator := "ComparatorChallenges/PeriodicTilingThree.json", declaration := "OAI.PeriodicTilingThree.periodic_tiling_counterexample_and_minimality", file := "OAI/Geometry/PeriodicTiling/Counterexample.lean" }
    , { comparator := "ComparatorChallenges/PettyProjectionVolume.json", declaration := "OAI.PettyProjection.petty_projection_volume", file := "OAI/Geometry/ProjectionBodies/Main.lean" }
    , { comparator := "ComparatorChallenges/PinchedKahler.json", declaration := "OAI.PinchedHartogs.main_theorem", file := "OAI/Geometry/Kahler/Main.lean" }
    , { comparator := "ComparatorChallenges/PinnedDistances.json", declaration := "OAI.WeakPinned.main", file := "OAI/Geometry/PinnedDistances/Main.lean" }
    , { comparator := "ComparatorChallenges/PlanarFalconer.json", declaration := "OAI.PlanarFalconer.mainTarget_proved", file := "OAI/MeasureTheory/Falconer/Main.lean" }
    , { comparator := "ComparatorChallenges/PlanarFirstPassage.json", declaration := "OAI.PlanarFPP.manuscriptMain", file := "OAI/Probability/FirstPassage/BoundaryCurve.lean" }
    , { comparator := "ComparatorChallenges/PlanarL1.json", declaration := "OAI.PlanarL1.planar_graph_metrics_embed_L1", file := "OAI/Combinatorics/PlanarL1/Embedding.lean" }
    , { comparator := "ComparatorChallenges/PlaneColoring.json", declaration := "OAI.Problem160.properColoring_seven", file := "OAI/Geometry/PlaneColoring/Seven.lean" }
    , { comparator := "ComparatorChallenges/PosteriorReplicas.json", declaration := "OAI.PosteriorReplicas.source_main", file := "OAI/Probability/PosteriorReplicas/Main.lean" }
    , { comparator := "ComparatorChallenges/PowerFreeValues.json", declaration := "OAI.QuarticPowerFree.allDegrees", file := "OAI/NumberTheory/PowerFree/Main.lean" }
    , { comparator := "ComparatorChallenges/ProjectionCounterexample.json", declaration := "OAI.ProjectionCounterexample.universal_simplex_upper_bound_false", file := "OAI/Geometry/ProjectionBody/Counterexample.lean" }
    , { comparator := "ComparatorChallenges/ProjectionMoments.json", declaration := "OAI.ProjectionMoments.main", file := "OAI/Probability/ProjectionMoments/Main.lean" }
    , { comparator := "ComparatorChallenges/ProjectionVolume.json", declaration := "OAI.Paper092.product_counterexample", file := "OAI/Geometry/ProjectionVolume/ProductCounterexample.lean" }
    , { comparator := "ComparatorChallenges/QACParity.json", declaration := "OAI.QAC.parity_lower_bound", file := "OAI/InformationTheory/QuantumCircuit/Parity.lean" }
    , { comparator := "ComparatorChallenges/QuadricBundles.json", declaration := "OAI.QuadricCounterexample.main_theorem", file := "OAI/Geometry/QuadricBundles/Main.lean" }
    , { comparator := "ComparatorChallenges/QuantitativeVanDerWaerden.json", declaration := "OAI.QuantitativeVanDerWaerden.uniform_lower_bound", file := "OAI/Combinatorics/ProgressionColoring/Main.lean" }
    , { comparator := "ComparatorChallenges/QuasiRiemannHypothesis.json", declaration := "OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re", file := "OAI/NumberTheory/DirichletL/Nonvanishing.lean" }
    , { comparator := "ComparatorChallenges/QuinticLienard.json", declaration := "OAI.QuinticLienard.main", file := "OAI/Analysis/LienardCycles/Main.lean" }
    , { comparator := "ComparatorChallenges/RadialTransition.json", declaration := "OAI.RadialTransition.main", file := "OAI/Probability/RadialTransition/Main.lean" }
    , { comparator := "ComparatorChallenges/RandomizedMeanPayoff.json", declaration := "OAI.randomized_quasipolynomial_mean_payoff", file := "OAI/Computability/RandomMean/Main.lean" }
    , { comparator := "ComparatorChallenges/RationalHitting.json", declaration := "OAI.RationalHitting.main", file := "OAI/Computability/RationalHitting/Main.lean" }
    , { comparator := "ComparatorChallenges/RecursivePotentials.json", declaration := "OAI.ComparatorModel.RecursivePotentials.main", file := "OAI/Analysis/RecursivePotentials/Challenge.lean" }
    , { comparator := "ComparatorChallenges/ReflexiveFixedPoints.json", declaration := "OAI.ReflexiveFixedPoints.exists_fixedPoint_of_canonicallyReflexive", file := "OAI/Analysis/Nonexpansive/Main.lean" }
    , { comparator := "ComparatorChallenges/RegularParity.json", declaration := "OAI.QAC.parity_lower_bound_polynomial_size", file := "OAI/InformationTheory/QuantumCircuit/Main.lean" }
    , { comparator := "ComparatorChallenges/RieszQuantitative.json", declaration := "OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability", file := "OAI/Analysis/RieszRectifiability/Uniformity/Rectifiability.lean" }
    , { comparator := "ComparatorChallenges/RyserCovering.json", declaration := "OAI.RyserCoveringCounterexample.exists_prime_eventually_counterexampleRank", file := "OAI/Combinatorics/Ryser/Construction/Main.lean" }
    , { comparator := "ComparatorChallenges/RyserOddExtensions.json", declaration := "OAI.RyserOdd.eventualOddFailures_and_infinite", file := "OAI/Combinatorics/Ryser/OddExtensions.lean" }
    , { comparator := "ComparatorChallenges/Saxl.json", declaration := "OAI.Saxl.saxl_conjecture", file := "OAI/RepresentationTheory/Saxl/Main.lean" }
    , { comparator := "ComparatorChallenges/SecondKahnKalai.json", declaration := "OAI.LeanBlast.SecondKahnKalai.secondKahnKalaiBounds", file := "OAI/Combinatorics/GraphThreshold/Main.lean" }
    , { comparator := "ComparatorChallenges/SelfSimilar.json", declaration := "OAI.EntropyRateDimension.entropy_rate_dimension", file := "OAI/MeasureTheory/SelfSimilar/Main.lean" }
    , { comparator := "ComparatorChallenges/SensitivitySeparation.json", declaration := "OAI.Paper320.quantitative_separation", file := "OAI/Combinatorics/Sensitivity/Separation.lean" }
    , { comparator := "ComparatorChallenges/SeymourSecondNeighborhood.json", declaration := "OAI.SeymourSecondNeighborhood.exists_goodVertex", file := "OAI/Combinatorics/SecondNeighborhood/Main.lean" }
    , { comparator := "ComparatorChallenges/SiegelZeros.json", declaration := "OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap", file := "OAI/NumberTheory/SiegelZeros/Conclusions/Theorem.lean" }
    , { comparator := "ComparatorChallenges/SignedFiniteBand.json", declaration := "OAI.SignedDisk.CenteredDiskEndpoint.main_signed_finite_band", file := "OAI/Analysis/SignedDisk/Main.lean" }
    , { comparator := "ComparatorChallenges/SimpleAmenable.json", declaration := "OAI.SimpleAmenable.main", file := "OAI/GroupTheory/SimpleAmenable/Main.lean" }
    , { comparator := "ComparatorChallenges/SingleFold.json", declaration := "OAI.SingleFold.main", file := "OAI/NumberTheory/SingleFold/Main.lean" }
    , { comparator := "ComparatorChallenges/SingleLatticeCovering.json", declaration := "OAI.SingleLatticeCovering.single_lattice_covering", file := "OAI/Geometry/LatticeCovering/Main.lean" }
    , { comparator := "ComparatorChallenges/SingletonLoopMatching.json", declaration := "OAI.LoopMatching.fullEndpoint", file := "OAI/Computability/LoopMatching/Main.lean" }
    , { comparator := "ComparatorChallenges/SmoothYau.json", declaration := "OAI.YauCounterexamples.sphere_three", file := "OAI/Geometry/SmoothYau/SphereMetric/ThreeSphere.lean" }
    , { comparator := "ComparatorChallenges/SmoothYau.json", declaration := "OAI.YauCounterexamples.sphere_two_torus_two", file := "OAI/Geometry/SmoothYau/ProductMetric/SphereProduct.lean" }
    , { comparator := "ComparatorChallenges/StableCoordinateFour.json", declaration := "OAI.StableCoordinate.principal_package", file := "OAI/AlgebraicGeometry/StableCoordinate/Principal.lean" }
    , { comparator := "ComparatorChallenges/SteinitzBergstrom.json", declaration := "OAI.EuclideanSteinitzBergstrom.main", file := "OAI/Analysis/Steinitz/Main.lean" }
    , { comparator := "ComparatorChallenges/StrictMeans.json", declaration := "OAI.StrictInverseFirstPower.main", file := "OAI/Analysis/StrictMeans/Main.lean" }
    , { comparator := "ComparatorChallenges/StrongThinTree.json", declaration := "OAI.StrongThinTree.strongThinTree", file := "OAI/Combinatorics/ThinTrees/Main.lean" }
    , { comparator := "ComparatorChallenges/StructuralCrouzeix.json", declaration := "OAI.StructuralCrouzeixReference.challenge", file := "OAI/Analysis/StructuralCrouzeix/Endpoint.lean" }
    , { comparator := "ComparatorChallenges/SubexponentialSAT.json", declaration := "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat", file := "OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean" }
    , { comparator := "ComparatorChallenges/SubpolynomialLp.json", declaration := "OAI.SubpolynomialLp.source_main", file := "OAI/Analysis/LpDimension/Main.lean" }
    , { comparator := "ComparatorChallenges/SubsphereCurrent.json", declaration := "OAI.SubsphereCurrent.full_current_main_scope", file := "OAI/Probability/Subsphere/Main.lean" }
    , { comparator := "ComparatorChallenges/Superstring.json", declaration := "OAI.Superstring.main", file := "OAI/Computability/Superstring/Main.lean" }
    , { comparator := "ComparatorChallenges/SurfaceConeCandidateSupport.json", declaration := "OAI.SmallCM.candidate_ring_properties", file := "OAI/AlgebraicGeometry/SurfaceCones/CandidateRing.lean" }
    , { comparator := "ComparatorChallenges/SymmetricDomains.json", declaration := "OAI.Release061.main", file := "OAI/Analysis/SymmetricDomains/Main.lean" }
    , { comparator := "ComparatorChallenges/SymmetricMahlerEquality.json", declaration := "OAI.SymmetricMahler.symmetric_mahler_equality", file := "OAI/Analysis/Mahler/Classification.lean" }
    , { comparator := "ComparatorChallenges/SymmetricPolar.json", declaration := "OAI.SymmetricPolar.symmetric_polar_main", file := "OAI/Geometry/PolarProducts/Main.lean" }
    , { comparator := "ComparatorChallenges/Tachikawa.json", declaration := "OAI.Tachikawa.main_theorem", file := "OAI/RingTheory/Tachikawa/Counterexample.lean" }
    , { comparator := "ComparatorChallenges/TalagrandDiscreteConvexity.json", declaration := "OAI.TalagrandDiscreteConvexity.talagrand_discrete_convexity", file := "OAI/Combinatorics/DiscreteConvexity/Main.lean" }
    , { comparator := "ComparatorChallenges/TalagrandExpectationThreshold.json", declaration := "OAI.TalagrandThreshold.talagrand_expectation_threshold_equivalence", file := "OAI/Combinatorics/ExpectationThreshold/Main.lean" }
    , { comparator := "ComparatorChallenges/TamingCompatibility.json", declaration := "OAI.TamingCompatibility.taming_implies_compatibility", file := "OAI/Geometry/TamingCompatibility/Main.lean" }
    , { comparator := "ComparatorChallenges/ThompsonNonamenability.json", declaration := "OAI.ThompsonNonamenability.thompson_F_nonamenable_composition", file := "OAI/GroupTheory/Thompson/Main.lean" }
    , { comparator := "ComparatorChallenges/ThorpRouting.json", declaration := "OAI.ThorpNine.main", file := "OAI/Probability/ThorpRouting/Main.lean" }
    , { comparator := "ComparatorChallenges/ThorpWeightedCompatibility.json", declaration := "OAI.ThorpCompatibility.weightedCompatibility_main", file := "OAI/Probability/ThorpCompatibility/Main.lean" }
    , { comparator := "ComparatorChallenges/TingleySphereIsometry.json", declaration := "OAI.Tingley.tingley_sphere_isometry_full", file := "OAI/Analysis/SphereIsometry/Extension.lean" }
    , { comparator := "ComparatorChallenges/TorsionFreeHyperbolic.json", declaration := "OAI.Release075.main", file := "OAI/GroupTheory/Hyperbolic/Main.lean" }
    , { comparator := "ComparatorChallenges/TorsionFreeZeroDivisors.json", declaration := "OAI.TorsionFreeZeroDivisors.main", file := "OAI/Algebra/GroupRing/Main.lean" }
    , { comparator := "ComparatorChallenges/TraceIdealTransportSupport.json", declaration := "OAI.TraceConeClassification.TraceConeEquiv.idealOrderIso_finIdeal", file := "OAI/Analysis/TraceCone/IdealTransport.lean" }
    , { comparator := "ComparatorChallenges/TraceIdealTransportSupport.json", declaration := "OAI.TraceConeClassification.TraceConeEquiv.idealOrderIso_zeroIdeal", file := "OAI/Analysis/TraceCone/IdealTransport.lean" }
    , { comparator := "ComparatorChallenges/TraceIdealTransportSupport.json", declaration := "OAI.TraceConeClassification.closed_ideal_weight_exists", file := "OAI/Analysis/TraceCone/FiniteIdeal.lean" }
    , { comparator := "ComparatorChallenges/TriangularHilbert.json", declaration := "OAI.TriangularHilbert.main_estimate", file := "OAI/Analysis/TriangularHilbert/Main.lean" }
    , { comparator := "ComparatorChallenges/TwoWayComplementation.json", declaration := "OAI.TwoWayComplementation.complementation_lower_bound_finite", file := "OAI/Combinatorics/TwoWayAutomata/Main.lean" }
    , { comparator := "ComparatorChallenges/TwoWayDeterminization.json", declaration := "OAI.TwoWayComplementation.explicit_family_main", file := "OAI/Combinatorics/TwoWayAutomata/ExplicitFamily.lean" }
    , { comparator := "ComparatorChallenges/UniformFourier.json", declaration := "OAI.PowerSaving.transform_main", file := "OAI/Computability/FourierTransform/Main.lean" }
    , { comparator := "ComparatorChallenges/UniformFourier.json", declaration := "OAI.PowerSaving.convolution_main", file := "OAI/Computability/FourierTransform/Main.lean" }
    , { comparator := "ComparatorChallenges/UniformGamma.json", declaration := "OAI.ComparatorModel.CurrentMain.main", file := "OAI/Analysis/TracialSplitting/Challenge.lean" }
    , { comparator := "ComparatorChallenges/UniformSparsestCut.json", declaration := "OAI.UniformSparsestCut.mainGap", file := "OAI/Combinatorics/SparsestCut/Main.lean" }
    , { comparator := "ComparatorChallenges/UniqueGamesTheorem.json", declaration := "OAI.UniqueGamesTheorem.theorem11", file := "OAI/Computability/UniqueGames/Theorem.lean" }
    , { comparator := "ComparatorChallenges/UniversalFInfinity.json", declaration := "OAI.UniversalFInfinity.universal_group_of_type_FInfinity", file := "OAI/GroupTheory/UniversalGroup/Main.lean" }
    , { comparator := "ComparatorChallenges/VertexCover.json", declaration := "OAI.VertexCover.every_fixed_factor_below_two", file := "OAI/Computability/VertexCover/Main.lean" }
    , { comparator := "ComparatorChallenges/VlasovMaxwell.json", declaration := "OAI.RVM.global_classical_solution", file := "OAI/Analysis/VlasovMaxwell/Main.lean" }
    , { comparator := "ComparatorChallenges/WeakHessian.json", declaration := "OAI.WeakHessian.every_geodesic", file := "OAI/Geometry/WeakHessian/Main.lean" }
    , { comparator := "ComparatorChallenges/WeakMTWGlobalSupport.json", declaration := "OAI.WeakMTWGlobalSupport.current_main_convexity", file := "OAI/Geometry/WeakMTW/Convexity.lean" }
    , { comparator := "ComparatorChallenges/YauCounterexample.json", declaration := "OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample", file := "OAI/Geometry/NodalSets/Main.lean" }
  ]

theorem catalogueEntryCount : mainResultDeclarations.length = 208 := by decide

/-- This inventory has *zero* evidence of same-object DASHI imports. -/
def allCatalogueDeclarationsImportedIntoDASHI : Bool := false
/-- Status `partial progress` is copied from upstream's own YAML. -/
def upstreamCatalogueScope : String := "Partial progress"

end Integration.OpenAIMath

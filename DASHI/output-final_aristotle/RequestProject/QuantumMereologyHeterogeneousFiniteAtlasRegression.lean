import RequestProject.QuantumMereologyHeterogeneousFiniteAtlas

namespace QuantumMereology
namespace HeterogeneousFiniteAtlasRegression

example :
    HeterogeneousFiniteAtlas.canonicalBoundary.canonicalPairChartExists = true :=
  HeterogeneousFiniteAtlas.canonical_pair_chart_exists

example :
    HeterogeneousFiniteAtlas.canonicalBoundary.everyPairMarginalComesFromSameGlobalState = true :=
  HeterogeneousFiniteAtlas.every_pair_marginal_comes_from_same_global_state

example :
    HeterogeneousFiniteAtlas.canonicalBoundary.arbitraryHilbertTPSAutomaticallyCoordinates = false :=
  HeterogeneousFiniteAtlas.arbitrary_hilbert_tps_does_not_automatically_coordinate

example :
    HeterogeneousFiniteAtlas.canonicalBoundary.fullSubsetMarginalPresheafPaid = false :=
  HeterogeneousFiniteAtlas.full_subset_marginal_presheaf_not_yet_paid

end HeterogeneousFiniteAtlasRegression
end QuantumMereology

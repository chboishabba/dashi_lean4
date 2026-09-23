# The one-sided geometry payment (`B3`), in Lean

This note records exactly what was added to the Lean lane in this round and what it does
and does not settle.  Everything below builds with `lake build` end to end, contains no
`sorry`, `axiom` or placeholder, and every headline theorem is followed in its own file
by `#print axioms`, all of which report only `propext`, `Classical.choice`, `Quot.sound`.

The target was item `B3` of the Goal-1 backlog — *one-sided geometry: Euclidean time is
bounded by the selected support separation; the connected component's path length is
bounded by the source distance `d_k(Y)`* — together with its consequences for the finite
covariance estimate and the mass-gap chain.

## What is now a theorem

### The connected-core path geometry

`RequestProject/YangMills/Cluster/DomainPathDistance.lean`

* `dist_succ_le_card_of_domainConnected` — in a domain-connected localization domain `Y`
  containing both source marks, `dist(a, b) + 1 ≤ #Y`.  The proof bypasses an internal
  walk to a path, whose support is duplicate free and contained in `Y`.  This is the
  `Y₀`-path half of `B3`: the mark separation never exceeds the domain tree distance
  `d_k(Y) = #Y − 1`.
* `pow_card_le_pow_dist` — the form in which it is consumed: a geometric weight at
  `d_k(Y)` dominates the same weight at the mark separation, so a per-domain estimate in
  the source's own coordinate implies the estimate in the separation coordinate.

### The literal lattice support graph and Euclidean time

`RequestProject/YangMills/Cluster/LatticeTimeSeparation.lean`

* `circNorm` — the periodic norm on `ZMod m` (the least number of unit steps reaching a
  class, in either direction), with `circNorm_neg`, `circNorm_add_le` (triangle
  inequality) and `abs_circNorm_sub_circNorm_le`.  This is the correct separation on a
  periodic lattice.
* `latticeGraph` — the literal nearest-neighbour graph on `Site n`.
  * `degree_le_eight` — the entropy constant of the cluster expansion, `Δ = 8 = 2 · 4`,
    is **proved**, not assumed;
  * `latticeGraph_reachable` — the graph is connected, so the distances used below are
    finite and the estimates are not vacuous.
* `coordSep_le_dist`, `timeSep_le_dist` — the periodic separation in any lattice
  direction, in particular the Euclidean time separation, is at most the graph distance.
  This is the Euclidean-time half of `B3`.
* `selected_boundary_clustering_euclidean_time` — consequently the selected boundary of
  the differentiated expansion decays as `exp(−m · t)` in the Euclidean time separation
  of the two marks, with `m = −log η > 0` and a volume-independent constant, in the
  small-field regime `64 η < 1`.

`RequestProject/YangMills/Cluster/LatticeTimeDistance.lean`

* `circNorm_natCast_eq_self` — below half the period the periodic norm is the number
  itself;
* `dist_add_single_le`, `dist_timeVec_eq` — a `t`-step time translation is at graph
  distance exactly `t` (for `2t` below the period);
* `le_dist_timeVec_of_sameSlice` — the form the covariance estimate needs: for two
  insertions based on a common time slice, `t ≤ dist(x, y + timeVec t)`.

### The source rate split composed with the geometry

`RequestProject/YangMills/Cluster/SourceRateSplitTime.lean`

* `rate_split_decay`, `rate_split_exponential_decay`, `rate_split_euclidean_time_decay` —
  from `|commonY Y| ≤ A_Y · η^{d_k(Y)}` on connected domains through the two marks and
  `Σ_Y A_Y ≤ A_src`, the total obeys `A_src · exp(−m · t)` in the Euclidean time
  separation.  This is Bałaban's `(1.26)–(1.29)` *shape* discharged into physical decay;
  the shape itself remains a hypothesis.
* `RequestProject/YangMills/Cluster/LatticeTimeWitness.lean` — the hypotheses are jointly
  satisfiable with a nonzero total, two distinct marks and time separation exactly `1`,
  so the statement is not vacuous.

### The bridge into the continuum, with the separation hypothesis removed

`RequestProject/YangMills/Continuum/EventualClustering.lean`

* `exists_subseq_wilson_continuum_clustering_eventually` — the literal Wilson capstone
  with the honest hypothesis: the finite bound is needed only at all *sufficiently large*
  cutoffs for each fixed separation.  A periodic volume cannot cluster beyond half its
  period, so this — not a bound at every cutoff — is what a finite-geometry estimate can
  deliver.

`RequestProject/YangMills/Cluster/WilsonLatticeBridge.lean`

* `wilson_lattice_clustering_of_cluster_expansion` — the finite-volume estimate for the
  literal Wilson covariance.  Compared with `Cluster/WilsonClusterBridge.lean` the
  separation hypothesis `hsep` is **gone**: it is now the theorem
  `le_dist_timeVec_of_sameSlice`.  Only the source attachment `henv` survives.
* `exists_subseq_wilson_lattice_continuum_clustering` — with growing volumes, the
  continuum connected covariance inherits the same mass and constant.

### The mass-gap composite

`RequestProject/YangMills/Cluster/LatticeMassGap.lean`

* `wilson_massGapConclusion_of_continuum_clustering` — the terminal Route-`S` step from a
  continuum clustering estimate;
* `lattice_cluster_expansion_massGapConclusion` — the composite: lattice cluster
  expansion data, growing volumes, convergence of the three literal Wilson expectations
  and the same-object spectral representation give the repository's full
  `MassGapConclusion` for the reconstructed Hamiltonian at the gap `m = −log η > 0`.

## What is still open

Unchanged in substance, and none of it is claimed here:

| item | status |
|---|---|
| `B1` literal differentiated two-source term = the selected boundary of the expansion (the hypothesis `henv`, and the majorant/support data `hterm`, `hsupp`) | OPEN — the source attachment |
| `B2` common analytic domain and shared Hessian envelope for the physical trajectory | OPEN |
| `B3` one-sided geometry | **PROVED** (this round), in both halves, on the literal lattice |
| convergence of the three literal Wilson expectations | OPEN (input of the composite) |
| `S₅` same-object spectral representation of the reconstructed Hamiltonian | OPEN (input of the composite) |

The small-field regime enters only through the explicit inequality `64 η < 1` with the
*proved* lattice degree bound `Δ = 8`; no entropy constant is postulated anywhere in the
chain.

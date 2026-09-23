# Literal lattice Yang–Mills: what is now proved, and the exact remaining wall

This note describes the state of the `RequestProject/YangMills/Lattice/` modules,
which construct the **actual** finite-spacing Yang–Mills objects (not a synthetic
witness) and connect them to the existing conditional Clay assembly in
`RequestProject/YangMills/Clay/`.

No Clay-level claim is made anywhere in this development.  The four-dimensional
quantum Yang–Mills existence and mass-gap theorem is **not** proved here.

## 1. What the new modules construct and prove

All of the following are theorems, with no `sorry`, no `axiom`, no `postulate`,
and an axiom audit showing only `propext`, `Classical.choice`, `Quot.sound`.

`Lattice/CompactHaar.lean`
* `haarProb G` — the normalised Haar measure of a compact Hausdorff topological
  group, proved to be a probability measure, left invariant, and right invariant
  (right invariance is *derived*, from uniqueness of the Haar probability
  measure, not assumed);
* `measurePreserving_mul_left_mul_right` — two-sided translation of one link
  variable preserves it.

`Lattice/Config.lean`
* `prodHaar ι G` — the product of normalised Haar measures on the space `ι → G`
  of link configurations, a probability measure;
* `measurePreserving_reindex`, `measurePreserving_translate`,
  `measurePreserving_translate_reindex` — relabelling links and translating each
  link variable on both sides preserve it.

`Lattice/Wilson.lean` (the periodic four-dimensional lattice, `n+1` sites per
direction, sites `Fin 4 → ZMod (n+1)`, links `Site × Fin 4`)
* `plaqHol` — the literal plaquette holonomy
  `U(x,μ) U(x+μ̂,ν) U(x+ν̂,μ)⁻¹ U(x,ν)⁻¹`;
* `wilsonAction` — the literal Wilson action `−β Σ_x Σ_{μ,ν} χ(plaquette)`;
* `plaqHol_gaugeTransform` — gauge covariance of the plaquette (the holonomy is
  conjugated by the gauge function at the base point), proved by group algebra;
* `wilsonAction_gaugeTransform`, `wilsonAction_translate` — gauge invariance and
  translation invariance of the action;
* `gibbs` — the Wilson–Gibbs probability measure `Z⁻¹ e^{−S} dU`, with
  `0 < Z < ∞` proved from compactness of the configuration space and continuity
  of the character;
* `measurePreserving_gauge_gibbs`, `measurePreserving_translate_gibbs` — the
  Gibbs measure is gauge invariant and translation invariant.

`Lattice/TransferForm.lean`
* `sliceMeasure` — the law of the time-zero slice of the gauge field under the
  Wilson–Gibbs measure: the literal finite-spacing physical measure;
* `measurePreserving_slice0`, `measurePreserving_slice1` — the time-zero and
  time-one slices have the same law (this *uses* translation invariance of the
  Gibbs measure, it is not assumed);
* `energyForm` — the literal energy form
  `q(φ,ψ) = ⟪φ,ψ⟫ − ½(⟪φ∘p₀,ψ∘p₁⟫ + ⟪φ∘p₁,ψ∘p₀⟫)`, that is `1 − ½(T+T*)` for the
  Euclidean transfer operator `T` of the Wilson measure.  Sesquilinearity,
  Hermiticity and the continuity bound are **proved**, not posited;
* `vacuum`, `norm_vacuum` — the constant wavefunction is a unit vector because
  the slice measure is a probability measure;
* `energyForm_vacuum` — the form annihilates the vacuum; this is exactly the
  transfer-operator identity `T Ω = Ω`, and it is proved from the fact that both
  slice maps carry the constant wavefunction to the same constant.

`Lattice/SU2.lean`
* the gauge group `SU(2)`, in the unit-quaternion model already used by this
  repository, as a compact Hausdorff second-countable topological group with its
  Borel σ-algebra;
* `chiSU2 g = Re tr ρ(g) = 2 Re g` — the Wilson character of the defining
  two-dimensional representation, computed from the literal `2 × 2` matrix model
  `su2` of `SU2QuaternionOperatorNorm.lean`, together with its continuity and its
  conjugation invariance.

`Lattice/SU2YangMills.lean` — the literal four-dimensional `SU(2)` package
* `ymGibbs` with `ymGibbs_gauge_invariant` and `ymGibbs_translation_invariant`;
* `ymHilbert`, `ymVacuum`, `norm_ymVacuum`;
* `ymEnergyForm` — the physical energy form `a⁻¹(1 − ½(T+T*))` at lattice
  spacing `a`, with `ymEnergyForm_vacuum`;
* `ymHamiltonian` — the finite-spacing Hamiltonian produced from this form by
  Riesz representation, with `ymHamiltonian_isSelfAdjoint` and
  `ymHamiltonian_vacuum` (`H_a Ω_a = 0`);
* `lattice_massGap_of_coercivity` — **the literal finite-spacing mass-gap
  theorem**: coercivity of this same form on the vacuum complement implies the
  full mass-gap conclusion (form gap, no eigenvalue in `(0,Δ)`, unique
  solvability of `H_aψ − λψ = y` on the vacuum sector for every `λ < Δ`, and the
  resolvent bound `(Δ−λ)⁻¹`) for the literal lattice Hamiltonian.

`Lattice/GaugeInvariantSlice.lean` — the **physical (gauge-invariant)** space
* `sliceGauge`, `slice0_gaugeTransform` — the gauge action on slice
  configurations, which is the restriction of the gauge action on
  configurations;
* `measurePreserving_sliceGauge` — the slice measure is gauge invariant;
* `PhysicalSlice` — the gauge-invariant `L²` carrier, i.e. `L²_gauge(μ_a)`, with
  the physical vacuum `physVacuum` (a unit vector) and the physical energy form
  and Hamiltonian `physEnergyForm`, `physHamiltonian`, self-adjoint and
  annihilating the vacuum;
* `phys_massGap_of_coercivity` — coercivity on the physical space gives the full
  mass-gap conclusion there;
* `ymPhysicalHamiltonian`, `ym_phys_massGap_zero_coupling` — the `SU(2)`
  instances.

`Lattice/FreeCoupling.lean` — the package is inhabited by the literal objects
* `gibbs_zero` — at `β = 0` the Wilson–Gibbs measure *is* the product of
  normalised Haar measures;
* `indepFun_slice` — under that measure the time-zero and time-one slices are
  independent (they are functions of disjoint sets of links);
* `energyForm_coercive_of_zero_coupling` — hence at zero coupling the transfer
  operator of the literal Wilson measure is the vacuum projection and the energy
  form is coercive on the vacuum complement;
* `ym_massGap_zero_coupling`, `ym_phys_massGap_zero_coupling` — therefore the
  literal four-dimensional `SU(2)` lattice theory at zero coupling satisfies the
  full mass-gap conclusion with gap `a⁻¹` at spacing `a`, both on the slice space
  and on the gauge-invariant physical space.  This is the strong-coupling end of
  the theory: the gap diverges as `a → 0`, and it says nothing about the
  continuum limit.  Its role here is that the finite-spacing package is
  demonstrably inhabited by the literal Yang–Mills objects rather than by a
  synthetic witness.

`Lattice/StrongCoupling.lean` — the estimate holds on an open range of couplings
* `gibbs_eq_withDensity` — the literal Wilson–Gibbs measure is the product Haar
  measure weighted by the explicit real density `e^{-S}/Z`;
* `le_gibbsRealDensity`, `gibbsRealDensity_le` — that density lies in
  `[e^{-2M}, e^{2M}]` whenever the Wilson action is bounded by `M` (which it is,
  by compactness);
* `prodHaar_le_smul_gibbs`, `haarSlice_le_smul_sliceMeasure` — the resulting
  two-sided comparison of the Gibbs measure with the product Haar measure, which
  transports square integrability between the two;
* `norm_inner_embed_le` — **the quantitative decorrelation estimate**: for
  `ψ ⊥ Ω`,
  `|⟪P₀ψ, P₁ψ⟫| ≤ ((e^{2M}-1)² + e^{4M} - 1)‖ψ‖²`.  The proof splits the density
  as `e^{-2M} + (density - e^{-2M})`; the first piece factorises exactly by the
  slice independence of `FreeCoupling.lean` and is then killed by the vacuum
  orthogonality up to the density oscillation, and the second is controlled by
  Cauchy–Schwarz;
* `energyForm_coercive_of_small_action` — hence the literal Wilson form is
  coercive on the vacuum complement with constant `2 - (e^{2M}-1)² - e^{4M}`,
  which equals `1` at `M = 0` and is positive for `M` small;
* `abs_chiSU2_le`, `abs_wilsonAction_SU2_le` — the explicit bound
  `|S| ≤ 32|β|(n+1)⁴` on the literal `SU(2)` Wilson action;
* `ym_massGap_of_small_action`, `ym_massGap_of_small_coupling`,
  `ym_massGap_of_coupling_le` — therefore the literal four-dimensional `SU(2)`
  lattice theory has the full mass-gap conclusion at spacing `a` for every
  coupling with `64|β|(n+1)⁴ ≤ 1/10`.

`Lattice/PhysicalStrongCoupling.lean`
* `phys_massGap_of_small_action`, `ym_phys_massGap_of_coupling_le` — the same
  conclusion on the gauge-invariant physical Hilbert space
  `L²_gauge(μ_a)`: for `64|β|(n+1)⁴ ≤ 1/10` the physical Hamiltonian of the
  literal `SU(2)` Wilson theory has a positive vacuum-sector mass gap, with the
  form gap, the absence of an eigenvalue below the gap, unique solvability of
  `Hψ − λψ = y` on the vacuum sector and the resolvent bound.

So, for the actual `SU(2)` Wilson theory at fixed spacing, the operator side is
no longer hypothetical: the Hilbert space, the vacuum, the energy form, the
Hamiltonian, its self-adjointness and the zero-energy vacuum are all constructed
and proved, and the remaining finite-spacing input — the coercivity estimate
`HasLatticeCoercivity` — is itself proved on an explicit open range of couplings.
What is *not* proved is that estimate uniformly in the lattice volume and along
the renormalisation-group trajectory, which is where the Clay problem lives.

## 2. The exact remaining wall

### G1 — coercivity of the literal energy form, uniformly in the spacing

`HasLatticeCoercivity n β a Δ` says

    Δ‖ψ‖² ≤ Re q_a(ψ,ψ)   for all ψ ⊥ Ω_a,

for the literal `SU(2)` Wilson form `q_a = a⁻¹(1 − ½(T+T*))`.  Equivalently, the
spectrum of `½(T+T*)` on `Ω_a^⊥` lies below `1 − aΔ`: the transfer matrix of the
literal Wilson measure has a spectral gap, and the corresponding mass is at least
`Δ` in physical units.

This estimate is now **proved** on an explicit open range of couplings: at
`β = 0` with `Δ = a⁻¹` (`ym_hasLatticeCoercivity_zero_coupling`), and more
generally for every `β` with `64|β|(n+1)⁴ ≤ 1/10`
(`ym_massGap_of_coupling_le`, `ym_phys_massGap_of_coupling_le`), by the
Doeblin-type decorrelation argument of `Lattice/StrongCoupling.lean`.

What remains open is the estimate **in the regime that matters**.  The threshold
above shrinks like `(n+1)^{-4}`, so it is not uniform in the lattice volume, and
it is a small-`β` (strong-coupling) statement, whereas the continuum limit
requires a bound that survives the joint limit `n → ∞` (infinite volume) and
`a → 0` along the renormalisation-group trajectory `β = β(a) → ∞`, with `Δ`
bounded below by a fixed positive constant.  That uniform estimate is the content
of the Clay problem.  Nothing in this repository proves it, and nothing here
should be read as proving it.

Note also the normalisation, which is a real constraint and not a bookkeeping
detail: the unscaled form `1 − ½(T+T*)` has gap of order `m·a`, so a gap
constant that is uniform in `a` can only be asserted for the rescaled form
`a⁻¹(1 − ½(T+T*))`, which is what `ymEnergyForm` uses.  In particular the Row-A1
constant `b₋(SU(N);r,h)` cannot be substituted for the gap of the *unscaled*
transfer form; whichever constant is used must be a mass, i.e. must appear after
the `a⁻¹` rescaling.

### G2 — a common carrier for the cutoff family

The existing consumer `Clay.CutoffFamily` requires all finite-spacing
Hamiltonians `H_a` to act on **one** Hilbert space `E`, with the continuum
Hamiltonian obtained as a vacuum-sector graph limit inside that same `E`.  The
literal objects constructed here do not have this shape: `ymHilbert n β` is
`L²` of the slice measure of the lattice with `n+1` sites per direction, and
these are different measure spaces for different `n`.  Feeding the literal
family into the existing assembly therefore requires, in addition to G1, the
isometric identifications (or an inductive-limit construction) that are part of
the constructive continuum limit itself.  This is a structural gap, and it is
not closed here.

### G3 — the continuum limit

Convergence `μ_a → μ_∞` of the Wilson measures along the RG trajectory, the
Osterwalder–Schrader axioms for the limiting Schwinger functions, and the
resulting `(H_∞, Ω)` are not constructed here.  Nothing in this development
provides them, and no statement here presupposes them.

### G4 — the Yang–Mills/Osterwalder–Schrader same-object weld

`U_∞^{YM}(t) = U^{OS}(t)` for the actual continuum theory is not proved here; it
presupposes G3.

## 3. Summary

The finite-spacing physical objects of four-dimensional `SU(2)` lattice
Yang–Mills are now literally constructed in Lean, with their gauge and
translation symmetries, their slice Hilbert space, their vacuum and their
self-adjoint Hamiltonian all proved rather than assumed, and the theory has a
proved positive mass gap at every lattice spacing for all couplings with
`64|β|(n+1)⁴ ≤ 1/10`.  The remaining debt is
G1 (the transfer-matrix gap estimate, uniformly in the volume and the spacing),
G2 (a common
carrier for the cutoff family), G3 (the continuum limit) and G4 (the OS weld).
G1 and G3 are the two genuinely open mathematical problems; G2 is structural and
would be resolved as part of G3.

## 4. Update: the varying-carrier weld (round of 2026-09-17)

Section 2 above listed G2 — "a common carrier for the cutoff family" — as a
structural gap, because `Clay.CutoffFamily` and
`ContinuumGapTransport.IsVacuumGraphLimit` require all cutoff Hamiltonians to act
on one Hilbert space, whereas `ymPhysicalSlice n β = L²_gauge(μ_{n,β})` varies
with the cutoff.

That structural gap is now closed, in `RequestProject/YangMills/VaryingCarrierTransport.lean`:
the transport layer is proved for a family of carriers `F : ℕ → Type*` with
isometric embeddings `J n : F n →ₗᵢ[ℂ] E`, and the fixed-carrier theorem is
recovered as the case `J = id`.  Consequently
`RequestProject/YangMills/Lattice/ContinuumWeld.lean` feeds the **literal**
Wilson family directly into the continuum consumer:
`ym_continuum_massGap_of_uniform_gap_and_graphLimit` and
`ym_continuum_massGap_os_of_same_evolution`.  Note that the weld needs only the
embeddings — no vacuum compatibility, intertwining or domain-preservation
conditions — because the gap hypothesis is stated on each literal carrier in its
own inner product.

`RequestProject/YangMills/Lattice/UniformGapReduction.lean` then states G1 in its
smallest form: coercivity of the literal transfer form follows from the single
two-slice estimate `‖⟪P₀ψ, P₁ψ⟫‖ ≤ c‖ψ‖²` on the vacuum complement, with gap
constant `a⁻¹(1−c)`, so the remaining finite-side payment is one correlation
inequality for the Wilson–Gibbs slice measure, uniform in volume and spacing
along the trajectory.  At `β = 0` that estimate holds with `c = 0` for every
volume (`ym_uniform_decorrelation_zero_coupling`), which shows the reduced
hypothesis is inhabited and that the obstruction lies in the coupling flow
`β → ∞`, not in the volume alone.

G1, G3 and G4 remain open exactly as described above.  No Clay-level claim is
made.

## Update (2026-09-17, second round): the frontier is `F1 / F3 / F4`

The finite-side payment has been restated on the literal Euclidean transfer
operator `T = P₁* P₀` of the Wilson–Gibbs measure
(`Lattice/TransferOperatorGap.lean`), where the literal energy form is
`q(ψ,ψ) = ‖ψ‖² − Re⟪Tψ, ψ⟫`.  Three equivalent shapes of the same input are now
available: the two-slice correlation bound, contractivity of `T` on the vacuum
complement, and phase-separation of the two slice embeddings
(`decorrelation_iff_phase_separated`).

The payment is also weaker than previously stated.  It is **not** a uniform
constant `c < 1`: the weld consumes only the per-step spectral defect

    Δ · a_k ≤ 1 − c_k,

so `c_k → 1` is permitted at rate `O(a_k)` along the physical trajectory
(`ym_uniform_gap_of_trajectory_decorrelation`, `trajectory_gap_bound_of_defect`).

The former carrier obligation is gone.  `CommonCarrier.lean` proves that a
carrier with isometric embeddings always exists, and that the canonical `ℓ²`
embeddings can approximate nothing, so the embeddings along which the physical
family converges are data of the continuum limit rather than a separate
compatibility theorem; `ymCanonicalCarrier_graphLimit_degenerate` states this for
the literal Yang–Mills family.  The recut endpoint is in
`Lattice/FrontierF1F3F4.lean`: `clay_massGap_of_F1_F3`,
`clay_massGap_os_of_F1_F3_F4`, `clay_massGap_of_transfer_defect_F3`.  See
`docs/ym/frontier_recut_f1_f3_f4.md`.

## Update (2026-09-17, third round): `F1` on a dense algebra of gauge-invariant observables

The finite-side input no longer has to be verified for every square-integrable
state.  `Lattice/DenseCorrelationExtension.lean` proves that the two-slice
estimate is a *closed* condition on the state, and that the mean-zero part of
any dense subspace containing the vacuum is dense in the vacuum complement;
together with the density of continuous functions in `L²` (and Stone–Weierstrass
for a separating star algebra) this turns a connected two-slice correlation
bound on a dense algebra of observables into the estimate for every state.
`Lattice/WilsonObservableAlgebra.lean` exhibits such an algebra concretely: the
link-coordinate observables separate slice configurations, so polynomials in the
link variables suffice.

`Lattice/GaugeInvariantDenseObservables.lean` goes one step further and makes
the input *gauge invariant*.  Haar averaging over the lattice gauge group sends
a continuous observable to a continuous gauge-invariant observable, and
`norm_obsToL2_gaugeAvg_sub_le` shows that averaging never increases the distance
to a gauge-invariant state, so the mean-zero gauge-invariant continuous
observables are dense in the vacuum complement of the *physical* Hilbert space.
Consequently only correlations of gauge-invariant observables need estimating:
`ym_uniform_gap_of_gauge_invariant_mixing`, with the endpoints
`clay_massGap_of_gauge_invariant_mixing_F3` and
`clay_massGap_os_of_gauge_invariant_mixing_F3_F4` in
`Lattice/FrontierDenseObservables.lean`.  See
`docs/ym/dense_observable_f1_round.md`.  `F1`, `F3` and `F4` remain open.

## Update: the finite Euclidean (hypercubic) symmetry, item `A1`

The finite Euclidean symmetry of the literal lattice theory is now complete, not
only the translation part.

`Lattice/Hypercubic.lean`
* `haarProb.isInvInvariant` — the normalised Haar measure of a compact group is
  inversion invariant, *derived* from uniqueness of the Haar probability
  measure; this is what makes a reflection (which reverses the links pointing in
  the reflected direction) measure preserving;
* `rotate`, `reflect` — the action of a permutation of the coordinate axes and
  of a reflection in a coordinate hyperplane on gauge configurations;
* `wilsonAction_rotate`, `wilsonAction_reflect` — invariance of the literal
  Wilson action.  The reflection statement needs only conjugation invariance of
  the character: a plane containing the reflected direction is carried to the
  *oppositely oriented* reflected plane, and the action sums over ordered pairs
  of directions, so the reflected sum is a permutation of the original one
  (`orientationSwap`).  No reality assumption `χ(g⁻¹) = χ(g)` is used;
* `measurePreserving_rotate_gibbs`, `measurePreserving_reflect_gibbs` — the
  Wilson–Gibbs measure is preserved by the whole hypercubic point group;
* `integral_rotate_gibbs`, `integral_reflect_gibbs`, `integral_translate_gibbs`
  — every finite-volume expectation is invariant;
* `expectation_bosonic_permutation` — the finite bosonic (permutation) symmetry
  of the lattice Schwinger functions.

`Lattice/HypercubicLoop.lean`
* `pathHol_rotate`, `pathHol_reflect` — the holonomy of a rotated/reflected loop
  is the pullback of the holonomy of the original loop; a reflection reverses
  the orientation of the steps along the reflected direction (`refStep`);
* `EuclideanRelated` — the relation generated by translations, axis permutations
  and hyperplane reflections on based loops;
* `integral_loopObs_euclidean` — Euclidean related loops have the same literal
  Wilson expectation at every cutoff.

`Lattice/SchwingerBounds.lean`
* `norm_integral_prod_loopObs_le` — the cutoff-uniform bound `|S| ≤ M^m` on the
  finite-volume Wilson Schwinger functions of arbitrary order `m`;
* `integral_prod_loopObs_translate`, `integral_prod_loopObs_rotate`,
  `integral_prod_loopObs_reflect` — Euclidean invariance of those Schwinger
  functions.

`Lattice/HypercubicWitness.lean` checks the invariance is not vacuous: the
plaquette loop in the `(0,1)` plane is Euclidean related to genuinely different
loops.

`Continuum/LimitEuclidean.lean`
* `exists_wilson_limit_euclidean_invariant` — along one subsequence of cutoffs
  all selected literal Wilson expectations converge and any two selected loops
  that are Euclidean related at every cutoff have the *same* limit.  This is OS1
  for the subsequential limit functional; the rotation/reflection half that
  `Continuum/LimitSymmetries.lean` explicitly left open.

What this does **not** do: it is a statement about the limit expectation
functional on the Wilson sector, not about a continuum measure.  Uniqueness of
the limit, projective consistency, and the remaining OS axioms are untouched by
this round.

`Lattice/SchwingerBounds.lean` additionally packages the point group as
`LatticeMove` (translation, axis permutation, hyperplane reflection) and proves
`integral_prod_loopObs_moves`: the `m`-loop Schwinger function is unchanged when
*every* loop of the family is moved by the same composition of generators.
`Continuum/LimitSchwinger.lean` transports this through the subsequential limit
(`exists_wilson_limit_schwinger_euclidean_invariant`): along one subsequence all
selected `m`-loop Wilson Schwinger functions converge, with limits bounded by
`M ^ m`, and families related by a lattice Euclidean transformation at every
cutoff have equal limits.

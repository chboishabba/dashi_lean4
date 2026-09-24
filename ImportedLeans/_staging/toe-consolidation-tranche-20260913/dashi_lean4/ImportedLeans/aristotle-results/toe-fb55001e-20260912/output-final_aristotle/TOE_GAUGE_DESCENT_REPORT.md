# Gauge reduction and observational resolution

This tranche adds two abstractions to the welded `Spine` × `Integration` schema
and instantiates both on finite corpus lanes.  Everything named below is checked
by `lake build` (full build, no `sorry`), and every headline result is listed in
`Lean/Integration/AxiomAudit.lean`, where it depends only on `propext`,
`Classical.choice` and `Quot.sound`.

---

## 1. Orbit quotient vs gauge reduction

`Lean/Integration/GaugeReduction.lean` (namespace `Integration.Gauge`).

The starting observation is a theorem, not a design choice:

> **`GaugeReduction.coarse_action_trivial_of_orbit`** — if the projection of an
> equivariant quotient is constant on the orbits of the acting group, then the
> induced coarse action is trivial.

So `[x] = [g·x]` forces `ḡ·[x] = [x]`: on a full orbit quotient there is no
nontrivial residual action to find.  The distinction that *does* leave a
symmetry downstairs is the subgroup one.

* `GaugeQuotient G H Q` — monoid maps `H → G` and `G ↠ Q` with `quot ∘ incl = 1`.
  `GaugeQuotient.Exact` adds that the kernel of `quot` is no bigger than the
  image of `incl`, i.e. that `Q` is exactly `G/H`.
* `GaugeReduction G H Q Rich Coarse` — a `G`-action upstairs, a `Q`-action
  downstairs, a surjective `red`, and the square `red (g·x) = quot g · red x`.
* `gauge_invariant` — the gauge subgroup is automatically invisible downstairs.
* `toEquivariantQuotient` — every gauge reduction is an `EquivariantQuotient`
  for the full group, so the whole existing welded library applies unchanged.
* `Effective` + `effective_not_orbit_quotient` — if some surviving symmetry
  moves the coarse layer, the reduction provably is *not* an orbit quotient.
* **`redundant_iff_gauge`** — under exactness and downstairs faithfulness, the
  symmetries invisible to the coarse layer are *exactly* the gauge subgroup:
  the reduction removes a redundancy and nothing else.
* `compGauge` — gauge reductions compose, and `compGauge_redundant_iff`
  identifies what the composite makes redundant: exactly the symmetries whose
  image in the middle group is a second-stage gauge element, i.e. the preimage
  of the second gauge subgroup.  `toResidualQuotient` and
  `residual_nontrivial_of_card` give the residual support.

### The transverse channel had to be generalised

`Lean/Integration/EquivariantChannel.lean`.

The existing observer constructor requires a class coordinate *invariant* under
the symmetry.  A surviving effective symmetry moves the coarse layer by design,
and in the instances below the enlarged group acts transitively on the rich
carrier, so the only invariant class functions are constant — and a constant
channel has zero transverse area.  `EqObserverBuild` weakens the hypothesis to
equivariance, `cls (g·x) = ǧ · cls x`, which is exactly what the permutation
representation needs (`channelVec_equivariant`), and `toObserver` then produces
a `SymmetryResolvedObserver` with all three welded conclusions.

`Lean/Integration/GaugeObserver.lean` states the combined result once:

> **`gauge_welded_theorem`** — gauge reduction + effective surviving symmetry +
> equivariant channel gives: the observer's visible layer is the gauge-reduced
> carrier; the gauge subgroup is invisible on it; the surviving symmetry is not;
> the rich state is exactly recoverable from visible state plus residual; the
> transverse certificate is strictly positive; and it is constant along the
> whole symmetry.

---

## 2. Two instances where a redundancy is quotiented and a symmetry survives

### 2.1 The finite `SU(2)/{±1}` pattern — `Lean/Integration/GaugeSU2.lean`

```
G = C₂ × C₃  (sheet flip × axis rotation)
H = C₂       (the deck transformation — redundant)
Q = G/H ≅ C₃ (axis rotation — survives, acts nontrivially)

AxisLift (6) ──/H──▶ SU2Axis (3),  residual = lift polarity (2)
```

* `gaugeDatum_exact` — the kernel of `G ↠ C₃` is exactly the sheet subgroup.
* `sheet_is_deck_transformation` — the quotiented generator *is* the central
  flip of the already-checked `axisLiftDoubleCover`.
* `su2_effective`, `su2_not_orbit_quotient`, `su2_redundant_iff_gauge`.
* `su2GaugeObserver`, `su2_gauge_theorem`, `su2_welded` — the welded
  conclusions, including the positive transverse certificate.

This is the same projection `6 → 3` that was previously registered as an orbit
quotient with trivial induced action; enlarging the group is what turns it into
a gauge reduction with an effective `C₃` downstairs.  No claim is made that
these six and three element carriers *are* `SU(2)` and `SO(3)`; the proved
statement is that they instantiate the quotient pattern `G/H` with `H` central
and the quotient acting nontrivially.

### 2.2 The SSP nine-cell lane — `Lean/Integration/GaugeSSP.lean`

```
G = C₃ × C₂  (depth-wheel rotation × lane-polarity flip)
H = C₃       (the wheel phase — redundant for the visible lane)
Q = G/H ≅ C₂ (the polarity flip — survives, acts nontrivially)

FullPhaseCell (9) ──/H──▶ KernelTrit (3),  residual = wheel phase (3)
```

`wheel_vs_gauge` states the contrast as one theorem: the *same* projection
`9 → 3` necessarily has a trivial induced action when the acting group is the
whole depth wheel, and has a nontrivial one when the wheel is only the gauge
subgroup of the larger lane symmetry.  `ssp_redundant_iff_gauge` identifies the
invisible symmetries with the wheel rotations exactly, and `ssp_gauge_theorem` /
`ssp_welded` give the welded conclusions with the positive certificate.

---

## 3. Where an invariant stops being observable

`Lean/Integration/DescentLevel.lean`.

* `LayerTower` — carriers `X₀ → X₁ → X₂ → ⋯` with a coarsening at each step;
  `projTo k` is the composite from the finest level.
* `FactorsAt T c k` — the invariant `c : X₀ → ℝ` is a function of the level-`k`
  observation.  `factorsAt_zero` and `factorsAt_of_le` make the sufficient
  levels an initial segment, and `factorsAt_iff_fibre` gives the exact
  criterion (constancy on the fibres of `projTo k`).
* **`CoarsestSufficient T c k`** — factors at `k`, fails at `k+1`: the minimum
  observational resolution at which the invariant is still visible.
  `coarsest_unique` makes it a well-defined number and `exists_coarsest` shows
  it exists whenever the invariant is lost somewhere up the tower.
* `factorsAt_one_of_orbitFibred` — the bridge to the welded schema: an
  orbit-fibred symmetry-resolved observer's certificate factors at its own
  visible level.

### The instance is computed, not assumed

On the axis-lift lane with the class coordinate "is this the distinguished
axis?", the two classes have sizes four and two, and the certificate is
evaluated exactly:

```
cert_mid  :  nondegeneracy (axisMid , pos) = 107/9
cert_high :  nondegeneracy (axisHigh, pos) = 104/9
```

Hence on the tower `6 → 3 → 2` (the last step merging the distinguished axis
with another):

* `cert_factorsAt_one` — the certificate is an observable of the three-axis
  layer (via orbit-fibredness);
* `cert_not_factorsAt_two` — it is not an observable of the merged two-state
  layer;
* **`axis_coarsest_sufficient`** — the coarsest sufficient observation is
  exactly level 1, and `axis_coarsest_unique` says no other level has this
  property.

### And a contrast on the same six points

Under the *enlarged* symmetry of §2.1 the group acts transitively
(`su2_transitive`), so that lane's certificate is constant (`su2_cert_constant`)
and factors at every level (`su2_cert_factorsAt`); `su2_no_coarsest` records
that it therefore has no resolution threshold at all.  The general statement is
`factorsAt_all_of_transitive`.  A threshold is thus a property of the chosen
transverse channel, not of the carrier.

---

## 4. Wiring

* `Lean/Integration.lean` imports the five new modules.
* `Lean/Integration/Registry.lean` gains two further level-iv rows (the axis
  lane and the SSP lane, each as a *gauge* reduction with surviving symmetry)
  and one boundary (the two-state coarsening does not retain the certificate).
  `registry_levels` is still checked by `rfl`.
* `Lean/Integration/AxiomAudit.lean` gains 40 further `#print axioms` lines.

## 5. Frontier after this tranche

1. **Closed**: the previous frontier item "no equivariant quotient whose coarse
   action is nontrivial for a group of order three" — `su2GaugeReduction` has a
   surviving `C₃` acting faithfully on the three-element coarse carrier.
2. **Partly closed**: composition is proved (`compGauge`), and
   `compGauge_redundant_iff` characterises the composite's invisible symmetries
   as the preimage of the second gauge subgroup.  What is still not carried in
   the data is a group structure on that preimage; the composite `GaugeQuotient`
   field still records the first subgroup only.
3. **Open**: `CoarsestSufficient` is computed on one lane and shown not to exist
   on another (`su2_no_coarsest`).  It is not computed for the SSP tower.
4. **Open**: the certificate still depends on the chosen enumeration of the
   carrier; independence of that choice is not proved.
5. **Unchanged**: no analytic content is imported in either physics-named lane,
   the Agda sources are read but not rechecked here (no Agda toolchain in this
   environment), and no physical or Lie-group claim is made anywhere.

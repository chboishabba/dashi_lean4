# The Spine: dependency map and frontier report

This document describes the `Spine` Lean library (`Lean/Spine/`), added in the
current session, and records honestly what is proved and what is not.

The premise it implements: **do not unify the corpus by vocabulary, unify it by a
small family of reusable structural theorems plus explicit, nondegenerate
observers into those structures.**  The recurring theorem is

> a carrier with a distinguished fixed/constant mode splits as
> `fixed ⊕ transverse`; a symmetry acts trivially on the fixed part and by
> conjugation/rotation on the transverse part; the real observables are
> degree-two invariants of the transverse part; and the inherited theorem says
> something only when a **nondegeneracy witness** is supplied.

## Build status

Everything below is machine-checked in Lean 4.28.0 against the Mathlib commit
pinned by `lake-manifest.json`.

* `lake build` (all default targets: `Synthesis`, `Cuisine`, `AgdaMirror`,
  `Spine`) completes successfully.
* `Lean/Spine` contains **no** `sorry`, no `axiom`, no `@[implemented_by]`, and
  no `native_decide`.
* `Lean/Spine/AxiomAudit.lean` prints the transitive axiom dependencies of every
  headline theorem.  They are exactly `propext`, `Classical.choice`,
  `Quot.sound` — and the purely finite Ogg facts use only `propext`,
  `Quot.sound`.

## Module dependency graph

```
  Spine.AnchoredGram                Spine.OggGrid            Spine.TwoRegime
     |            \                      |                    (standalone)
     |             \                     v
     |              \            Spine.EqualCardinality
     v               v
 Spine.MeanSplit   Spine.TernaryPhase
     |               |        \
     v               v         v
 Spine.Observer   Spine.TraceNorm   Spine.FixedLocus
     |
     v
 Spine.TritCarrier   <-- also Spine.TernaryPhase and AgdaMirror.TritBridge
 Spine.Duality       <-- Spine.Observer (for the taste carrier)

        Spine.EndToEnd   <-- AnchoredGram, TernaryPhase, TraceNorm, MeanSplit,
              |              Observer, OggGrid, FixedLocus, EqualCardinality
              v
      Spine.AxiomAudit   <-- EndToEnd, TwoRegime
              |
              v
           Spine          (aggregate: imports every module above)
```

Two modules reach outside the library, in both cases deliberately, to build an
observer instance from the project's *existing* data: `Spine.Observer` imports
`Cuisine.SensoryCore` (for `SensoryProfile` / `TasteDimension`), and
`Spine.TritCarrier` imports `AgdaMirror.TritBridge` (for the balanced-ternary
digit type `Trit`, its negation `Trit.inv`, and its rotation `rotTrit`).

## Stage 1 — the spine theorem: anchored exterior coercivity

`Lean/Spine/AnchoredGram.lean`.  For an inner product space over `ℝ`, if
`⟪f, t₀⟫ = 0` and `⟪f, t j⟫ = 0` for all `j`, then with `v₀ = f + t₀` and
`v_j = t_j`:

| name | statement |
| --- | --- |
| `Spine.det_gram_anchored_eq` | `det Gram(v₀, t) = ‖f‖²·det Gram(t) + det Gram(t₀ :: t)` (exact identity) |
| `Spine.det_gram_anchored_ge` | `‖f‖²·det Gram(t) ≤ det Gram(v₀, t)` (coercivity, arbitrary rank) |
| `Spine.det_gram_anchored_pos` | `f ≠ 0` and `t` independent ⟹ `0 < det Gram(v₀, t)` (the gate) |
| `Spine.linearIndependent_anchored` | the same hypotheses give linear independence of the whole family |
| `Spine.anchored_area_ge` | the `r = 1` (area) case, the previously known instance |

The proof is a cofactor expansion (`Spine.det_add_single_zero_zero`) plus
`Matrix.posSemidef_gram` for the nonnegativity of the second summand; it does not
go through exterior algebra, but it proves exactly the stated inequality.

This is the general-rank statement that was requested as the highest-alpha item.

## Stage 2 — the canonical fixed ⊕ transverse splitting

`Lean/Spine/MeanSplit.lean`.  On `EuclideanSpace ℝ (Fin n)` with `[NeZero n]`:
`ones`, `avg`, `meanPart`, `fluct`, with `meanPart x + fluct x = x`,
`⟪meanPart x, fluct y⟫ = 0`, `‖meanPart x‖² = n·(avg x)²`, and
`fluct x = 0 ↔ x` is constant.  `det_gram_mean_anchored_ge` /
`det_gram_mean_anchored_pos` / `anchored_plane_area` are Stage 1 transported into
this splitting; `anchored_plane_area` gives the explicit floor
`n·(avg x)²·‖fluct y‖²`.

## Stage 3 — the ternary phase core, as an exact representation statement

`Lean/Spine/TernaryPhase.lean`.

*Complex phase algebra.*  `zeta = (−1 + i√3)/2` explicitly, with `zeta_cube`,
`zeta_ne_one`, `zeta_sum` (`1 + ζ + ζ² = 0`), `conj_zeta` (`ζ̄ = ζ²`),
`zeta_inv` (`ζ⁻¹ = ζ²`), `conj_zeta_sq`.  The C₃ character table is an actual
`Matrix (Fin 3) (Fin 3) ℂ` with `charMatrix_orthogonality : F₃ · F₃ᴴ = 3 • I`
and `charMatrix_det_ne_zero`.

*Realification.*  On `ℝ[C₃] = EuclideanSpace ℝ (Fin 3)` with the cyclic shift `σ`:

| name | content |
| --- | --- |
| `RealC3.fixed_iff_constant` | `σ x = x ↔ x` constant — the fixed sector is the trivial character |
| `RealC3.isCompl_fixedSub_transverse` | **`ℝ[C₃] = ℝ_triv ⊕ transverse`** as a literal internal direct sum |
| `RealC3.inner_fixedSub_transverse` | the two sectors are orthogonal |
| `RealC3.finrank_transverse` | the transverse sector has real dimension `2` |
| `RealC3.shift_sq_add_shift_add_one` | `σ² + σ + 1 = 0` on the transverse sector — the rotation relation |
| `RealC3.no_real_eigenvector_transverse` | `σ` has no real eigenvector inside it |
| `RealC3.transverse_irreducible` | **no proper nonzero invariant subspace** — it is one irreducible real plane |

*The binary contrast.*  `RealC2.swap_eq_neg_on_transverse` and
`RealC2.finrank_transverse = 1`: in `C₂` the nontrivial character is already
real, the transverse sector is an eigenline, and label count and real transverse
dimension coincide.  In `C₃` they demonstrably come apart.  This is the precise
sense in which the ternary case is the first one where the binary intuition is
forced to become exact.

## Stage 4 — descent to real observables

`Lean/Spine/TraceNorm.lean`.  With `Cyc.mk u v = u + vζ` for rational `u, v`:
`conj_mk` (`conj (u + vζ) = (u − v) − vζ`), `trace_mk` (`Tr = 2u − v`),
`mul_conj_eq_norm` (`x·x̄ = u² − uv + v²`, landing on the rational axis),
`norm_nonneg`, `norm_eq_zero_iff`, `mk_injective`.

The caveat is proved, not asserted: `Cyc.conj_fixed_iff_rational` says
`conj (u + vζ) = u + vζ ↔ v = 0`, i.e. the conjugation-fixed part of `ℚ(ζ₃)` is
exactly `ℚ`.  Phases alone therefore give nothing continuous; amplitudes are
required.  This permanently blocks the inference "15 phase labels ⟹ ℝ".

## Stage 5 — the observer interface, and its instances

`Lean/Spine/Observer.lean`.  `area2 a b = ‖a‖²‖b‖² − ⟪a,b⟫²`, with
`area2_eq_det_gram`.  The interface is

```lean
structure MeanObserver (D : Type*) (n : ℕ) [NeZero n] where
  read          : D → EuclideanSpace ℝ (Fin n)
  channel       : D → EuclideanSpace ℝ (Fin n)
  mean_ne_zero  : ∀ d, MeanSplit.avg (read d) ≠ 0
  fluct_ne_zero : ∀ d, MeanSplit.fluct (channel d) ≠ 0
```

— domain, map into a structured carrier, and the two nondegeneracy witnesses.
The inherited theorems are `MeanObserver.transverse_area_pos` (strictly positive
transverse area) and `MeanObserver.read_channel_independent`.

Instances actually constructed:

* `monster_five_transverse_planes` — five modes, each with a nonzero constant
  part and a nonconstant ternary channel, give five genuinely positive
  transverse areas.  This is what upgrades `5 × 2` from a cardinality to five
  actual planes.
* `Cuisine.taste_plane_pos` — the cuisine taste carrier, built from the
  project's existing `Cuisine.SensoryCore.SensoryProfile`, with the witnesses
  discharged from "some taste intensity is positive" and "the intensities are
  not all equal".

* `TritCarrier.trit_weighting_plane_pos` — the project's own balanced-ternary
  digit carrier, with the witnesses discharged from "the digit weights do not
  sum to zero" and "the channel's digit values are not all equal".

The degeneracy controls are first-class: `degenerate_observer_area_zero` and
`Cuisine.flat_profile_degenerate` say that a constant channel — in particular a
map sending all of a domain's data to a single value — has zero observed area.
The inherited theorem is then true and empty.  **A name is not an operator; an
instance without a nondegeneracy witness proves nothing.**

## Stage 5b — the corpus's own trit carrier, wired in by equivariance

`Lean/Spine/TritCarrier.lean`.  The project already carried a balanced-ternary
digit type `Trit` with an involution `Trit.inv` (`neg ↔ pos`, fixing `zer`) and
an order-three rotation `rotTrit`.  That is a `C₃` carrier with an inversion, so
it should *instantiate* the ternary phase core rather than sit beside it.  The
link is established by theorems, not by vocabulary:

| name | content |
| --- | --- |
| `TritCarrier.tritOf_succ` | the index dictionary carries `Fin 3` successor to `rotTrit` |
| `TritCarrier.embed_rot` | `σ ∘ embed = embed ∘ (· ∘ rotTrit)` — rotation is intertwined with the cyclic shift |
| `TritCarrier.embed_inv` | digit negation is intertwined with an explicit linear reflection `ρ` |
| `TritCarrier.reflect_involutive` | `ρ² = 1` |
| `TritCarrier.reflect_shift` | **`ρσ = σ²ρ`** — the involution conjugates the rotation, exactly as `ζ ↦ ζ²` |
| `TritCarrier.reflect_on_fixedSub` | `ρ` fixes the constant line pointwise |
| `TritCarrier.reflect_mem_transverse` | `ρ` preserves the transverse plane |
| `TritCarrier.reflect_eigenvector_transverse` | `ρ` has the real eigenvector `neg ↦ 1, zer ↦ 0, pos ↦ −1`, eigenvalue `−1` |
| `TritCarrier.reflect_ne_shift` | **negation is not rotation, as linear maps** |

The last line is the payoff.  The corpus already recorded the digit-level
obstruction "negation is not the rotation, witnessed at `neg`"
(`AgdaMirror.TritBridge.inv_not_rotation_at_neg`).  Here is its structural
cause: on the transverse plane the reflection is real-diagonalizable and the
rotation provably is not (`RealC3.no_real_eigenvector_transverse`), so the two
maps differ in linear type, not merely in one value.  In `C₂` this distinction
is invisible, because there the nontrivial character *is* the reflection.

## Stage 5c — which operator a carrier actually admits

`Lean/Spine/Duality.lean`.  The rule is that "the X of Y" is earned only by
exhibiting `Y`'s data as an instance of the structure theorem `X` is about, with
the hypotheses checked.  This module settles that question for two candidate
operators on an amounts carrier, one negatively and one positively.

**Negative — no Hamiltonian.**  A Hamiltonian needs a phase space: a
nondegenerate alternating form.  `odd_skew_det_zero` and
`odd_alternating_form_degenerate` show that over `ℝ` every alternating form on a
finite carrier of odd cardinality is degenerate.  Since
`card_tasteDimension = 5`, `taste_carrier_no_symplectic_form` concludes that the
sensory taste carrier admits **no** symplectic structure.  So "the Hamiltonian
of cinnamon in a dish's taste" is not merely unproved here; the structure the
phrase names provably is not present on that carrier.

**Positive — convex duality is available.**

| name | content |
| --- | --- |
| `Duality.conjugate` | the Legendre–Fenchel conjugate `sup_x (⟪y,x⟫ − f x)` of an acceptability functional |
| `Duality.fenchel_young` | `⟪y,x⟫ ≤ f x + f*(y)` whenever the conjugate is finite |
| `Duality.dual_eq_deriv` | **at an interior optimum the dual coordinate *is* the derivative** |
| `Duality.tradeoff_rate` | hence "how much of one ingredient another is worth here" is a ratio of derivatives |
| `Duality.conjugate_eq_of_isMaxOn` | the conjugate is computed by a global optimum |
| `Duality.flat_not_bddAbove` | **the gate**: a flat functional has no finite conjugate in any nonzero direction |

The last row is the duality lane's version of the nondegeneracy gate: constant
preference carries no trade-off information, exactly as a constant channel
carries no transverse area.

## Stage 6 — the discipline: cardinality is not a map

`Lean/Spine/EqualCardinality.lean`.  `exists_two_distinct_equivs`: equinumerous
finite types with at least two elements admit at least two distinct bijections,
so `|A| = |B|` never singles one out.  Only `card_eq_of_equiv` runs the other
way.  `no_structure_preserving_equiv_of_orbit_obstruction` is the general shape
of the refutation used below.

`Lean/Spine/OggGrid.lean` makes this concrete on the fifteen supersingular
("Ogg") primes.  All finite facts are `decide`-checked:

* `grid_subset`: the affine map `(i, j) ↦ 5 + 12i + 42j`, `i < 3`, `j < 2`,
  lands inside the Ogg set — stated as a geometry statement, not a list of
  equalities.  `grid_injective`, `grid_steps`, `steps_sum` (`12 + 42 = 54`).
* `prod_row_one`: `47 · 59 · 71 = 196883`.
* `translation_ne_pointed`: `p ↦ p + 42` is **not** the pointed-sign map
  `p ↦ 2p + 1`; `pointed_preimage_47` records `(47 − 1)/2 = 23`.  The two
  observers stay separated.
* `mode_counts` and `mod_nine_not_uniform`: the residues mod 9 give fibre sizes
  `0,1,4,1,2,4,0,1,2`, not a uniform `5 × 3`.  This is negative evidence against
  forcing `15 = 5 × 3` on the primes.
* `cmClass` (the mod-7 / `ℚ(√−7)` splitting character), `cm_class_counts`
  (`5, 9, 1`), `cm_ramified_unique`.
* `no_free_order_three_cm_preserving` and `no_equivariant_labelling`: **no**
  bijection from the internal `5 × 3` ternary carrier onto the Ogg set turns the
  free ternary shift into a CM-class-preserving permutation.  The fifteen-element
  coincidence therefore does not become an identification.
* `moonshine_nonary_decomposition`: `196883 = 10·3⁹ + 53` and `53 = 5·9 + 8` are
  recorded as decidable arithmetic identities.  The docstring states explicitly
  that they carry no structural weight, because nothing here acts on the pieces.

## Stage 7 — the fixed-locus lane, second customer

`Lean/Spine/FixedLocus.lean`.  For a general involution `σ` on a real vector
space: `symmPart`, `antiPart`, `symm_add_anti`, `σ_symmPart`, `σ_antiPart`,
`fixed_iff_antiPart_zero`.  Instantiated at `s ↦ −conj s` on `ℂ`:

* `re_eq_half_iff : s.re = 1/2 ↔ 1 − s = conj s`;
* `criticalLine_eq_half_add_fixed`: the same as the coset `½ + Fix(−conj)`.

This is a *reuse of the fixed/transverse theorem shape* in a second, independent
lane.  It is a reformulation of a line in the complex plane.  **It says nothing
about the Riemann Hypothesis and asserts no Monster ↔ zeta identification.**

## Stage 8 — the two-regime envelope (gap-free summation)

`Lean/Spine/TwoRegime.lean`.

* `norm_fourier_le_L1` — the `L¹` regime.
* `freq_mul_norm_fourier_le` — the decay regime, via `Real.fourier_deriv`.
* `norm_fourier_le_envelope` — for integrable, differentiable `f` with
  integrable derivative and `ξ ≠ 0`,
  `‖𝓕 f ξ‖ ≤ min (∫‖f‖) ((∫‖f'‖)/(2π|ξ|))`.  Finite as `ξ → 0`, unlike the
  `1/|ξ|` regime alone (`single_regime_unbounded` proves the latter admits no
  finite constant).
* `sum_envelope_le` — over a finite point set inside `|x| < M` with at most `N`
  points per unit window, `∑ envelope ≤ N·K₀ + N·K₁·∑_{m=1}^{M−1} 1/m`.
  **No minimum-separation hypothesis appears anywhere in this statement.**

This delivers the requested mechanism — replace a uniform gap `δ > 0` by local
counts plus kernel decay — as an abstract, reusable theorem.

## Stage 9 — the end-to-end receipt

`Lean/Spine/EndToEnd.lean` defines `SpineLedger`, a record whose fields *are* the
statements above (not Booleans, not placeholders), and `spineLedger : SpineLedger`
discharges every field from the corresponding theorem.  Nothing in it can be
satisfied by a token.

---

# Frontier: what is *not* proved

This section is deliberately blunt.

1. **The Agda side of this tranche is unchecked here.**  Agda is not installed in
   this environment, so no `.agda` file in `Agda/` was typechecked during this
   session.  The `Spine` results are Lean-only.  Mirroring them into Agda is an
   open task, and any claim about the Agda kernel status of the corpus should be
   treated as unverified by this session.

2. **The prime side of the zeta lane is entirely absent from this cutset.**
   There is no matrix `G`, no explicit-formula bridge, and no prime-side error
   term in this project.  Consequently the target
   `∑ m_ρ² Δ_ρ ≤ E_prime(T) + E_tail(T) + E_mixed(T)` is *not* stated, let alone
   proved.  `Spine.TwoRegime` supplies only the abstract envelope and the
   abstract gap-free summation; connecting them to zeta ordinates would require
   (a) a local zero-counting input and (b) a concrete kernel with the two
   integrability hypotheses discharged.  Neither exists here.

3. **`det_gram_anchored_ge` is proved by cofactor expansion, not through
   exterior algebra.**  The inequality is exactly the stated one, but the
   accompanying sentence "the two summands lie in orthogonal exterior sectors"
   is *motivation* in this project, not a formalized statement.  An
   `⋀^k`-level version is open.

4. **The five "Monster" transverse planes are conditional on supplied
   witnesses.**  `monster_five_transverse_planes` takes the anchor and channel
   data and the two nondegeneracy hypotheses as inputs.  It does *not* construct
   them from any Monster-specific object in the corpus.  Producing genuine
   per-mode anchor/channel data from the existing Monster modules, and
   discharging `avg ≠ 0` and `fluct ≠ 0` for it, is the exact remaining
   obligation before "five actual planes in the Monster lane" is earned.
   By contrast `Spine.TritCarrier` *does* start from an object already in the
   project (`Trit`, `Trit.inv`, `rotTrit`) and proves the equivariance, so that
   link is earned rather than assumed — but the witnesses there are still
   hypotheses on the supplied weightings, not theorems about a particular one.

5. **Likewise for cuisine.**  `Cuisine.taste_plane_pos` is a real instance built
   on the project's real `SensoryProfile`, but the witnesses are hypotheses on
   the profiles supplied, not theorems about any particular dish.  The
   cross-domain transfer claim is exactly: *the taste carrier and the ternary
   mode carrier map into the same structure, so the same theorem applies to
   both.*  It is not a claim that cuisine and the Monster are related.

6. **`53 / 54 / 56 / 64` remain arithmetic.**  `moonshine_nonary_decomposition`
   checks the identities and nothing more.  No action or observer attaches to
   the pieces in this project, so they carry no structural weight, exactly as the
   docstring says.

7. **The duality lane stops short of biconjugation.**  `Duality.conjugate` is
   defined and Fenchel–Young is proved, but the Fenchel–Moreau theorem
   (`f** = f` for a proper convex lower-semicontinuous `f`) is *not* proved
   here, and Mathlib as pinned by this project does not supply it.  Nor is
   convexity anywhere assumed: the results above hold for an arbitrary
   functional, which is why `dual_eq_deriv` needs a local maximum as an explicit
   hypothesis rather than deriving one.

8. **Two of the operator lanes named in the request are absent.**  Neither
   Perron–Frobenius (a nonnegative matrix has a dominant eigenvector with
   positive entries) nor a Hecke-style commuting family of averaging operators
   is present in this project, and neither is available in Mathlib as pinned
   here.  Building them is open work.  In particular, no claim of the form "the
   Perron–Frobenius of X" or "the Hecke of X" is supported by anything in this
   repository.

9. **No physical or metaphysical claim is made.**  Nothing here is a theory of
   everything.  What is proved is a small pile of elementary linear algebra,
   representation theory of `C₃`, cyclotomic arithmetic, finite decidable facts
   about fifteen primes, two Fourier estimates and some elementary convex
   duality — together with an interface that makes the reuse across lanes
   explicit and the degenerate cases visible.

## The standing rule

No identification enters the spine without an explicit map plus a nondegeneracy
obligation appropriate to the theorem being transferred.  Where the map does not
exist, the corpus records the refutation instead
(`no_equivariant_labelling`, `translation_ne_pointed`, `mod_nine_not_uniform`,
`exists_two_distinct_equivs`).  Where the instance is degenerate, the corpus
records that the inherited theorem is empty
(`degenerate_observer_area_zero`, `flat_profile_degenerate`,
`single_regime_unbounded`).

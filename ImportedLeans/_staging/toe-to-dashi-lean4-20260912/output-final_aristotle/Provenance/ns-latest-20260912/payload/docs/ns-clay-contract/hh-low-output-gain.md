# The `HH→low` leaf: exact multiplier geometry, transverse gain, collinear cancellation

*Lean source:* `RequestProject/NavierStokes/WaleffeHighHighOutputGain.lean`
(builds with the rest of the tree; no `sorry`, no postulates, no added axioms;
every headline theorem was checked to depend only on `propext`,
`Classical.choice`, `Quot.sound`).

This note continues `external-residue-bony-classes.md`.  It attacks the
`HH→low` leaf of the classwise payment — the near-diagonal class `a ≈ k − a`,
where the raw convolution multiplicity is worst — instead of a generic Schur
summability statement.  The whole file works on the shared output fibre
`a + q = k`, `q = k − a`, `q − a = k − 2a`.

## 1. The exact algebra of the multiplier difference

Everything below is derived from two polynomial identities on the integer
lattice, both proved from scratch:

* `wcrossSq_eq` — the **Lagrange identity** `|x × y|² = |x|²|y|² − ⟨x,y⟩²`.  The
  Cauchy–Schwarz inequality `wdot_sq_le` used later is *derived* from it, so no
  analytic square-root input is assumed anywhere.
* `sq_gap_add_crossSq_eq` — the **square-gap identity** on a fibre `a + q = k`:

  ```
  (|q|² − |a|²)² + |k × (q − a)|² = |k|² ( 2|a|² + 2|q|² − |k|² ).
  ```

  (Lagrange for `(k, q − a)` plus the parallelogram law `wsq_sub_partner`.)

From these:

* `gap_mul_sum_eq_abs_wdot` — the **division-free exact gap identity**

  ```
  | |q| − |a| | · ( |a| + |q| ) = | ⟨k, q − a⟩ | .
  ```

  Both sides are exact; no inequality, no absolute value inside, no cardinality.
* `abs_wlen_sub_le_output_of_square_gap` — the literal **unsquared** estimate
  `| |q| − |a| | ≤ |k|`, obtained from the square-gap identity and the
  Lagrange-derived Cauchy–Schwarz inequality (not from the triangle
  inequality), and `abs_helicity_gap_le_output_of_square_gap`, its co-helical
  form `|λ_q − λ_a| ≤ |k|`.

## 2. The `HH→low` refinement

On the class `|k| ≤ θ min(|a|, |k − a|)`:

* `hhlow_gap_mul_le` (division-free):

  ```
  | |k−a| − |a| | · ( (2 − θ) |a| )  ≤  θ |k| |a| + 2 |⟨k, a⟩| .
  ```

  The first term is a full factor `θ` below the trivial bound `|k| · |a|`; the
  second is purely the **alignment** of the output with the leg.
* `hhlow_gap_le_div` — the divided form
  `| |k−a| − |a| | ≤ ( θ|k| + 2|⟨k,a⟩|/|a| ) / (2 − θ)`.
* `hhlow_gap_le_of_transverse` — if the leg is `ε`-transverse to the output,
  `|⟨k,a⟩| ≤ ε|k||a|`, then `| |k−a| − |a| | ≤ ((θ + 2ε)/(2 − θ)) |k|`.

## 3. Classwise payment of the signed `HH→low` residue

* `abs_bonyCells_HHlow_alignment_le` — unconditional, with the exact weight:

  ```
  |R^{HH→low}_{p,q}| ≤ (1/(2(2−θ))) ∑_a ( θ|k| + 2|⟨k,a⟩|/|a| ) ‖u_a‖‖u_{k−a}‖ ‖u_p‖‖u_q‖ .
  ```

* `abs_bonyCells_HHlow_transverse_le` (and its Galerkin-carrier form in
  `ClayNS.Waleffe.GalerkinFlow`) — under `ε`-transversality of the class,

  ```
  |R^{HH→low}_{p,q}| ≤ ((θ + 2ε)/(2(2 − θ))) · |k| · E(t) · ‖u_p‖‖u_q‖ ,
  ```

  cutoff-uniformly.  The fibre sum is estimated by Cauchy–Schwarz in `ℓ²`
  (`sum_pair_nrm_le_energy`): there is no Wiener `ℓ¹` factor, no
  convolution-fibre cardinality, no shell count and no matching hypothesis.

## 4. The extremal incidences pay nothing

The bound `| |k−a| − |a| | ≤ |k|` is saturated exactly at the **collinear**
incidences `a ∥ k`.  Those contribute nothing at all:

* `leray_cross_eq_zero_of_orthogonal` — the Leray projector at `k` annihilates
  the cross product of two vectors transverse to `k` (`k × (v × w) =
  v⟨k,w⟩ − w⟨k,v⟩`, formalised componentwise).
* `herm_wC_eq_zero_of_collinear` — a nonzero leg collinear with `k` is, by
  incompressibility, transverse to `k`.
* `crossCell_partner_sum_eq_zero_of_collinear`, and its Galerkin-carrier form —
  hence the partner sum of the two quartic cells `a`, `k − a` **vanishes
  identically** for a collinear incidence.  This is an identity, not an
  estimate.

## 4b. The quantitative form of that cancellation

The vanishing is the endpoint of an estimate.  With `outTrans k a` the length of
the component of `k` orthogonal to the direction `a`:

* `abs_herm_wC_le_of_transverse` — an incompressible leg only sees the
  transverse part of the output: `|⟨k, u_a⟩| ≤ outTrans k a · ‖u_a‖`.
* `wlen_mul_nrm_leray_cross_le` — `|k|·‖P_k(v × w)‖ ≤ |⟨k,w⟩|‖v‖ + |⟨k,v⟩|‖w‖`
  (from the BAC–CAB identity `cross_wC_cross` and the Lagrange identity).
* `wlen_mul_nrm_leray_cross_le_outTrans` — hence, for incompressible legs,
  `|k|·‖P_k(u_a × u_b)‖ ≤ (outTrans k a + outTrans k b)‖u_a‖‖u_b‖`.
* `abs_crossCell_partner_sum_angular_le` — so the partner sum of the two quartic
  cells carries the **angular profile**

  ```
  |R_a + R_{k−a}| ≤ ( |λ_{k−a} − λ_a| · (outTrans k a + outTrans k (k−a)) / |k| )
                      ‖u_a‖‖u_{k−a}‖‖u_p‖‖u_q‖ .
  ```

## 5. What this does not close

The classwise bounds of §3 still bound each cell and sum absolute values inside
the class, so they are energy/enstrophy level, not critical (`H^{1/2}`).  The
open package A2 — a cutoff-independent critical payment of the complete
*signed* sum over the pairs `(p,q)` — is untouched.  What is new is that on
`HH→low` the commutator multiplier is now an exact algebraic object with an
explicit low-output/transverse decomposition, and that its extremal
configuration is exactly cancelled by the projector.

A caveat recorded honestly, and flagged as an **unverified heuristic** (it is
not a theorem in the Lean tree): the two factors of the angular profile of §4b
pull in opposite directions — the gap is largest for nearly collinear
incidences, exactly where the projected cross product is smallest — and a
back-of-the-envelope evaluation of the profile suggests that their product is
again of size `|k|` at intermediate angles.  On that reading the
ε-transversality hypothesis of `abs_bonyCells_HHlow_transverse_le` is a genuine
hypothesis rather than a removable one, and the remaining `HH→low` difficulty
sits on the intermediate-angle incidences.  Nothing in the formalisation
depends on this reading.

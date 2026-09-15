/-
# R571 Gate-A paired second moment on a real carrier: the radial half is paid,
the state half is the residual.

## Lane

Lane **B** (unforced periodic `T³`).  No transport to lane A, no use of the
released forced C/D material.

## Source → carrier → consumer

* **Agda owner (source).**
  `DASHI.Physics.Closure.NSTriadKNLuoCenteredPairedCommutatorIdentityExact`
  proves the exact paired identity
  `(a₋-a₀)g₋ + (a₊-a₀)g₊ = (a₋-2a₀+a₊)g₋ + (a₊-a₀)(g₊-g₋)`
  over `ℚ`, and
  `DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact`
  turns the four envelopes `A1, G2, A2, G1` into the pointwise and finite-family
  bound with coefficient `A1·G2 + A2·G1 + A2·G1`.
  `DASHI.Physics.Closure.NSTriadKNR571PhysicalSecondMomentEnvelopeSplitExact`
  splits those four into a *radial* pair `(A1, A2)` and a *state* pair
  `(G2, G1)` and records
  `r571RadialTaylorEnvelopeConstructedHere = false`,
  `r571StateDerivativeEnvelopeConstructedHere = false`.

* **Lean carrier (here).**  The identity and the second-moment budget are
  re-proved over `ℝ` — the Agda owners are rational-arithmetic carriers, so they
  cannot be consumed by a real analytic estimate as they stand — and the radial
  pair is then *discharged* rather than assumed, using
  `RequestProject.NavierStokes.R571RadialCurvature`.

* **Consumer.**  `r571_pairedSecondMoment_of_stateEnvelope` and its finite-family
  form `r571_finite_pairedSecondMoment_of_stateEnvelope` are the Lean analogue of
  `compiledFiniteSecondMomentBound`, but with `A1 = A2 = 1` *proved* instead of
  hypothesised.

## Status

Paid here: the two radial Gate-A leaves, with cutoff-uniform constants.
**Not paid here:** the two state-side leaves `G1` (`|g±| ≤ G1`) and `G2`
(`|g₊-g₋| ≤ |y| G2`).  They are genuine analytic obligations on the transported
high-frequency field and are carried as explicit hypotheses, named
`StateDerivativeEnvelope`.  Nothing in this file closes R568, the A1 spacetime
budget, or periodic regularity, and nothing claims to.
-/
import RequestProject.NavierStokes.R571RadialCurvature

noncomputable section

namespace RequestProject.NavierStokes.R571

open DASHI.NS.Unforced Finset

/-! ## The exact paired identity, over `ℝ` -/

/-- **The centred paired-commutator identity** of the Agda owner
`NSTriadKNLuoCenteredPairedCommutatorIdentityExact`, transported to `ℝ`.  It is
an identity, not an estimate: the signed structure is intact on both sides. -/
theorem paired_commutator_identity (aMinus aCenter aPlus gMinus gPlus : ℝ) :
    (aMinus - aCenter) * gMinus + (aPlus - aCenter) * gPlus
      = (aMinus - (aCenter + aCenter) + aPlus) * gMinus
        + (aPlus - aCenter) * (gPlus - gMinus) := by
  ring

/-- The weighted form, matching `weightedPairedCommutatorIdentity`. -/
theorem weighted_paired_commutator_identity (w aMinus aCenter aPlus gMinus gPlus : ℝ) :
    w * ((aMinus - aCenter) * gMinus + (aPlus - aCenter) * gPlus)
      = w * ((aMinus - (aCenter + aCenter) + aPlus) * gMinus)
        + w * ((aPlus - aCenter) * (gPlus - gMinus)) := by
  ring

/-- The finite-family form, matching `finiteWeightedPairedCommutatorIdentity`. -/
theorem finite_weighted_paired_commutator_identity {ι : Type*} (s : Finset ι)
    (w aMinus aCenter aPlus gMinus gPlus : ι → ℝ) :
    ∑ i ∈ s, w i * ((aMinus i - aCenter i) * gMinus i + (aPlus i - aCenter i) * gPlus i)
      = (∑ i ∈ s, w i * ((aMinus i - (aCenter i + aCenter i) + aPlus i) * gMinus i))
        + ∑ i ∈ s, w i * ((aPlus i - aCenter i) * (gPlus i - gMinus i)) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => weighted_paired_commutator_identity _ _ _ _ _ _

/-! ## The abstract second-moment budget, over `ℝ` -/

/-- **Pointwise second-moment bound** (real-carrier form of
`pointwisePairedSecondMomentBound`).  With the four envelopes
`|L| ≤ y·A1`, `|Δg| ≤ y·G2`, `|R±| ≤ y²·A2`, `|g±| ≤ G1`, the paired magnitude
costs two displacements. -/
theorem paired_second_moment_pointwise
    {w y ell dg rPlus rMinus gPlus gMinus a1 a2 g1 g2 : ℝ}
    (hw : 0 ≤ w) (hy : 0 ≤ y)
    (hdg : 0 ≤ dg) (hgp : 0 ≤ gPlus) (hgm : 0 ≤ gMinus)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hL : ell ≤ y * a1) (hDg : dg ≤ y * g2)
    (hRp : rPlus ≤ y * y * a2) (hRm : rMinus ≤ y * y * a2)
    (hGp : gPlus ≤ g1) (hGm : gMinus ≤ g1) :
    w * (ell * dg + rPlus * gPlus + rMinus * gMinus)
      ≤ w * (y * y) * (a1 * g2 + a2 * g1 + a2 * g1) := by
  have h1 : ell * dg ≤ (y * a1) * (y * g2) :=
    mul_le_mul hL hDg hdg (by positivity)
  have h2 : rPlus * gPlus ≤ (y * y * a2) * g1 :=
    mul_le_mul hRp hGp hgp (by positivity)
  have h3 : rMinus * gMinus ≤ (y * y * a2) * g1 :=
    mul_le_mul hRm hGm hgm (by positivity)
  have hsum : ell * dg + rPlus * gPlus + rMinus * gMinus
      ≤ (y * y) * (a1 * g2 + a2 * g1 + a2 * g1) := by nlinarith
  calc w * (ell * dg + rPlus * gPlus + rMinus * gMinus)
      ≤ w * ((y * y) * (a1 * g2 + a2 * g1 + a2 * g1)) :=
        mul_le_mul_of_nonneg_left hsum hw
    _ = w * (y * y) * (a1 * g2 + a2 * g1 + a2 * g1) := by ring

/-! ## The R571 realization: the radial pair is discharged -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **state-side** half of the Gate-A envelope split, i.e. the two leaves
this development does *not* pay: a uniform amplitude bound `G1` and a
Lipschitz-in-displacement bound `G2` on the transported high-frequency field.
These are analytic obligations on the solution, not geometry. -/
structure StateDerivativeEnvelope (g1 g2 : ℝ) (gPlus gMinus : ℝ) (y : ℝ) : Prop where
  g1_nonneg : 0 ≤ g1
  g2_nonneg : 0 ≤ g2
  plus_le : |gPlus| ≤ g1
  minus_le : |gMinus| ≤ g1
  difference_le : |gPlus - gMinus| ≤ y * g2

/-- **The R571 paired second-moment payment, with the radial leaves discharged.**

For the homochiral R571 multiplier `m_σ(k) = σ‖k‖` at a periodic centre mode
(`‖k‖ ≥ 1`), with the preferred Taylor model (the `+y` increment itself, so the
`+` remainder is exactly zero), the paired magnitude of one cell obeys

`w·(|L||Δg| + |R₋||g₋|) ≤ w‖y‖²·(G2 + G1)`,

where only `G1` and `G2` are hypotheses.  Both radial constants are the absolute
constant `1`: `A1 = 1` by `abs_radialIncrement_le` and `A2 = 1` by
`abs_centeredRadialDefect_le_of_one_le_norm`.  In particular the bound does not
see the Galerkin cutoff. -/
theorem r571_pairedSecondMoment_of_stateEnvelope
    (s : HelicitySign) {k y : E} {w g1 g2 gPlus gMinus : ℝ}
    (hw : 0 ≤ w) (hk : 1 ≤ ‖k‖)
    (hstate : StateDerivativeEnvelope g1 g2 gPlus gMinus ‖y‖) :
    w * (|radialSymbol s (k + y) - radialSymbol s k| * |gPlus - gMinus|
          + |centeredRadialDefect s k y| * |gMinus|)
      ≤ w * (‖y‖ * ‖y‖) * (g2 + g1) := by
  have hy : (0:ℝ) ≤ ‖y‖ := norm_nonneg y
  have hA1 : |radialSymbol s (k + y) - radialSymbol s k| ≤ ‖y‖ * 1 := by
    simpa using abs_radialIncrement_le s k y
  have hA2 : |centeredRadialDefect s k y| ≤ ‖y‖ * ‖y‖ * 1 := by
    have := abs_centeredRadialDefect_le_of_one_le_norm s y hk
    nlinarith [abs_nonneg (centeredRadialDefect s k y)]
  have hterm1 : |radialSymbol s (k + y) - radialSymbol s k| * |gPlus - gMinus|
      ≤ (‖y‖ * ‖y‖) * g2 := by
    have := mul_le_mul hA1 hstate.difference_le (abs_nonneg _) (by positivity)
    nlinarith
  have hterm2 : |centeredRadialDefect s k y| * |gMinus| ≤ (‖y‖ * ‖y‖) * g1 := by
    have := mul_le_mul hA2 hstate.minus_le (abs_nonneg _) (by positivity)
    nlinarith
  have hsum : |radialSymbol s (k + y) - radialSymbol s k| * |gPlus - gMinus|
      + |centeredRadialDefect s k y| * |gMinus| ≤ (‖y‖ * ‖y‖) * (g2 + g1) := by
    nlinarith
  calc w * (|radialSymbol s (k + y) - radialSymbol s k| * |gPlus - gMinus|
          + |centeredRadialDefect s k y| * |gMinus|)
      ≤ w * ((‖y‖ * ‖y‖) * (g2 + g1)) := mul_le_mul_of_nonneg_left hsum hw
    _ = w * (‖y‖ * ‖y‖) * (g2 + g1) := by ring

/-- **Finite-family form.**  Summed over a Galerkin-truncated family of cells,
the same payment holds with the *same* constants: the coefficient `g2 + g1`
carries no index and no cutoff. -/
theorem r571_finite_pairedSecondMoment_of_stateEnvelope {ι : Type*} (fam : Finset ι)
    (sgn : ι → HelicitySign) (kv yv : ι → E) (w gPlus gMinus : ι → ℝ) {g1 g2 : ℝ}
    (hw : ∀ i ∈ fam, 0 ≤ w i) (hk : ∀ i ∈ fam, 1 ≤ ‖kv i‖)
    (hstate : ∀ i ∈ fam, StateDerivativeEnvelope g1 g2 (gPlus i) (gMinus i) ‖yv i‖) :
    ∑ i ∈ fam, w i *
        (|radialSymbol (sgn i) (kv i + yv i) - radialSymbol (sgn i) (kv i)|
            * |gPlus i - gMinus i|
          + |centeredRadialDefect (sgn i) (kv i) (yv i)| * |gMinus i|)
      ≤ (g2 + g1) * ∑ i ∈ fam, w i * (‖yv i‖ * ‖yv i‖) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have h := r571_pairedSecondMoment_of_stateEnvelope (sgn i) (hw i hi) (hk i hi) (hstate i hi)
  calc _ ≤ w i * (‖yv i‖ * ‖yv i‖) * (g2 + g1) := h
    _ = (g2 + g1) * (w i * (‖yv i‖ * ‖yv i‖)) := by ring

/-- **Non-vacuity of the reduction.**  The hypotheses of
`r571_pairedSecondMoment_of_stateEnvelope` are simultaneously satisfiable with a
strictly positive left-hand side, so the theorem is not an empty implication:
take `k = 1`, `y = 2` on `ℝ`, `g₊ = 1`, `g₋ = -1`, `G1 = 1`, `G2 = 1`. -/
theorem r571_pairedSecondMoment_nonvacuous :
    StateDerivativeEnvelope 1 1 (1 : ℝ) (-1) ‖(2 : ℝ)‖ ∧
      0 < (1 : ℝ) * (|radialSymbol HelicitySign.plus ((1:ℝ) + 2)
            - radialSymbol HelicitySign.plus (1:ℝ)| * |(1:ℝ) - (-1)|
          + |centeredRadialDefect HelicitySign.plus (1:ℝ) (2:ℝ)| * |(-1:ℝ)|) := by
  constructor
  · refine ⟨zero_le_one, zero_le_one, by norm_num, by norm_num, ?_⟩
    norm_num
  · norm_num [radialSymbol, centeredRadialDefect, HelicitySign.signedRadius]

end RequestProject.NavierStokes.R571

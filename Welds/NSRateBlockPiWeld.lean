/-
# NS ⟶ Spine weld: the lane's Gram carrier *is* the Euclidean one

`RequestProject.NavierStokes.SpineRateBlockAdapter` (donor payload, preserved
under `Provenance/ns-latest-20260912/`) routes the Navier–Stokes rate-block Gram
consumer through the domain-neutral scalar kernel
`Spine.RateBlockSchur.schur_form_le_blockMultiplicity`, and records one seam it
deliberately does **not** repair:

> `Spine.RateBlockSchur.schur_gram_le_blockMultiplicity` … is stated for `E` with
> `[NormedAddCommGroup E] [InnerProductSpace ℂ E]` … The NS cells live in
> `Fin 3 → ℂ` carrying Mathlib's **sup-norm** `Pi` instance … So that instance
> does **not** apply to the NS carrier … Repairing the mismatch would mean
> transporting the lane to `EuclideanSpace ℂ (Fin 3)`, which is a separate (and
> much larger) refactor of every NS file.

`Spine.RateBlockSchurPiCarrier` owns the transport that the seam is about
(`hermPi_eq_inner`, `nrmPi_eq_norm`: the plain-carrier pairing and mass *are* the
`EuclideanSpace ℂ (Fin n)` inner product and norm, along `WithLp.toLp 2`).  This
module is the weld between the two: it shows the identification applies to the
NS lane **on the nose**, with no refactor of any NS file, and re-pays the literal
consumer through the inner-product route.

What is established here:

* `herm_eq_hermPi`, `nsq_eq_nsqPi`, `nrm_eq_nrmPi` — the lane's `herm`/`nsq`/`nrm`
  and the Spine carrier's `hermPi`/`nsqPi`/`nrmPi` are the *same functions*
  (`rfl`); this is what makes the weld free;
* `ns_herm_eq_euclidean_inner`, `ns_nrm_eq_euclidean_norm` — hence the NS
  Hermitian form and Euclidean mass are literally the `EuclideanSpace ℂ (Fin 3)`
  inner product and norm.  **This is the seam above, closed**: the sup-norm `Pi`
  instance is simply never used, so no transport of the lane is required;
* `gramOperatorBound_of_pair_estimate` — the missing *factorisation* step.  The
  donor proved the consumer twice (once in `RateBlockGramBound`, once in
  `SpineRateBlockAdapter`) by repeating the same viscous-rate massaging inline.
  Here that massaging is isolated once, as a lemma taking the pair estimate as
  its hypothesis, so any producer of the pair estimate pays the consumer;
* `sum_resForm_le_blockMultiplicity_viaPi` — the pair estimate obtained from the
  *inner-product* Spine carrier (`schur_gramPi_le_blockMultiplicity`), i.e.
  without the lane's hand-supplied Cauchy–Schwarz;
* `gramOperatorBound_viaPiCarrier` — the literal consumer
  `ClayNS.Schur.GramOperatorBound nu modes G k (32·m)`, paid along that route;
* `spineAdapter_consumer_refactored` and `gramOperatorBound_routes_agree` — the
  three routes (lane-private, scalar Spine adapter, Euclidean Pi carrier) prove
  the same proposition, and the adapter's own consumer theorem is re-derived
  from the factorisation lemma, so the repetition is redundant rather than
  merely parallel.

Status discipline.  Everything here is a proved Lean theorem about finite sums
over a `Finset Wave` of cells in `Fin 3 → ℂ`.  The bound is the
cancellation-free one and still degrades linearly in the block multiplicity
(`Spine.RateBlockSchur.schur_form_ge_half_mul_multiplicity`,
`ClayNS.RateBlocks.gramOperatorBound_fails_on_comparable_shells`).  No Clay
obligation is closed here and none is claimed; the open payments of the lane
(truncation-uniform constant from signed cancellation,
`NestedSlotClassNormPayment584`, the outer-spectator seam) are untouched.
-/
import Spine.RateBlockSchurPiCarrier
import RequestProject.NavierStokes.SpineRateBlockAdapter

noncomputable section

namespace Welds.NSRateBlockPi

open ClayNS.Waleffe ClayNS.Resolvent ClayNS.Schur ClayNS.RateBlocks
open Spine.RateBlockSchurPi

/-! ## 1.  The lane's pairing and mass are the Spine carrier's -/

/-- The NS lane's Hermitian pairing **is** the Spine plain-carrier pairing. -/
theorem herm_eq_hermPi (u v : Fin 3 → ℂ) : herm u v = hermPi u v := rfl

/-- The NS lane's Euclidean mass **is** the Spine plain-carrier mass. -/
theorem nsq_eq_nsqPi (u : Fin 3 → ℂ) : nsq u = nsqPi u := rfl

/-- The NS lane's norm **is** the Spine plain-carrier norm. -/
theorem nrm_eq_nrmPi (u : Fin 3 → ℂ) : nrm u = nrmPi u := rfl

/-! ## 2.  The documented carrier mismatch, closed -/

/-- **Seam closed.**  The NS Hermitian form is the `EuclideanSpace ℂ (Fin 3)`
inner product, transported along `WithLp.toLp 2`.  No NS file changes: the
sup-norm `Pi` instance on `Fin 3 → ℂ` plays no role in either side. -/
theorem ns_herm_eq_euclidean_inner (u v : Fin 3 → ℂ) :
    (inner ℂ (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin 3)) (WithLp.toLp 2 v) : ℂ) = herm u v :=
  hermPi_eq_inner u v

/-- **Seam closed, mass half.**  The NS norm is the `EuclideanSpace ℂ (Fin 3)`
norm under the same transport. -/
theorem ns_nrm_eq_euclidean_norm (u : Fin 3 → ℂ) :
    ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin 3))‖ = nrm u := nrmPi_eq_norm u

/-- Consequently the lane's Cauchy–Schwarz step is an instance of the Spine
transport rather than a private argument. -/
theorem ns_herm_re_le_nrm_mul_ofCarrier (u v : Fin 3 → ℂ) :
    (herm u v).re ≤ nrm u * nrm v := hermPi_re_le_nrmPi_mul u v

/-! ## 3.  The missing factorisation: consumer from any pair estimate -/

/-- **The consumer, factored.**  Any producer of the rate-block pair estimate at
`lam p = viscousPairRate nu p (k - p)` pays `GramOperatorBound … (32·m)`.  The
donor repeated this viscous-rate massaging inline in two modules; isolating it
here makes each producer a one-line consumer weld. -/
theorem gramOperatorBound_of_pair_estimate {nu : ℝ} {m : ℕ} (hnu : 0 < nu)
    (modes : Finset Wave) (G : Wave → Fin 3 → ℂ) (k : Wave)
    (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hmain : ∑ p ∈ modes, ∑ q ∈ modes,
        (herm (G p) (G q)).re / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))
      ≤ 16 * m * ∑ p ∈ modes, nsq (G p) / viscousPairRate nu p (k - p)) :
    GramOperatorBound nu modes G k (32 * m) := by
  classical
  have hmass : ∑ p ∈ modes, nsq (G p) / viscousPairRate nu p (k - p)
      ≤ (∑ p ∈ modes, nsq (G p) / wsq p) / nu := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun p hpm => ?_
    have hwp : 0 < wsq p := lt_of_le_of_ne (wsq_nonneg' p) (Ne.symm (hp p hpm))
    have hkp : 0 ≤ wsq (k - p) := wsq_nonneg' (k - p)
    have hrate : wsq p * nu ≤ viscousPairRate nu p (k - p) := by
      rw [viscousPairRate]
      nlinarith
    have hrpos : 0 < wsq p * nu := by positivity
    rw [div_div]
    exact div_le_div_of_nonneg_left (nsq_nonneg _) hrpos hrate
  have hmnn : (0 : ℝ) ≤ 16 * m := by positivity
  have hchain := hmain.trans (mul_le_mul_of_nonneg_left hmass hmnn)
  have heq : (16 : ℝ) * m * ((∑ p ∈ modes, nsq (G p) / wsq p) / nu)
      = 32 * m * (∑ p ∈ modes, nsq (G p) / wsq p) / (2 * nu) := by
    field_simp
    ring
  show ∑ p ∈ modes, ∑ q ∈ modes,
      (herm (G p) (G q)).re
        / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))
    ≤ 32 * m * (∑ p ∈ modes, nsq (G p) / wsq p) / (2 * nu)
  rw [← heq]
  exact hchain

/-! ## 4.  The pair estimate from the Euclidean carrier -/

/-- The NS pair estimate, produced by the **inner-product** Spine carrier: the
Cauchy–Schwarz input is the Euclidean transport, not a lane-local lemma. -/
theorem sum_resForm_le_blockMultiplicity_viaPi {lam : Wave → ℝ} {blk : Wave → ℤ} {m : ℕ}
    (modes : Finset Wave) (G : Wave → Fin 3 → ℂ)
    (hblk : Spine.RateBlockSchur.DyadicRateBlocks lam modes blk)
    (hm : Spine.RateBlockSchur.BlockMultiplicity modes blk m) :
    ∑ p ∈ modes, ∑ q ∈ modes, (herm (G p) (G q)).re / (lam p + lam q)
      ≤ 16 * m * ∑ p ∈ modes, nsq (G p) / lam p :=
  schur_gramPi_le_blockMultiplicity modes G hblk hm

/-- **The literal consumer, paid through the Euclidean carrier.**  Same
proposition as `ClayNS.RateBlocks.gramOperatorBound_of_rateBlockMultiplicity` and
as the donor adapter's `…_ofSpine`, but the only analytic input is the
`EuclideanSpace ℂ (Fin 3)` structure owned by `Spine.RateBlockSchurPiCarrier`. -/
theorem gramOperatorBound_viaPiCarrier {nu : ℝ} {m : ℕ} (hnu : 0 < nu)
    (modes : Finset Wave) (G : Wave → Fin 3 → ℂ) (k : Wave) (blk : Wave → ℤ)
    (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hblk : Spine.RateBlockSchur.DyadicRateBlocks
      (fun p => viscousPairRate nu p (k - p)) modes blk)
    (hm : Spine.RateBlockSchur.BlockMultiplicity modes blk m) :
    GramOperatorBound nu modes G k (32 * m) :=
  gramOperatorBound_of_pair_estimate hnu modes G k hp
    (sum_resForm_le_blockMultiplicity_viaPi modes G hblk hm)

/-- The donor adapter's consumer theorem, **re-derived from the factorisation
lemma**: its inline massaging is redundant, not parallel. -/
theorem spineAdapter_consumer_refactored {nu : ℝ} {m : ℕ} (hnu : 0 < nu)
    (modes : Finset Wave) (G : Wave → Fin 3 → ℂ) (k : Wave) (blk : Wave → ℤ)
    (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hblk : Spine.RateBlockSchur.DyadicRateBlocks
      (fun p => viscousPairRate nu p (k - p)) modes blk)
    (hm : Spine.RateBlockSchur.BlockMultiplicity modes blk m) :
    GramOperatorBound nu modes G k (32 * m) :=
  gramOperatorBound_of_pair_estimate hnu modes G k hp
    (ClayNS.SpineAdapter.sum_resForm_le_blockMultiplicity_ofSpine modes G hblk hm)

/-- All three routes — the lane's private kernel, the donor's scalar Spine
adapter, and the Euclidean Pi carrier — prove the *same* proposition, so the
consumer may be paid by any of them and two of the three copies of the argument
can be retired. -/
theorem gramOperatorBound_routes_agree {nu : ℝ} {m : ℕ} (hnu : 0 < nu)
    (modes : Finset Wave) (G : Wave → Fin 3 → ℂ) (k : Wave) (blk : Wave → ℤ)
    (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hblk : ClayNS.RateBlocks.DyadicRateBlocks
      (fun p => viscousPairRate nu p (k - p)) modes blk)
    (hm : ClayNS.RateBlocks.BlockMultiplicity modes blk m) :
    GramOperatorBound nu modes G k (32 * m)
      ∧ GramOperatorBound nu modes G k (32 * m)
      ∧ GramOperatorBound nu modes G k (32 * m) :=
  ⟨ClayNS.RateBlocks.gramOperatorBound_of_rateBlockMultiplicity hnu modes G k blk hp hblk hm,
   ClayNS.SpineAdapter.gramOperatorBound_of_rateBlockMultiplicity_ofSpine hnu modes G k blk hp
     ((ClayNS.SpineAdapter.spine_dyadicRateBlocks_iff _ _ _).mp hblk)
     ((ClayNS.SpineAdapter.spine_blockMultiplicity_iff _ _ _).mp hm),
   gramOperatorBound_viaPiCarrier hnu modes G k blk hp
     ((ClayNS.SpineAdapter.spine_dyadicRateBlocks_iff _ _ _).mp hblk)
     ((ClayNS.SpineAdapter.spine_blockMultiplicity_iff _ _ _).mp hm)⟩

end Welds.NSRateBlockPi

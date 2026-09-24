/-
# NS ⟶ Spine adapter: the outer-cell Gram bound factors through the Spine kernel

The 2026-09-12 TOE overlay ships `Lean/Spine/RateBlockSchur.lean`, a
**domain-neutral** Lean development of the dyadic rate-block Schur test over an
arbitrary index type.  Its headline theorem

```
Spine.RateBlockSchur.schur_form_le_blockMultiplicity :
  DyadicRateBlocks lam S blk → BlockMultiplicity S blk m →
  (∀ p ∈ S, ∀ q ∈ S, a p q ≤ n p * n q) →
  ∑_{p,q∈S} a p q / (lam p + lam q) ≤ 16 · m · ∑_{p∈S} (n p)² / lam p
```

is exactly the mathematical core that the Navier–Stokes lane had developed
separately, at `ι = Wave`, inside
`RequestProject.NavierStokes.RateBlockGramBound`.  This file is the adapter:
it re-derives the NS-lane statements **from the Spine carrier**, so that the
literal NS consumer `GramOperatorBound` factors through a proved, reusable
Spine theorem rather than through a private copy of the argument.

What is discharged here, and how:

* `spine_dyadicRateBlocks_iff` / `spine_blockMultiplicity_iff` — the two NS-lane
  hypotheses **are** the Spine hypotheses at `ι = Wave` (definitional; the
  proofs are `Iff.rfl`).  There is no transport to construct and no side
  condition to check.
* `sum_resForm_le_blockMultiplicity_ofSpine` — the NS pair estimate obtained
  from `Spine.RateBlockSchur.schur_form_le_blockMultiplicity` with
  `a p q = Re⟪G p, G q⟫`, `n p = ‖G p‖`.  The only NS-specific input is
  Cauchy–Schwarz on `ℂ³` (`herm_re_le_nrm_mul`) and `nrm² = nsq`.
* `gramOperatorBound_of_rateBlockMultiplicity_ofSpine` — the **literal
  consumer**: `GramOperatorBound nu modes G k (32·m)`, proved by running the
  Spine bound against `lam p = viscousPairRate nu p (k − p) ≥ nu·|p|²`.
* `gramOperatorBound_ofSpine_eq_local` — the adapter's conclusion is *the same
  proposition* as the lane's own `gramOperatorBound_of_rateBlockMultiplicity`,
  so the two are interchangeable at the consumer and the private copy of the
  kernel in `RateBlockGramBound` is redundant, not merely parallel.

### Carrier mismatch that is *not* repaired here

`Spine.RateBlockSchur.schur_gram_le_blockMultiplicity` (the inner-product-space
instance of the same kernel) is stated for `E` with
`[NormedAddCommGroup E] [InnerProductSpace ℂ E]` and uses `inner ℂ` and `‖·‖`.
The NS cells live in `Fin 3 → ℂ` carrying Mathlib's **sup-norm** `Pi` instance,
with the Hermitian form and Euclidean mass supplied by the lane's own `herm`
and `nsq`.  So that instance does **not** apply to the NS carrier: the adapter
goes through the scalar form `schur_form_le_blockMultiplicity`, which is
carrier-free, and supplies Cauchy–Schwarz by hand.  Repairing the mismatch would
mean transporting the lane to `EuclideanSpace ℂ (Fin 3)`, which is a separate
(and much larger) refactor of every NS file.

Nothing here closes any Clay obligation and none is claimed.  The bound is
cancellation-free and therefore still degrades linearly in the rate-block
multiplicity, exactly as `Spine.RateBlockSchur.schur_form_ge_half_mul_multiplicity`
and the lane's `gramOperatorBound_fails_on_comparable_shells` record.
-/
import Spine.RateBlockSchur
import RequestProject.NavierStokes.RateBlockGramBound

noncomputable section

namespace ClayNS.SpineAdapter

open ClayNS.Waleffe ClayNS.Resolvent ClayNS.TTStar ClayNS.Schur ClayNS.RateBlocks

/-! ## 1.  The hypotheses coincide -/

/-- The NS-lane dyadic rate-block hypothesis **is** the Spine one at
`ι = Wave`. -/
theorem spine_dyadicRateBlocks_iff (lam : Wave → ℝ) (modes : Finset Wave) (blk : Wave → ℤ) :
    ClayNS.RateBlocks.DyadicRateBlocks lam modes blk
      ↔ Spine.RateBlockSchur.DyadicRateBlocks lam modes blk := Iff.rfl

/-- The NS-lane block-multiplicity hypothesis **is** the Spine one at
`ι = Wave`. -/
theorem spine_blockMultiplicity_iff (modes : Finset Wave) (blk : Wave → ℤ) (m : ℕ) :
    ClayNS.RateBlocks.BlockMultiplicity modes blk m
      ↔ Spine.RateBlockSchur.BlockMultiplicity modes blk m := Iff.rfl

/-! ## 2.  The NS pair estimate, from the Spine carrier -/

/-- **The NS Schur estimate, factored through the Spine kernel.**  Identical in
statement to `ClayNS.RateBlocks.sum_resForm_le_blockMultiplicity`, but proved by
instantiating the domain-neutral `Spine.RateBlockSchur.schur_form_le_blockMultiplicity`
at `a p q = Re⟪G p, G q⟫`, `n p = ‖G p‖`. -/
theorem sum_resForm_le_blockMultiplicity_ofSpine {lam : Wave → ℝ} {blk : Wave → ℤ} {m : ℕ}
    (modes : Finset Wave) (G : Wave → Fin 3 → ℂ)
    (hblk : Spine.RateBlockSchur.DyadicRateBlocks lam modes blk)
    (hm : Spine.RateBlockSchur.BlockMultiplicity modes blk m) :
    ∑ p ∈ modes, ∑ q ∈ modes, (herm (G p) (G q)).re / (lam p + lam q)
      ≤ 16 * m * ∑ p ∈ modes, nsq (G p) / lam p := by
  classical
  have hspine := Spine.RateBlockSchur.schur_form_le_blockMultiplicity
    (lam := lam) (blk := blk) (m := m) modes
    (fun p q => (herm (G p) (G q)).re) (fun p => nrm (G p)) hblk hm
    (fun p _ q _ => herm_re_le_nrm_mul (G p) (G q))
  have hmass : ∑ p ∈ modes, nrm (G p) ^ 2 / lam p = ∑ p ∈ modes, nsq (G p) / lam p :=
    Finset.sum_congr rfl fun p _ => by rw [nrm_sq]
  rwa [hmass] at hspine

/-! ## 3.  The literal consumer -/

/-- **The physical instance `A = 32·m`, paid by the Spine kernel.**  Same
statement as `ClayNS.RateBlocks.gramOperatorBound_of_rateBlockMultiplicity`; the
proof now factors through `Spine.RateBlockSchur`. -/
theorem gramOperatorBound_of_rateBlockMultiplicity_ofSpine {nu : ℝ} {m : ℕ} (hnu : 0 < nu)
    (modes : Finset Wave) (G : Wave → Fin 3 → ℂ) (k : Wave) (blk : Wave → ℤ)
    (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hblk : Spine.RateBlockSchur.DyadicRateBlocks
      (fun p => viscousPairRate nu p (k - p)) modes blk)
    (hm : Spine.RateBlockSchur.BlockMultiplicity modes blk m) :
    GramOperatorBound nu modes G k (32 * m) := by
  classical
  have hmain := sum_resForm_le_blockMultiplicity_ofSpine
    (lam := fun p => viscousPairRate nu p (k - p)) (blk := blk) (m := m) modes G hblk hm
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
  have hchain : ∑ p ∈ modes, ∑ q ∈ modes,
      (herm (G p) (G q)).re
        / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))
      ≤ 16 * m * ((∑ p ∈ modes, nsq (G p) / wsq p) / nu) :=
    hmain.trans (mul_le_mul_of_nonneg_left hmass hmnn)
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

/-- The adapter and the lane's private copy prove **the same proposition**, so
the consumer may be paid by either and the private kernel is redundant. -/
theorem gramOperatorBound_ofSpine_eq_local {nu : ℝ} {m : ℕ} (hnu : 0 < nu)
    (modes : Finset Wave) (G : Wave → Fin 3 → ℂ) (k : Wave) (blk : Wave → ℤ)
    (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hblk : ClayNS.RateBlocks.DyadicRateBlocks
      (fun p => viscousPairRate nu p (k - p)) modes blk)
    (hm : ClayNS.RateBlocks.BlockMultiplicity modes blk m) :
    GramOperatorBound nu modes G k (32 * m)
      ∧ GramOperatorBound nu modes G k (32 * m) :=
  ⟨ClayNS.RateBlocks.gramOperatorBound_of_rateBlockMultiplicity hnu modes G k blk hp hblk hm,
   gramOperatorBound_of_rateBlockMultiplicity_ofSpine hnu modes G k blk hp
     ((spine_dyadicRateBlocks_iff _ _ _).mp hblk)
     ((spine_blockMultiplicity_iff _ _ _).mp hm)⟩

/-! ## 4.  The Spine lower bound transported to the lane's vocabulary

`Spine.RateBlockSchur.schur_form_ge_half_mul_multiplicity` says the linear
dependence on the block multiplicity is real.  Restated here so the NS lane can
quote the Spine witness instead of rebuilding one. -/

/-- For every `m` there is a single rate block of `m` indices, unit rates, unit
masses and a saturating pairing, forcing a constant at least `m/2`. -/
theorem spine_multiplicity_lower_bound (m : ℕ) :
    ∃ (S : Finset ℕ) (lam : ℕ → ℝ) (blk : ℕ → ℤ) (a : ℕ → ℕ → ℝ) (n : ℕ → ℝ),
      S.card = m ∧ Spine.RateBlockSchur.DyadicRateBlocks lam S blk ∧
      Spine.RateBlockSchur.BlockMultiplicity S blk m ∧
      (∀ p ∈ S, ∀ q ∈ S, a p q ≤ n p * n q) ∧
      (m / 2 : ℝ) * (∑ p ∈ S, n p ^ 2 / lam p)
        ≤ ∑ p ∈ S, ∑ q ∈ S, a p q / (lam p + lam q) :=
  Spine.RateBlockSchur.schur_form_ge_half_mul_multiplicity m

end ClayNS.SpineAdapter

/-
# The rate-block Schur kernel on the plain `Fin n → ℂ` carrier

`Spine.RateBlockSchur.schur_gram_le_blockMultiplicity` states the kernel for an
`E` with `[NormedAddCommGroup E] [InnerProductSpace ℂ E]`.  The Navier–Stokes
lane delivered by the 2026-09-12 tranche cannot use that instance: its cells
live in `Fin 3 → ℂ`, which carries Mathlib's **sup-norm** `Pi` instance, with the
Hermitian form and the Euclidean mass supplied by the lane's own `herm` and
`nsq`.  The lane therefore goes through the carrier-free scalar form and
supplies Cauchy–Schwarz by hand (see
`NS_LATEST_TRANCHE_LINEAGE.md` §4.1, retained mismatch 1).

This module removes that hand step on the spine side, for the scalar Gram form,
by owning the transport once:

* `hermPi`, `nsqPi`, `nrmPi` — the pairing, the Euclidean mass and its square
  root on the plain function type `Fin n → ℂ`, defined exactly as the NS lane
  defines them (`∑ i, conj (u i) * v i`, `∑ i, normSq (u i)`, `√·`);
* `hermPi_eq_inner`, `nrmPi_eq_norm` — they *are* the `EuclideanSpace ℂ (Fin n)`
  inner product and norm, transported along `WithLp.toLp 2`.  This is the
  identification the NS lane lacks, and it is the only content needed: the
  sup-norm `Pi` instance is never used;
* `hermPi_re_le_nrmPi_mul` — Cauchy–Schwarz on the plain carrier, obtained from
  the transport rather than proved again;
* `schur_gramPi_le_blockMultiplicity` — the rate-block Schur bound in exactly
  the shape the lane consumes it, at the lane's own carrier and its own
  pairing/mass, with no inner-product instance on `Fin n → ℂ` required.

Nothing here is Navier–Stokes specific: `ι`, `lam` and `G` are arbitrary, and no
Clay obligation is closed or claimed.  The bound is the cancellation-free one,
so it still degrades linearly in the block multiplicity, exactly as
`Spine.RateBlockSchur.schur_form_ge_half_mul_multiplicity` records.
-/
import Spine.RateBlockSchur

noncomputable section

namespace Spine
namespace RateBlockSchurPi

open Finset

variable {ι : Type*} {n : ℕ}

/-! ## 1.  The lane's pairing and mass on the plain carrier -/

/-- The Hermitian pairing on `Fin n → ℂ`, conjugate-linear in the first slot. -/
def hermPi (u v : Fin n → ℂ) : ℂ := ∑ i, (starRingEnd ℂ) (u i) * v i

/-- The Euclidean mass on `Fin n → ℂ`. -/
def nsqPi (u : Fin n → ℂ) : ℝ := ∑ i, Complex.normSq (u i)

/-- The Euclidean norm on `Fin n → ℂ`. -/
def nrmPi (u : Fin n → ℂ) : ℝ := Real.sqrt (nsqPi u)

theorem nsqPi_nonneg (u : Fin n → ℂ) : 0 ≤ nsqPi u :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem nrmPi_nonneg (u : Fin n → ℂ) : 0 ≤ nrmPi u := Real.sqrt_nonneg _

@[simp] theorem nrmPi_sq (u : Fin n → ℂ) : nrmPi u ^ 2 = nsqPi u :=
  Real.sq_sqrt (nsqPi_nonneg u)

/-! ## 2.  The transport: they are the Euclidean structure -/

/-- The pairing is the `EuclideanSpace ℂ (Fin n)` inner product, transported
along `WithLp.toLp 2`. -/
theorem hermPi_eq_inner (u v : Fin n → ℂ) :
    (inner ℂ (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 v) : ℂ)
      = hermPi u v := by
  simp [PiLp.inner_apply, RCLike.inner_apply, hermPi, mul_comm]

/-- The norm is the `EuclideanSpace ℂ (Fin n)` norm, transported along
`WithLp.toLp 2`. -/
theorem nrmPi_eq_norm (u : Fin n → ℂ) :
    ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin n))‖ = nrmPi u := by
  rw [EuclideanSpace.norm_eq]
  simp [nrmPi, nsqPi, Complex.sq_norm]

/-- **Cauchy–Schwarz on the plain carrier**, from the transport alone. -/
theorem hermPi_re_le_nrmPi_mul (u v : Fin n → ℂ) :
    (hermPi u v).re ≤ nrmPi u * nrmPi v := by
  have h := re_inner_le_norm (𝕜 := ℂ)
    (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 v)
  rwa [hermPi_eq_inner, nrmPi_eq_norm, nrmPi_eq_norm] at h

/-! ## 3.  The kernel at the lane's carrier -/

/-- **The rate-block Schur bound for a family of `Fin n → ℂ` cells**, stated with
the lane's own pairing and mass.  This is
`Spine.RateBlockSchur.schur_gram_le_blockMultiplicity` for a carrier that has no
`InnerProductSpace ℂ` instance: the Euclidean structure is supplied by the
transport above instead of by an instance on `Fin n → ℂ`. -/
theorem schur_gramPi_le_blockMultiplicity [DecidableEq ι] {lam : ι → ℝ} {blk : ι → ℤ}
    {m : ℕ} (S : Finset ι) (G : ι → Fin n → ℂ)
    (hblk : RateBlockSchur.DyadicRateBlocks lam S blk)
    (hm : RateBlockSchur.BlockMultiplicity S blk m) :
    ∑ p ∈ S, ∑ q ∈ S, (hermPi (G p) (G q)).re / (lam p + lam q)
      ≤ 16 * m * ∑ p ∈ S, nsqPi (G p) / lam p := by
  have h := RateBlockSchur.schur_form_le_blockMultiplicity S
    (fun p q => (hermPi (G p) (G q)).re) (fun p => nrmPi (G p)) hblk hm
    (fun p _ q _ => hermPi_re_le_nrmPi_mul (G p) (G q))
  have hmass : ∑ p ∈ S, nrmPi (G p) ^ 2 / lam p = ∑ p ∈ S, nsqPi (G p) / lam p :=
    Finset.sum_congr rfl fun p _ => by rw [nrmPi_sq]
  rwa [hmass] at h

end RateBlockSchurPi
end Spine

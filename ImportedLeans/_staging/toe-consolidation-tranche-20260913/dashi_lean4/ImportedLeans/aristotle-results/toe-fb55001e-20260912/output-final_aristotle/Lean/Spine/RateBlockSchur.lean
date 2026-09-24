/-
# The dyadic rate-block Schur kernel, owned once

This module extracts, as a **domain-neutral spine theorem**, the mathematical
core of the Navier–Stokes worker's outer-cell Gram file
(`Provenance/ns_worker_result/RequestProject/NavierStokes/RateBlockGramBound.lean`,
shipped with the 2026-09-10 cross-pollination handoff).  That file is *not*
buildable in this checkout — it imports `RequestProject.NavierStokes.TransverseFrameSplit`,
which the handoff does not ship — so nothing of it is quoted here; what follows
is a self-contained Lean development over an arbitrary index type.

The kernel.  Let `lam : ι → ℝ` be a positive "rate" on a finite index set `S`,
let `blk : ι → ℤ` place each index in the dyadic rate window
`[4^b, 4^{b+1})`, and suppose each window carries at most `m` indices.  Then for
*any* pairing `a : ι → ι → ℝ` dominated by a product of nonnegative masses,
`a p q ≤ n p * n q`, the Cauchy-kernel form obeys

  `∑_{p,q∈S} a p q / (lam p + lam q) ≤ 16 · m · ∑_{p∈S} (n p)² / lam p`.

No cancellation, no signs and no structure on `ι` are used: this is a Schur test
against `1/(lam p + lam q)`, whose across-block decay is geometric and whose
geometric series is summable over `ℤ` uniformly in `S`.

The matching lower bound `schur_form_ge_half_mul_multiplicity` shows the linear
dependence on `m` is real: a single rate block of `m` indices with a constant
pairing forces the constant to be at least `m/2`.  So the constant of the kernel
is `Θ(m)`, and no argument that ignores the values `a p q` can do better.

Consumers.  The Navier–Stokes outer-cell Gram bound is the instance
`ι = Wave`, `lam p = viscousPairRate ν p (k − p)`, `a p q = Re⟪G_p, G_q⟫`,
`n p = ‖G_p‖`; that instance lives in the NS lane and is *not* reproduced here.
Nothing in this file closes any Clay obligation, and none is claimed: the
positive theorem is cancellation-free and therefore degrades exactly as the
block multiplicity grows, which is what the lower bound records.
-/
import Mathlib

noncomputable section

namespace Spine
namespace RateBlockSchur

open Finset

variable {ι : Type*}

/-! ## 1.  A geometric series over the integers, uniform in the index set -/

/-- The kernel `2^{-|d|}` has total mass at most `4` over *any* finite set of
integers — the bound is uniform in the set. -/
theorem sum_half_pow_natAbs_le (T : Finset ℤ) : ∑ d ∈ T, (1 / 2 : ℝ) ^ d.natAbs ≤ 4 := by
  classical
  have hsplit : ∑ d ∈ T, (1 / 2 : ℝ) ^ d.natAbs
      = (∑ d ∈ T.filter (fun d => 0 ≤ d), (1 / 2 : ℝ) ^ d.natAbs)
        + (∑ d ∈ T.filter (fun d => ¬ (0 ≤ d)), (1 / 2 : ℝ) ^ d.natAbs) :=
    (Finset.sum_filter_add_sum_filter_not T _ _).symm
  have part : ∀ S : Finset ℤ, Set.InjOn Int.natAbs S →
      ∑ d ∈ S, (1 / 2 : ℝ) ^ d.natAbs ≤ 2 := by
    intro S hinj
    have h1 : ∑ d ∈ S, (1 / 2 : ℝ) ^ d.natAbs = ∑ n ∈ S.image Int.natAbs, (1 / 2 : ℝ) ^ n :=
      (Finset.sum_image fun x hx y hy h => hinj hx hy h).symm
    rw [h1]
    set K := (S.image Int.natAbs).sup id with hK
    have hsub : S.image Int.natAbs ⊆ Finset.range (K + 1) := by
      intro n hn
      simp only [Finset.mem_range]
      have : n ≤ K := Finset.le_sup (f := id) hn
      omega
    calc ∑ n ∈ S.image Int.natAbs, (1 / 2 : ℝ) ^ n
        ≤ ∑ n ∈ Finset.range (K + 1), (1 / 2 : ℝ) ^ n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro i _ _; positivity)
      _ ≤ 2 := sum_geometric_two_le _
  have hA : Set.InjOn Int.natAbs (T.filter (fun d => 0 ≤ d)) := by
    intro x hx y hy h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
    omega
  have hB : Set.InjOn Int.natAbs (T.filter (fun d => ¬ (0 ≤ d))) := by
    intro x hx y hy h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
    omega
  have h2 := part _ hA
  have h3 := part _ hB
  rw [hsplit]
  linarith

/-- The same bound after a shift of the origin. -/
theorem sum_half_pow_shift_le (S : Finset ℤ) (c : ℤ) :
    ∑ b ∈ S, (1 / 2 : ℝ) ^ (c - b).natAbs ≤ 4 := by
  classical
  have hinj : Set.InjOn (fun b => c - b) (S : Set ℤ) := by
    intro x _ y _ h
    simp only at h
    omega
  have h := Finset.sum_image (f := fun d : ℤ => (1 / 2 : ℝ) ^ d.natAbs)
    (g := fun b => c - b) hinj
  rw [← h]
  exact sum_half_pow_natAbs_le _

/-! ## 2.  Rate blocks and their multiplicity -/

/-- `blk` places each index of `S` in a dyadic rate window: `blk p = b` means
`lam p ∈ [4^b, 4^{b+1})`. -/
def DyadicRateBlocks (lam : ι → ℝ) (S : Finset ι) (blk : ι → ℤ) : Prop :=
  ∀ p ∈ S, (4 : ℝ) ^ (blk p) ≤ lam p ∧ lam p < 4 * (4 : ℝ) ^ (blk p)

/-- Every dyadic rate window carries at most `m` indices of `S`. -/
def BlockMultiplicity [DecidableEq ι] (S : Finset ι) (blk : ι → ℤ) (m : ℕ) : Prop :=
  ∀ b : ℤ, {p ∈ S | blk p = b}.card ≤ m

/-- Rates are positive wherever the blocks are defined. -/
theorem lam_pos {lam : ι → ℝ} {S : Finset ι} {blk : ι → ℤ}
    (hblk : DyadicRateBlocks lam S blk) {p : ι} (hp : p ∈ S) : 0 < lam p :=
  lt_of_lt_of_le (by positivity) (hblk p hp).1

/-- **The Schur row sum.**  With multiplicity `m`, the geometric kernel has row
sums at most `4m` — uniformly in the index set. -/
theorem rowsum_le [DecidableEq ι] {S : Finset ι} {blk : ι → ℤ} {m : ℕ}
    (hm : BlockMultiplicity S blk m) (c : ℤ) :
    ∑ q ∈ S, (1 / 2 : ℝ) ^ (c - blk q).natAbs ≤ 4 * m := by
  classical
  rw [Finset.sum_comp (fun b : ℤ => (1 / 2 : ℝ) ^ (c - b).natAbs) blk]
  have h1 : ∑ b ∈ S.image blk,
        ({p ∈ S | blk p = b}.card : ℕ) • (1 / 2 : ℝ) ^ (c - b).natAbs
      ≤ ∑ b ∈ S.image blk, (m : ℝ) * (1 / 2 : ℝ) ^ (c - b).natAbs := by
    refine Finset.sum_le_sum fun b _ => ?_
    rw [nsmul_eq_mul]
    have hc : (({p ∈ S | blk p = b}.card : ℝ)) ≤ (m : ℝ) := by exact_mod_cast hm b
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  refine h1.trans ?_
  rw [← Finset.mul_sum]
  have hgeo := sum_half_pow_shift_le (S.image blk) c
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

/-! ## 3.  The pointwise Cauchy-kernel estimate -/

/-- **The elementary block estimate.**  If `s` sits in the dyadic window of ratio
`4` based at `L` and `t` is at least `4^d` times that base, the Cauchy-kernel
pair term is controlled by the two rate-normalized masses, with a factor
decaying geometrically in `d`.  No square root and no cancellation enter. -/
theorem amgm_block (u v L s t : ℝ) (d : ℕ) (hL : 0 < L)
    (hs1 : L ≤ s) (hs2 : s < 4 * L) (ht : (4 : ℝ) ^ d * L ≤ t) :
    u * v / (s + t) ≤ 2 * (1 / 2 : ℝ) ^ d * (u ^ 2 / s + v ^ 2 / t) := by
  have hs : 0 < s := lt_of_lt_of_le hL hs1
  have h4d : (0 : ℝ) < (4 : ℝ) ^ d := by positivity
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hst : 0 < s + t := by linarith
  set τ : ℝ := (2 : ℝ) ^ d with hτdef
  set r : ℝ := (1 / 2 : ℝ) ^ d with hrdef
  have hτ : 0 < τ := by positivity
  have hr : 0 < r := by positivity
  have hτr : τ * r = 1 := by rw [hτdef, hrdef, ← mul_pow]; norm_num
  have hr4 : r * (4 : ℝ) ^ d = τ := by rw [hrdef, hτdef, ← mul_pow]; norm_num
  have key1 : u * v ≤ (1 / 2) * (τ * u ^ 2 + v ^ 2 / τ) := by
    have hexp : (1 / 2) * (τ * u ^ 2 + v ^ 2 / τ) - u * v = ((τ * u - v) ^ 2) / (2 * τ) := by
      field_simp; ring
    nlinarith [div_nonneg (sq_nonneg (τ * u - v)) (by positivity : (0 : ℝ) ≤ 2 * τ)]
  have key2 : τ / (s + t) ≤ 4 * r / s := by
    rw [div_le_div_iff₀ hst hs]
    have h1 : τ * s ≤ τ * (4 * L) := by nlinarith
    have h2 : 4 * r * ((4 : ℝ) ^ d * L) ≤ 4 * r * (s + t) := by nlinarith
    have h3 : 4 * r * ((4 : ℝ) ^ d * L) = τ * (4 * L) := by nlinarith [hr4]
    nlinarith
  have key3 : 1 / (τ * (s + t)) ≤ 4 * r / t := by
    rw [div_le_div_iff₀ (by positivity) ht0]
    nlinarith
  calc u * v / (s + t) ≤ ((1 / 2) * (τ * u ^ 2 + v ^ 2 / τ)) / (s + t) := by gcongr
    _ = (1 / 2) * ((τ / (s + t)) * u ^ 2 + (1 / (τ * (s + t))) * v ^ 2) := by field_simp
    _ ≤ (1 / 2) * ((4 * r / s) * u ^ 2 + (4 * r / t) * v ^ 2) := by
        have h1 : (τ / (s + t)) * u ^ 2 ≤ (4 * r / s) * u ^ 2 := by nlinarith [sq_nonneg u]
        have h2 : (1 / (τ * (s + t))) * v ^ 2 ≤ (4 * r / t) * v ^ 2 := by nlinarith [sq_nonneg v]
        linarith
    _ = 2 * r * (u ^ 2 / s + v ^ 2 / t) := by field_simp; ring

theorem four_zpow_natAbs_mul {bp bq : ℤ} (h : bp ≤ bq) :
    (4 : ℝ) ^ ((bq - bp).natAbs) * (4 : ℝ) ^ bp = (4 : ℝ) ^ bq := by
  have hcast : (((bq - bp).natAbs : ℤ)) = bq - bp := Int.natAbs_of_nonneg (by omega)
  rw [← zpow_natCast (4 : ℝ) ((bq - bp).natAbs), hcast,
    ← zpow_add₀ (by norm_num : (4 : ℝ) ≠ 0)]
  ring_nf

/-- **The pair term**, bounded by the two rate-normalized masses with a factor
decaying geometrically in the rate-block distance. -/
theorem pair_term_le {lam : ι → ℝ} {blk : ι → ℤ} {n : ι → ℝ} {p q : ι} {v : ℝ}
    (hp : (4 : ℝ) ^ (blk p) ≤ lam p ∧ lam p < 4 * (4 : ℝ) ^ (blk p))
    (hq : (4 : ℝ) ^ (blk q) ≤ lam q ∧ lam q < 4 * (4 : ℝ) ^ (blk q))
    (hv : v ≤ n p * n q) :
    v / (lam p + lam q)
      ≤ 2 * (1 / 2 : ℝ) ^ (blk p - blk q).natAbs * (n p ^ 2 / lam p + n q ^ 2 / lam q) := by
  have hlp : 0 < lam p := lt_of_lt_of_le (by positivity) hp.1
  have hlq : 0 < lam q := lt_of_lt_of_le (by positivity) hq.1
  have hsum : 0 < lam p + lam q := by linarith
  have hcs : v / (lam p + lam q) ≤ n p * n q / (lam p + lam q) :=
    (div_le_div_iff_of_pos_right hsum).mpr hv
  refine hcs.trans ?_
  rcases le_total (blk p) (blk q) with hle | hle
  · have ht : (4 : ℝ) ^ ((blk q - blk p).natAbs) * (4 : ℝ) ^ (blk p) ≤ lam q := by
      rw [four_zpow_natAbs_mul hle]; exact hq.1
    have h := amgm_block (n p) (n q) ((4 : ℝ) ^ (blk p)) (lam p) (lam q)
      ((blk q - blk p).natAbs) (by positivity) hp.1 hp.2 ht
    rwa [show (blk p - blk q).natAbs = (blk q - blk p).natAbs from by omega]
  · have ht : (4 : ℝ) ^ ((blk p - blk q).natAbs) * (4 : ℝ) ^ (blk q) ≤ lam p := by
      rw [four_zpow_natAbs_mul hle]; exact hp.1
    have h := amgm_block (n q) (n p) ((4 : ℝ) ^ (blk q)) (lam q) (lam p)
      ((blk p - blk q).natAbs) (by positivity) hq.1 hq.2 ht
    calc n p * n q / (lam p + lam q)
        = n q * n p / (lam q + lam p) := by ring_nf
      _ ≤ 2 * (1 / 2 : ℝ) ^ (blk p - blk q).natAbs * (n q ^ 2 / lam q + n p ^ 2 / lam p) := h
      _ = 2 * (1 / 2 : ℝ) ^ (blk p - blk q).natAbs
            * (n p ^ 2 / lam p + n q ^ 2 / lam q) := by ring

/-! ## 4.  The Schur bound in terms of the block multiplicity -/

/-- **The rate-block Schur kernel.**  For an arbitrary positive rate whose dyadic
blocks carry at most `m` indices, every pairing dominated by a product of
nonnegative masses has Cauchy-kernel form at most `16m` times the
rate-normalized ℓ² mass.  No cancellation is used, and the index type is
arbitrary. -/
theorem schur_form_le_blockMultiplicity [DecidableEq ι] {lam : ι → ℝ} {blk : ι → ℤ} {m : ℕ}
    (S : Finset ι) (a : ι → ι → ℝ) (n : ι → ℝ)
    (hblk : DyadicRateBlocks lam S blk) (hm : BlockMultiplicity S blk m)
    (ha : ∀ p ∈ S, ∀ q ∈ S, a p q ≤ n p * n q) :
    ∑ p ∈ S, ∑ q ∈ S, a p q / (lam p + lam q)
      ≤ 16 * m * ∑ p ∈ S, n p ^ 2 / lam p := by
  classical
  set M : ι → ℝ := fun p => n p ^ 2 / lam p with hM
  have hMnn : ∀ p ∈ S, 0 ≤ M p := fun p hp =>
    div_nonneg (sq_nonneg _) (lam_pos hblk hp).le
  have step1 : ∑ p ∈ S, ∑ q ∈ S, a p q / (lam p + lam q)
      ≤ ∑ p ∈ S, ∑ q ∈ S,
          2 * (1 / 2 : ℝ) ^ (blk p - blk q).natAbs * (M p + M q) :=
    Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq =>
      pair_term_le (hblk p hp) (hblk q hq) (ha p hp q hq)
  refine step1.trans ?_
  set r : ι → ι → ℝ := fun p q => (1 / 2 : ℝ) ^ (blk p - blk q).natAbs with hr
  have hsplit : ∑ p ∈ S, ∑ q ∈ S, 2 * r p q * (M p + M q)
      = 2 * (∑ p ∈ S, ∑ q ∈ S, r p q * M p)
        + 2 * (∑ p ∈ S, ∑ q ∈ S, r p q * M q) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have hrow1 : ∑ p ∈ S, ∑ q ∈ S, r p q * M p ≤ 4 * m * ∑ p ∈ S, M p := by
    have hterm : ∀ p ∈ S, ∑ q ∈ S, r p q * M p ≤ 4 * m * M p := by
      intro p hp
      have hrs := rowsum_le hm (blk p)
      have hMp := hMnn p hp
      have hEq : ∑ q ∈ S, r p q * M p = (∑ q ∈ S, r p q) * M p := by
        rw [Finset.sum_mul]
      have hEq2 : (∑ q ∈ S, r p q) = ∑ q ∈ S, (1 / 2 : ℝ) ^ (blk p - blk q).natAbs := rfl
      rw [hEq, hEq2]
      nlinarith
    calc ∑ p ∈ S, ∑ q ∈ S, r p q * M p ≤ ∑ p ∈ S, 4 * m * M p :=
          Finset.sum_le_sum hterm
      _ = 4 * m * ∑ p ∈ S, M p := by rw [Finset.mul_sum]
  have hrow2 : ∑ p ∈ S, ∑ q ∈ S, r p q * M q ≤ 4 * m * ∑ p ∈ S, M p := by
    rw [Finset.sum_comm]
    have hterm : ∀ q ∈ S, ∑ p ∈ S, r p q * M q ≤ 4 * m * M q := by
      intro q hq
      have hrs := rowsum_le hm (blk q)
      have hMq := hMnn q hq
      have hEq : ∑ p ∈ S, r p q * M q = (∑ p ∈ S, r p q) * M q := by
        rw [Finset.sum_mul]
      have hEq2 : (∑ p ∈ S, r p q) = ∑ p ∈ S, (1 / 2 : ℝ) ^ (blk q - blk p).natAbs :=
        Finset.sum_congr rfl fun p _ => by
          rw [hr]
          exact congrArg _ (by omega : (blk p - blk q).natAbs = (blk q - blk p).natAbs)
      rw [hEq, hEq2]
      nlinarith
    calc ∑ q ∈ S, ∑ p ∈ S, r p q * M q ≤ ∑ q ∈ S, 4 * m * M q :=
          Finset.sum_le_sum hterm
      _ = 4 * m * ∑ q ∈ S, M q := by rw [Finset.mul_sum]
  rw [hsplit]
  linarith

/-! ## 5.  The matching lower bound: linear growth in the multiplicity is real -/

/-- **A single block of `m` indices forces a constant at least `m/2`.**  The
configuration is the honest worst case for a cancellation-free argument: `m`
indices in one dyadic window, unit rates, unit masses, and the constant pairing
`a ≡ 1`, which saturates `a p q ≤ n p * n q`.  Together with
`schur_form_le_blockMultiplicity` this pins the kernel's constant at `Θ(m)`. -/
theorem schur_form_ge_half_mul_multiplicity (m : ℕ) :
    ∃ (S : Finset ℕ) (lam : ℕ → ℝ) (blk : ℕ → ℤ) (a : ℕ → ℕ → ℝ) (n : ℕ → ℝ),
      S.card = m ∧ DyadicRateBlocks lam S blk ∧ BlockMultiplicity S blk m ∧
      (∀ p ∈ S, ∀ q ∈ S, a p q ≤ n p * n q) ∧
      (m / 2 : ℝ) * (∑ p ∈ S, n p ^ 2 / lam p)
        ≤ ∑ p ∈ S, ∑ q ∈ S, a p q / (lam p + lam q) := by
  classical
  refine ⟨Finset.range m, fun _ => 1, fun _ => 0, fun _ _ => 1, fun _ => 1,
    Finset.card_range m, ?_, ?_, ?_, ?_⟩
  · intro p _; norm_num
  · intro b
    calc {p ∈ Finset.range m | (0 : ℤ) = b}.card ≤ (Finset.range m).card :=
          Finset.card_filter_le _ _
      _ = m := Finset.card_range m
  · intro p _ q _; norm_num
  · have h1 : ∑ p ∈ Finset.range m, ((1 : ℝ) ^ 2 / 1) = (m : ℝ) := by
      simp
    have h2 : ∑ p ∈ Finset.range m, ∑ q ∈ Finset.range m, ((1 : ℝ) / (1 + 1))
        = (m : ℝ) * m / 2 := by
      simp [Finset.sum_const, Finset.card_range]
      ring
    rw [h1, h2]
    ring_nf
    rfl

/-- **The inner-product instance.**  For a family of vectors in any complex
inner-product space, the real part of the Gram pairing is dominated by the
product of the norms, so the kernel applies verbatim: the signed Gram form of an
arbitrary cell family is bounded by `16m` times the rate-normalized ℓ² mass.
This is the shape in which the Navier–Stokes lane consumes the kernel; the lane
supplies `lam` (a viscous pair rate) and `G` (its outer cells), neither of which
occurs here. -/
theorem schur_gram_le_blockMultiplicity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [DecidableEq ι] {lam : ι → ℝ} {blk : ι → ℤ} {m : ℕ}
    (S : Finset ι) (G : ι → E)
    (hblk : DyadicRateBlocks lam S blk) (hm : BlockMultiplicity S blk m) :
    ∑ p ∈ S, ∑ q ∈ S, (inner ℂ (G p) (G q) : ℂ).re / (lam p + lam q)
      ≤ 16 * m * ∑ p ∈ S, ‖G p‖ ^ 2 / lam p :=
  schur_form_le_blockMultiplicity S (fun p q => (inner ℂ (G p) (G q) : ℂ).re)
    (fun p => ‖G p‖) hblk hm (fun p _ q _ => (re_inner_le_norm (𝕜 := ℂ) (G p) (G q)))

/-- The kernel is vacuous — but true — on the empty index set. -/
theorem schur_form_empty {lam : ι → ℝ} (a : ι → ι → ℝ) :
    ∑ p ∈ (∅ : Finset ι), ∑ q ∈ (∅ : Finset ι), a p q / (lam p + lam q) = 0 := by
  simp

end RateBlockSchur
end Spine

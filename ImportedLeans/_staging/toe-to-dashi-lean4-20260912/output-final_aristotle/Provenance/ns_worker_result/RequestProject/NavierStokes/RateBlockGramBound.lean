/-
# The outer-cell Gram bound, measured against dyadic rate blocks

The single remaining hypothesis of the critical spacetime consumer is
`GramOperatorBound nu modes G k A`: a truncation-uniform `ℓ² → ℓ²` bound for the
outer-cell Gram operator at a retained output, i.e.

  `∑_{p,q} Re⟪G_p,G_q⟫/(λ_p+λ_q) ≤ A·(∑_p ‖G_p‖²/|p|²)/(2ν)`,

with `λ_p` the viscous pair rate of the cell `p` at the output `k`.  This file
measures exactly how large `A` has to be, in terms of one geometric quantity of
the retained mode set: the *multiplicity of its dyadic rate blocks*, i.e. the
largest number of retained modes whose viscous pair rates lie in one dyadic
window `[4^b, 4^{b+1})`.

Two matching theorems:

* `gramOperatorBound_of_rateBlockMultiplicity` — **positive**.  If every dyadic
  rate block carries at most `m` retained modes, then the bound holds with
  `A = 32·m`, for *every* cell family, with no cancellation used at all.  The
  proof is a Schur test against the Cauchy kernel `1/(λ_p+λ_q)`: across blocks
  the kernel decays geometrically (`pair_term_le`), and the geometric series is
  summable over `ℤ` uniformly in the mode set (`sum_half_pow_natAbs_le`).

* `gramOperatorBound_fails_on_comparable_shells` — **negative, and sharp**.  For
  every `N` there is a retained output `k`, a set of at least `N` nonzero modes
  with pairwise comparable lengths — hence all inside boundedly many rate blocks
  — and a *transverse* cell family for which every admissible `A` is at least
  `N`.  So the linear growth in the block multiplicity above is not an artifact
  of the Schur test: for a general cell family it is the truth.

Together these locate the remaining obligation precisely.  The physical retained
mode set at a truncation `N` has rate-block multiplicity growing with `N`
(a dyadic shell contains many lattice modes), so the free, cancellation-free
bound degrades exactly as the truncation grows, and the negative result shows no
argument that ignores the cell values can do better.  Any truncation-uniform
`A` must therefore come from cancellation *inside* a dyadic rate block, i.e.
from the actual field dependence of the cells `G_p = P_k(N_p × u_{k−p})`, not
from the kernel, the transversality, or the shell geometry.

Nothing here closes that obligation.  Package A and the literal periodic Clay
regularity target are **not** closed and nothing is claimed for them; no axiom,
postulate, conditional bridge or placeholder is introduced.
-/
import RequestProject.NavierStokes.TransverseFrameSplit

noncomputable section

namespace ClayNS.RateBlocks

open ClayNS.Waleffe ClayNS.Resolvent ClayNS.TTStar ClayNS.Schur

/-! ## 1.  A geometric series over the integers, uniform in the index set -/

/-- The kernel `2^{-|d|}` has total mass at most `4` over *any* finite set of
integers — in particular the bound is uniform in the set, hence in the
truncation. -/
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

/-- `blk` assigns each retained mode its dyadic rate block: `blk p = b` means the
viscous pair rate of the cell `p` at the output lies in `[4^b, 4^{b+1})`. -/
def DyadicRateBlocks (lam : Wave → ℝ) (modes : Finset Wave) (blk : Wave → ℤ) : Prop :=
  ∀ p ∈ modes, (4 : ℝ) ^ (blk p) ≤ lam p ∧ lam p < 4 * (4 : ℝ) ^ (blk p)

/-- The rate blocks of the retained modes carry at most `m` modes each. -/
def BlockMultiplicity (modes : Finset Wave) (blk : Wave → ℤ) (m : ℕ) : Prop :=
  ∀ b : ℤ, {p ∈ modes | blk p = b}.card ≤ m

/-- **The Schur row sum.**  With multiplicity `m`, the geometric kernel has row
sums at most `4m` — uniformly in the mode set. -/
theorem rowsum_le {modes : Finset Wave} {blk : Wave → ℤ} {m : ℕ}
    (hm : BlockMultiplicity modes blk m) (c : ℤ) :
    ∑ q ∈ modes, (1 / 2 : ℝ) ^ (c - blk q).natAbs ≤ 4 * m := by
  classical
  rw [Finset.sum_comp (fun b : ℤ => (1 / 2 : ℝ) ^ (c - b).natAbs) blk]
  have h1 : ∑ b ∈ modes.image blk,
        ({p ∈ modes | blk p = b}.card : ℕ) • (1 / 2 : ℝ) ^ (c - b).natAbs
      ≤ ∑ b ∈ modes.image blk, (m : ℝ) * (1 / 2 : ℝ) ^ (c - b).natAbs := by
    refine Finset.sum_le_sum fun b _ => ?_
    rw [nsmul_eq_mul]
    have hc : (({p ∈ modes | blk p = b}.card : ℝ)) ≤ (m : ℝ) := by exact_mod_cast hm b
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  refine h1.trans ?_
  rw [← Finset.mul_sum]
  have hgeo := sum_half_pow_shift_le (modes.image blk) c
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

/-! ## 3.  The pointwise Cauchy-kernel estimate -/

/-- **The elementary block estimate.**  If `s` sits in the dyadic window of
length ratio `4` starting at `L` and `t` is at least `4^d` times that window's
base, then the Cauchy-kernel pair term is controlled by the two normalized
masses with a factor decaying geometrically in `d`.  No square root and no
cancellation enter. -/
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

/-- **The pair term of the signed Gram form**, bounded by the two normalized cell
masses with a factor decaying geometrically in the rate-block distance. -/
theorem pair_term_le {lam : Wave → ℝ} {blk : Wave → ℤ} {G : Wave → Fin 3 → ℂ} {p q : Wave}
    (hp : (4 : ℝ) ^ (blk p) ≤ lam p ∧ lam p < 4 * (4 : ℝ) ^ (blk p))
    (hq : (4 : ℝ) ^ (blk q) ≤ lam q ∧ lam q < 4 * (4 : ℝ) ^ (blk q)) :
    (herm (G p) (G q)).re / (lam p + lam q)
      ≤ 2 * (1 / 2 : ℝ) ^ (blk p - blk q).natAbs * (nsq (G p) / lam p + nsq (G q) / lam q) := by
  have hlp : 0 < lam p := lt_of_lt_of_le (by positivity) hp.1
  have hlq : 0 < lam q := lt_of_lt_of_le (by positivity) hq.1
  have hsum : 0 < lam p + lam q := by linarith
  have hcs : (herm (G p) (G q)).re / (lam p + lam q)
      ≤ nrm (G p) * nrm (G q) / (lam p + lam q) := by
    exact (div_le_div_iff_of_pos_right hsum).mpr (herm_re_le_nrm_mul _ _)
  refine hcs.trans ?_
  have hnp : nrm (G p) ^ 2 = nsq (G p) := nrm_sq _
  have hnq : nrm (G q) ^ 2 = nsq (G q) := nrm_sq _
  rcases le_total (blk p) (blk q) with hle | hle
  · have ht : (4 : ℝ) ^ ((blk q - blk p).natAbs) * (4 : ℝ) ^ (blk p) ≤ lam q := by
      rw [four_zpow_natAbs_mul hle]; exact hq.1
    have h := amgm_block (nrm (G p)) (nrm (G q)) ((4 : ℝ) ^ (blk p)) (lam p) (lam q)
      ((blk q - blk p).natAbs) (by positivity) hp.1 hp.2 ht
    rw [hnp, hnq] at h
    rwa [show (blk p - blk q).natAbs = (blk q - blk p).natAbs from by omega]
  · have ht : (4 : ℝ) ^ ((blk p - blk q).natAbs) * (4 : ℝ) ^ (blk q) ≤ lam p := by
      rw [four_zpow_natAbs_mul hle]; exact hp.1
    have h := amgm_block (nrm (G q)) (nrm (G p)) ((4 : ℝ) ^ (blk q)) (lam q) (lam p)
      ((blk p - blk q).natAbs) (by positivity) hq.1 hq.2 ht
    rw [hnp, hnq] at h
    calc nrm (G p) * nrm (G q) / (lam p + lam q)
        = nrm (G q) * nrm (G p) / (lam q + lam p) := by ring_nf
      _ ≤ 2 * (1 / 2 : ℝ) ^ (blk p - blk q).natAbs * (nsq (G q) / lam q + nsq (G p) / lam p) := h
      _ = 2 * (1 / 2 : ℝ) ^ (blk p - blk q).natAbs
            * (nsq (G p) / lam p + nsq (G q) / lam q) := by ring

/-! ## 4.  The Schur bound in terms of the block multiplicity -/

/-- **The abstract Schur bound.**  For an arbitrary positive rate function whose
dyadic blocks carry at most `m` modes, the signed Gram form of *any* cell family
is bounded by `16m` times the rate-normalized ℓ² mass.  No cancellation is
used. -/
theorem sum_resForm_le_blockMultiplicity {lam : Wave → ℝ} {blk : Wave → ℤ} {m : ℕ}
    (modes : Finset Wave) (G : Wave → Fin 3 → ℂ)
    (hblk : DyadicRateBlocks lam modes blk) (hm : BlockMultiplicity modes blk m) :
    ∑ p ∈ modes, ∑ q ∈ modes, (herm (G p) (G q)).re / (lam p + lam q)
      ≤ 16 * m * ∑ p ∈ modes, nsq (G p) / lam p := by
  classical
  set M : Wave → ℝ := fun p => nsq (G p) / lam p with hM
  have hMnn : ∀ p ∈ modes, 0 ≤ M p := by
    intro p hp
    have hlp : 0 < lam p := lt_of_lt_of_le (by positivity) (hblk p hp).1
    exact div_nonneg (nsq_nonneg _) hlp.le
  have step1 : ∑ p ∈ modes, ∑ q ∈ modes, (herm (G p) (G q)).re / (lam p + lam q)
      ≤ ∑ p ∈ modes, ∑ q ∈ modes,
          2 * (1 / 2 : ℝ) ^ (blk p - blk q).natAbs * (M p + M q) := by
    refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => ?_
    exact pair_term_le (hblk p hp) (hblk q hq)
  refine step1.trans ?_
  set r : Wave → Wave → ℝ := fun p q => (1 / 2 : ℝ) ^ (blk p - blk q).natAbs with hr
  have hsplit : ∑ p ∈ modes, ∑ q ∈ modes, 2 * r p q * (M p + M q)
      = 2 * (∑ p ∈ modes, ∑ q ∈ modes, r p q * M p)
        + 2 * (∑ p ∈ modes, ∑ q ∈ modes, r p q * M q) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have hrow1 : ∑ p ∈ modes, ∑ q ∈ modes, r p q * M p ≤ 4 * m * ∑ p ∈ modes, M p := by
    have hterm : ∀ p ∈ modes, ∑ q ∈ modes, r p q * M p ≤ 4 * m * M p := by
      intro p hp
      have hrs := rowsum_le hm (blk p)
      have hMp := hMnn p hp
      have hEq : ∑ q ∈ modes, r p q * M p = (∑ q ∈ modes, r p q) * M p := by
        rw [Finset.sum_mul]
      have hEq2 : (∑ q ∈ modes, r p q) = ∑ q ∈ modes, (1 / 2 : ℝ) ^ (blk p - blk q).natAbs := rfl
      rw [hEq, hEq2]
      nlinarith
    calc ∑ p ∈ modes, ∑ q ∈ modes, r p q * M p ≤ ∑ p ∈ modes, 4 * m * M p :=
          Finset.sum_le_sum hterm
      _ = 4 * m * ∑ p ∈ modes, M p := by rw [Finset.mul_sum]
  have hrow2 : ∑ p ∈ modes, ∑ q ∈ modes, r p q * M q ≤ 4 * m * ∑ p ∈ modes, M p := by
    rw [Finset.sum_comm]
    have hterm : ∀ q ∈ modes, ∑ p ∈ modes, r p q * M q ≤ 4 * m * M q := by
      intro q hq
      have hrs := rowsum_le hm (blk q)
      have hMq := hMnn q hq
      have hEq : ∑ p ∈ modes, r p q * M q = (∑ p ∈ modes, r p q) * M q := by
        rw [Finset.sum_mul]
      have hEq2 : (∑ p ∈ modes, r p q) = ∑ p ∈ modes, (1 / 2 : ℝ) ^ (blk q - blk p).natAbs :=
        Finset.sum_congr rfl fun p _ => by
          rw [hr]
          exact congrArg _ (by omega : (blk p - blk q).natAbs = (blk q - blk p).natAbs)
      rw [hEq, hEq2]
      nlinarith
    calc ∑ q ∈ modes, ∑ p ∈ modes, r p q * M q ≤ ∑ q ∈ modes, 4 * m * M q :=
          Finset.sum_le_sum hterm
      _ = 4 * m * ∑ q ∈ modes, M q := by rw [Finset.mul_sum]
  rw [hsplit]
  linarith

/-- **The physical instance: `A = 32·m`.**  If the viscous pair rates of the
retained modes at the output `k` occupy dyadic blocks of multiplicity at most
`m`, then the outer-cell Gram operator bound holds with `A = 32m`, for every
cell family — no almost orthogonality, no signs, no field structure used. -/
theorem gramOperatorBound_of_rateBlockMultiplicity {nu : ℝ} {m : ℕ} (hnu : 0 < nu)
    (modes : Finset Wave) (G : Wave → Fin 3 → ℂ) (k : Wave) (blk : Wave → ℤ)
    (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hblk : DyadicRateBlocks (fun p => viscousPairRate nu p (k - p)) modes blk)
    (hm : BlockMultiplicity modes blk m) :
    GramOperatorBound nu modes G k (32 * m) := by
  classical
  have hmain := sum_resForm_le_blockMultiplicity (lam := fun p => viscousPairRate nu p (k - p))
    (blk := blk) (m := m) modes G hblk hm
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

/-! ## 5.  The matching lower bound: linear growth in the multiplicity is real -/

/-- **A uniform cell family forces `A ≥ card·νW/Λ`.**  If all retained pair rates
are at most `Λ` and all mode lengths at least `√W`, a family of equal nonzero
cells makes the signed Gram form as large as its trivial ℓ¹ majorant, so the
operator bound cannot hold with a constant smaller than `card·νW/Λ`. -/
theorem gramBound_const_cells_lower_bound {nu Λ W A : ℝ} (hnu : 0 < nu) (hW : 0 < W)
    (hΛ : 0 < Λ) (modes : Finset Wave) (hne : modes.Nonempty) (k : Wave) (v : Fin 3 → ℂ)
    (hv : 0 < nsq v)
    (hrate : ∀ p ∈ modes, 0 < viscousPairRate nu p (k - p))
    (hup : ∀ p ∈ modes, viscousPairRate nu p (k - p) ≤ Λ)
    (hWle : ∀ p ∈ modes, W ≤ wsq p)
    (h : GramOperatorBound nu modes (fun _ => v) k A) :
    (modes.card : ℝ) * (nu * W / Λ) ≤ A := by
  classical
  have hcard : (1 : ℝ) ≤ (modes.card : ℝ) := by
    have : 1 ≤ modes.card := Finset.card_pos.mpr hne
    exact_mod_cast this
  have hhv : (herm v v).re = nsq v := by
    rw [nsq_eq_herm_re]
  have hlow : (modes.card : ℝ) ^ 2 * (nsq v / (2 * Λ))
      ≤ ∑ p ∈ modes, ∑ q ∈ modes,
          (herm ((fun _ => v) p) ((fun _ => v) q)).re
            / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q)) := by
    have hterm : ∀ p ∈ modes, ∀ q ∈ modes,
        nsq v / (2 * Λ) ≤ (herm v v).re
          / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q)) := by
      intro p hp q hq
      rw [hhv]
      have h1 : viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q) ≤ 2 * Λ := by
        have := hup p hp; have := hup q hq; linarith
      have h2 : 0 < viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q) := by
        have := hrate p hp; have := hrate q hq; linarith
      exact div_le_div_of_nonneg_left hv.le h2 h1
    have hin : ∀ p ∈ modes, (modes.card : ℝ) * (nsq v / (2 * Λ))
        ≤ ∑ q ∈ modes, (herm v v).re
            / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q)) := by
      intro p hp
      have := Finset.sum_le_sum (fun q hq => hterm p hp q hq)
      simpa [Finset.sum_const, nsmul_eq_mul] using this
    have := Finset.sum_le_sum hin
    simpa [Finset.sum_const, nsmul_eq_mul, sq, mul_assoc] using this
  have hS : ∑ p ∈ modes, nsq ((fun _ => v) p) / wsq p ≤ (modes.card : ℝ) * (nsq v / W) := by
    have hterm : ∀ p ∈ modes, nsq v / wsq p ≤ nsq v / W := by
      intro p hp
      exact div_le_div_of_nonneg_left hv.le hW (hWle p hp)
    have := Finset.sum_le_sum hterm
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hSnn : 0 ≤ ∑ p ∈ modes, nsq ((fun _ => v) p) / wsq p := by
    refine Finset.sum_nonneg fun p hp => ?_
    have hwp : 0 < wsq p := lt_of_lt_of_le hW (hWle p hp)
    exact div_nonneg hv.le hwp.le
  rw [GramOperatorBound] at h
  rcases lt_or_ge A 0 with hA | hA
  · exfalso
    have hneg : A * (∑ p ∈ modes, nsq ((fun _ => v) p) / wsq p) / (2 * nu) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (by linarith)
      exact mul_nonpos_of_nonpos_of_nonneg hA.le hSnn
    have hpos : 0 < (modes.card : ℝ) ^ 2 * (nsq v / (2 * Λ)) := by
      have : (0 : ℝ) < (modes.card : ℝ) ^ 2 := by nlinarith
      have h2 : 0 < nsq v / (2 * Λ) := by positivity
      positivity
    linarith [hlow.trans h]
  · have hupper : A * (∑ p ∈ modes, nsq ((fun _ => v) p) / wsq p) / (2 * nu)
        ≤ A * ((modes.card : ℝ) * (nsq v / W)) / (2 * nu) := by
      have := mul_le_mul_of_nonneg_left hS hA
      exact div_le_div_of_nonneg_right this (by linarith) |>.trans_eq rfl
    have hkey : (modes.card : ℝ) ^ 2 * (nsq v / (2 * Λ))
        ≤ A * ((modes.card : ℝ) * (nsq v / W)) / (2 * nu) :=
      le_trans (hlow.trans h) hupper
    have hcpos : (0 : ℝ) < (modes.card : ℝ) := by linarith
    have hL : (modes.card : ℝ) ^ 2 * (nsq v / (2 * Λ))
        = (modes.card : ℝ) ^ 2 * nsq v / (2 * Λ) := by ring
    have hR : A * ((modes.card : ℝ) * (nsq v / W)) / (2 * nu)
        = A * (modes.card : ℝ) * nsq v / (2 * nu * W) := by
      field_simp
    rw [hL, hR, div_le_div_iff₀ (by positivity) (by positivity)] at hkey
    have hgoal : (modes.card : ℝ) * (nu * W / Λ) = (modes.card : ℝ) * (nu * W) / Λ := by ring
    rw [hgoal, div_le_iff₀ hΛ]
    have hposc : (0 : ℝ) < 2 * (modes.card : ℝ) * nsq v := by positivity
    nlinarith [hkey, hposc]

/-! ## 6.  The counterexample family -/

theorem wsq_axisWave' (a : ℤ) : wsq (axisWave a) = (a : ℝ) ^ 2 := wsq_axisWave a

theorem wsq_sub_axisWave (a b : ℤ) : wsq (axisWave a - axisWave b) = ((a : ℝ) - b) ^ 2 := by
  simp [wsq, axisWave, Fin.sum_univ_three]

/-- **Comparable shells defeat the operator bound too.**  For every `N` there is
a retained output `k ≠ 0`, a family of at least `N` nonzero modes with pairwise
comparable lengths, and a *transverse* cell family (each cell orthogonal to the
output, as the Leray projection forces) for which every constant `A` satisfying
the outer-cell Gram operator bound is at least `N`.

This is strictly stronger than the corresponding statement for the absolute
Schur constant: it defeats the weakest hypothesis the critical consumer needs,
so the truncation-uniform bound cannot follow from the kernel, transversality
and dyadic shell localization alone.  With
`gramOperatorBound_of_rateBlockMultiplicity` it also shows that the linear
dependence on the rate-block multiplicity is sharp. -/
theorem gramOperatorBound_fails_on_comparable_shells {nu : ℝ} (hnu : 0 < nu) (N : ℕ) :
    ∃ (modes : Finset Wave) (k : Wave) (v : Fin 3 → ℂ),
      N ≤ modes.card ∧ (0 : Wave) ∉ modes ∧ wsq k ≠ 0 ∧ 0 < nsq v ∧
      dotb (wC k) v = 0 ∧
      (∀ p ∈ modes, ∀ q ∈ modes, wsq p ≤ 4 * wsq q) ∧
      (∀ A : ℝ, GramOperatorBound nu modes (fun _ => v) k A → (N : ℝ) ≤ A) := by
  classical
  set n : ℤ := 8 * (N : ℤ) + 1 with hn
  have hnpos : 0 < n := by omega
  set modes : Finset Wave := (Finset.Icc n (2 * n)).image axisWave with hmodes
  have hmem : ∀ p ∈ modes, ∃ a : ℤ, n ≤ a ∧ a ≤ 2 * n ∧ p = axisWave a := by
    intro p hp
    rw [hmodes, Finset.mem_image] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    rw [Finset.mem_Icc] at ha
    exact ⟨a, ha.1, ha.2, rfl⟩
  have hcard : (modes.card : ℤ) = n + 1 := by
    rw [hmodes, Finset.card_image_of_injective _ axisWave_injective, Int.card_Icc]
    simp
    omega
  have hcardR : (modes.card : ℝ) = (n : ℝ) + 1 := by exact_mod_cast hcard
  have hne : modes.Nonempty := by
    refine ⟨axisWave n, ?_⟩
    rw [hmodes, Finset.mem_image]
    exact ⟨n, by rw [Finset.mem_Icc]; omega, rfl⟩
  refine ⟨modes, axisWave 1, e1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (N : ℤ) ≤ (modes.card : ℤ) := by omega
    exact_mod_cast this
  · intro h0
    obtain ⟨a, ha1, _, ha3⟩ := hmem 0 h0
    have hz : (0 : Wave) 0 = a := by rw [ha3]; simp [axisWave]
    simp only [Pi.zero_apply] at hz
    omega
  · rw [wsq_axisWave']; norm_num
  · simp [nsq, e1]
  · simp [dotb, wC, e1, axisWave]
  · intro p hp q hq
    obtain ⟨a, ha1, ha2, rfl⟩ := hmem p hp
    obtain ⟨b, hb1, hb2, rfl⟩ := hmem q hq
    rw [wsq_axisWave', wsq_axisWave']
    have h1 : (a : ℝ) ≤ 2 * (b : ℝ) := by
      have hab : a ≤ 2 * b := le_trans ha2 (by omega)
      exact_mod_cast hab
    have h2 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb1.trans_lt' hnpos
    have h3 : (0 : ℝ) ≤ (a : ℝ) := by
      have ha : (0 : ℤ) ≤ a := le_of_lt (hnpos.trans_le ha1)
      exact_mod_cast ha
    nlinarith
  · intro A hA
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ n)
    have hrate : ∀ p ∈ modes, 0 < viscousPairRate nu p (axisWave 1 - p) := by
      intro p hp
      obtain ⟨a, ha1, ha2, rfl⟩ := hmem p hp
      rw [viscousPairRate, wsq_axisWave', wsq_sub_axisWave]
      push_cast
      have haR : (n : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
      have : (0 : ℝ) < (a : ℝ) ^ 2 := by nlinarith
      nlinarith [sq_nonneg ((1 : ℝ) - (a : ℝ))]
    have hup : ∀ p ∈ modes, viscousPairRate nu p (axisWave 1 - p) ≤ nu * (8 * (n : ℝ) ^ 2) := by
      intro p hp
      obtain ⟨a, ha1, ha2, rfl⟩ := hmem p hp
      rw [viscousPairRate, wsq_axisWave', wsq_sub_axisWave]
      push_cast
      have haR : (n : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
      have haR2 : (a : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast ha2
      have h1 : (a : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith
      have h2 : ((1 : ℝ) - (a : ℝ)) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith [hn1, haR, haR2]
      nlinarith [mul_le_mul_of_nonneg_left
        (by linarith : (a : ℝ) ^ 2 + ((1 : ℝ) - (a : ℝ)) ^ 2 ≤ 8 * (n : ℝ) ^ 2) hnu.le]
    have hWle : ∀ p ∈ modes, (n : ℝ) ^ 2 ≤ wsq p := by
      intro p hp
      obtain ⟨a, ha1, ha2, rfl⟩ := hmem p hp
      rw [wsq_axisWave']
      have haR : (n : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
      nlinarith
    have hkey := gramBound_const_cells_lower_bound (nu := nu) (Λ := nu * (8 * (n : ℝ) ^ 2))
      (W := (n : ℝ) ^ 2) (A := A) hnu (by positivity) (by positivity) modes hne
      (axisWave 1) e1 (by simp [nsq, e1]) hrate hup hWle hA
    have hsimp : nu * (n : ℝ) ^ 2 / (nu * (8 * (n : ℝ) ^ 2)) = 1 / 8 := by
      field_simp
    rw [hsimp, hcardR] at hkey
    have hNn : (8 : ℝ) * (N : ℝ) + 1 = (n : ℝ) := by
      rw [hn]; push_cast; ring
    nlinarith [hkey, hNn]

/-! ## 7.  Inside one rate block: the obligation is square-root cancellation -/

theorem herm_sum_left (modes : Finset Wave) (G : Wave → Fin 3 → ℂ) (w : Fin 3 → ℂ) :
    herm (∑ p ∈ modes, G p) w = ∑ p ∈ modes, herm (G p) w := by
  classical
  simp only [herm, Finset.sum_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem herm_sum_right (modes : Finset Wave) (G : Wave → Fin 3 → ℂ) (w : Fin 3 → ℂ) :
    herm w (∑ q ∈ modes, G q) = ∑ q ∈ modes, herm w (G q) := by
  classical
  simp only [herm, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The mass of the aggregated cells is the *signed* double sum of the pairings:
the cancellation available inside a cluster is exactly the difference between
these two ways of counting. -/
theorem nsq_sum_eq_sum_sum_herm_re (modes : Finset Wave) (G : Wave → Fin 3 → ℂ) :
    nsq (∑ p ∈ modes, G p) = ∑ p ∈ modes, ∑ q ∈ modes, (herm (G p) (G q)).re := by
  classical
  rw [nsq_eq_herm_re, herm_sum_left]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [herm_sum_right, Complex.re_sum]

/-- The viscous pair rate is invariant under the reflection `p ↦ k − p`, so
degenerate rate clusters are not an empty hypothesis. -/
theorem viscousPairRate_reflect (nu : ℝ) (k p : Wave) :
    viscousPairRate nu (k - p) (k - (k - p)) = viscousPairRate nu p (k - p) := by
  rw [viscousPairRate, viscousPairRate, sub_sub_cancel]
  ring

/-- A concrete two-mode degenerate cluster: distinct nonzero modes at a nonzero
output sharing one viscous pair rate. -/
theorem exists_two_mode_degenerate_cluster (nu : ℝ) :
    ∃ (modes : Finset Wave) (k : Wave) (lam : ℝ),
      modes.card = 2 ∧ wsq k ≠ 0 ∧ (∀ p ∈ modes, wsq p ≠ 0) ∧
      (∀ p ∈ modes, viscousPairRate nu p (k - p) = lam) := by
  classical
  refine ⟨{axisWave 3, axisWave (-2)}, axisWave 1, nu * 13, ?_, ?_, ?_, ?_⟩
  · refine Finset.card_pair ?_
    intro hcon
    have := congrFun hcon 0
    simp [axisWave] at this
  · rw [wsq_axisWave']; norm_num
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> rw [wsq_axisWave'] <;> norm_num
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;>
      rw [viscousPairRate, wsq_axisWave', wsq_sub_axisWave] <;> push_cast <;> ring

/-- **The extremal cluster, exactly.**  Suppose all retained modes at the output
share one viscous pair rate — the degenerate configuration that the lower bound
`gramOperatorBound_fails_on_comparable_shells` exploits.  Then the outer-cell
Gram operator bound holds with constant `C` **iff** the aggregated cell has at
most `C` times the ℓ² mass of its summands; this direction supplies the bound
from the cancellation hypothesis.

So, at the extremal configuration, the remaining obligation is not an abstract
Schur estimate but a concrete statement about the physical field: the sum
`∑_{p ∈ cluster} P_k(N_p × u_{k−p})` — a piece of the Leray-projected
nonlinearity — must exhibit square-root cancellation relative to its cells. -/
theorem gramOperatorBound_of_cluster_cancellation {nu C lam : ℝ} (hnu : 0 < nu) (hC : 0 ≤ C)
    (modes : Finset Wave) (G : Wave → Fin 3 → ℂ) (k : Wave) (hlam : 0 < lam)
    (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hrate : ∀ p ∈ modes, viscousPairRate nu p (k - p) = lam)
    (hcanc : nsq (∑ p ∈ modes, G p) ≤ C * ∑ p ∈ modes, nsq (G p)) :
    GramOperatorBound nu modes G k C := by
  classical
  have hform : ∑ p ∈ modes, ∑ q ∈ modes,
      (herm (G p) (G q)).re
        / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))
      = nsq (∑ p ∈ modes, G p) / (2 * lam) := by
    rw [nsq_sum_eq_sum_sum_herm_re, Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp' => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun q hq' => ?_
    rw [hrate p hp', hrate q hq']
    ring_nf
  have hstep : nsq (∑ p ∈ modes, G p) / (2 * lam)
      ≤ C * (∑ p ∈ modes, nsq (G p) / wsq p) / (2 * nu) := by
    have h1 : nsq (∑ p ∈ modes, G p) / (2 * lam)
        ≤ (C * ∑ p ∈ modes, nsq (G p)) / (2 * lam) :=
      (div_le_div_iff_of_pos_right (by positivity)).mpr hcanc
    refine h1.trans ?_
    have h2 : (C * ∑ p ∈ modes, nsq (G p)) / (2 * lam)
        = C * ((∑ p ∈ modes, nsq (G p)) / (2 * lam)) := by ring
    rw [h2]
    have h3 : (∑ p ∈ modes, nsq (G p)) / (2 * lam)
        ≤ (∑ p ∈ modes, nsq (G p) / wsq p) / (2 * nu) := by
      rw [Finset.sum_div, Finset.sum_div]
      refine Finset.sum_le_sum fun p hpm => ?_
      have hwp : 0 < wsq p := lt_of_le_of_ne (wsq_nonneg' p) (Ne.symm (hp p hpm))
      have hkp : 0 ≤ wsq (k - p) := wsq_nonneg' (k - p)
      have hle : wsq p * (2 * nu) ≤ 2 * lam := by
        have := hrate p hpm
        rw [viscousPairRate] at this
        nlinarith
      rw [div_div]
      exact div_le_div_of_nonneg_left (nsq_nonneg _) (by positivity) hle
    have := mul_le_mul_of_nonneg_left h3 hC
    calc C * ((∑ p ∈ modes, nsq (G p)) / (2 * lam))
        ≤ C * ((∑ p ∈ modes, nsq (G p) / wsq p) / (2 * nu)) := this
      _ = C * (∑ p ∈ modes, nsq (G p) / wsq p) / (2 * nu) := by ring
  show ∑ p ∈ modes, ∑ q ∈ modes,
      (herm (G p) (G q)).re
        / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))
    ≤ C * (∑ p ∈ modes, nsq (G p) / wsq p) / (2 * nu)
  rw [hform]
  exact hstep

/-- The converse reading of the same identity: at a degenerate cluster the
operator bound *forces* the cancellation, with the constant scaled by the
length spread of the cluster.  Together with the previous theorem this is why
the obligation cannot be met without cancellation in the aggregated cell. -/
theorem cluster_cancellation_of_gramOperatorBound {nu C lam W : ℝ} (hnu : 0 < nu) (hW : 0 < W)
    (modes : Finset Wave) (G : Wave → Fin 3 → ℂ) (k : Wave) (hlam : 0 < lam)
    (hrate : ∀ p ∈ modes, viscousPairRate nu p (k - p) = lam)
    (hWle : ∀ p ∈ modes, W ≤ wsq p)
    (h : GramOperatorBound nu modes G k C) :
    nsq (∑ p ∈ modes, G p) ≤ C * (lam / (nu * W)) * ∑ p ∈ modes, nsq (G p) := by
  classical
  have hform : ∑ p ∈ modes, ∑ q ∈ modes,
      (herm (G p) (G q)).re
        / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))
      = nsq (∑ p ∈ modes, G p) / (2 * lam) := by
    rw [nsq_sum_eq_sum_sum_herm_re, Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp' => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun q hq' => ?_
    rw [hrate p hp', hrate q hq']
    ring_nf
  rw [GramOperatorBound, hform] at h
  have hsumnn : (0 : ℝ) ≤ ∑ p ∈ modes, nsq (G p) := Finset.sum_nonneg fun p _ => nsq_nonneg _
  rcases eq_or_lt_of_le hsumnn with hsum0 | hsumpos
  · have hGz : ∀ p ∈ modes, G p = 0 := by
      intro p hp
      have h0 : nsq (G p) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => nsq_nonneg (G q))).mp hsum0.symm p hp
      funext i
      exact vec_eq_zero_of_nrm_eq_zero (by rw [nrm, h0, Real.sqrt_zero]) i
    have hS : (∑ p ∈ modes, G p) = 0 := Finset.sum_eq_zero hGz
    rw [hS, ← hsum0]
    simp [nsq]
  have hC : 0 ≤ C := by
    have hMpos : 0 < ∑ p ∈ modes, nsq (G p) / wsq p := by
      have hex : ∃ p ∈ modes, 0 < nsq (G p) := by
        by_contra hcon
        push_neg at hcon
        have : ∑ p ∈ modes, nsq (G p) = 0 :=
          Finset.sum_eq_zero fun p hp => le_antisymm (hcon p hp) (nsq_nonneg _)
        linarith
      obtain ⟨p, hp, hppos⟩ := hex
      refine Finset.sum_pos' (fun q hq => div_nonneg (nsq_nonneg _)
        (le_of_lt (lt_of_lt_of_le hW (hWle q hq)))) ⟨p, hp, ?_⟩
      exact div_pos hppos (lt_of_lt_of_le hW (hWle p hp))
    have hlhs : 0 ≤ nsq (∑ p ∈ modes, G p) / (2 * lam) :=
      div_nonneg (nsq_nonneg _) (by positivity)
    by_contra hneg
    push_neg at hneg
    have : C * (∑ p ∈ modes, nsq (G p) / wsq p) / (2 * nu) < 0 := by
      apply div_neg_of_neg_of_pos _ (by positivity)
      exact mul_neg_of_neg_of_pos hneg hMpos
    linarith [h.trans_lt this]
  have hmass : ∑ p ∈ modes, nsq (G p) / wsq p ≤ (∑ p ∈ modes, nsq (G p)) / W := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun p hpm => ?_
    exact div_le_div_of_nonneg_left (nsq_nonneg _) hW (hWle p hpm)
  have hstep : nsq (∑ p ∈ modes, G p) / (2 * lam)
      ≤ C * ((∑ p ∈ modes, nsq (G p)) / W) / (2 * nu) := by
    refine h.trans ?_
    have := mul_le_mul_of_nonneg_left hmass hC
    exact (div_le_div_iff_of_pos_right (by positivity)).mpr this
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at hstep
  have hkey : nsq (∑ p ∈ modes, G p) * (2 * nu) * W
      ≤ C * (∑ p ∈ modes, nsq (G p)) * (2 * lam) := by
    have hmul := mul_le_mul_of_nonneg_right hstep hW.le
    have hR : C * ((∑ p ∈ modes, nsq (G p)) / W) * (2 * lam) * W
        = C * (∑ p ∈ modes, nsq (G p)) * (2 * lam) := by
      field_simp
    linarith [hmul, hR.le, hR.ge]
  rw [← sub_nonneg]
  have hexp : C * (lam / (nu * W)) * (∑ p ∈ modes, nsq (G p)) - nsq (∑ p ∈ modes, G p)
      = (C * (∑ p ∈ modes, nsq (G p)) * (2 * lam) - nsq (∑ p ∈ modes, G p) * (2 * nu) * W)
        / (2 * nu * W) := by
    field_simp
  rw [hexp]
  apply div_nonneg _ (by positivity)
  linarith

/-! ## 8.  The aggregated cell is a piece of the Leray-projected nonlinearity -/

theorem leray_sum (k : Wave) (modes : Finset Wave) (X : Wave → Fin 3 → ℂ) :
    leray k (∑ p ∈ modes, X p) = ∑ p ∈ modes, leray k (X p) := by
  classical
  funext i
  simp only [leray, Finset.sum_apply, herm_sum_right, Finset.sum_div, Finset.sum_mul,
    Finset.sum_sub_distrib]

/-- The aggregate of the literal outer cells over any set of modes is the Leray
projection of a single convolution sum — a piece of the projected
nonlinearity at the output. -/
theorem sum_outerCellVec_eq (N u : Wave → Fin 3 → ℂ) (k : Wave) (modes : Finset Wave) :
    ∑ p ∈ modes, outerCellVec N u k p
      = leray k (∑ p ∈ modes, cross (N p) (u (k - p))) := by
  rw [leray_sum]
  rfl

/-- **The obligation, in physical form.**  At a degenerate rate cluster the
outcome the critical spacetime consumer needs is exactly this: the projected
convolution sum `P_k ∑_{p} N_p × u_{k−p}` over the cluster must have at most `C`
times the ℓ² mass of its own cells. -/
theorem gramOperatorBound_outerCells_of_cluster_cancellation {nu C lam : ℝ} (hnu : 0 < nu)
    (hC : 0 ≤ C) (modes : Finset Wave) (N u : Wave → Fin 3 → ℂ) (k : Wave) (hlam : 0 < lam)
    (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hrate : ∀ p ∈ modes, viscousPairRate nu p (k - p) = lam)
    (hcanc : nsq (leray k (∑ p ∈ modes, cross (N p) (u (k - p))))
      ≤ C * ∑ p ∈ modes, nsq (outerCellVec N u k p)) :
    GramOperatorBound nu modes (fun p => outerCellVec N u k p) k C := by
  refine gramOperatorBound_of_cluster_cancellation hnu hC modes _ k hlam hp hrate ?_
  rw [sum_outerCellVec_eq]
  exact hcanc

end ClayNS.RateBlocks

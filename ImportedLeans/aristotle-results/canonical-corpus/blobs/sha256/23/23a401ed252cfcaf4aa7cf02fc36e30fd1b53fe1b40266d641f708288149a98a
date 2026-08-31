/-
# The cardinality-free lattice Riesz convolution bound

`WaleffeCriticalCompanionSummation.lean` reduces the critical production to the
companion `∑_k |k| M(k)²` of the cellwise majorant `M(k) = ∑_a E_a E_{k−a}`, and
`WaleffeOutputGainFibre.lean` proves the low-output gain that licenses that
reduction.  Two ways of summing the fibre were available there, and both are
lossy in the Galerkin cutoff: the Wiener bound pays an `ℓ¹` velocity norm, and
the cardinality bound pays `#S`.

This file removes both.  The fibre is summed as an *operator*: Cauchy–Schwarz
against the Riesz weight `|a|⁻¹|k−a|⁻¹`, whose square sums to `C/|k|` on the
lattice.

* `lattice_riesz_convolution` — the master bound `∑_a |a|⁻²|k−a|⁻² ≤ 4000/|k|`
  for `k ≠ 0`, uniformly over *all* finite index sets of incidences;
* `cellCompanion_le_enstrophy_sq` — hence
  `∑_k |k| M(k)² ≤ 4000 (∑_a |a|² E_a²)²`;
* `GalerkinFlow.abs_critProd_le_enstrophy_absorption` — the critical absorption
  on the literal Galerkin carrier with **no** cardinality, shell count, matching
  number or Wiener `ℓ¹` factor: for every `θ > 0`,
  `|P_crit| ≤ θ D_crit + θ⁻¹ · 1000 · (enstrophy)²`.

The enstrophy square cannot be improved in order of growth on the flat
high-high configuration of `cellwise_companion_not_controlled_by_energy_enstrophy`:
there the companion is at least `N¹⁰` while the enstrophy is at most `C N⁵`, so
both sides of `cellCompanion_le_enstrophy_sq` grow like `N¹⁰` in `N`.  Together
with that no-go — which rules out any bound of the shape energy × enstrophy —
the cellwise companion is now pinned from both sides.

What this does **not** give is the Clay target.  The absorption leaves the
companion `‖u‖⁴_{H¹}`, quartic in `H¹`, whereas the energy inequality only
supplies `∫₀^T ‖u‖²_{H¹} ≤ E₀/ν`.  A cutoff-uniform bound for
`∫₀^T (companion) dt` is exactly the remaining time-integrated companion budget,
and is not proved here.
-/
import RequestProject.NavierStokes.LatticeShellCounting
import RequestProject.NavierStokes.WaleffeOutputGainFibre

noncomputable section

open Finset

namespace ClayNS.Waleffe

/-! ## 1. The master convolution bound -/

/-- **The lattice Riesz convolution bound.**  For every nonzero output `k` and
*every* finite index set of incidences,

  `∑_a |a|⁻² |k − a|⁻² ≤ 4000 / |k|`.

The constant is absolute: there is no fibre cardinality, shell count, matching
number or Wiener `ℓ¹` factor, so the bound is uniform in the Galerkin cutoff. -/
theorem lattice_riesz_convolution {k : Wave} (hk : k ≠ 0) (S : Finset Wave)
    (h0 : ∀ p ∈ S, p ≠ 0) (h1 : ∀ p ∈ S, k - p ≠ 0) :
    ∑ p ∈ S, 1 / (wlen p) ^ 2 * (1 / (wlen (k - p)) ^ 2) ≤ 4000 / wlen k := by
  classical
  set K := wlen k with hK
  have hK1 : 1 ≤ K := one_le_wlen_of_ne_zero hk
  have hKpos : (0 : ℝ) < K := by linarith
  set f : Wave → ℝ := fun p => 1 / (wlen p) ^ 2 * (1 / (wlen (k - p)) ^ 2) with hf
  set P1 : Wave → Prop := fun p => wlen p ≤ K / 2 with hP1
  set P2 : Wave → Prop := fun p => wlen (k - p) ≤ K / 2 with hP2
  set P3 : Wave → Prop := fun p => wlen p ≤ 2 * K with hP3
  have e1 := Finset.sum_filter_add_sum_filter_not S P1 f
  have e2 := Finset.sum_filter_add_sum_filter_not (S.filter (fun p => ¬ P1 p)) P2 f
  have e3 := Finset.sum_filter_add_sum_filter_not
    ((S.filter (fun p => ¬ P1 p)).filter (fun p => ¬ P2 p)) P3 f
  -- region A : the incidence is low, so the partner carries the output
  have hA : ∑ p ∈ S.filter P1, f p ≤ 52 / K := by
    have hbound : ∀ p ∈ S.filter P1, f p ≤ (4 / K ^ 2) * (1 / (wlen p) ^ 2) := by
      intro p hp
      simp only [Finset.mem_filter, hP1] at hp
      have hleg : K ≤ wlen p + wlen (k - p) := wlen_le_legs k p
      have hkp : K / 2 ≤ wlen (k - p) := by linarith [hp.2]
      have hkppos : (0 : ℝ) < wlen (k - p) := by linarith
      have hppos : (0 : ℝ) < wlen p := wlen_pos_of_ne_zero (h0 p hp.1)
      have hle : 1 / (wlen (k - p)) ^ 2 ≤ 4 / K ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hkp, hkppos, hKpos]
      rw [hf]
      calc 1 / (wlen p) ^ 2 * (1 / (wlen (k - p)) ^ 2)
          ≤ 1 / (wlen p) ^ 2 * (4 / K ^ 2) := mul_le_mul_of_nonneg_left hle (by positivity)
        _ = (4 / K ^ 2) * (1 / (wlen p) ^ 2) := by ring
    have hsum : ∑ p ∈ S.filter P1, f p
        ≤ (4 / K ^ 2) * ∑ p ∈ S.filter P1, 1 / (wlen p) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hbound
    have hinner : ∑ p ∈ S.filter P1, 1 / (wlen p) ^ 2 ≤ 26 * (K / 2) := by
      refine sum_inv_sq_le_of_bounded _ (by positivity) ?_ ?_
      · intro p hp; exact h0 p (Finset.mem_filter.1 hp).1
      · intro p hp
        have := (Finset.mem_filter.1 hp).2
        simpa [hP1] using this
    have hfin : (4 / K ^ 2) * (26 * (K / 2)) = 52 / K := by field_simp; ring
    calc ∑ p ∈ S.filter P1, f p ≤ (4 / K ^ 2) * ∑ p ∈ S.filter P1, 1 / (wlen p) ^ 2 := hsum
      _ ≤ (4 / K ^ 2) * (26 * (K / 2)) := mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = 52 / K := hfin
  -- region B : the partner is low
  have hB : ∑ p ∈ (S.filter (fun p => ¬ P1 p)).filter P2, f p ≤ 52 / K := by
    set B := (S.filter (fun p => ¬ P1 p)).filter P2 with hBdef
    have hBmem : ∀ p ∈ B, p ∈ S ∧ ¬ P1 p ∧ P2 p := by
      intro p hp
      simp only [hBdef, Finset.mem_filter] at hp
      exact ⟨hp.1.1, hp.1.2, hp.2⟩
    have hbound : ∀ p ∈ B, f p ≤ (4 / K ^ 2) * (1 / (wlen (k - p)) ^ 2) := by
      intro p hp
      obtain ⟨hpS, hnp1, _⟩ := hBmem p hp
      have hppos : (0 : ℝ) < wlen p := wlen_pos_of_ne_zero (h0 p hpS)
      have hpge : K / 2 ≤ wlen p := by
        rw [hP1] at hnp1
        push_neg at hnp1
        linarith [hnp1]
      have hkppos : (0 : ℝ) < wlen (k - p) := wlen_pos_of_ne_zero (h1 p hpS)
      have hle : 1 / (wlen p) ^ 2 ≤ 4 / K ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hpge, hppos, hKpos]
      rw [hf]
      exact mul_le_mul_of_nonneg_right hle (by positivity)
    have hsum : ∑ p ∈ B, f p ≤ (4 / K ^ 2) * ∑ p ∈ B, 1 / (wlen (k - p)) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hbound
    have hinj : ∀ x ∈ B, ∀ y ∈ B, (fun p : Wave => k - p) x = (fun p : Wave => k - p) y → x = y := by
      intro x _ y _ h
      exact sub_right_injective h
    have himg : ∑ p ∈ B, 1 / (wlen (k - p)) ^ 2
        = ∑ q ∈ B.image (fun p => k - p), 1 / (wlen q) ^ 2 :=
      (Finset.sum_image (f := fun q => 1 / (wlen q) ^ 2) (g := fun p => k - p) hinj).symm
    have hinner : ∑ q ∈ B.image (fun p => k - p), 1 / (wlen q) ^ 2 ≤ 26 * (K / 2) := by
      refine sum_inv_sq_le_of_bounded _ (by positivity) ?_ ?_
      · intro q hq
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
        exact h1 p (hBmem p hp).1
      · intro q hq
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
        have := (hBmem p hp).2.2
        simpa [hP2] using this
    have hfin : (4 / K ^ 2) * (26 * (K / 2)) = 52 / K := by field_simp; ring
    calc ∑ p ∈ B, f p ≤ (4 / K ^ 2) * ∑ p ∈ B, 1 / (wlen (k - p)) ^ 2 := hsum
      _ = (4 / K ^ 2) * ∑ q ∈ B.image (fun p => k - p), 1 / (wlen q) ^ 2 := by rw [himg]
      _ ≤ (4 / K ^ 2) * (26 * (K / 2)) := mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = 52 / K := hfin
  -- region C₁ : both legs comparable to the output
  have hC1 : ∑ p ∈ ((S.filter (fun p => ¬ P1 p)).filter (fun p => ¬ P2 p)).filter P3, f p
      ≤ 3328 / K := by
    set C := ((S.filter (fun p => ¬ P1 p)).filter (fun p => ¬ P2 p)).filter P3 with hCdef
    have hCmem : ∀ p ∈ C, p ∈ S ∧ ¬ P1 p ∧ ¬ P2 p ∧ P3 p := by
      intro p hp
      simp only [hCdef, Finset.mem_filter] at hp
      exact ⟨hp.1.1.1, hp.1.1.2, hp.1.2, hp.2⟩
    have hbound : ∀ p ∈ C, f p ≤ 16 / K ^ 4 := by
      intro p hp
      obtain ⟨hpS, hnp1, hnp2, _⟩ := hCmem p hp
      have hpge : K / 2 ≤ wlen p := by
        rw [hP1] at hnp1; push_neg at hnp1; linarith [hnp1]
      have hqge : K / 2 ≤ wlen (k - p) := by
        rw [hP2] at hnp2; push_neg at hnp2; linarith [hnp2]
      have hppos : (0 : ℝ) < wlen p := wlen_pos_of_ne_zero (h0 p hpS)
      have hqpos : (0 : ℝ) < wlen (k - p) := wlen_pos_of_ne_zero (h1 p hpS)
      have ha : 1 / (wlen p) ^ 2 ≤ 4 / K ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hpge, hppos, hKpos]
      have hb : 1 / (wlen (k - p)) ^ 2 ≤ 4 / K ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hqge, hqpos, hKpos]
      have hprod : 1 / (wlen p) ^ 2 * (1 / (wlen (k - p)) ^ 2) ≤ (4 / K ^ 2) * (4 / K ^ 2) :=
        mul_le_mul ha hb (by positivity) (by positivity)
      have hval : (4 / K ^ 2) * (4 / K ^ 2) = 16 / K ^ 4 := by field_simp; ring
      rw [hf]
      linarith [hprod]
    have hcard : (C.card : ℝ) ≤ 26 * (2 * K) ^ 3 := by
      refine card_le_of_bounded _ (by positivity) ?_ ?_
      · intro p hp; exact h0 p (hCmem p hp).1
      · intro p hp
        have := (hCmem p hp).2.2.2
        simpa [hP3] using this
    have hsum : ∑ p ∈ C, f p ≤ (C.card : ℝ) * (16 / K ^ 4) := by
      calc ∑ p ∈ C, f p ≤ ∑ _p ∈ C, (16 / K ^ 4) := Finset.sum_le_sum hbound
        _ = (C.card : ℝ) * (16 / K ^ 4) := by rw [Finset.sum_const, nsmul_eq_mul]
    have hfin : (26 * (2 * K) ^ 3) * (16 / K ^ 4) = 3328 / K := by field_simp; ring
    calc ∑ p ∈ C, f p ≤ (C.card : ℝ) * (16 / K ^ 4) := hsum
      _ ≤ (26 * (2 * K) ^ 3) * (16 / K ^ 4) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 3328 / K := hfin
  -- region C₂ : the incidence is far above the output
  have hC2 : ∑ p ∈ ((S.filter (fun p => ¬ P1 p)).filter (fun p => ¬ P2 p)).filter
      (fun p => ¬ P3 p), f p ≤ 208 / K := by
    set D := ((S.filter (fun p => ¬ P1 p)).filter (fun p => ¬ P2 p)).filter (fun p => ¬ P3 p)
      with hDdef
    have hDmem : ∀ p ∈ D, p ∈ S ∧ ¬ P3 p := by
      intro p hp
      simp only [hDdef, Finset.mem_filter] at hp
      exact ⟨hp.1.1.1, hp.2⟩
    have hbound : ∀ p ∈ D, f p ≤ 4 * (1 / (wlen p) ^ 4) := by
      intro p hp
      obtain ⟨hpS, hnp3⟩ := hDmem p hp
      have hpge : 2 * K < wlen p := by
        rw [hP3] at hnp3; push_neg at hnp3; exact hnp3
      have hppos : (0 : ℝ) < wlen p := wlen_pos_of_ne_zero (h0 p hpS)
      have hqpos : (0 : ℝ) < wlen (k - p) := wlen_pos_of_ne_zero (h1 p hpS)
      have hsym : wlen (p - k) = wlen (k - p) := by
        rw [show p - k = -(k - p) by abel, wlen_neg]
      have hrev : wlen p ≤ K + wlen (k - p) := by
        have h := wlen_le_legs p k
        rw [hsym] at h
        exact h
      have hhalf : wlen p / 2 ≤ wlen (k - p) := by linarith
      have hle : 1 / (wlen (k - p)) ^ 2 ≤ 4 / (wlen p) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hhalf, hqpos, hppos]
      rw [hf]
      calc 1 / (wlen p) ^ 2 * (1 / (wlen (k - p)) ^ 2)
          ≤ 1 / (wlen p) ^ 2 * (4 / (wlen p) ^ 2) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ = 4 * (1 / (wlen p) ^ 4) := by field_simp
    have hinner : ∑ p ∈ D, 1 / (wlen p) ^ 4 ≤ 104 / (2 * K) := by
      refine sum_inv_four_le_of_lower _ (by linarith) ?_ ?_
      · intro p hp; exact h0 p (hDmem p hp).1
      · intro p hp
        have hnp3 := (hDmem p hp).2
        rw [hP3] at hnp3; push_neg at hnp3
        exact hnp3.le
    have hsum : ∑ p ∈ D, f p ≤ 4 * ∑ p ∈ D, 1 / (wlen p) ^ 4 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hbound
    have hfin : (4 : ℝ) * (104 / (2 * K)) = 208 / K := by field_simp; ring
    calc ∑ p ∈ D, f p ≤ 4 * ∑ p ∈ D, 1 / (wlen p) ^ 4 := hsum
      _ ≤ 4 * (104 / (2 * K)) := mul_le_mul_of_nonneg_left hinner (by norm_num)
      _ = 208 / K := hfin
  have htotal : (52 : ℝ) / K + 52 / K + 3328 / K + 208 / K ≤ 4000 / K := by
    have hval : (52 : ℝ) / K + 52 / K + 3328 / K + 208 / K = 3640 / K := by ring
    rw [hval]
    gcongr
    norm_num
  linarith [hA, hB, hC1, hC2, e1, e2, e3, htotal]

/-! ## 2. The cardinality-free companion bound -/

/-- **The companion of the low-output gain is bounded by the square of the
enstrophy.**  No fibre cardinality, no Wiener `ℓ¹` norm, absolute constant:

  `∑_k |k| (∑_a E_a E_{k−a})² ≤ 4000 (∑_a |a|² E_a²)²`.

This is the cutoff-uniform fibre summation that preserves the low-output gain. -/
theorem cellCompanion_le_enstrophy_sq {S T : Finset Wave} {E : Wave → ℝ}
    (hEsupp : ∀ a, a ∉ S → E a = 0) (hS : ∀ a ∈ S, a ≠ 0)
    (hT : ∀ k ∈ T, k ≠ 0) :
    cellCompanion S T E ≤ 4000 * (∑ a ∈ S, (wlen a) ^ 2 * (E a) ^ 2) ^ 2 := by
  classical
  set G : Wave → ℝ := fun a => (wlen a) ^ 2 * (E a) ^ 2 with hG
  have hG0 : ∀ a, 0 ≤ G a := by intro a; rw [hG]; positivity
  have hGS : ∀ b, b ∉ S → G b = 0 := by
    intro b hb
    rw [hG]
    simp [hEsupp b hb]
  have hfibre : ∀ k ∈ T, wlen k * (cellMajorant S E k) ^ 2 ≤ 4000 * ∑ a ∈ S, G a * G (k - a) := by
    intro k hk
    have hk0 : k ≠ 0 := hT k hk
    have hKpos : (0 : ℝ) < wlen k := wlen_pos_of_ne_zero hk0
    set S' := S.filter (fun a => k - a ≠ 0) with hS'
    have hMeq : cellMajorant S E k = ∑ a ∈ S', E a * E (k - a) := by
      rw [cellMajorant, hS']
      refine (Finset.sum_filter_of_ne ?_).symm
      intro a _ hne hzero
      rw [hzero] at hne
      have hzeroE : E (0 : Wave) = 0 := hEsupp 0 (fun h0mem => hS 0 h0mem rfl)
      rw [hzeroE, mul_zero] at hne
      exact hne rfl
    have hS'0 : ∀ a ∈ S', a ≠ 0 := fun a ha => hS a (Finset.mem_filter.1 ha).1
    have hS'1 : ∀ a ∈ S', k - a ≠ 0 := fun a ha => (Finset.mem_filter.1 ha).2
    have hCS : (∑ a ∈ S', E a * E (k - a)) ^ 2
        ≤ (∑ a ∈ S', (1 / (wlen a) ^ 2) * (1 / (wlen (k - a)) ^ 2))
          * (∑ a ∈ S', G a * G (k - a)) := by
      have hfactor : ∀ a ∈ S', E a * E (k - a)
          = ((1 / wlen a) * (1 / wlen (k - a)))
            * ((wlen a * E a) * (wlen (k - a) * E (k - a))) := by
        intro a ha
        have ha1 : wlen a ≠ 0 := ne_of_gt (wlen_pos_of_ne_zero (hS'0 a ha))
        have ha2 : wlen (k - a) ≠ 0 := ne_of_gt (wlen_pos_of_ne_zero (hS'1 a ha))
        field_simp
      have hsq1 : ∀ a ∈ S', ((1 / wlen a) * (1 / wlen (k - a))) ^ 2
          = (1 / (wlen a) ^ 2) * (1 / (wlen (k - a)) ^ 2) := by
        intro a _; ring
      have hsq2 : ∀ a ∈ S', ((wlen a * E a) * (wlen (k - a) * E (k - a))) ^ 2
          = G a * G (k - a) := by
        intro a _; rw [hG]; ring
      calc (∑ a ∈ S', E a * E (k - a)) ^ 2
          = (∑ a ∈ S', ((1 / wlen a) * (1 / wlen (k - a)))
              * ((wlen a * E a) * (wlen (k - a) * E (k - a)))) ^ 2 := by
            rw [Finset.sum_congr rfl hfactor]
        _ ≤ (∑ a ∈ S', ((1 / wlen a) * (1 / wlen (k - a))) ^ 2)
              * (∑ a ∈ S', ((wlen a * E a) * (wlen (k - a) * E (k - a))) ^ 2) :=
            Finset.sum_mul_sq_le_sq_mul_sq S' _ _
        _ = (∑ a ∈ S', (1 / (wlen a) ^ 2) * (1 / (wlen (k - a)) ^ 2))
              * (∑ a ∈ S', G a * G (k - a)) := by
            rw [Finset.sum_congr rfl hsq1, Finset.sum_congr rfl hsq2]
    have hriesz : ∑ a ∈ S', (1 / (wlen a) ^ 2) * (1 / (wlen (k - a)) ^ 2) ≤ 4000 / wlen k :=
      lattice_riesz_convolution hk0 S' hS'0 hS'1
    have hGpos : 0 ≤ ∑ a ∈ S', G a * G (k - a) :=
      Finset.sum_nonneg fun a _ => mul_nonneg (hG0 a) (hG0 _)
    have hstep : (cellMajorant S E k) ^ 2 ≤ (4000 / wlen k) * ∑ a ∈ S', G a * G (k - a) := by
      rw [hMeq]
      exact le_trans hCS (mul_le_mul_of_nonneg_right hriesz hGpos)
    have hmul : wlen k * (cellMajorant S E k) ^ 2
        ≤ wlen k * ((4000 / wlen k) * ∑ a ∈ S', G a * G (k - a)) :=
      mul_le_mul_of_nonneg_left hstep (le_of_lt hKpos)
    have heq : wlen k * ((4000 / wlen k) * ∑ a ∈ S', G a * G (k - a))
        = 4000 * ∑ a ∈ S', G a * G (k - a) := by
      field_simp
    have hsubset : ∑ a ∈ S', G a * G (k - a) ≤ ∑ a ∈ S, G a * G (k - a) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun a _ _ => mul_nonneg (hG0 a) (hG0 _))
    calc wlen k * (cellMajorant S E k) ^ 2
        ≤ 4000 * ∑ a ∈ S', G a * G (k - a) := by rw [← heq]; exact hmul
      _ ≤ 4000 * ∑ a ∈ S, G a * G (k - a) :=
          mul_le_mul_of_nonneg_left hsubset (by norm_num)
  have hsum : cellCompanion S T E ≤ 4000 * ∑ k ∈ T, ∑ a ∈ S, G a * G (k - a) := by
    rw [cellCompanion, Finset.mul_sum]
    exact Finset.sum_le_sum hfibre
  have hswap : ∑ k ∈ T, ∑ a ∈ S, G a * G (k - a) = ∑ a ∈ S, G a * ∑ k ∈ T, G (k - a) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
  have hshift : ∀ a ∈ S, G a * ∑ k ∈ T, G (k - a) ≤ G a * ∑ b ∈ S, G b := fun a _ =>
    mul_le_mul_of_nonneg_left (sum_shift_le hG0 hGS a) (hG0 a)
  have hfinal : ∑ a ∈ S, G a * ∑ k ∈ T, G (k - a) ≤ (∑ a ∈ S, G a) * (∑ b ∈ S, G b) := by
    calc ∑ a ∈ S, G a * ∑ k ∈ T, G (k - a) ≤ ∑ a ∈ S, G a * ∑ b ∈ S, G b :=
          Finset.sum_le_sum hshift
      _ = (∑ a ∈ S, G a) * (∑ b ∈ S, G b) := by rw [← Finset.sum_mul]
  calc cellCompanion S T E ≤ 4000 * ∑ k ∈ T, ∑ a ∈ S, G a * G (k - a) := hsum
    _ = 4000 * ∑ a ∈ S, G a * ∑ k ∈ T, G (k - a) := by rw [hswap]
    _ ≤ 4000 * ((∑ a ∈ S, G a) * (∑ b ∈ S, G b)) :=
        mul_le_mul_of_nonneg_left hfinal (by norm_num)
    _ = 4000 * (∑ a ∈ S, G a) ^ 2 := by ring

/-! ## 3. The critical absorption on the physical carrier -/

namespace GalerkinFlow

variable (G : GalerkinFlow)

/-- **The cutoff-uniform critical absorption.**  On the literal Galerkin carrier,
for every `θ > 0`,

  `|P_crit| ≤ θ · D_crit + θ⁻¹ · 1000 · (∑_a |a|² ‖u_a‖²)²`,

with an absolute constant and **no** fibre cardinality, shell count, matching
number or Wiener `ℓ¹` factor.  The low-output gain is proved, not assumed. -/
theorem abs_critProd_le_enstrophy_absorption (t : ℝ) {theta : ℝ} (hth : 0 < theta) :
    |G.critProd t| ≤ theta * G.critDiss t
      + (1 / theta) * (1000 * (∑ a ∈ G.modes, (wlen a) ^ 2 * nrm (G.u t a) ^ 2) ^ 2) := by
  classical
  set E : Wave → ℝ := fun a => nrm (G.u t a) with hE
  have hE0 : ∀ a, 0 ≤ E a := fun a => nrm_nonneg _
  have hEsupp : ∀ a, a ∉ G.modes → E a = 0 := fun a ha => G.nrm_u_support t ha
  have hS : ∀ a ∈ G.modes, a ≠ 0 := by
    intro a ha h0
    exact G.wsq_ne_zero_of_mem ha (by rw [h0]; simp [wsq])
  have hgain : ∀ k ∈ G.modes, nrm (G.force t k) ≤ wlen k * cellMajorant G.modes E k :=
    fun k hk => G.nrm_force_le_output_gain t (G.wsq_ne_zero_of_mem hk)
  have hcs : |G.critProd t|
      ≤ Real.sqrt (G.critDiss t) * Real.sqrt (cellCompanion G.modes G.modes E) :=
    abs_critProduction_le_cellCompanion hE0 (fun k hk => G.wsq_ne_zero_of_mem hk) hgain
  have hcomp : cellCompanion G.modes G.modes E
      ≤ 4000 * (∑ a ∈ G.modes, (wlen a) ^ 2 * (E a) ^ 2) ^ 2 :=
    cellCompanion_le_enstrophy_sq hEsupp hS hS
  have hD0 : 0 ≤ G.critDiss t := critDissipation_nonneg _ _
  set Z : ℝ := ∑ a ∈ G.modes, (wlen a) ^ 2 * (E a) ^ 2 with hZ
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun a _ => by positivity
  have hsqrt : Real.sqrt (cellCompanion G.modes G.modes E) ≤ Real.sqrt 4000 * Z := by
    have h1 : Real.sqrt (cellCompanion G.modes G.modes E) ≤ Real.sqrt (4000 * Z ^ 2) :=
      Real.sqrt_le_sqrt hcomp
    have h2 : Real.sqrt (4000 * Z ^ 2) = Real.sqrt 4000 * Z := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hZ0]
    linarith [h1, h2.le, h2.ge]
  have hmain : |G.critProd t| ≤ Real.sqrt (G.critDiss t) * (Real.sqrt 4000 * Z) :=
    le_trans hcs (mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _))
  -- weighted Young
  have hyoung : Real.sqrt (G.critDiss t) * (Real.sqrt 4000 * Z)
      ≤ theta * G.critDiss t + (1 / theta) * (1000 * Z ^ 2) := by
    have hsq : (Real.sqrt (G.critDiss t)) ^ 2 = G.critDiss t := Real.sq_sqrt hD0
    have hkey : 0 ≤ (Real.sqrt theta * Real.sqrt (G.critDiss t)
        - (1 / (2 * Real.sqrt theta)) * (Real.sqrt 4000 * Z)) ^ 2 := sq_nonneg _
    have hthpos : 0 < Real.sqrt theta := Real.sqrt_pos.2 hth
    have hthsq : (Real.sqrt theta) ^ 2 = theta := Real.sq_sqrt hth.le
    have h4000 : (Real.sqrt 4000) ^ 2 = 4000 := Real.sq_sqrt (by norm_num)
    have hne : Real.sqrt theta ≠ 0 := ne_of_gt hthpos
    have hexpand : (Real.sqrt theta * Real.sqrt (G.critDiss t)
        - (1 / (2 * Real.sqrt theta)) * (Real.sqrt 4000 * Z)) ^ 2
        = (Real.sqrt theta) ^ 2 * (Real.sqrt (G.critDiss t)) ^ 2
          - Real.sqrt (G.critDiss t) * (Real.sqrt 4000 * Z)
          + (1 / (4 * (Real.sqrt theta) ^ 2)) * ((Real.sqrt 4000) ^ 2 * Z ^ 2) := by
      field_simp
      ring
    rw [hthsq, hsq, h4000] at hexpand
    have hpos := hkey
    rw [hexpand] at hpos
    have hval : (1 / (4 * theta)) * ((4000 : ℝ) * Z ^ 2) = (1 / theta) * (1000 * Z ^ 2) := by
      field_simp
      ring
    rw [hval] at hpos
    linarith [hpos]
  linarith [hmain, hyoung]

end GalerkinFlow

end ClayNS.Waleffe

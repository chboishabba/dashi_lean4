/-
# The external cross-triad residue as a frequency commutator, class by class

`WaleffeExternalCrossTriadCells.lean` proves the exact same-object identity: after
the shared-output-fibre reindexing `a ↦ k − a` the external residue of the
resonant pair `p + q = k` is *equal* to one half of the helicity-**gap**-weighted
sum of projected cross energies,

  `2 R^{ext}_{p,q} = ∑_a (λ_{k−a} − λ_a) · Re⟪P_k(u_a × u_{k−a}), u_p × u_q⟫`,

with no residual antisymmetry defect.  This file develops the two consequences
that the analytic payment needs.

## 1. The gain is the *output* frequency

`abs_wlen_partner_sub_le_output`: for **every** lattice pair `a, k − a` summing to
`k`,

  `| |k − a| − |a| | ≤ |k|` ,

and also `| |k−a| − |a| | ≤ |k − 2a|`, so the helicity gap of a co-helical field
obeys

  `|λ_{k−a} − λ_a| ≤ min (|k|, |k − 2a|)` .

The multiplier difference is therefore controlled by the **output** frequency,
never by the (possibly enormous) individual leg frequencies: the external
residue behaves like a frequency commutator on the whole carrier, not only on a
matched selection.  `abs_externalResidue_le_output_frequency_sum` and
`abs_externalResidue_le_output_energy` are the resulting estimates; the latter is

  `|R^{ext}_{p,q}| ≤ ½ |p+q| · E · ‖u_p‖ ‖u_q‖` ,

cutoff-uniform, with no cardinality, shell or Wiener factor.

## 2. The signed Bony split

`bonyClass` routes each incidence `a` of the fibre `k` into exactly one of the
four classes `LH`, `HL`, `HH→low`, `comparable` (threshold `θ`), and
`sum_split_four` / `sum_cells_eq_bony_split` split the residue accordingly.  The
split is an **equality of signed sums**, taken *before* any absolute value, so it
introduces no shell count, no matching number and no triangle-inequality loss.

The partner map `a ↦ k − a` fixes the classes `HH→low` and `comparable` and
exchanges `LH ↔ HL` (`bonyClass_partner`), so the gap-weighted pairing identity
holds *classwise* (`two_mul_sum_cells_filter_eq_pairing`).

## 3. Classwise payment

* `abs_bonyCells_HHlow_le` — on the `HH→low` class the output frequency is
  `θ`-small compared with the leg frequencies, so this class costs at most
  `(θ/2)·√(𝔇E)·‖u_p‖‖u_q‖`: an arbitrarily small share of the enstrophy-level
  budget.  This is the near-diagonal commutator gain, exactly where the raw
  convolution multiplicity is worst.
* `abs_bonyCells_LH_le`, `abs_bonyCells_HL_le`, `abs_bonyCells_comparable_le` —
  the other three classes are bounded at the same `√(𝔇E)` level as the
  unclassified residue, with constants `1/(2(1−θ))` and `1/(2θ)`.

**What this does not close.**  The classwise bounds above are still obtained by
bounding *each cell* and summing absolute values inside a class; they are
enstrophy-level (`√(𝔇E)`), not critical (`H^{1/2}`).  The open package A2 — a
cutoff-independent critical payment of the complete *signed* classwise sum — is
untouched by this file; what is established is the exact signed routing it must
act on, and the fact that the `HH→low` class already carries a free small
parameter.
-/
import RequestProject.NavierStokes.WaleffeExternalCrossTriadCells

noncomputable section

namespace ClayNS.Waleffe

/-! ## The output-frequency bound on the helicity gap -/

theorem wlen_nonneg' (k : Wave) : 0 ≤ wlen k := Real.sqrt_nonneg _

/-- **The partner frequency difference is bounded by the output frequency.**
For any decomposition `a + (k − a) = k` of the output wavevector, the difference
of the two leg frequencies is at most the output frequency. -/
theorem abs_wlen_partner_sub_le_output (k a : Wave) : |wlen (k - a) - wlen a| ≤ wlen k := by
  have h1 : wlen (k - a) ≤ wlen k + wlen a := by
    have h := wlen_triangle k (-a)
    rw [← sub_eq_add_neg, wlen_neg] at h
    exact h
  have h2 : wlen a ≤ wlen k + wlen (k - a) := by
    have h := wlen_triangle k (-(k - a))
    rw [← sub_eq_add_neg, wlen_neg] at h
    have hka : k - (k - a) = a := by abel
    rwa [hka] at h
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- The same difference is also bounded by the *separation* frequency `|k − 2a|`
(the near-diagonal gain).  Combining the two: `min (|k|, |k − 2a|)`. -/
theorem abs_wlen_partner_sub_le_min (k a : Wave) :
    |wlen (k - a) - wlen a| ≤ min (wlen k) (wlen (k - a - a)) :=
  le_min (abs_wlen_partner_sub_le_output k a) (abs_wlen_sub_le (k - a) a)

/-- **The co-helical helicity gap is an output-frequency commutator.**  If every
mode carries the same helicity sign, the helicity gap of the shared-fibre
partners is at most the output frequency `|k|`. -/
theorem abs_helicity_gap_le_output {k a : Wave} (l : Wave → ℝ) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hl : ∀ b, l b = s * wlen b) : |l (k - a) - l a| ≤ wlen k := by
  have h : |l (k - a) - l a| = |wlen (k - a) - wlen a| := by
    rw [hl, hl, ← mul_sub, abs_mul]
    rcases hs with h | h <;> simp [h]
  rw [h]
  exact abs_wlen_partner_sub_le_output k a

/-- **The external cross-triad residue is a frequency commutator with the output
frequency as gain.**  For a co-helical field the whole external residue of the
pair `(p,q)` is bounded by the *output* frequency `|k|` times the mass of the
external convolution — no individual leg frequency appears. -/
theorem abs_externalResidue_le_output_frequency_sum (modes : Finset Wave)
    (u : Wave → Fin 3 → ℂ) {k p q : Wave} (hpq : p + q = k) (hk : wsq k ≠ 0)
    (hsupp : ∀ a, a ∉ modes → u a = 0) (l : Wave → ℝ) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hl : ∀ a, l a = s * wlen a)
    (hbel : ∀ a, cross (wC a) (u a) = fun i => (-Complex.I) * (l a : ℂ) * u a i) :
    |(herm (fun i => -(leray k (externalAdvection modes u k p q) i))
        (cross (u p) (u q))).re|
      ≤ (1 / 2) * wlen k * ∑ a ∈ extIdxSym modes k p q,
          (nrm (u a) * nrm (u (k - a)) * (nrm (u p) * nrm (u q))) := by
  refine le_trans (abs_externalResidue_le_helicity_gap_sum modes u hpq hk hsupp l hbel) ?_
  have hterm : ∑ a ∈ extIdxSym modes k p q,
      |l (k - a) - l a| * (nrm (u a) * nrm (u (k - a)) * (nrm (u p) * nrm (u q)))
      ≤ ∑ a ∈ extIdxSym modes k p q,
        wlen k * (nrm (u a) * nrm (u (k - a)) * (nrm (u p) * nrm (u q))) := by
    refine Finset.sum_le_sum fun a _ => ?_
    exact mul_le_mul_of_nonneg_right (abs_helicity_gap_le_output l hs hl)
      (mul_nonneg (mul_nonneg (nrm_nonneg _) (nrm_nonneg _))
        (mul_nonneg (nrm_nonneg _) (nrm_nonneg _)))
  rw [← Finset.mul_sum] at hterm
  rw [mul_assoc]
  linarith

/-! ## Cauchy–Schwarz on the external fibre -/

/-- The external convolution mass of a fibre is at most the energy. -/
theorem sum_pair_nrm_le_energy (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (S : Finset Wave)
    (k : Wave) (hsupp : ∀ a, a ∉ modes → u a = 0) :
    ∑ a ∈ S, nrm (u a) * nrm (u (k - a)) ≤ ∑ m ∈ modes, nsq (u m) := by
  classical
  set E := ∑ m ∈ modes, nsq (u m) with hE
  have hEnn : 0 ≤ E := Finset.sum_nonneg fun m _ => nsq_nonneg _
  have h := sum_mul_le_sqrt_mul S (fun a => nrm (u a)) (fun a => nrm (u (k - a)))
    (fun a => nrm_nonneg _) (fun a => nrm_nonneg _) E E ?_ ?_
  · calc ∑ a ∈ S, nrm (u a) * nrm (u (k - a)) ≤ Real.sqrt (E * E) := h
      _ = E := Real.sqrt_mul_self hEnn
  · refine le_trans (le_of_eq ?_) (sum_nsq_le_energy modes u S hsupp)
    exact Finset.sum_congr rfl fun a _ => nrm_sq _
  · refine le_trans (le_of_eq ?_) (sum_partner_nsq_le_energy modes u S k hsupp)
    exact Finset.sum_congr rfl fun a _ => nrm_sq _

/-- The frequency-weighted external convolution mass, weighted by the **first**
leg, is at most `√(𝔇E)`. -/
theorem sum_wlen_pair_le_sqrt (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (S : Finset Wave)
    (k : Wave) (hsupp : ∀ a, a ∉ modes → u a = 0) :
    ∑ a ∈ S, wlen a * (nrm (u a) * nrm (u (k - a)))
      ≤ Real.sqrt ((∑ m ∈ modes, wsq m * nsq (u m)) * (∑ m ∈ modes, nsq (u m))) := by
  classical
  set D := ∑ m ∈ modes, wsq m * nsq (u m) with hD
  set E := ∑ m ∈ modes, nsq (u m) with hE
  have h := sum_mul_le_sqrt_mul S (fun a => wlen a * nrm (u a)) (fun a => nrm (u (k - a)))
    (fun a => mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg _)) (fun a => nrm_nonneg _) D E
    ?_ ?_
  · refine le_trans (le_of_eq ?_) h
    exact Finset.sum_congr rfl fun a _ => by ring
  · refine le_trans (le_of_eq ?_) (sum_wsq_nsq_le_dissipation modes u S hsupp)
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_pow, wlen, Real.sq_sqrt (wsq_nonneg' a), nrm_sq]
  · refine le_trans (le_of_eq ?_) (sum_partner_nsq_le_energy modes u S k hsupp)
    exact Finset.sum_congr rfl fun a _ => nrm_sq _

/-- The same, weighted by the **partner** leg. -/
theorem sum_wlen_partner_pair_le_sqrt (modes : Finset Wave) (u : Wave → Fin 3 → ℂ)
    (S : Finset Wave) (k : Wave) (hsupp : ∀ a, a ∉ modes → u a = 0) :
    ∑ a ∈ S, wlen (k - a) * (nrm (u a) * nrm (u (k - a)))
      ≤ Real.sqrt ((∑ m ∈ modes, wsq m * nsq (u m)) * (∑ m ∈ modes, nsq (u m))) := by
  classical
  set D := ∑ m ∈ modes, wsq m * nsq (u m) with hD
  set E := ∑ m ∈ modes, nsq (u m) with hE
  have h := sum_mul_le_sqrt_mul S (fun a => wlen (k - a) * nrm (u (k - a)))
    (fun a => nrm (u a))
    (fun a => mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg _)) (fun a => nrm_nonneg _) D E
    ?_ ?_
  · refine le_trans (le_of_eq ?_) h
    exact Finset.sum_congr rfl fun a _ => by ring
  · refine le_trans (le_of_eq ?_) (sum_partner_wsq_nsq_le_dissipation modes u S k hsupp)
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_pow, wlen, Real.sq_sqrt (wsq_nonneg' (k - a)), nrm_sq]
  · refine le_trans (le_of_eq ?_) (sum_nsq_le_energy modes u S hsupp)
    exact Finset.sum_congr rfl fun a _ => nrm_sq _

/-- **The output-frequency energy bound for the external residue.**  For a
co-helical field, `|R^{ext}_{p,q}| ≤ ½ |k| E ‖u_p‖ ‖u_q‖` with `k = p + q`:
the residue costs the *output* frequency times the energy, cutoff-uniformly. -/
theorem abs_externalResidue_le_output_energy (modes : Finset Wave)
    (u : Wave → Fin 3 → ℂ) {k p q : Wave} (hpq : p + q = k) (hk : wsq k ≠ 0)
    (hsupp : ∀ a, a ∉ modes → u a = 0) (l : Wave → ℝ) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hl : ∀ a, l a = s * wlen a)
    (hbel : ∀ a, cross (wC a) (u a) = fun i => (-Complex.I) * (l a : ℂ) * u a i) :
    |(herm (fun i => -(leray k (externalAdvection modes u k p q) i))
        (cross (u p) (u q))).re|
      ≤ (1 / 2) * wlen k * (∑ m ∈ modes, nsq (u m)) * (nrm (u p) * nrm (u q)) := by
  classical
  refine le_trans
    (abs_externalResidue_le_output_frequency_sum modes u hpq hk hsupp l hs hl hbel) ?_
  set S := extIdxSym modes k p q with hS
  set W := nrm (u p) * nrm (u q) with hW
  have hWnn : 0 ≤ W := mul_nonneg (nrm_nonneg _) (nrm_nonneg _)
  have hfact : ∑ a ∈ S, (nrm (u a) * nrm (u (k - a)) * W)
      = (∑ a ∈ S, nrm (u a) * nrm (u (k - a))) * W := by
    rw [Finset.sum_mul]
  rw [hfact]
  have hmass := sum_pair_nrm_le_energy modes u S k hsupp
  have hnn : (0:ℝ) ≤ 1 / 2 * wlen k := by
    have := wlen_nonneg' k
    linarith
  have := mul_le_mul_of_nonneg_right hmass hWnn
  calc 1 / 2 * wlen k * ((∑ a ∈ S, nrm (u a) * nrm (u (k - a))) * W)
      ≤ 1 / 2 * wlen k * ((∑ m ∈ modes, nsq (u m)) * W) :=
        mul_le_mul_of_nonneg_left this hnn
    _ = 1 / 2 * wlen k * (∑ m ∈ modes, nsq (u m)) * W := by ring

/-! ## The Bony classification of the external incidences -/

open Classical in
/-- **The Bony class of the incidence `a` in the output fibre `k`**, at
threshold `θ`:
`0 = LH` (first leg low), `1 = HL` (partner leg low), `2 = HH→low` (both legs
high compared with the output), `3 = comparable`.  The four classes are
mutually exclusive and exhaustive by construction. -/
def bonyClass (θ : ℝ) (k a : Wave) : Fin 4 :=
  if wlen k ≤ θ * min (wlen a) (wlen (k - a)) then 2
  else if wlen a ≤ θ * wlen k then 0
  else if wlen (k - a) ≤ θ * wlen k then 1
  else 3

/-- **The exact four-way signed split of any incidence sum.**  This is an
equality in the ambient additive monoid — no absolute values, no triangle
inequality, hence no shell, matching or cardinality factor. -/
theorem sum_split_four {M : Type*} [AddCommMonoid M] (S : Finset Wave) (g : Wave → Fin 4)
    (V : Wave → M) :
    ∑ a ∈ S, V a =
      (∑ a ∈ S with g a = 0, V a) + (∑ a ∈ S with g a = 1, V a)
        + (∑ a ∈ S with g a = 2, V a) + (∑ a ∈ S with g a = 3, V a) := by
  classical
  rw [← Finset.sum_fiberwise S g V, Fin.sum_univ_four]

/-! ### Characterisation of the four classes -/

theorem bonyClass_eq_two_iff (θ : ℝ) (k a : Wave) :
    bonyClass θ k a = 2 ↔ wlen k ≤ θ * min (wlen a) (wlen (k - a)) := by
  classical
  unfold bonyClass
  split_ifs with h1 h2 h3 <;> simp_all

theorem bonyClass_eq_zero_iff (θ : ℝ) (k a : Wave) :
    bonyClass θ k a = 0 ↔
      ¬ (wlen k ≤ θ * min (wlen a) (wlen (k - a))) ∧ wlen a ≤ θ * wlen k := by
  classical
  unfold bonyClass
  split_ifs with h1 h2 h3 <;> simp_all

theorem bonyClass_eq_one_iff (θ : ℝ) (k a : Wave) :
    bonyClass θ k a = 1 ↔
      ¬ (wlen k ≤ θ * min (wlen a) (wlen (k - a))) ∧ ¬ (wlen a ≤ θ * wlen k)
        ∧ wlen (k - a) ≤ θ * wlen k := by
  classical
  unfold bonyClass
  split_ifs with h1 h2 h3 <;> simp_all

theorem bonyClass_eq_three_iff (θ : ℝ) (k a : Wave) :
    bonyClass θ k a = 3 ↔
      ¬ (wlen k ≤ θ * min (wlen a) (wlen (k - a))) ∧ ¬ (wlen a ≤ θ * wlen k)
        ∧ ¬ (wlen (k - a) ≤ θ * wlen k) := by
  classical
  unfold bonyClass
  split_ifs with h1 h2 h3 <;> simp_all

/-- The triangle inequality in the form used by the classification. -/
theorem wlen_le_legs (k a : Wave) : wlen k ≤ wlen a + wlen (k - a) := by
  have h := wlen_triangle a (k - a)
  have hka : a + (k - a) = k := by abel
  rwa [hka] at h

/-- Below the Bony threshold `θ < 1/2` the two legs cannot both be low unless the
class is `HH→low`. -/
theorem not_both_legs_low {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : 2 * θ < 1) (k a : Wave)
    (hA : ¬ (wlen k ≤ θ * min (wlen a) (wlen (k - a))))
    (hB : wlen a ≤ θ * wlen k) : ¬ (wlen (k - a) ≤ θ * wlen k) := by
  intro hC
  apply hA
  have htri := wlen_le_legs k a
  have hknn := wlen_nonneg' k
  have hk0 : wlen k ≤ 0 := by nlinarith
  have hmin : 0 ≤ θ * min (wlen a) (wlen (k - a)) :=
    mul_nonneg hθ0 (le_min (wlen_nonneg' a) (wlen_nonneg' (k - a)))
  linarith

/-- **The partner map fixes the classes `HH→low` and `comparable`, and exchanges
`LH ↔ HL`.**  (Below the Bony threshold `θ < 1/2`.) -/
theorem bonyClass_partner {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : 2 * θ < 1) (k a : Wave) :
    bonyClass θ k (k - a) =
      (if bonyClass θ k a = 0 then 1 else if bonyClass θ k a = 1 then 0
        else bonyClass θ k a) := by
  classical
  have hka : k - (k - a) = a := by abel
  have hmineq : min (wlen (k - a)) (wlen (k - (k - a))) = min (wlen a) (wlen (k - a)) := by
    rw [hka, min_comm]
  by_cases hA : wlen k ≤ θ * min (wlen a) (wlen (k - a))
  · have h1 : bonyClass θ k (k - a) = 2 := by
      rw [bonyClass_eq_two_iff, hmineq]; exact hA
    have h2 : bonyClass θ k a = 2 := (bonyClass_eq_two_iff θ k a).mpr hA
    rw [h1, h2]
    decide
  · have hA' : ¬ (wlen k ≤ θ * min (wlen (k - a)) (wlen (k - (k - a)))) := by
      rw [hmineq]; exact hA
    by_cases hB : wlen a ≤ θ * wlen k
    · have hC : ¬ (wlen (k - a) ≤ θ * wlen k) := not_both_legs_low hθ0 hθ1 k a hA hB
      have h1 : bonyClass θ k (k - a) = 1 := by
        refine (bonyClass_eq_one_iff θ k (k - a)).mpr ⟨hA', hC, ?_⟩
        rw [hka]; exact hB
      have h2 : bonyClass θ k a = 0 := (bonyClass_eq_zero_iff θ k a).mpr ⟨hA, hB⟩
      rw [h1, h2]
      decide
    · by_cases hC : wlen (k - a) ≤ θ * wlen k
      · have h1 : bonyClass θ k (k - a) = 0 :=
          (bonyClass_eq_zero_iff θ k (k - a)).mpr ⟨hA', hC⟩
        have h2 : bonyClass θ k a = 1 := (bonyClass_eq_one_iff θ k a).mpr ⟨hA, hB, hC⟩
        rw [h1, h2]
        decide
      · have h1 : bonyClass θ k (k - a) = 3 := by
          refine (bonyClass_eq_three_iff θ k (k - a)).mpr ⟨hA', hC, ?_⟩
          rw [hka]; exact hB
        have h2 : bonyClass θ k a = 3 := (bonyClass_eq_three_iff θ k a).mpr ⟨hA, hB, hC⟩
        rw [h1, h2]
        decide

/-- `HH→low` is a partner-invariant class. -/
theorem bonyClass_partner_two (θ : ℝ) (k a : Wave) :
    bonyClass θ k (k - a) = 2 ↔ bonyClass θ k a = 2 := by
  have hka : k - (k - a) = a := by abel
  rw [bonyClass_eq_two_iff, bonyClass_eq_two_iff, hka, min_comm]

/-- `comparable` is a partner-invariant class. -/
theorem bonyClass_partner_three (θ : ℝ) (k a : Wave) :
    bonyClass θ k (k - a) = 3 ↔ bonyClass θ k a = 3 := by
  have hka : k - (k - a) = a := by abel
  rw [bonyClass_eq_three_iff, bonyClass_eq_three_iff, hka, min_comm]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, h2⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, h2⟩

/-! ## The classwise pairing identity -/

/-- **The gap-weighted pairing identity, restricted to a partner-invariant class
of incidences.**  Exactly as for the whole fibre, the class-restricted signed
sum of cells equals one half of the gap-weighted pairing over the same class. -/
theorem two_mul_sum_cells_filter_eq_pairing (modes : Finset Wave) (u : Wave → Fin 3 → ℂ)
    (k p q : Wave) (hk : wsq k ≠ 0) (P : Wave → Prop) [DecidablePred P]
    (hP : ∀ a, P a ↔ P (k - a)) (l : Wave → ℝ)
    (hbel : ∀ a, cross (wC a) (u a) = fun i => (-Complex.I) * (l a : ℂ) * u a i) :
    2 * ∑ a ∈ (extIdxSym modes k p q).filter P, crossCell u k p q a
      = ∑ a ∈ (extIdxSym modes k p q).filter P,
          (l (k - a) - l a)
            * (herm (leray k (cross (u a) (u (k - a)))) (cross (u p) (u q))).re := by
  classical
  set S := (extIdxSym modes k p q).filter P with hS
  have hcl : ∀ a ∈ S, k - a ∈ S := by
    intro a ha
    rw [hS, Finset.mem_filter] at ha ⊢
    exact ⟨extIdxSym_partner_mem ha.1, (hP a).mp ha.2⟩
  have hdouble : 2 * ∑ a ∈ S, crossCell u k p q a
      = ∑ a ∈ S, (crossCell u k p q a + crossCell u k p q (k - a)) := by
    rw [Finset.sum_add_distrib,
      sum_partner_reindex S k hcl (fun a => crossCell u k p q a)]
    ring
  rw [hdouble]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact crossCell_partner_sum hk u (hbel a) (hbel (k - a))

/-- The signed contribution of one Bony class to the external residue. -/
def bonyCells (θ : ℝ) (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (k p q : Wave)
    (c : Fin 4) : ℝ :=
  ∑ a ∈ (extIdxSym modes k p q).filter (fun a => bonyClass θ k a = c),
    crossCell u k p q a

open Classical in
/-- **The external residue splits exactly, and with signs retained, into its four
Bony classes.**  The identity holds before any absolute value is taken, so no
shell count, matching number or Wiener factor is created by the routing. -/
theorem externalResidue_eq_bony_split (θ : ℝ) (modes : Finset Wave) (u : Wave → Fin 3 → ℂ)
    {k p q : Wave} (hpq : p + q = k) (hsupp : ∀ a, a ∉ modes → u a = 0) :
    (herm (fun i => -(leray k (externalAdvection modes u k p q) i))
        (cross (u p) (u q))).re
      = bonyCells θ modes u k p q 0 + bonyCells θ modes u k p q 1
        + bonyCells θ modes u k p q 2 + bonyCells θ modes u k p q 3 := by
  classical
  rw [externalResidue_eq_sum_cells]
  have hext : (modes.erase p).erase q = extIdx modes p q := rfl
  rw [hext, sum_cells_eq_sym modes u hpq hsupp]
  exact sum_split_four _ (fun a => bonyClass θ k a) _

/-! ## Classwise estimates -/

/-- A convenient abbreviation for the classwise bounds. -/
theorem abs_bonyCells_le_of_gap_bound (θ : ℝ) (modes : Finset Wave) (u : Wave → Fin 3 → ℂ)
    {k p q : Wave} (hk : wsq k ≠ 0) (c : Fin 4)
    (hinv : ∀ a, bonyClass θ k a = c ↔ bonyClass θ k (k - a) = c)
    (l : Wave → ℝ)
    (hbel : ∀ a, cross (wC a) (u a) = fun i => (-Complex.I) * (l a : ℂ) * u a i)
    (w : Wave → ℝ) (hw : ∀ a ∈ (extIdxSym modes k p q).filter (fun a => bonyClass θ k a = c),
      |l (k - a) - l a| ≤ w a) :
    |bonyCells θ modes u k p q c|
      ≤ (1 / 2) * ∑ a ∈ (extIdxSym modes k p q).filter (fun a => bonyClass θ k a = c),
          w a * (nrm (u a) * nrm (u (k - a)) * (nrm (u p) * nrm (u q))) := by
  classical
  set S := (extIdxSym modes k p q).filter (fun a => bonyClass θ k a = c) with hS
  have hid := two_mul_sum_cells_filter_eq_pairing modes u k p q hk
    (fun a => bonyClass θ k a = c) (fun a => hinv a) l hbel
  have habs : |2 * bonyCells θ modes u k p q c|
      ≤ ∑ a ∈ S, w a * (nrm (u a) * nrm (u (k - a)) * (nrm (u p) * nrm (u q))) := by
    rw [bonyCells, hid]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun a ha => ?_
    refine le_trans (abs_pairing_term_le k a p q u hk _) ?_
    exact mul_le_mul_of_nonneg_right (hw a ha)
      (mul_nonneg (mul_nonneg (nrm_nonneg _) (nrm_nonneg _))
        (mul_nonneg (nrm_nonneg _) (nrm_nonneg _)))
  rw [abs_mul] at habs
  simp only [abs_two] at habs
  linarith

/-- **The `HH→low` class carries a free small parameter.**  On the class where
the output frequency is `θ`-small compared with both legs, the helicity gap is at
most `θ |a|`, so this class of the external residue costs at most
`(θ/2)·√(𝔇E)·‖u_p‖‖u_q‖`: an arbitrarily small share of the enstrophy-level
budget.  This is the near-diagonal (`a ≈ k − a`) commutator gain, precisely where
the raw convolution multiplicity is worst. -/
theorem abs_bonyCells_HHlow_le {θ : ℝ} (hθ : 0 ≤ θ) (modes : Finset Wave)
    (u : Wave → Fin 3 → ℂ) {k p q : Wave} (hk : wsq k ≠ 0)
    (hsupp : ∀ a, a ∉ modes → u a = 0) (l : Wave → ℝ) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hl : ∀ a, l a = s * wlen a)
    (hbel : ∀ a, cross (wC a) (u a) = fun i => (-Complex.I) * (l a : ℂ) * u a i) :
    |bonyCells θ modes u k p q 2|
      ≤ (θ / 2) * Real.sqrt ((∑ m ∈ modes, wsq m * nsq (u m)) * (∑ m ∈ modes, nsq (u m)))
          * (nrm (u p) * nrm (u q)) := by
  classical
  set S := (extIdxSym modes k p q).filter (fun a => bonyClass θ k a = 2) with hS
  set W := nrm (u p) * nrm (u q) with hW
  have hWnn : 0 ≤ W := mul_nonneg (nrm_nonneg _) (nrm_nonneg _)
  -- on the class, the gap is at most `θ |a|`
  have hgap : ∀ a ∈ S, |l (k - a) - l a| ≤ θ * wlen a := by
    intro a ha
    have hc : bonyClass θ k a = 2 := by
      rw [hS, Finset.mem_filter] at ha; exact ha.2
    have hA : wlen k ≤ θ * min (wlen a) (wlen (k - a)) := by
      by_contra hcon
      rw [bonyClass, if_neg hcon] at hc
      split_ifs at hc <;> simp_all
    have hmin : θ * min (wlen a) (wlen (k - a)) ≤ θ * wlen a :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hθ
    exact le_trans (abs_helicity_gap_le_output l hs hl) (le_trans hA hmin)
  have hstep := abs_bonyCells_le_of_gap_bound θ modes u hk 2
    (fun a => (bonyClass_partner_two θ k a).symm) l hbel (fun a => θ * wlen a) hgap
  refine le_trans hstep ?_
  have hrw : ∑ a ∈ S, θ * wlen a * (nrm (u a) * nrm (u (k - a)) * W)
      = θ * ((∑ a ∈ S, wlen a * (nrm (u a) * nrm (u (k - a)))) * W) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hrw]
  have hcs := sum_wlen_pair_le_sqrt modes u S k hsupp
  have h1 : (∑ a ∈ S, wlen a * (nrm (u a) * nrm (u (k - a)))) * W
      ≤ Real.sqrt ((∑ m ∈ modes, wsq m * nsq (u m)) * (∑ m ∈ modes, nsq (u m))) * W :=
    mul_le_mul_of_nonneg_right hcs hWnn
  nlinarith [Real.sqrt_nonneg ((∑ m ∈ modes, wsq m * nsq (u m)) * (∑ m ∈ modes, nsq (u m)))]

/-- **The `comparable` class.**  There the output frequency is at most `|a|/θ`,
so the class is bounded at the enstrophy level with constant `1/(2θ)`. -/
theorem abs_bonyCells_comparable_le {θ : ℝ} (hθ : 0 < θ) (modes : Finset Wave)
    (u : Wave → Fin 3 → ℂ) {k p q : Wave} (hk : wsq k ≠ 0)
    (hsupp : ∀ a, a ∉ modes → u a = 0) (l : Wave → ℝ) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hl : ∀ a, l a = s * wlen a)
    (hbel : ∀ a, cross (wC a) (u a) = fun i => (-Complex.I) * (l a : ℂ) * u a i) :
    |bonyCells θ modes u k p q 3|
      ≤ (1 / (2 * θ))
          * Real.sqrt ((∑ m ∈ modes, wsq m * nsq (u m)) * (∑ m ∈ modes, nsq (u m)))
          * (nrm (u p) * nrm (u q)) := by
  classical
  set S := (extIdxSym modes k p q).filter (fun a => bonyClass θ k a = 3) with hS
  set W := nrm (u p) * nrm (u q) with hW
  have hWnn : 0 ≤ W := mul_nonneg (nrm_nonneg _) (nrm_nonneg _)
  have hgap : ∀ a ∈ S, |l (k - a) - l a| ≤ (1 / θ) * wlen a := by
    intro a ha
    have hc : bonyClass θ k a = 3 := by
      rw [hS, Finset.mem_filter] at ha; exact ha.2
    have hB : ¬ (wlen a ≤ θ * wlen k) := by
      intro hB
      rw [bonyClass] at hc
      split_ifs at hc <;> simp_all
    have hlt : θ * wlen k < wlen a := lt_of_not_ge hB
    have hkle : wlen k ≤ (1 / θ) * wlen a := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hθ]
      linarith
    exact le_trans (abs_helicity_gap_le_output l hs hl) hkle
  have hstep := abs_bonyCells_le_of_gap_bound θ modes u hk 3
    (fun a => (bonyClass_partner_three θ k a).symm) l hbel (fun a => (1 / θ) * wlen a) hgap
  refine le_trans hstep ?_
  have hrw : ∑ a ∈ S, (1 / θ) * wlen a * (nrm (u a) * nrm (u (k - a)) * W)
      = (1 / θ) * ((∑ a ∈ S, wlen a * (nrm (u a) * nrm (u (k - a)))) * W) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hrw]
  have hcs := sum_wlen_pair_le_sqrt modes u S k hsupp
  have h1 : (∑ a ∈ S, wlen a * (nrm (u a) * nrm (u (k - a)))) * W
      ≤ Real.sqrt ((∑ m ∈ modes, wsq m * nsq (u m)) * (∑ m ∈ modes, nsq (u m))) * W :=
    mul_le_mul_of_nonneg_right hcs hWnn
  have hinv : 0 < 1 / θ := by positivity
  have hrw2 : (1 / (2 * θ)) = (1 / 2) * (1 / θ) := by
    field_simp
  rw [hrw2]
  nlinarith [Real.sqrt_nonneg ((∑ m ∈ modes, wsq m * nsq (u m)) * (∑ m ∈ modes, nsq (u m)))]


/-! ## The paraproduct classes `LH ∪ HL` -/

/-- The union `LH ∪ HL` of the two paraproduct classes: the class of incidences
with one low leg.  Unlike each of them separately, this union is
partner-invariant. -/
def bonyCellsLowHigh (θ : ℝ) (modes : Finset Wave) (u : Wave → Fin 3 → ℂ)
    (k p q : Wave) : ℝ :=
  ∑ a ∈ (extIdxSym modes k p q).filter
      (fun a => bonyClass θ k a = 0 ∨ bonyClass θ k a = 1),
    crossCell u k p q a

theorem bonyCellsLowHigh_eq (θ : ℝ) (modes : Finset Wave) (u : Wave → Fin 3 → ℂ)
    (k p q : Wave) :
    bonyCellsLowHigh θ modes u k p q
      = bonyCells θ modes u k p q 0 + bonyCells θ modes u k p q 1 := by
  classical
  rw [bonyCellsLowHigh, bonyCells, bonyCells, Finset.filter_or]
  refine Finset.sum_union ?_
  rw [Finset.disjoint_left]
  intro a ha ha'
  rw [Finset.mem_filter] at ha ha'
  rw [ha.2] at ha'
  exact absurd ha'.2 (by decide)

/-- The union `LH ∪ HL` is partner-invariant (below the Bony threshold). -/
theorem bonyClass_partner_lowhigh {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : 2 * θ < 1) (k a : Wave) :
    (bonyClass θ k a = 0 ∨ bonyClass θ k a = 1)
      ↔ (bonyClass θ k (k - a) = 0 ∨ bonyClass θ k (k - a) = 1) := by
  classical
  rw [bonyClass_partner hθ0 hθ1]
  by_cases h0 : bonyClass θ k a = 0
  · simp [h0]
  · by_cases h1 : bonyClass θ k a = 1
    · simp [h1]
    · simp [h0, h1]

/-- **The paraproduct classes.**  On `LH ∪ HL` one leg is `θ`-low, so the output
frequency is comparable to the *high* leg and the helicity gap is at most
`(wlen a + wlen (k−a))/(1−θ)`.  The class is therefore bounded at the same
enstrophy level as the whole residue, with constant `1/(1−θ)` — this is the
far-low (Kato–Ponce/Bony) regime, where the multiplier difference is controlled
by the low leg and no extra small parameter is available. -/
theorem abs_bonyCellsLowHigh_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : 2 * θ < 1)
    (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) {k p q : Wave} (hk : wsq k ≠ 0)
    (hsupp : ∀ a, a ∉ modes → u a = 0) (l : Wave → ℝ) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hl : ∀ a, l a = s * wlen a)
    (hbel : ∀ a, cross (wC a) (u a) = fun i => (-Complex.I) * (l a : ℂ) * u a i) :
    |bonyCellsLowHigh θ modes u k p q|
      ≤ (1 / (1 - θ))
          * Real.sqrt ((∑ m ∈ modes, wsq m * nsq (u m)) * (∑ m ∈ modes, nsq (u m)))
          * (nrm (u p) * nrm (u q)) := by
  classical
  set S := (extIdxSym modes k p q).filter
      (fun a => bonyClass θ k a = 0 ∨ bonyClass θ k a = 1) with hS
  set W := nrm (u p) * nrm (u q) with hW
  have hWnn : 0 ≤ W := mul_nonneg (nrm_nonneg _) (nrm_nonneg _)
  have hθlt : θ < 1 := by linarith
  have hcpos : 0 < 1 - θ := by linarith
  set c := 1 / (1 - θ) with hc
  have hcnn : 0 ≤ c := by positivity
  -- the classwise gap bound
  have hgap : ∀ a ∈ S, |l (k - a) - l a| ≤ c * (wlen a + wlen (k - a)) := by
    intro a ha
    have hmem : bonyClass θ k a = 0 ∨ bonyClass θ k a = 1 := by
      rw [hS, Finset.mem_filter] at ha; exact ha.2
    have htri := wlen_le_legs k a
    have hkle : wlen k ≤ c * (wlen a + wlen (k - a)) := by
      have hlow : wlen a ≤ θ * wlen k ∨ wlen (k - a) ≤ θ * wlen k := by
        rcases hmem with h | h
        · exact Or.inl ((bonyClass_eq_zero_iff θ k a).mp h).2
        · exact Or.inr ((bonyClass_eq_one_iff θ k a).mp h).2.2
      have hstep : (1 - θ) * wlen k ≤ wlen a + wlen (k - a) := by
        rcases hlow with h | h
        · have := wlen_nonneg' a
          nlinarith
        · have := wlen_nonneg' (k - a)
          nlinarith
      rw [hc, one_div, inv_mul_eq_div, le_div_iff₀ hcpos]
      linarith
    exact le_trans (abs_helicity_gap_le_output l hs hl) hkle
  -- the pairing identity on the (partner-invariant) union
  have hid := two_mul_sum_cells_filter_eq_pairing modes u k p q hk
    (fun a => bonyClass θ k a = 0 ∨ bonyClass θ k a = 1)
    (fun a => bonyClass_partner_lowhigh hθ0 hθ1 k a) l hbel
  have habs : |2 * bonyCellsLowHigh θ modes u k p q|
      ≤ ∑ a ∈ S, (c * (wlen a + wlen (k - a))) * (nrm (u a) * nrm (u (k - a)) * W) := by
    rw [bonyCellsLowHigh, hid]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun a ha => ?_
    refine le_trans (abs_pairing_term_le k a p q u hk _) ?_
    exact mul_le_mul_of_nonneg_right (hgap a ha)
      (mul_nonneg (mul_nonneg (nrm_nonneg _) (nrm_nonneg _))
        (mul_nonneg (nrm_nonneg _) (nrm_nonneg _)))
  rw [abs_mul] at habs
  simp only [abs_two] at habs
  -- evaluate the majorant
  have hrw : ∑ a ∈ S, (c * (wlen a + wlen (k - a))) * (nrm (u a) * nrm (u (k - a)) * W)
      = c * (((∑ a ∈ S, wlen a * (nrm (u a) * nrm (u (k - a)))) * W)
          + ((∑ a ∈ S, wlen (k - a) * (nrm (u a) * nrm (u (k - a)))) * W)) := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hrw] at habs
  have hcs1 := sum_wlen_pair_le_sqrt modes u S k hsupp
  have hcs2 := sum_wlen_partner_pair_le_sqrt modes u S k hsupp
  set R := Real.sqrt ((∑ m ∈ modes, wsq m * nsq (u m)) * (∑ m ∈ modes, nsq (u m))) with hR
  have h1 : (∑ a ∈ S, wlen a * (nrm (u a) * nrm (u (k - a)))) * W ≤ R * W :=
    mul_le_mul_of_nonneg_right hcs1 hWnn
  have h2 : (∑ a ∈ S, wlen (k - a) * (nrm (u a) * nrm (u (k - a)))) * W ≤ R * W :=
    mul_le_mul_of_nonneg_right hcs2 hWnn
  nlinarith [abs_nonneg (bonyCellsLowHigh θ modes u k p q)]

/-! ## The assembled classwise estimate -/

/-- **The exact three-way partner-invariant split.**  The external residue is the
signed sum of its paraproduct part `LH ∪ HL`, its near-diagonal part `HH→low`
and its comparable part — each of the three being a class on which the
shared-fibre pairing identity is available. -/
theorem externalResidue_eq_lowhigh_split (θ : ℝ) (modes : Finset Wave)
    (u : Wave → Fin 3 → ℂ) {k p q : Wave} (hpq : p + q = k)
    (hsupp : ∀ a, a ∉ modes → u a = 0) :
    (herm (fun i => -(leray k (externalAdvection modes u k p q) i))
        (cross (u p) (u q))).re
      = bonyCellsLowHigh θ modes u k p q + bonyCells θ modes u k p q 2
        + bonyCells θ modes u k p q 3 := by
  rw [externalResidue_eq_bony_split θ modes u hpq hsupp, bonyCellsLowHigh_eq]

/-- **The classwise bound for the whole external cross-triad residue.**  Every
Bony class is paid at the enstrophy level `√(𝔇E)‖u_p‖‖u_q‖`, and the
near-diagonal class `HH→low` is paid with the extra small factor `θ`.  The
routing is exact and signed; only the final step takes absolute values, and it
does so *classwise*, not cell by cell. -/
theorem abs_externalResidue_classwise_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : 2 * θ < 1)
    (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) {k p q : Wave} (hpq : p + q = k)
    (hk : wsq k ≠ 0) (hsupp : ∀ a, a ∉ modes → u a = 0) (l : Wave → ℝ) {s : ℝ}
    (hs : s = 1 ∨ s = -1) (hl : ∀ a, l a = s * wlen a)
    (hbel : ∀ a, cross (wC a) (u a) = fun i => (-Complex.I) * (l a : ℂ) * u a i) :
    |(herm (fun i => -(leray k (externalAdvection modes u k p q) i))
        (cross (u p) (u q))).re|
      ≤ (1 / (1 - θ) + θ / 2 + 1 / (2 * θ))
          * Real.sqrt ((∑ m ∈ modes, wsq m * nsq (u m)) * (∑ m ∈ modes, nsq (u m)))
          * (nrm (u p) * nrm (u q)) := by
  classical
  set R := Real.sqrt ((∑ m ∈ modes, wsq m * nsq (u m)) * (∑ m ∈ modes, nsq (u m))) with hR
  set W := nrm (u p) * nrm (u q) with hW
  have h1 := abs_bonyCellsLowHigh_le hθ0.le hθ1 modes u (k := k) (p := p) (q := q)
    hk hsupp l hs hl hbel
  have h2 := abs_bonyCells_HHlow_le hθ0.le modes u (k := k) (p := p) (q := q) hk hsupp l hs hl hbel
  have h3 := abs_bonyCells_comparable_le hθ0 modes u (k := k) (p := p) (q := q) hk hsupp l hs hl hbel
  rw [externalResidue_eq_lowhigh_split θ modes u hpq hsupp]
  calc |bonyCellsLowHigh θ modes u k p q + bonyCells θ modes u k p q 2
          + bonyCells θ modes u k p q 3|
      ≤ |bonyCellsLowHigh θ modes u k p q + bonyCells θ modes u k p q 2|
          + |bonyCells θ modes u k p q 3| := abs_add_le _ _
    _ ≤ (|bonyCellsLowHigh θ modes u k p q| + |bonyCells θ modes u k p q 2|)
          + |bonyCells θ modes u k p q 3| := by
        have := abs_add_le (bonyCellsLowHigh θ modes u k p q) (bonyCells θ modes u k p q 2)
        linarith
    _ ≤ (1 / (1 - θ) + θ / 2 + 1 / (2 * θ)) * R * W := by
        rw [add_mul, add_mul, add_mul, add_mul]
        linarith

/-! ## On the Galerkin carrier -/

namespace GalerkinFlow

variable (G : GalerkinFlow)

/-- **The external residue of a Galerkin flow is an output-frequency
commutator.**  `|R^{ext}_{p,q}| ≤ ½ |p+q| · E(t) · ‖u_p‖‖u_q‖`, cutoff-uniformly:
the price of the whole external convolution is the *output* frequency times the
energy, with no leg frequency, shell count or Wiener factor. -/
theorem abs_externalResidue_le_output_energy (t : ℝ) {p q : Wave}
    (hpq : p + q ∈ G.modes) (l : Wave → ℝ) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hl : ∀ a, l a = s * wlen a)
    (hbel : ∀ a ∈ G.modes,
      cross (wC a) (G.u t a) = fun i => (-Complex.I) * (l a : ℂ) * G.u t a i) :
    |G.externalResidue t (p, q)|
      ≤ (1 / 2) * wlen (p + q) * G.energy t * (nrm (G.u t p) * nrm (G.u t q)) := by
  have hsupp : ∀ a, a ∉ G.modes → G.u t a = 0 := fun a ha => G.support t a ha
  have hbel' := beltrami_of_support G.modes (G.u t) l hsupp hbel
  exact ClayNS.Waleffe.abs_externalResidue_le_output_energy G.modes (G.u t) rfl
    (G.wsq_ne_zero_of_mem hpq) hsupp l hs hl hbel'

/-- **The classwise (Bony-routed) bound on the Galerkin carrier.** -/
theorem abs_externalResidue_classwise_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : 2 * θ < 1) (t : ℝ)
    {p q : Wave} (hpq : p + q ∈ G.modes) (l : Wave → ℝ) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hl : ∀ a, l a = s * wlen a)
    (hbel : ∀ a ∈ G.modes,
      cross (wC a) (G.u t a) = fun i => (-Complex.I) * (l a : ℂ) * G.u t a i) :
    |G.externalResidue t (p, q)|
      ≤ (1 / (1 - θ) + θ / 2 + 1 / (2 * θ))
          * Real.sqrt (G.dissipation t * G.energy t) * (nrm (G.u t p) * nrm (G.u t q)) := by
  have hsupp : ∀ a, a ∉ G.modes → G.u t a = 0 := fun a ha => G.support t a ha
  have hbel' := beltrami_of_support G.modes (G.u t) l hsupp hbel
  exact ClayNS.Waleffe.abs_externalResidue_classwise_le hθ0 hθ1 G.modes (G.u t) rfl
    (G.wsq_ne_zero_of_mem hpq) hsupp l hs hl hbel'

end GalerkinFlow


/-! ## The Young (absorption) form -/

/-- `√(DE) ≤ εD + E/(4ε)`: the elementary Young inequality behind the absorption
form below. -/
theorem sqrt_mul_le_young {D E eps : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E) (heps : 0 < eps) :
    Real.sqrt (D * E) ≤ eps * D + E / (4 * eps) := by
  have hx : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD
  have hy : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE
  rw [Real.sqrt_mul hD]
  have h4 : (0:ℝ) < 4 * eps := by linarith
  rw [← sub_nonneg]
  have hexp : eps * D + E / (4 * eps) - Real.sqrt D * Real.sqrt E
      = (2 * eps * Real.sqrt D - Real.sqrt E) ^ 2 / (4 * eps) := by
    field_simp
    nlinarith [hx, hy]
  rw [hexp]
  positivity

namespace GalerkinFlow

variable (G : GalerkinFlow)

/-- **The absorption form of the external residue bound.**  For every `ε > 0`
the external cross-triad residue of a resonant pair is bounded by an
`ε`-fraction of the dissipation plus an `ε`-dependent multiple of the energy,
uniformly in the Galerkin cutoff:

  `|R^{ext}_{p,q}| ≤ (ε 𝔇(t) + E(t)/(4ε)) ‖u_p‖‖u_q‖` .

This is the shape the absorption ladder consumes; what it does *not* yet provide
is a cutoff-independent constant in front of the *summed* residue at the
critical `H^{1/2}` level. -/
theorem abs_externalResidue_absorption_le (t : ℝ) {p q : Wave} (hpq : p + q ∈ G.modes)
    (l : Wave → ℝ)
    (hbel : ∀ a ∈ G.modes,
      cross (wC a) (G.u t a) = fun i => (-Complex.I) * (l a : ℂ) * G.u t a i)
    {eps : ℝ} (heps : 0 < eps) :
    |G.externalResidue t (p, q)|
      ≤ (eps * G.dissipation t + G.energy t / (4 * eps))
          * (nrm (G.u t p) * nrm (G.u t q)) := by
  refine le_trans (G.abs_externalResidue_le_sqrt_energy_dissipation t hpq l hbel) ?_
  refine mul_le_mul_of_nonneg_right ?_
    (mul_nonneg (nrm_nonneg _) (nrm_nonneg _))
  exact sqrt_mul_le_young (G.dissipation_nonneg t) (G.energy_nonneg t) heps

end GalerkinFlow

end ClayNS.Waleffe

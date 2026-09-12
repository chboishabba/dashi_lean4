/-
# Dyadic shell counting on the lattice `ℤ³`

The fibre sums of the Navier–Stokes companion are sums over lattice waves, and
the two summation routes available so far — the Wiener `ℓ¹` bound and the raw
fibre cardinality — are both lossy in the Galerkin cutoff.  This file supplies
the geometry needed to sum a fibre *without* paying either: the elementary
counting of lattice points on a max-norm sphere, and the two inverse-power sums
it yields.

* `waveMaxCoord`, `waveBox` — the max-norm and its balls;
* `card_shell_le` — a max-norm sphere of radius `m ≥ 1` carries at most `26m²`
  lattice points;
* `sum_shell_bound` — the resulting fibrewise summation principle;
* `sum_inv_sq_le_of_bounded` — `∑_{0<|a|≤R} |a|⁻² ≤ 26R`;
* `sum_inv_four_le_of_lower` — `∑_{|a|≥R} |a|⁻⁴ ≤ 104/R` for `R ≥ 2`;
* `card_le_of_bounded` — `#{0<|a| ≤ R} ≤ 26R³`.

Every constant is absolute; no statement here refers to a Galerkin cutoff, a
shell index or a fibre cardinality on the right-hand side.
-/
import RequestProject.NavierStokes.WaleffeCriticalCompanionSummation

noncomputable section

open Finset

namespace ClayNS.Waleffe

/-! ## 1. The max-norm and its balls -/

/-- The max-norm of a lattice wave. -/
def waveMaxCoord (p : Wave) : ℕ := max (max (p 0).natAbs (p 1).natAbs) (p 2).natAbs

/-- The max-norm ball of radius `m`. -/
def waveBox (m : ℕ) : Finset Wave :=
  Fintype.piFinset (fun _ => Finset.Icc (-(m : ℤ)) m)

theorem natAbs_cast_abs (n : ℤ) : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
  rw [Nat.cast_natAbs, Int.cast_abs]

theorem waveMaxCoord_le_iff {m : ℕ} {p : Wave} :
    waveMaxCoord p ≤ m ↔ ∀ i, (p i).natAbs ≤ m := by
  simp only [waveMaxCoord, max_le_iff]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩ i; fin_cases i <;> assumption
  · intro h; exact ⟨⟨h 0, h 1⟩, h 2⟩

theorem mem_waveBox {m : ℕ} {p : Wave} : p ∈ waveBox m ↔ waveMaxCoord p ≤ m := by
  rw [waveMaxCoord_le_iff]
  simp only [waveBox, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · intro h i; have := h i; omega
  · intro h i; have := h i; omega

theorem card_waveBox (m : ℕ) : (waveBox m).card = (2 * m + 1) ^ 3 := by
  rw [waveBox, Fintype.card_piFinset]
  simp [Int.card_Icc]
  omega

theorem abs_coord_le_wlen (p : Wave) (i : Fin 3) : ((p i).natAbs : ℝ) ≤ wlen p := by
  have hle : ((p i : ℝ)) ^ 2 ≤ wsq p := by
    rw [wsq]
    exact Finset.single_le_sum (f := fun j => ((p j : ℝ)) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h2 := Real.sqrt_le_sqrt hle
  rw [Real.sqrt_sq_eq_abs] at h2
  rw [natAbs_cast_abs]
  exact h2

/-- The max-norm is at most the Euclidean length. -/
theorem waveMaxCoord_le_wlen (p : Wave) : (waveMaxCoord p : ℝ) ≤ wlen p := by
  simp only [waveMaxCoord, Nat.cast_max]
  exact max_le (max_le (abs_coord_le_wlen p 0) (abs_coord_le_wlen p 1)) (abs_coord_le_wlen p 2)

theorem coord_le_waveMaxCoord (p : Wave) (i : Fin 3) :
    ((p i).natAbs : ℝ) ≤ (waveMaxCoord p : ℝ) := by
  have : (p i).natAbs ≤ waveMaxCoord p := waveMaxCoord_le_iff.1 le_rfl i
  exact_mod_cast this

/-- The Euclidean length is at most twice the max-norm. -/
theorem wlen_le_two_waveMaxCoord (p : Wave) : wlen p ≤ 2 * waveMaxCoord p := by
  have hi : ∀ i : Fin 3, ((p i : ℝ)) ^ 2 ≤ (waveMaxCoord p : ℝ) ^ 2 := by
    intro i
    have h := coord_le_waveMaxCoord p i
    rw [natAbs_cast_abs] at h
    calc ((p i : ℝ)) ^ 2 = |(p i : ℝ)| ^ 2 := (sq_abs _).symm
      _ ≤ (waveMaxCoord p : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  have h : wsq p ≤ (2 * (waveMaxCoord p : ℝ)) ^ 2 := by
    have h3 : wsq p ≤ 3 * (waveMaxCoord p : ℝ) ^ 2 := by
      rw [wsq, Fin.sum_univ_three]
      have := hi 0; have := hi 1; have := hi 2; linarith
    nlinarith [Nat.cast_nonneg (α := ℝ) (waveMaxCoord p)]
  calc wlen p = Real.sqrt (wsq p) := rfl
    _ ≤ Real.sqrt ((2 * (waveMaxCoord p : ℝ)) ^ 2) := Real.sqrt_le_sqrt h
    _ = 2 * waveMaxCoord p := Real.sqrt_sq (by positivity)

theorem waveMaxCoord_pos_of_ne_zero {p : Wave} (hp : p ≠ 0) : 1 ≤ waveMaxCoord p := by
  rcases Nat.eq_zero_or_pos (waveMaxCoord p) with h | h
  · refine absurd (funext fun i => ?_) hp
    have h1 := waveMaxCoord_le_iff.1 h.le i
    have h2 : p i = 0 := by omega
    simpa using h2
  · exact h

/-- Every nonzero lattice wave has length at least `1`. -/
theorem one_le_wlen_of_ne_zero {p : Wave} (hp : p ≠ 0) : 1 ≤ wlen p := by
  have h1 : (1 : ℝ) ≤ (waveMaxCoord p : ℝ) := by exact_mod_cast waveMaxCoord_pos_of_ne_zero hp
  exact le_trans h1 (waveMaxCoord_le_wlen p)

theorem wlen_pos_of_ne_zero {p : Wave} (hp : p ≠ 0) : 0 < wlen p :=
  lt_of_lt_of_le zero_lt_one (one_le_wlen_of_ne_zero hp)

/-- **The shell count.**  The max-norm sphere of radius `m ≥ 1` carries at most
`26m²` lattice points. -/
theorem card_shell_le (S : Finset Wave) {m : ℕ} (hm : 1 ≤ m) :
    ((S.filter (fun p => waveMaxCoord p = m)).card : ℝ) ≤ 26 * (m : ℝ) ^ 2 := by
  classical
  have hbox : waveBox (m - 1) ⊆ waveBox m := by
    intro p hp
    rw [mem_waveBox] at hp ⊢
    omega
  have hsub : S.filter (fun p => waveMaxCoord p = m) ⊆ waveBox m \ waveBox (m - 1) := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    rw [Finset.mem_sdiff, mem_waveBox, mem_waveBox]
    exact ⟨hp.2.le, by omega⟩
  have hcard : (S.filter (fun p => waveMaxCoord p = m)).card
      ≤ (waveBox m).card - (waveBox (m - 1)).card :=
    calc (S.filter (fun p => waveMaxCoord p = m)).card
        ≤ (waveBox m \ waveBox (m - 1)).card := Finset.card_le_card hsub
      _ = (waveBox m).card - (waveBox (m - 1)).card := Finset.card_sdiff_of_subset hbox
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [card_waveBox, card_waveBox] at hcard
  simp only [Nat.add_sub_cancel] at hcard
  have harith : (2 * (j + 1) + 1) ^ 3 - (2 * j + 1) ^ 3 ≤ 26 * (j + 1) ^ 2 := by
    have h1 : (2 * (j + 1) + 1) ^ 3 ≤ (2 * j + 1) ^ 3 + 26 * (j + 1) ^ 2 := by
      nlinarith [sq_nonneg j]
    omega
  have hfin : (S.filter (fun p => waveMaxCoord p = j + 1)).card ≤ 26 * (j + 1) ^ 2 :=
    le_trans hcard harith
  exact_mod_cast hfin

/-- **The fibrewise summation principle.**  A nonnegative function of a lattice
wave that is controlled by a function of the max-norm is summed shell by shell. -/
theorem sum_shell_bound (S : Finset Wave) (f : Wave → ℝ) (c : ℕ → ℝ) (M : ℕ)
    (h0 : ∀ p ∈ S, p ≠ 0) (hM : ∀ p ∈ S, waveMaxCoord p ≤ M)
    (hc : ∀ p ∈ S, f p ≤ c (waveMaxCoord p)) (hc0 : ∀ m, 0 ≤ c m) :
    ∑ p ∈ S, f p ≤ ∑ m ∈ Finset.Icc 1 M, 26 * (m : ℝ) ^ 2 * c m := by
  classical
  have hmaps : ∀ p ∈ S, waveMaxCoord p ∈ Finset.Icc 1 M := by
    intro p hp
    exact Finset.mem_Icc.2 ⟨waveMaxCoord_pos_of_ne_zero (h0 p hp), hM p hp⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
  refine Finset.sum_le_sum fun m hm => ?_
  have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
  have hle : ∑ p ∈ S.filter (fun p => waveMaxCoord p = m), f p
      ≤ (S.filter (fun p => waveMaxCoord p = m)).card • c m := by
    refine Finset.sum_le_card_nsmul _ _ _ ?_
    intro x hx
    simp only [Finset.mem_filter] at hx
    have := hc x hx.1
    rwa [hx.2] at this
  calc ∑ p ∈ S.filter (fun p => waveMaxCoord p = m), f p
      ≤ (S.filter (fun p => waveMaxCoord p = m)).card • c m := hle
    _ = ((S.filter (fun p => waveMaxCoord p = m)).card : ℝ) * c m := nsmul_eq_mul _ _
    _ ≤ 26 * (m : ℝ) ^ 2 * c m := mul_le_mul_of_nonneg_right (card_shell_le S hm1) (hc0 m)

/-! ## 2. Two elementary sums over the shell index -/

theorem sum_inv_sq_tail_aux (j : ℕ) : ∀ d : ℕ,
    (∑ m ∈ Finset.Icc (j + 1) (j + d), (1 : ℝ) / (m : ℝ) ^ 2) + 1 / ((j + d : ℕ) + 1 / 2)
      ≤ 1 / ((j : ℝ) + 1 / 2) := by
  intro d
  induction d with
  | zero => simp
  | succ n ih =>
      have hstep : ∑ m ∈ Finset.Icc (j + 1) (j + (n + 1)), (1 : ℝ) / (m : ℝ) ^ 2
          = (∑ m ∈ Finset.Icc (j + 1) (j + n), (1 : ℝ) / (m : ℝ) ^ 2)
            + 1 / ((j + n + 1 : ℕ) : ℝ) ^ 2 := by
        rw [show j + (n + 1) = (j + n) + 1 from rfl, Finset.sum_Icc_succ_top (by omega)]
      rw [hstep]
      have hx : (0 : ℝ) ≤ (j : ℝ) + n := by positivity
      have key : (1 : ℝ) / ((j + n + 1 : ℕ) : ℝ) ^ 2 + 1 / ((j + (n + 1) : ℕ) + 1 / 2)
          ≤ 1 / ((j + n : ℕ) + 1 / 2) := by
        push_cast
        rw [div_add_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hx, sq_nonneg ((j : ℝ) + n)]
      linarith [ih, key]

/-- The tail of `∑ m⁻²` beyond a real threshold `T ≥ 1`. -/
theorem sum_inv_sq_tail_le {T : ℝ} (hT : 1 ≤ T) (M : ℕ) :
    ∑ m ∈ (Finset.Icc 1 M).filter (fun m : ℕ => T ≤ (m : ℝ)), (1 : ℝ) / (m : ℝ) ^ 2 ≤ 2 / T := by
  classical
  set m0 := ⌈T⌉₊ with hm0
  have hm01 : 1 ≤ m0 := Nat.one_le_ceil_iff.2 (lt_of_lt_of_le zero_lt_one hT)
  obtain ⟨j, hj⟩ : ∃ j, m0 = j + 1 := ⟨m0 - 1, by omega⟩
  have hsub : (Finset.Icc 1 M).filter (fun m : ℕ => T ≤ (m : ℝ)) ⊆ Finset.Icc m0 M := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    exact ⟨Nat.ceil_le.2 hm.2, hm.1.2⟩
  have hstep : ∑ m ∈ (Finset.Icc 1 M).filter (fun m : ℕ => T ≤ (m : ℝ)), (1 : ℝ) / (m : ℝ) ^ 2
      ≤ ∑ m ∈ Finset.Icc m0 M, (1 : ℝ) / (m : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
  have hbound : ∑ m ∈ Finset.Icc m0 M, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / ((j : ℝ) + 1 / 2) := by
    rcases le_or_gt m0 M with hle | hgt
    · obtain ⟨d, hd⟩ : ∃ d, M = j + d := ⟨M - j, by omega⟩
      have h := sum_inv_sq_tail_aux j d
      have hpos : (0 : ℝ) < 1 / ((j + d : ℕ) + 1 / 2) := by positivity
      rw [hj, hd]
      linarith [h]
    · have he : Finset.Icc m0 M = ∅ := Finset.Icc_eq_empty (by omega)
      rw [he, Finset.sum_empty]
      positivity
  have hjT : T - 1 ≤ (j : ℝ) := by
    have hm0j : (m0 : ℝ) = (j : ℝ) + 1 := by rw [hj]; push_cast; ring
    have hceil : T ≤ (m0 : ℝ) := Nat.le_ceil T
    linarith
  have hfinal : 1 / ((j : ℝ) + 1 / 2) ≤ 2 / T := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  linarith [hstep, hbound, hfinal]

/-- `∑_{m ≤ M} m² ≤ M³`. -/
theorem sum_sq_Icc_le (M : ℕ) : ∑ m ∈ Finset.Icc 1 M, (m : ℝ) ^ 2 ≤ (M : ℝ) ^ 3 := by
  induction M with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      push_cast
      nlinarith [ih, hn]

/-! ## 3. The three lattice estimates -/

/-- `∑_{0 < |a| ≤ R} |a|⁻² ≤ 26R`, with no cardinality factor. -/
theorem sum_inv_sq_le_of_bounded (S : Finset Wave) {R : ℝ} (hR : 0 ≤ R)
    (h0 : ∀ p ∈ S, p ≠ 0) (hb : ∀ p ∈ S, wlen p ≤ R) :
    ∑ p ∈ S, 1 / (wlen p) ^ 2 ≤ 26 * R := by
  classical
  set M := ⌊R⌋₊ with hM
  have hMle : ∀ p ∈ S, waveMaxCoord p ≤ M := fun p hp =>
    Nat.le_floor (le_trans (waveMaxCoord_le_wlen p) (hb p hp))
  have hc : ∀ p ∈ S, 1 / (wlen p) ^ 2 ≤ 1 / ((waveMaxCoord p : ℝ)) ^ 2 := by
    intro p hp
    have h1 : 1 ≤ waveMaxCoord p := waveMaxCoord_pos_of_ne_zero (h0 p hp)
    have hpos : (0 : ℝ) < (waveMaxCoord p : ℝ) := by
      have h2 : (1 : ℝ) ≤ (waveMaxCoord p : ℝ) := by exact_mod_cast h1
      linarith
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_left₀ hpos.le (waveMaxCoord_le_wlen p) 2)
  have hmain := sum_shell_bound S (fun p => 1 / (wlen p) ^ 2)
    (fun m : ℕ => 1 / ((m : ℝ)) ^ 2) M h0 hMle hc (fun m => by positivity)
  have hcongr : ∑ m ∈ Finset.Icc 1 M, 26 * (m : ℝ) ^ 2 * (1 / ((m : ℝ)) ^ 2)
      = ∑ _m ∈ Finset.Icc 1 M, (26 : ℝ) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    have hpos : (0 : ℝ) < (m : ℝ) := by
      have h2 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      linarith
    field_simp
  have hcard : ∑ _m ∈ Finset.Icc 1 M, (26 : ℝ) = 26 * M := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    simp
    ring
  have hfloor : (M : ℝ) ≤ R := Nat.floor_le hR
  simp only at hmain
  rw [hcongr, hcard] at hmain
  linarith

/-- `∑_{|a| ≥ R} |a|⁻⁴ ≤ 104/R` for `R ≥ 2`, with no cardinality factor. -/
theorem sum_inv_four_le_of_lower (S : Finset Wave) {R : ℝ} (hR : 2 ≤ R)
    (h0 : ∀ p ∈ S, p ≠ 0) (hb : ∀ p ∈ S, R ≤ wlen p) :
    ∑ p ∈ S, 1 / (wlen p) ^ 4 ≤ 104 / R := by
  classical
  set M := S.sup waveMaxCoord with hM
  have hMle : ∀ p ∈ S, waveMaxCoord p ≤ M := fun p hp => Finset.le_sup hp
  set c : ℕ → ℝ := fun m => if R / 2 ≤ (m : ℝ) then 1 / ((m : ℝ)) ^ 4 else 0 with hc_def
  have hc0 : ∀ m, 0 ≤ c m := by
    intro m
    rw [hc_def]
    dsimp only
    split <;> positivity
  have hc : ∀ p ∈ S, 1 / (wlen p) ^ 4 ≤ c (waveMaxCoord p) := by
    intro p hp
    have h1 : 1 ≤ waveMaxCoord p := waveMaxCoord_pos_of_ne_zero (h0 p hp)
    have hpos : (0 : ℝ) < (waveMaxCoord p : ℝ) := by
      have h2 : (1 : ℝ) ≤ (waveMaxCoord p : ℝ) := by exact_mod_cast h1
      linarith
    have hhalf : R / 2 ≤ (waveMaxCoord p : ℝ) := by
      have hR1 : R ≤ wlen p := hb p hp
      have hR2 : wlen p ≤ 2 * waveMaxCoord p := wlen_le_two_waveMaxCoord p
      linarith
    have hpow := pow_le_pow_left₀ hpos.le (waveMaxCoord_le_wlen p) 4
    rw [hc_def]
    dsimp only
    rw [if_pos hhalf]
    exact one_div_le_one_div_of_le (by positivity) hpow
  have hmain := sum_shell_bound S (fun p => 1 / (wlen p) ^ 4) c M h0 hMle hc hc0
  have hsum : ∑ m ∈ Finset.Icc 1 M, 26 * (m : ℝ) ^ 2 * c m
      ≤ 26 * ∑ m ∈ (Finset.Icc 1 M).filter (fun m : ℕ => R / 2 ≤ (m : ℝ)),
          (1 : ℝ) / (m : ℝ) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 M)
      (fun m : ℕ => R / 2 ≤ (m : ℝ)) (fun m => 26 * (m : ℝ) ^ 2 * c m)]
    have hzero : ∑ m ∈ (Finset.Icc 1 M).filter (fun m : ℕ => ¬ (R / 2 ≤ (m : ℝ))),
        26 * (m : ℝ) ^ 2 * c m = 0 := by
      refine Finset.sum_eq_zero fun m hm => ?_
      simp only [Finset.mem_filter] at hm
      rw [hc_def]
      dsimp only
      rw [if_neg hm.2]
      ring
    rw [hzero, add_zero]
    refine Finset.sum_le_sum fun m hm => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    have hm1 : 1 ≤ m := hm.1.1
    have hpos : (0 : ℝ) < (m : ℝ) := by
      have h2 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      linarith
    rw [hc_def]
    dsimp only
    rw [if_pos hm.2, show (26 : ℝ) * (m : ℝ) ^ 2 * (1 / (m : ℝ) ^ 4)
      = 26 * (1 / (m : ℝ) ^ 2) by field_simp]
  have htail := sum_inv_sq_tail_le (T := R / 2) (by linarith) M
  have hRpos : (0 : ℝ) < R := by linarith
  have hconst : 26 * (2 / (R / 2)) = 104 / R := by field_simp; ring
  have hscaled := mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 26)
  simp only at hmain
  linarith [hmain, hsum, hscaled]

/-- `#{0 < |a| ≤ R} ≤ 26R³`. -/
theorem card_le_of_bounded (S : Finset Wave) {R : ℝ} (hR : 0 ≤ R)
    (h0 : ∀ p ∈ S, p ≠ 0) (hb : ∀ p ∈ S, wlen p ≤ R) :
    (S.card : ℝ) ≤ 26 * R ^ 3 := by
  classical
  set M := ⌊R⌋₊ with hM
  have hMle : ∀ p ∈ S, waveMaxCoord p ≤ M := fun p hp =>
    Nat.le_floor (le_trans (waveMaxCoord_le_wlen p) (hb p hp))
  have hmain := sum_shell_bound S (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) M h0 hMle
    (fun p _ => le_rfl) (fun _ => zero_le_one)
  have hleft : ∑ _p ∈ S, (1 : ℝ) = (S.card : ℝ) := by simp
  have hright : ∑ m ∈ Finset.Icc 1 M, 26 * (m : ℝ) ^ 2 * (1 : ℝ) ≤ 26 * (M : ℝ) ^ 3 := by
    have heq : ∑ m ∈ Finset.Icc 1 M, 26 * (m : ℝ) ^ 2 * (1 : ℝ)
        = 26 * ∑ m ∈ Finset.Icc 1 M, (m : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left (sum_sq_Icc_le M) (by norm_num)
  have hfloor : (M : ℝ) ≤ R := Nat.floor_le hR
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hcube : (M : ℝ) ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ hM0 hfloor 3
  simp only at hmain
  rw [hleft] at hmain
  linarith

end ClayNS.Waleffe

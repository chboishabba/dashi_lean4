/-
# The external cross-triad residue, cell by cell

`WaleffeExternalForcingSplit.lean` isolates the *external* part of the Waleffe
network forcing: for a resonant pair `p + q = k` of distinct retained modes the
forcing of `k` splits into the triad's own convolution pair (paid outright by
the classical energy expenditure) and the external convolution

  `f_k^{ext(p,q)} = −P_k ∑_{a ∈ modes∖{p,q}} i (u_a · (k−a)) u_{k−a}`,

whose pairing against `u_p × u_q` is the last open budget of that slot.

This file **expands that residue into its individual quartic incidence cells**
and computes the shared-output-fibre partner sum literally.

* `crossCellVec` / `crossCell` — one incidence cell `a ↦ Re⟪−P_k(i(u_a·(k−a))u_{k−a}), u_p×u_q⟫`,
  and `externalResidue_eq_sum_cells`: the external residue is exactly the sum of
  its cells over the external index set.
* The **partner map** is the shared-output-fibre reindexing `a ↦ k − a`, which
  exchanges the two convolution orderings of one external pair `{a, k−a}` inside
  the same output fibre `k`.  `crossCellVec_partner` is the exact identity
      `cellVec(a) + cellVec(k−a) = pairAdvection a (k−a) u_a u_{k−a}` ,
  an *algebraic identity*: no transversality, helicity or support hypothesis.
* `crossCell_partner_sum` — hence, on helical (Beltrami) modes,
      `T_a + T_{k−a} = (λ_{k−a} − λ_a) · Re⟪P_k(u_a×u_{k−a}), u_p×u_q⟫`.
  **The partner sum carries the helicity multiplier only through its
  difference**, exactly as the internal (self) slot does; there is no leftover
  `λ_a + λ_{k−a}` term and no unpaid remainder.  In particular
  `crossCell_partner_cancel`: helicity-degenerate external partners cancel
  identically.
* `two_mul_externalResidue_eq_pairing` — summing over the symmetrised external
  index set (`extIdxSym`, closed under the partner map, the added cells being
  unoccupied and hence zero), the whole external residue is *equal* to one half
  of the helicity-gap-weighted sum of projected cross energies.
* `abs_externalResidue_le_helicity_gap_sum` and
  `abs_externalResidue_le_frequency_sum` — the resulting quantitative estimates,
  the second with the gap replaced by the physical helical frequency bound
  `|λ_a| ≤ |a|`; `GalerkinFlow.abs_externalResidue_le_frequency_sum` states the
  latter on the literal Galerkin carrier.

So the external cross-triad residue is *not* an unstructured quartic sum: after
the shared-mode reindexing it is a helicity-**gap**-weighted quadratic form in
the projected cross products, i.e. exactly the multiplier-difference object the
far-low machinery is designed to act on.  What is still open is the quantitative
payment of that gap-weighted sum (a frequency-weighted, i.e. enstrophy-level,
quantity), not its algebraic structure.
-/
import RequestProject.NavierStokes.WaleffeTriadInternalPayment

noncomputable section

namespace ClayNS.Waleffe

/-! ## Linearity helpers -/

theorem herm_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin 3 → ℂ) (w : Fin 3 → ℂ) :
    herm (fun i => ∑ a ∈ s, f a i) w = ∑ a ∈ s, herm (f a) w := by
  simp only [herm, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem leray_zero_fun (k : Wave) : leray k (fun _ => 0) = fun _ => 0 := by
  funext i
  simp [leray, herm]

theorem leray_sum {ι : Type*} (k : Wave) (s : Finset ι) (f : ι → Fin 3 → ℂ) :
    leray k (fun i => ∑ a ∈ s, f a i) = fun i => ∑ a ∈ s, leray k (f a) i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using leray_zero_fun k
  | insert a s ha ih =>
      have h : (fun i => ∑ b ∈ insert a s, f b i)
          = fun i => f a i + ∑ b ∈ s, f b i := by
        funext i
        rw [Finset.sum_insert ha]
      rw [h, leray_add, ih]
      funext i
      rw [Finset.sum_insert ha]

theorem herm_real_smul_left (c : ℝ) (v w : Fin 3 → ℂ) :
    herm (fun i => (c : ℂ) * v i) w = (c : ℂ) * herm v w := by
  simp only [herm, Finset.mul_sum, map_mul, Complex.conj_ofReal]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem cross_zero_left (v : Fin 3 → ℂ) : cross (fun _ => 0) v = fun _ => 0 := by
  funext i
  fin_cases i <;> simp [cross, crossProduct]

/-! ## The quartic incidence cells of the external residue -/

/-- One incidence cell of the external convolution at the output fibre `k`: the
convolution term with input mode `a` and partner `k − a`. -/
def crossCellVec (u : Wave → Fin 3 → ℂ) (k a : Wave) : Fin 3 → ℂ :=
  fun i => (Complex.I * dotb (u a) (wC (k - a))) * u (k - a) i

/-- The quartic cross-triad cell `T_a`: the incidence cell `a` of the external
forcing of the fibre `k`, paired against `u_p × u_q`. -/
def crossCell (u : Wave → Fin 3 → ℂ) (k p q a : Wave) : ℝ :=
  (herm (fun i => -(leray k (crossCellVec u k a) i)) (cross (u p) (u q))).re

theorem externalAdvection_eq_sum_cellVec (modes : Finset Wave) (u : Wave → Fin 3 → ℂ)
    (k p q : Wave) :
    externalAdvection modes u k p q
      = fun i => ∑ a ∈ (modes.erase p).erase q, crossCellVec u k a i := rfl

/-- **The external residue is the sum of its quartic incidence cells.** -/
theorem externalResidue_eq_sum_cells (modes : Finset Wave) (u : Wave → Fin 3 → ℂ)
    (k p q : Wave) :
    (herm (fun i => -(leray k (externalAdvection modes u k p q) i)) (cross (u p) (u q))).re
      = ∑ a ∈ (modes.erase p).erase q, crossCell u k p q a := by
  classical
  rw [externalAdvection_eq_sum_cellVec, leray_sum]
  have h : (fun i => -(∑ a ∈ (modes.erase p).erase q, leray k (crossCellVec u k a) i))
      = fun i => ∑ a ∈ (modes.erase p).erase q, -(leray k (crossCellVec u k a) i) := by
    funext i
    rw [Finset.sum_neg_distrib]
  rw [h, herm_sum_left, Complex.re_sum]
  rfl

/-- An unoccupied input mode contributes no cell. -/
theorem crossCell_eq_zero_of_left_zero (u : Wave → Fin 3 → ℂ) (k p q a : Wave)
    (h : u a = 0) : crossCell u k p q a = 0 := by
  have hv : crossCellVec u k a = fun _ => 0 := by
    funext i
    simp [crossCellVec, dotb, h]
  simp [crossCell, hv, leray_zero_fun, herm]

/-- An unoccupied partner mode contributes no cell. -/
theorem crossCell_eq_zero_of_right_zero (u : Wave → Fin 3 → ℂ) (k p q a : Wave)
    (h : u (k - a) = 0) : crossCell u k p q a = 0 := by
  have hv : crossCellVec u k a = fun _ => 0 := by
    funext i
    simp [crossCellVec, h]
  simp [crossCell, hv, leray_zero_fun, herm]

/-! ## The shared-output-fibre partner map -/

/-- **The exact partner identity.**  The two convolution orderings `a` and
`k − a` of one external pair inside the fibre `k` add up to the advective pair
of that pair.  This is an algebraic identity — no transversality, helicity,
support or resonance hypothesis is used. -/
theorem crossCellVec_partner (u : Wave → Fin 3 → ℂ) (k a : Wave) :
    (fun i => crossCellVec u k a i + crossCellVec u k (k - a) i)
      = pairAdvection a (k - a) (u a) (u (k - a)) := by
  funext i
  have h : k - (k - a) = a := by abel
  simp only [crossCellVec, pairAdvection, h]

/-- **The shared-mode partner sum of two quartic cross-triad cells.**  On
helical modes the partner sum of the cells `a` and `k − a` is the *helicity gap*
`λ_{k−a} − λ_a` times the projected cross energy of the pair against
`u_p × u_q`.  The helicity multipliers enter only through their difference. -/
theorem crossCell_partner_sum {k a p q : Wave} (hk : wsq k ≠ 0) (u : Wave → Fin 3 → ℂ)
    {la lb : ℝ}
    (hba : cross (wC a) (u a) = fun i => (-Complex.I) * (la : ℂ) * u a i)
    (hbb : cross (wC (k - a)) (u (k - a)) = fun i => (-Complex.I) * (lb : ℂ) * u (k - a) i) :
    crossCell u k p q a + crossCell u k p q (k - a)
      = (lb - la) * (herm (leray k (cross (u a) (u (k - a)))) (cross (u p) (u q))).re := by
  have hres : a + (k - a) = k := by abel
  have hL := leray_pairAdvection hres hk (u a) (u (k - a)) la lb hba hbb
  have hvec : (fun i => -(leray k (crossCellVec u k a) i)
        + -(leray k (crossCellVec u k (k - a)) i))
      = fun i => ((lb - la : ℝ) : ℂ) * leray k (cross (u a) (u (k - a))) i := by
    funext i
    have hadd : leray k (fun i => crossCellVec u k a i + crossCellVec u k (k - a) i)
        = fun i => leray k (crossCellVec u k a) i + leray k (crossCellVec u k (k - a)) i :=
      leray_add k _ _
    rw [crossCellVec_partner] at hadd
    have h1 := congrFun hadd i
    have h2 := congrFun hL i
    rw [h2] at h1
    push_cast
    linear_combination h1
  have hsum : crossCell u k p q a + crossCell u k p q (k - a)
      = (herm (fun i => -(leray k (crossCellVec u k a) i)
          + -(leray k (crossCellVec u k (k - a)) i)) (cross (u p) (u q))).re := by
    simp only [crossCell]
    rw [herm_add_left, Complex.add_re]
  rw [hsum, hvec, herm_real_smul_left]
  simp [Complex.mul_re]

/-- Helicity-degenerate external partners cancel identically. -/
theorem crossCell_partner_cancel {k a p q : Wave} (hk : wsq k ≠ 0) (u : Wave → Fin 3 → ℂ)
    {l : ℝ}
    (hba : cross (wC a) (u a) = fun i => (-Complex.I) * (l : ℂ) * u a i)
    (hbb : cross (wC (k - a)) (u (k - a)) = fun i => (-Complex.I) * (l : ℂ) * u (k - a) i) :
    crossCell u k p q a + crossCell u k p q (k - a) = 0 := by
  rw [crossCell_partner_sum hk u hba hbb]
  simp

/-! ## Symmetrising the external index set -/

/-- The external index set of the pair `(p,q)`. -/
def extIdx (modes : Finset Wave) (p q : Wave) : Finset Wave := (modes.erase p).erase q

/-- The external index set symmetrised by the partner map `a ↦ k − a`. -/
def extIdxSym (modes : Finset Wave) (k p q : Wave) : Finset Wave :=
  extIdx modes p q ∪ (extIdx modes p q).image (fun a => k - a)

theorem extIdx_subset_sym (modes : Finset Wave) (k p q : Wave) :
    extIdx modes p q ⊆ extIdxSym modes k p q := Finset.subset_union_left

/-- The symmetrised index set is closed under the partner map. -/
theorem extIdxSym_partner_mem {modes : Finset Wave} {k p q a : Wave}
    (ha : a ∈ extIdxSym modes k p q) : k - a ∈ extIdxSym modes k p q := by
  classical
  rcases Finset.mem_union.mp ha with h | h
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
  · obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp h
    have : k - a = b := by rw [← hba]; abel
    rw [this]
    exact Finset.mem_union_left _ hb

/-- Reindexing a sum by the partner map. -/
theorem sum_partner_reindex (S : Finset Wave) (k : Wave)
    (hcl : ∀ a ∈ S, k - a ∈ S) (f : Wave → ℝ) :
    ∑ a ∈ S, f (k - a) = ∑ a ∈ S, f a := by
  classical
  have hinj : ∀ x ∈ S, ∀ y ∈ S, k - x = k - y → x = y := by
    intro x _ y _ h
    have : k - (k - x) = k - (k - y) := by rw [h]
    simpa [sub_sub_cancel] using this
  have himg : S.image (fun a => k - a) = S := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨b, hb, hbx⟩ := Finset.mem_image.mp hx
      rw [← hbx]
      exact hcl b hb
    · intro x hx
      refine Finset.mem_image.mpr ⟨k - x, hcl x hx, ?_⟩
      abel
  calc ∑ a ∈ S, f (k - a) = ∑ x ∈ S.image (fun a => k - a), f x :=
        (Finset.sum_image hinj).symm
    _ = ∑ a ∈ S, f a := by rw [himg]

/-- The cells outside the external index set but inside its symmetrisation are
unoccupied, hence vanish. -/
theorem sum_cells_eq_sym (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) {k p q : Wave}
    (hpq : p + q = k) (hsupp : ∀ a, a ∉ modes → u a = 0) :
    ∑ a ∈ extIdx modes p q, crossCell u k p q a
      = ∑ a ∈ extIdxSym modes k p q, crossCell u k p q a := by
  classical
  refine Finset.sum_subset (extIdx_subset_sym modes k p q) ?_
  intro x hx hxn
  -- `x` comes from the image of the partner map
  have himg : x ∈ (extIdx modes p q).image (fun a => k - a) := by
    rcases Finset.mem_union.mp hx with h | h
    · exact absurd h hxn
    · exact h
  obtain ⟨b, hb, hbx⟩ := Finset.mem_image.mp himg
  have hbq : b ≠ q := (Finset.mem_erase.mp hb).1
  have hbp : b ≠ p := (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1
  -- `x` is not in the external index set, and it cannot be `p` or `q`
  have hxp : x ≠ p := by
    intro h
    apply hbp
    have : k - x = b := by rw [← hbx]; abel
    rw [h] at this
    have hkp : k - p = q := by rw [← hpq]; abel
    rw [hkp] at this
    exact absurd this.symm hbq
  have hxq : x ≠ q := by
    intro h
    have : k - x = b := by rw [← hbx]; abel
    rw [h] at this
    have hkq : k - q = p := by rw [← hpq]; abel
    rw [hkq] at this
    exact absurd this.symm hbp
  have hxm : x ∉ modes := by
    intro hm
    exact hxn (Finset.mem_erase.mpr ⟨hxq, Finset.mem_erase.mpr ⟨hxp, hm⟩⟩)
  exact crossCell_eq_zero_of_left_zero u k p q x (hsupp x hxm)

/-! ## The pairing law for the whole external residue -/

/-- Helicity relations extend from the retained modes to the whole lattice. -/
theorem beltrami_of_support (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (l : Wave → ℝ)
    (hsupp : ∀ a, a ∉ modes → u a = 0)
    (hbel : ∀ a ∈ modes, cross (wC a) (u a) = fun i => (-Complex.I) * (l a : ℂ) * u a i) :
    ∀ a, cross (wC a) (u a) = fun i => (-Complex.I) * (l a : ℂ) * u a i := by
  classical
  intro a
  by_cases ha : a ∈ modes
  · exact hbel a ha
  · have h0 : u a = 0 := hsupp a ha
    rw [h0]
    have hz : cross (wC a) (0 : Fin 3 → ℂ) = fun _ => (0 : ℂ) := by
      funext i
      fin_cases i <;> simp [cross, crossProduct]
    rw [hz]
    funext i
    simp

/-- **The external cross-triad residue as a helicity-gap-weighted quadratic
form.**  After the shared-output-fibre reindexing the entire external residue of
the pair `(p,q)` equals one half of the sum, over the symmetrised external index
set, of `(λ_{k−a} − λ_a)` times the projected cross energy of the external pair
against `u_p × u_q`.  The helicity multipliers appear *only* through their
difference: there is no unpaired `λ_a + λ_{k−a}` term and no remainder. -/
theorem two_mul_externalResidue_eq_pairing (modes : Finset Wave) (u : Wave → Fin 3 → ℂ)
    {k p q : Wave} (hpq : p + q = k) (hk : wsq k ≠ 0)
    (hsupp : ∀ a, a ∉ modes → u a = 0) (l : Wave → ℝ)
    (hbel : ∀ a, cross (wC a) (u a) = fun i => (-Complex.I) * (l a : ℂ) * u a i) :
    2 * (herm (fun i => -(leray k (externalAdvection modes u k p q) i))
          (cross (u p) (u q))).re
      = ∑ a ∈ extIdxSym modes k p q,
          (l (k - a) - l a)
            * (herm (leray k (cross (u a) (u (k - a)))) (cross (u p) (u q))).re := by
  classical
  rw [externalResidue_eq_sum_cells]
  have hext : (modes.erase p).erase q = extIdx modes p q := rfl
  rw [hext, sum_cells_eq_sym modes u hpq hsupp]
  set S := extIdxSym modes k p q with hS
  have hcl : ∀ a ∈ S, k - a ∈ S := fun a ha => extIdxSym_partner_mem ha
  have hdouble : 2 * ∑ a ∈ S, crossCell u k p q a
      = ∑ a ∈ S, (crossCell u k p q a + crossCell u k p q (k - a)) := by
    rw [Finset.sum_add_distrib,
      sum_partner_reindex S k hcl (fun a => crossCell u k p q a)]
    ring
  rw [hdouble]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact crossCell_partner_sum hk u (hbel a) (hbel (k - a))

/-! ## Quantitative consequences -/

theorem abs_pairing_term_le (k a p q : Wave) (u : Wave → Fin 3 → ℂ) (hk : wsq k ≠ 0) (c : ℝ) :
    |c * (herm (leray k (cross (u a) (u (k - a)))) (cross (u p) (u q))).re|
      ≤ |c| * (nrm (u a) * nrm (u (k - a)) * (nrm (u p) * nrm (u q))) := by
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
  calc |(herm (leray k (cross (u a) (u (k - a)))) (cross (u p) (u q))).re|
      ≤ ‖herm (leray k (cross (u a) (u (k - a)))) (cross (u p) (u q))‖ :=
        Complex.abs_re_le_norm _
    _ ≤ nrm (leray k (cross (u a) (u (k - a)))) * nrm (cross (u p) (u q)) := norm_herm_le _ _
    _ ≤ (nrm (u a) * nrm (u (k - a))) * (nrm (u p) * nrm (u q)) := by
        refine mul_le_mul ?_ (nrm_cross_le _ _) (nrm_nonneg _)
          (mul_nonneg (nrm_nonneg _) (nrm_nonneg _))
        exact le_trans (nrm_leray_le k _ hk) (nrm_cross_le _ _)
    _ = nrm (u a) * nrm (u (k - a)) * (nrm (u p) * nrm (u q)) := by ring

/-- **The helicity-gap bound for the external residue.** -/
theorem abs_externalResidue_le_helicity_gap_sum (modes : Finset Wave) (u : Wave → Fin 3 → ℂ)
    {k p q : Wave} (hpq : p + q = k) (hk : wsq k ≠ 0)
    (hsupp : ∀ a, a ∉ modes → u a = 0) (l : Wave → ℝ)
    (hbel : ∀ a, cross (wC a) (u a) = fun i => (-Complex.I) * (l a : ℂ) * u a i) :
    |(herm (fun i => -(leray k (externalAdvection modes u k p q) i))
        (cross (u p) (u q))).re|
      ≤ (1 / 2) * ∑ a ∈ extIdxSym modes k p q,
          |l (k - a) - l a| * (nrm (u a) * nrm (u (k - a)) * (nrm (u p) * nrm (u q))) := by
  classical
  have hid := two_mul_externalResidue_eq_pairing modes u hpq hk hsupp l hbel
  set R := (herm (fun i => -(leray k (externalAdvection modes u k p q) i))
      (cross (u p) (u q))).re with hR
  have habs : |2 * R| ≤ ∑ a ∈ extIdxSym modes k p q,
      |l (k - a) - l a| * (nrm (u a) * nrm (u (k - a)) * (nrm (u p) * nrm (u q))) := by
    rw [hid]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun a _ => ?_
    exact abs_pairing_term_le k a p q u hk _
  rw [abs_mul] at habs
  simp only [abs_two] at habs
  linarith

/-- **The frequency-weighted bound for the external residue.**  Replacing the
helicity gap by the physical helical frequency bound `|λ_a| ≤ |a|` gives a bound
in which the only unresolved quantity is the frequency-weighted (enstrophy
level) sum over the symmetrised external index set. -/
theorem abs_externalResidue_le_frequency_sum (modes : Finset Wave) (u : Wave → Fin 3 → ℂ)
    {k p q : Wave} (hpq : p + q = k) (hk : wsq k ≠ 0)
    (hsupp : ∀ a, a ∉ modes → u a = 0) (l : Wave → ℝ)
    (hbel : ∀ a, cross (wC a) (u a) = fun i => (-Complex.I) * (l a : ℂ) * u a i) :
    |(herm (fun i => -(leray k (externalAdvection modes u k p q) i))
        (cross (u p) (u q))).re|
      ≤ (1 / 2) * ∑ a ∈ extIdxSym modes k p q,
          (wlen a + wlen (k - a)) * (nrm (u a) * nrm (u (k - a)) * (nrm (u p) * nrm (u q))) := by
  classical
  refine le_trans (abs_externalResidue_le_helicity_gap_sum modes u hpq hk hsupp l hbel) ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_) (by norm_num)
  set W := nrm (u p) * nrm (u q) with hW
  by_cases ha : nsq (u a) = 0
  · have h0 : nrm (u a) = 0 := by rw [nrm, ha, Real.sqrt_zero]
    simp [h0]
  · by_cases hb : nsq (u (k - a)) = 0
    · have h0 : nrm (u (k - a)) = 0 := by rw [nrm, hb, Real.sqrt_zero]
      simp [h0]
    · have h1 : |l a| ≤ wlen a := abs_helical_le_wlen ha (hbel a)
      have h2 : |l (k - a)| ≤ wlen (k - a) := abs_helical_le_wlen hb (hbel (k - a))
      have hgap : |l (k - a) - l a| ≤ wlen a + wlen (k - a) := by
        calc |l (k - a) - l a| ≤ |l (k - a)| + |l a| := abs_sub _ _
          _ ≤ wlen (k - a) + wlen a := add_le_add h2 h1
          _ = wlen a + wlen (k - a) := by ring
      refine mul_le_mul_of_nonneg_right hgap ?_
      exact mul_nonneg (mul_nonneg (nrm_nonneg _) (nrm_nonneg _))
        (mul_nonneg (nrm_nonneg _) (nrm_nonneg _))

/-! ## Co-helical partners: the gap is a frequency *difference* -/

/-- A wavevector as a Euclidean vector. -/
def wvec (k : Wave) : EuclideanSpace ℝ (Fin 3) :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun i => (k i : ℝ))

theorem wvec_add (x y : Wave) : wvec (x + y) = wvec x + wvec y := by
  ext i
  simp [wvec]

theorem wvec_sub (x y : Wave) : wvec (x - y) = wvec x - wvec y := by
  ext i
  simp [wvec]

theorem norm_wvec (k : Wave) : ‖wvec k‖ = wlen k := by
  rw [EuclideanSpace.norm_eq, wlen, wsq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [wvec, Real.norm_eq_abs, sq_abs]

/-- The triangle inequality for the frequency. -/
theorem wlen_triangle (x y : Wave) : wlen (x + y) ≤ wlen x + wlen y := by
  have h := norm_add_le (wvec x) (wvec y)
  rwa [← wvec_add, norm_wvec, norm_wvec, norm_wvec] at h

/-- The reverse triangle inequality: the difference of two frequencies is at
most the frequency of their separation. -/
theorem abs_wlen_sub_le (x y : Wave) : |wlen x - wlen y| ≤ wlen (x - y) := by
  have h := abs_norm_sub_norm_le (wvec x) (wvec y)
  rwa [norm_wvec, norm_wvec, ← wvec_sub, norm_wvec] at h

/-- **The co-helical partner gain.**  If the two shared-fibre partners `a` and
`k − a` carry the *same* helicity sign, the helicity gap of their partner sum is
not the sum `|a| + |k−a|` of their frequencies but the *difference*
`| |k−a| − |a| |`, which is at most the frequency `|k − 2a|` of their
separation.  This is the multiplier-difference gain on the external cells: it is
small exactly on the high-high cells `a ≈ k/2`, where the two partners are
nearly equal and the naive frequency count is worst. -/
theorem abs_crossCell_partner_sum_cohelical_le {k a p q : Wave} (hk : wsq k ≠ 0)
    (u : Wave → Fin 3 → ℂ) {la lb s : ℝ} (hs : s = 1 ∨ s = -1)
    (hla : la = s * wlen a) (hlb : lb = s * wlen (k - a))
    (hba : cross (wC a) (u a) = fun i => (-Complex.I) * (la : ℂ) * u a i)
    (hbb : cross (wC (k - a)) (u (k - a)) = fun i => (-Complex.I) * (lb : ℂ) * u (k - a) i) :
    |crossCell u k p q a + crossCell u k p q (k - a)|
      ≤ wlen (k - a - a) * (nrm (u a) * nrm (u (k - a)) * (nrm (u p) * nrm (u q))) := by
  rw [crossCell_partner_sum hk u hba hbb]
  refine le_trans (abs_pairing_term_le k a p q u hk (lb - la)) ?_
  refine mul_le_mul_of_nonneg_right ?_
    (mul_nonneg (mul_nonneg (nrm_nonneg _) (nrm_nonneg _))
      (mul_nonneg (nrm_nonneg _) (nrm_nonneg _)))
  have hgap : |lb - la| = |wlen (k - a) - wlen a| := by
    rw [hla, hlb, ← mul_sub, abs_mul]
    rcases hs with h | h <;> simp [h]
  rw [hgap]
  exact abs_wlen_sub_le (k - a) a

/-- **The separation bound for a co-helical field.**  If every mode carries the
same helicity sign, the whole external cross-triad residue of the pair `(p,q)`
is controlled by the *separation* frequencies `|k − 2a|` of the external
partners, not by their individual frequencies. -/
theorem abs_externalResidue_le_cohelical_separation_sum (modes : Finset Wave)
    (u : Wave → Fin 3 → ℂ) {k p q : Wave} (hpq : p + q = k) (hk : wsq k ≠ 0)
    (hsupp : ∀ a, a ∉ modes → u a = 0) (l : Wave → ℝ) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hl : ∀ a, l a = s * wlen a)
    (hbel : ∀ a, cross (wC a) (u a) = fun i => (-Complex.I) * (l a : ℂ) * u a i) :
    |(herm (fun i => -(leray k (externalAdvection modes u k p q) i))
        (cross (u p) (u q))).re|
      ≤ (1 / 2) * ∑ a ∈ extIdxSym modes k p q,
          wlen (k - a - a) * (nrm (u a) * nrm (u (k - a)) * (nrm (u p) * nrm (u q))) := by
  refine le_trans (abs_externalResidue_le_helicity_gap_sum modes u hpq hk hsupp l hbel) ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_) (by norm_num)
  have hgap : |l (k - a) - l a| ≤ wlen (k - a - a) := by
    have h : |l (k - a) - l a| = |wlen (k - a) - wlen a| := by
      rw [hl, hl, ← mul_sub, abs_mul]
      rcases hs with h | h <;> simp [h]
    rw [h]
    exact abs_wlen_sub_le (k - a) a
  exact mul_le_mul_of_nonneg_right hgap
    (mul_nonneg (mul_nonneg (nrm_nonneg _) (nrm_nonneg _))
      (mul_nonneg (nrm_nonneg _) (nrm_nonneg _)))

/-! ## Domination by the energy and the dissipation -/

theorem nsq_zero_fun : nsq (0 : Fin 3 → ℂ) = 0 := by
  simp [nsq]

theorem partner_injOn (S : Finset Wave) (k : Wave) :
    ∀ x ∈ S, ∀ y ∈ S, k - x = k - y → x = y := by
  intro x _ y _ h
  have : k - (k - x) = k - (k - y) := by rw [h]
  simpa [sub_sub_cancel] using this

theorem sum_nsq_le_energy (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (S : Finset Wave)
    (hsupp : ∀ a, a ∉ modes → u a = 0) :
    ∑ a ∈ S, nsq (u a) ≤ ∑ m ∈ modes, nsq (u m) := by
  classical
  have h1 : ∑ a ∈ S ∩ modes, nsq (u a) = ∑ a ∈ S, nsq (u a) := by
    refine Finset.sum_subset Finset.inter_subset_left ?_
    intro x hx hxn
    have hxm : x ∉ modes := fun hm => hxn (Finset.mem_inter.mpr ⟨hx, hm⟩)
    rw [hsupp x hxm, nsq_zero_fun]
  rw [← h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    fun i _ _ => nsq_nonneg _

theorem sum_wsq_nsq_le_dissipation (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (S : Finset Wave)
    (hsupp : ∀ a, a ∉ modes → u a = 0) :
    ∑ a ∈ S, wsq a * nsq (u a) ≤ ∑ m ∈ modes, wsq m * nsq (u m) := by
  classical
  have h1 : ∑ a ∈ S ∩ modes, wsq a * nsq (u a) = ∑ a ∈ S, wsq a * nsq (u a) := by
    refine Finset.sum_subset Finset.inter_subset_left ?_
    intro x hx hxn
    have hxm : x ∉ modes := fun hm => hxn (Finset.mem_inter.mpr ⟨hx, hm⟩)
    rw [hsupp x hxm, nsq_zero_fun, mul_zero]
  rw [← h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    fun i _ _ => mul_nonneg (wsq_nonneg' i) (nsq_nonneg _)

theorem sum_partner_nsq_le_energy (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (S : Finset Wave)
    (k : Wave) (hsupp : ∀ a, a ∉ modes → u a = 0) :
    ∑ a ∈ S, nsq (u (k - a)) ≤ ∑ m ∈ modes, nsq (u m) := by
  classical
  have himg : ∑ x ∈ S.image (fun a => k - a), nsq (u x) = ∑ a ∈ S, nsq (u (k - a)) :=
    Finset.sum_image (partner_injOn S k)
  rw [← himg]
  exact sum_nsq_le_energy modes u _ hsupp

theorem sum_partner_wsq_nsq_le_dissipation (modes : Finset Wave) (u : Wave → Fin 3 → ℂ)
    (S : Finset Wave) (k : Wave) (hsupp : ∀ a, a ∉ modes → u a = 0) :
    ∑ a ∈ S, wsq (k - a) * nsq (u (k - a)) ≤ ∑ m ∈ modes, wsq m * nsq (u m) := by
  classical
  have himg : ∑ x ∈ S.image (fun a => k - a), wsq x * nsq (u x)
      = ∑ a ∈ S, wsq (k - a) * nsq (u (k - a)) :=
    Finset.sum_image (partner_injOn S k)
  rw [← himg]
  exact sum_wsq_nsq_le_dissipation modes u _ hsupp

/-- Discrete Cauchy–Schwarz in the form used below. -/
theorem sum_mul_le_sqrt_mul (S : Finset Wave) (f g : Wave → ℝ)
    (hf : ∀ a, 0 ≤ f a) (hg : ∀ a, 0 ≤ g a) (A B : ℝ)
    (hA : ∑ a ∈ S, f a ^ 2 ≤ A) (hB : ∑ a ∈ S, g a ^ 2 ≤ B) :
    ∑ a ∈ S, f a * g a ≤ Real.sqrt (A * B) := by
  have hnn : 0 ≤ ∑ a ∈ S, f a * g a :=
    Finset.sum_nonneg fun a _ => mul_nonneg (hf a) (hg a)
  have hA0 : 0 ≤ A := le_trans (Finset.sum_nonneg fun a _ => sq_nonneg _) hA
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S f g
  have hle : (∑ a ∈ S, f a * g a) ^ 2 ≤ A * B := by
    refine le_trans hcs ?_
    refine mul_le_mul hA hB (Finset.sum_nonneg fun a _ => sq_nonneg _) hA0
  have := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq hnn] at this

/-- **The external cross-triad residue costs at most one half power of the
enstrophy.**  The frequency-weighted sum of the partner pairing is controlled by
Cauchy–Schwarz by the geometric mean of the dissipation and the energy. -/
theorem abs_externalResidue_le_sqrt_energy_dissipation (modes : Finset Wave)
    (u : Wave → Fin 3 → ℂ) {k p q : Wave} (hpq : p + q = k) (hk : wsq k ≠ 0)
    (hsupp : ∀ a, a ∉ modes → u a = 0) (l : Wave → ℝ)
    (hbel : ∀ a, cross (wC a) (u a) = fun i => (-Complex.I) * (l a : ℂ) * u a i) :
    |(herm (fun i => -(leray k (externalAdvection modes u k p q) i))
        (cross (u p) (u q))).re|
      ≤ Real.sqrt ((∑ m ∈ modes, wsq m * nsq (u m)) * (∑ m ∈ modes, nsq (u m)))
          * (nrm (u p) * nrm (u q)) := by
  classical
  set S := extIdxSym modes k p q with hS
  set D := ∑ m ∈ modes, wsq m * nsq (u m) with hD
  set E := ∑ m ∈ modes, nsq (u m) with hE
  set W := nrm (u p) * nrm (u q) with hW
  have hWnn : 0 ≤ W := mul_nonneg (nrm_nonneg _) (nrm_nonneg _)
  -- the two Cauchy–Schwarz estimates
  have hcs1 : ∑ a ∈ S, wlen a * (nrm (u a) * nrm (u (k - a))) ≤ Real.sqrt (D * E) := by
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
  have hcs2 : ∑ a ∈ S, wlen (k - a) * (nrm (u a) * nrm (u (k - a))) ≤ Real.sqrt (D * E) := by
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
  refine le_trans (abs_externalResidue_le_frequency_sum modes u hpq hk hsupp l hbel) ?_
  have hsplit : ∑ a ∈ S, (wlen a + wlen (k - a)) * (nrm (u a) * nrm (u (k - a)) * W)
      = (∑ a ∈ S, wlen a * (nrm (u a) * nrm (u (k - a)))) * W
        + (∑ a ∈ S, wlen (k - a) * (nrm (u a) * nrm (u (k - a)))) * W := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hsplit]
  have h1 := mul_le_mul_of_nonneg_right hcs1 hWnn
  have h2 := mul_le_mul_of_nonneg_right hcs2 hWnn
  linarith

/-! ## On the Galerkin carrier -/

namespace GalerkinFlow

variable (G : GalerkinFlow)

/-- **The frequency-weighted bound for the external residue of a Galerkin
flow.**  This is the literal `G.externalResidue`, expanded into quartic
incidence cells, paired by the shared-output-fibre partner map, and estimated
through the helicity gap. -/
theorem abs_externalResidue_le_frequency_sum (t : ℝ) {p q : Wave}
    (hpq : p + q ∈ G.modes) (l : Wave → ℝ)
    (hbel : ∀ a ∈ G.modes,
      cross (wC a) (G.u t a) = fun i => (-Complex.I) * (l a : ℂ) * G.u t a i) :
    |G.externalResidue t (p, q)|
      ≤ (1 / 2) * ∑ a ∈ extIdxSym G.modes (p + q) p q,
          (wlen a + wlen ((p + q) - a))
            * (nrm (G.u t a) * nrm (G.u t ((p + q) - a))
                * (nrm (G.u t p) * nrm (G.u t q))) := by
  have hsupp : ∀ a, a ∉ G.modes → G.u t a = 0 := fun a ha => G.support t a ha
  have hbel' := beltrami_of_support G.modes (G.u t) l hsupp hbel
  exact ClayNS.Waleffe.abs_externalResidue_le_frequency_sum G.modes (G.u t) rfl
    (G.wsq_ne_zero_of_mem hpq) hsupp l hbel'

/-- **The external cross-triad residue of a Galerkin flow costs at most
`√(𝔇E)·‖u_p‖‖u_q‖`.**  This is the cutoff-uniform price of the residue in terms
of the two classical quantities of the flow: the dissipation (enstrophy) and the
energy. -/
theorem abs_externalResidue_le_sqrt_energy_dissipation (t : ℝ) {p q : Wave}
    (hpq : p + q ∈ G.modes) (l : Wave → ℝ)
    (hbel : ∀ a ∈ G.modes,
      cross (wC a) (G.u t a) = fun i => (-Complex.I) * (l a : ℂ) * G.u t a i) :
    |G.externalResidue t (p, q)|
      ≤ Real.sqrt (G.dissipation t * G.energy t) * (nrm (G.u t p) * nrm (G.u t q)) := by
  have hsupp : ∀ a, a ∉ G.modes → G.u t a = 0 := fun a ha => G.support t a ha
  have hbel' := beltrami_of_support G.modes (G.u t) l hsupp hbel
  exact ClayNS.Waleffe.abs_externalResidue_le_sqrt_energy_dissipation G.modes (G.u t) rfl
    (G.wsq_ne_zero_of_mem hpq) hsupp l hbel'

/-- **The external residue of a matched selection of pairs.**  If no mode is
used twice as a first component and none twice as a second component, the whole
external cross-triad residue of the selection is bounded by `√(𝔇E)·E` — with no
cardinality, shell or cutoff factor. -/
theorem selected_external_residue_le (t : ℝ) (chi : Finset (Wave × Wave))
    (hchi : chi ⊆ G.modes ×ˢ G.modes)
    (hinj1 : ∀ x ∈ chi, ∀ y ∈ chi, x.1 = y.1 → x = y)
    (hinj2 : ∀ x ∈ chi, ∀ y ∈ chi, x.2 = y.2 → x = y)
    (hsum : ∀ x ∈ chi, x.1 + x.2 ∈ G.modes) (l : Wave → ℝ)
    (hbel : ∀ a ∈ G.modes,
      cross (wC a) (G.u t a) = fun i => (-Complex.I) * (l a : ℂ) * G.u t a i) :
    ∑ x ∈ chi, |G.externalResidue t x|
      ≤ Real.sqrt (G.dissipation t * G.energy t) * G.energy t := by
  classical
  set Q := Real.sqrt (G.dissipation t * G.energy t) with hQ
  have hQnn : 0 ≤ Q := Real.sqrt_nonneg _
  have hterm : ∀ x ∈ chi,
      |G.externalResidue t x| ≤ Q * (nrm (G.u t x.1) * nrm (G.u t x.2)) := fun x hx =>
    G.abs_externalResidue_le_sqrt_energy_dissipation t (hsum x hx) l hbel
  have hfirst : ∑ x ∈ chi, nsq (G.u t x.1) ≤ G.energy t := by
    have himg : ∑ m ∈ chi.image (fun x => x.1), nsq (G.u t m)
        = ∑ x ∈ chi, nsq (G.u t x.1) := Finset.sum_image hinj1
    rw [← himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => nsq_nonneg _
    intro m hm
    obtain ⟨x, hx, hxm⟩ := Finset.mem_image.mp hm
    rw [← hxm]
    exact (Finset.mem_product.mp (hchi hx)).1
  have hsecond : ∑ x ∈ chi, nsq (G.u t x.2) ≤ G.energy t := by
    have himg : ∑ m ∈ chi.image (fun x => x.2), nsq (G.u t m)
        = ∑ x ∈ chi, nsq (G.u t x.2) := Finset.sum_image hinj2
    rw [← himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => nsq_nonneg _
    intro m hm
    obtain ⟨x, hx, hxm⟩ := Finset.mem_image.mp hm
    rw [← hxm]
    exact (Finset.mem_product.mp (hchi hx)).2
  have hprod : ∑ x ∈ chi, nrm (G.u t x.1) * nrm (G.u t x.2) ≤ G.energy t := by
    have hstep : ∑ x ∈ chi, nrm (G.u t x.1) * nrm (G.u t x.2)
        ≤ ∑ x ∈ chi, (nsq (G.u t x.1) + nsq (G.u t x.2)) / 2 := by
      refine Finset.sum_le_sum fun x _ => ?_
      have h1 : nsq (G.u t x.1) = nrm (G.u t x.1) ^ 2 := (nrm_sq _).symm
      have h2 : nsq (G.u t x.2) = nrm (G.u t x.2) ^ 2 := (nrm_sq _).symm
      rw [h1, h2]
      nlinarith [sq_nonneg (nrm (G.u t x.1) - nrm (G.u t x.2))]
    have hhalf : ∑ x ∈ chi, (nsq (G.u t x.1) + nsq (G.u t x.2)) / 2
        = ((∑ x ∈ chi, nsq (G.u t x.1)) + ∑ x ∈ chi, nsq (G.u t x.2)) / 2 := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_div]
    rw [hhalf] at hstep
    linarith
  calc ∑ x ∈ chi, |G.externalResidue t x|
      ≤ ∑ x ∈ chi, Q * (nrm (G.u t x.1) * nrm (G.u t x.2)) := Finset.sum_le_sum hterm
    _ = Q * ∑ x ∈ chi, nrm (G.u t x.1) * nrm (G.u t x.2) := by rw [Finset.mul_sum]
    _ ≤ Q * G.energy t := mul_le_mul_of_nonneg_left hprod hQnn

/-- **The integrated external cross-triad residue of a matched selection.**  For
every `c > 0` the time integral of the external residue is bounded, uniformly in
the Galerkin cutoff and in the number of pairs selected, by
`√E(t₀)·E(t₀)·(E(t₀)/(4νc) + c(t₁−t₀)/2)`.  The bound is finite on every finite
time interval but, unlike the internal payment `E(t₀)²/ν`, it grows with the
length of the interval. -/
theorem selected_external_residue_integrated_le (hnu : 0 < G.nu) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (chi : Finset (Wave × Wave)) (hchi : chi ⊆ G.modes ×ˢ G.modes)
    (hinj1 : ∀ x ∈ chi, ∀ y ∈ chi, x.1 = y.1 → x = y)
    (hinj2 : ∀ x ∈ chi, ∀ y ∈ chi, x.2 = y.2 → x = y)
    (hsum : ∀ x ∈ chi, x.1 + x.2 ∈ G.modes) (l : Wave → ℝ)
    (hbel : ∀ (t : ℝ), ∀ a ∈ G.modes,
      cross (wC a) (G.u t a) = fun i => (-Complex.I) * (l a : ℂ) * G.u t a i)
    {c : ℝ} (hc : 0 < c) :
    (∫ t in t₀..t₁, ∑ x ∈ chi, |G.externalResidue t x|)
      ≤ Real.sqrt (G.energy t₀) * G.energy t₀
          * (G.energy t₀ / (4 * G.nu * c) + c * (t₁ - t₀) / 2) := by
  classical
  set E₀ := G.energy t₀ with hE₀
  have hE₀nn : 0 ≤ E₀ := G.energy_nonneg t₀
  set K := Real.sqrt E₀ * E₀ with hK
  have hKnn : 0 ≤ K := mul_nonneg (Real.sqrt_nonneg _) hE₀nn
  -- the pointwise bound
  have hpt : ∀ t ∈ Set.uIcc t₀ t₁, ∑ x ∈ chi, |G.externalResidue t x|
      ≤ K * (G.dissipation t / (2 * c) + c / 2) := by
    intro t htmem
    have ht₀t : t₀ ≤ t := (Set.mem_uIcc.mp htmem).elim (fun h => h.1) (fun h => le_trans ht h.1)
    have hEt : G.energy t ≤ E₀ := G.energy_le_initial ht₀t
    have hEtnn : 0 ≤ G.energy t := G.energy_nonneg t
    have hDnn : 0 ≤ G.dissipation t := G.dissipation_nonneg t
    have h1 := G.selected_external_residue_le t chi hchi hinj1 hinj2 hsum l (hbel t)
    have hsplit : Real.sqrt (G.dissipation t * G.energy t)
        = Real.sqrt (G.dissipation t) * Real.sqrt (G.energy t) := Real.sqrt_mul hDnn _
    have hsqrtE : Real.sqrt (G.energy t) ≤ Real.sqrt E₀ := Real.sqrt_le_sqrt hEt
    have hamgm : Real.sqrt (G.dissipation t) ≤ G.dissipation t / (2 * c) + c / 2 := by
      have hsq : Real.sqrt (G.dissipation t) ^ 2 = G.dissipation t := Real.sq_sqrt hDnn
      have hkey : Real.sqrt (G.dissipation t) * (2 * c) ≤ G.dissipation t + c ^ 2 := by
        nlinarith [sq_nonneg (Real.sqrt (G.dissipation t) - c)]
      have hrw : G.dissipation t / (2 * c) + c / 2 = (G.dissipation t + c ^ 2) / (2 * c) := by
        field_simp
      rw [hrw, le_div_iff₀ (by positivity)]
      exact hkey
    have hchain : Real.sqrt (G.dissipation t * G.energy t) * G.energy t
        ≤ K * (G.dissipation t / (2 * c) + c / 2) := by
      have hamgmnn : 0 ≤ G.dissipation t / (2 * c) + c / 2 := by positivity
      calc Real.sqrt (G.dissipation t * G.energy t) * G.energy t
          = (Real.sqrt (G.dissipation t) * Real.sqrt (G.energy t)) * G.energy t := by
            rw [hsplit]
        _ ≤ ((G.dissipation t / (2 * c) + c / 2) * Real.sqrt E₀) * E₀ := by
            have hA : Real.sqrt (G.dissipation t) * Real.sqrt (G.energy t)
                ≤ (G.dissipation t / (2 * c) + c / 2) * Real.sqrt E₀ :=
              mul_le_mul hamgm hsqrtE (Real.sqrt_nonneg _) hamgmnn
            exact mul_le_mul hA hEt hEtnn
              (mul_nonneg hamgmnn (Real.sqrt_nonneg _))
        _ = K * (G.dissipation t / (2 * c) + c / 2) := by rw [hK]; ring
    exact le_trans h1 hchain
  -- integrate
  have hcontL : Continuous fun t => ∑ x ∈ chi, |G.externalResidue t x| :=
    continuous_finset_sum _ fun x _ => continuous_abs.comp (G.continuous_externalResidue x)
  have hcontR : Continuous fun t => K * (G.dissipation t / (2 * c) + c / 2) :=
    continuous_const.mul ((G.continuous_dissipation.div_const _).add continuous_const)
  have hmono : (∫ t in t₀..t₁, ∑ x ∈ chi, |G.externalResidue t x|)
      ≤ ∫ t in t₀..t₁, K * (G.dissipation t / (2 * c) + c / 2) := by
    refine intervalIntegral.integral_mono_on ht (hcontL.intervalIntegrable _ _)
      (hcontR.intervalIntegrable _ _) ?_
    intro t htmem
    exact hpt t (Set.mem_uIcc_of_le htmem.1 htmem.2)
  have hval : (∫ t in t₀..t₁, K * (G.dissipation t / (2 * c) + c / 2))
      = K * ((∫ t in t₀..t₁, G.dissipation t) / (2 * c) + c / 2 * (t₁ - t₀)) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      ((G.continuous_dissipation.div_const _).intervalIntegrable _ _)
      (intervalIntegrable_const)]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const]
    simp [mul_comm]
  have hdiss : (∫ t in t₀..t₁, G.dissipation t) ≤ E₀ / (2 * G.nu) :=
    G.integral_dissipation_le t₀ t₁ hnu
  have hfinal : K * ((∫ t in t₀..t₁, G.dissipation t) / (2 * c) + c / 2 * (t₁ - t₀))
      ≤ K * (E₀ / (4 * G.nu * c) + c * (t₁ - t₀) / 2) := by
    refine mul_le_mul_of_nonneg_left ?_ hKnn
    have hcpos : 0 < 2 * c := by linarith
    have h1 : (∫ t in t₀..t₁, G.dissipation t) / (2 * c) ≤ (E₀ / (2 * G.nu)) / (2 * c) :=
      div_le_div_of_nonneg_right hdiss hcpos.le
    have h2 : (E₀ / (2 * G.nu)) / (2 * c) = E₀ / (4 * G.nu * c) := by
      field_simp
      ring
    rw [h2] at h1
    linarith
  rw [hval] at hmono
  linarith

end GalerkinFlow

end ClayNS.Waleffe

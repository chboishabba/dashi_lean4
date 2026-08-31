/-
# The low-output gain of the physical modal forcing, on the whole fibre

`WaleffeForcingMajorant.lean` bounds the literal modal forcing termwise by

  `‖f_k‖ ≤ ∑_p ‖u_p‖ · |k − p| · ‖u_{k−p}‖`,

in which every term carries a *leg* frequency `|k − p|`.  That derivative is the
supercritical cost of termwise majorization, and in the dangerous high-high
regime (both legs huge, output small) it is exactly the wrong frequency.

This file removes it.  On the literal Galerkin carrier, using nothing but
incompressibility and the Leray projection,

  `‖f_k‖ ≤ |k| · ∑_p ‖u_p‖ ‖u_{k−p}‖`,

with the *output* frequency `|k|` and the constant `1`.  The mechanism is exact
and purely algebraic:

* `cross_triple` — the BAC–CAB identity on `ℂ³` for the bilinear cross and dot
  products;
* `pairAdvection_output_form` — for transverse legs with `p + q = k`, the
  advective pair of the incidence is

    `i(u_p·q)u_q + i(u_q·p)u_p
       = 2i (u_p·u_q) k − i ( u_p × (k × u_q) + u_q × (k × u_p) )`,

  so after the two BAC–CAB expansions the *leg* wavevectors have disappeared
  entirely: what is left is one longitudinal term and two terms carrying the
  output wavevector;
* `leray_pairAdvection_output_le` — the Leray projection annihilates the
  longitudinal term, whence `‖P_k(pair)‖ ≤ 2|k| ‖u_p‖‖u_q‖`;
* `GalerkinFlow.nrm_force_le_output_gain` — the fibre of `k` is symmetrised by
  the shared-output involution `p ↦ k − p` (the added indices are unoccupied and
  contribute nothing), so the factor `2` is halved and the gain survives the
  whole fibre sum.

Composing with `WaleffeCriticalCompanionSummation.lean` makes the critical
absorption on the Galerkin carrier **unconditional**:
`GalerkinFlow.abs_critProd_le_wiener_absorption_of_flow` no longer assumes the
gain, it proves it.
-/
import RequestProject.NavierStokes.WaleffeCriticalCompanionSummation

noncomputable section

namespace ClayNS.Waleffe

/-! ## 1. The exact output normal form of the advective pair -/

/-- **BAC–CAB on `ℂ³`** for the bilinear cross and dot products:
`a × (b × c) = b ⟨a,c⟩ − c ⟨a,b⟩`. -/
theorem cross_triple (a b c : Fin 3 → ℂ) :
    cross a (cross b c) = fun i => dotb a c * b i - dotb a b * c i := by
  funext i
  fin_cases i <;> simp [cross, crossProduct, dotb, Fin.sum_univ_three] <;> ring

/-- **The output normal form of the advective pair.**  For two transverse legs
with `p + q = k`, the two convolution terms of the incidence contain no leg
wavevector at all: one longitudinal term along `k`, and two terms in which the
cross product is taken against the *output* wavevector. -/
theorem pairAdvection_output_form {p q k : Wave} (hpq : p + q = k) (up uq : Fin 3 → ℂ)
    (htp : dotb up (wC p) = 0) (htq : dotb uq (wC q) = 0) :
    pairAdvection p q up uq
      = fun i => (2 * Complex.I * dotb up uq) * wC k i
          + (-Complex.I) * (cross up (cross (wC k) uq) i + cross uq (cross (wC k) up) i) := by
  have hkC : (fun i => wC p i + wC q i) = wC k := funext (wC_add hpq)
  have hk1 : dotb up (wC k) = dotb up (wC q) := by
    rw [← hkC, dotb_add_right, htp, zero_add]
  have hk2 : dotb uq (wC k) = dotb uq (wC p) := by
    rw [← hkC, dotb_add_right, htq, add_zero]
  have h1 := cross_triple up (wC k) uq
  have h2 := cross_triple uq (wC k) up
  funext i
  have e1 : cross up (cross (wC k) uq) i = dotb up uq * wC k i - dotb up (wC k) * uq i :=
    congrFun h1 i
  have e2 : cross uq (cross (wC k) up) i = dotb uq up * wC k i - dotb uq (wC k) * up i :=
    congrFun h2 i
  have hcomm : dotb uq up = dotb up uq := dotb_comm uq up
  rw [e1, e2, hk1, hk2, hcomm]
  simp only [pairAdvection]
  ring

/-- **The low-output gain of one incidence.**  For two transverse legs with
`p + q = k`, the Leray projection of the advective pair carries the *output*
frequency, not a leg frequency. -/
theorem leray_pairAdvection_output_le {p q k : Wave} (hpq : p + q = k) (hk : wsq k ≠ 0)
    (up uq : Fin 3 → ℂ) (htp : dotb up (wC p) = 0) (htq : dotb uq (wC q) = 0) :
    nrm (leray k (pairAdvection p q up uq)) ≤ 2 * wlen k * (nrm up * nrm uq) := by
  set A : Fin 3 → ℂ := fun i => cross up (cross (wC k) uq) i + cross uq (cross (wC k) up) i with hA
  have hform := pairAdvection_output_form hpq up uq htp htq
  have hsplit : leray k (pairAdvection p q up uq)
      = fun i => leray k (fun j => (2 * Complex.I * dotb up uq) * wC k j) i
          + leray k (fun j => (-Complex.I) * A j) i := by
    rw [hform]
    exact leray_add k _ _
  have hlong : leray k (fun j => (2 * Complex.I * dotb up uq) * wC k j) = fun _ => 0 :=
    leray_longitudinal k _ hk
  have hred : leray k (pairAdvection p q up uq) = leray k (fun j => (-Complex.I) * A j) := by
    rw [hsplit, hlong]
    funext i
    simp
  rw [hred]
  have hle1 : nrm (leray k (fun j => (-Complex.I) * A j)) ≤ nrm (fun j => (-Complex.I) * A j) :=
    nrm_leray_le k _ hk
  have hle2 : nrm (fun j => (-Complex.I) * A j) = nrm A := by
    rw [nrm_const_mul]
    simp
  have hcross1 : nrm (cross up (cross (wC k) uq)) ≤ nrm up * (wlen k * nrm uq) := by
    refine le_trans (nrm_cross_le _ _) ?_
    refine mul_le_mul_of_nonneg_left ?_ (nrm_nonneg _)
    have := nrm_cross_le (wC k) uq
    rwa [nrm_wC] at this
  have hcross2 : nrm (cross uq (cross (wC k) up)) ≤ nrm uq * (wlen k * nrm up) := by
    refine le_trans (nrm_cross_le _ _) ?_
    refine mul_le_mul_of_nonneg_left ?_ (nrm_nonneg _)
    have := nrm_cross_le (wC k) up
    rwa [nrm_wC] at this
  have hA_le : nrm A ≤ 2 * wlen k * (nrm up * nrm uq) := by
    have hadd : nrm A ≤ nrm (cross up (cross (wC k) uq)) + nrm (cross uq (cross (wC k) up)) :=
      nrm_add_le _ _
    have : nrm up * (wlen k * nrm uq) + nrm uq * (wlen k * nrm up)
        = 2 * wlen k * (nrm up * nrm uq) := by ring
    linarith [hadd, hcross1, hcross2]
  linarith [hle1, hle2 ▸ hle1]

/-! ## 2. The whole fibre -/

/-- The advective cell of the incidence `p` in the fibre of the output `k`. -/
def advCell (u : Wave → Fin 3 → ℂ) (k p : Wave) : Fin 3 → ℂ :=
  fun i => (Complex.I * dotb (u p) (wC (k - p))) * u (k - p) i

theorem advection_eq_sum_advCell (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) (k : Wave) :
    advection modes u k = fun i => ∑ p ∈ modes, advCell u k p i := by
  funext i
  simp [advection, advCell, dotb, wC]

/-- The shared-output involution pairs two cells into the advective pair. -/
theorem advCell_partner (u : Wave → Fin 3 → ℂ) (k p : Wave) :
    (fun i => advCell u k p i + advCell u k (k - p) i)
      = pairAdvection p (k - p) (u p) (u (k - p)) := by
  funext i
  simp only [advCell, pairAdvection, sub_sub_cancel]

namespace GalerkinFlow

variable (G : GalerkinFlow)

/-- The symmetrised fibre of the output `k`: the retained modes together with
their partners under `p ↦ k − p`. -/
def symFibre (k : Wave) : Finset Wave := G.modes ∪ G.modes.image (fun p => k - p)

theorem modes_subset_symFibre (k : Wave) : G.modes ⊆ G.symFibre k := Finset.subset_union_left

theorem symFibre_partner {k p : Wave} (hp : p ∈ G.symFibre k) : k - p ∈ G.symFibre k := by
  classical
  rcases Finset.mem_union.1 hp with h | h
  · exact Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨p, h, rfl⟩))
  · rcases Finset.mem_image.1 h with ⟨m, hm, hmp⟩
    have : k - p = m := by rw [← hmp]; abel
    rw [this]
    exact Finset.mem_union.2 (Or.inl hm)

theorem advCell_eq_zero_of_not_mem (t : ℝ) {k p : Wave} (hp : p ∉ G.modes) :
    advCell (G.u t) k p = fun _ => 0 := by
  funext i
  have h0 : G.u t p = 0 := G.support t p hp
  simp [advCell, h0, dotb]

theorem sum_advCell_symFibre (t : ℝ) (k : Wave) (i : Fin 3) :
    ∑ p ∈ G.modes, advCell (G.u t) k p i = ∑ p ∈ G.symFibre k, advCell (G.u t) k p i := by
  classical
  refine Finset.sum_subset (G.modes_subset_symFibre k) ?_
  intro p _ hp
  rw [G.advCell_eq_zero_of_not_mem t hp]

/-- **The low-output gain of the physical modal forcing.**  On the literal
Galerkin carrier, and using only incompressibility, the projected nonlinearity of
the mode `k` is bounded by the *output* frequency times the convolution of the
mode amplitudes — with no leg derivative and constant `1`. -/
theorem nrm_force_le_output_gain (t : ℝ) {k : Wave} (hk : wsq k ≠ 0) :
    nrm (G.force t k) ≤ wlen k * cellMajorant G.modes (fun a => nrm (G.u t a)) k := by
  classical
  set u := G.u t with hu
  -- the advection is the sum of its cells over the symmetrised fibre
  have hadv : advection G.modes u k = fun i => ∑ p ∈ G.symFibre k, advCell u k p i := by
    rw [advection_eq_sum_advCell]
    funext i
    exact G.sum_advCell_symFibre t k i
  -- pairing the fibre under `p ↦ k − p`
  have hreindex : ∑ p ∈ G.symFibre k, (fun i => advCell u k (k - p) i)
      = ∑ p ∈ G.symFibre k, (fun i => advCell u k p i) := by
    refine Finset.sum_nbij' (fun p => k - p) (fun p => k - p) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      exact G.symFibre_partner ha
    · intro a ha
      exact G.symFibre_partner ha
    · intro a _
      simp
    · intro a _
      simp
    · intro a _
      rfl
  have hdouble : (fun i => (2 : ℂ) * (∑ p ∈ G.symFibre k, advCell u k p i))
      = fun i => ∑ p ∈ G.symFibre k, pairAdvection p (k - p) (u p) (u (k - p)) i := by
    funext i
    have hsum : ∑ p ∈ G.symFibre k, pairAdvection p (k - p) (u p) (u (k - p)) i
        = ∑ p ∈ G.symFibre k, (advCell u k p i + advCell u k (k - p) i) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      exact (congrFun (advCell_partner u k p) i).symm
    have hsplit : ∑ p ∈ G.symFibre k, (advCell u k p i + advCell u k (k - p) i)
        = (∑ p ∈ G.symFibre k, advCell u k p i) + ∑ p ∈ G.symFibre k, advCell u k (k - p) i :=
      Finset.sum_add_distrib
    have hpart : ∑ p ∈ G.symFibre k, advCell u k (k - p) i
        = ∑ p ∈ G.symFibre k, advCell u k p i := by
      have := congrFun hreindex i
      simpa using this
    rw [hsum, hsplit, hpart]
    ring
  -- the projected pair of every incidence carries the output frequency
  have hpair : ∀ p ∈ G.symFibre k,
      nrm (leray k (pairAdvection p (k - p) (u p) (u (k - p))))
        ≤ 2 * wlen k * (nrm (u p) * nrm (u (k - p))) := by
    intro p _
    refine leray_pairAdvection_output_le (by abel) hk (u p) (u (k - p)) ?_ ?_
    · exact dotb_transverse (G.transverse t p)
    · exact dotb_transverse (G.transverse t (k - p))
  -- assemble
  have hforce : nrm (G.force t k) = nrm (leray k (advection G.modes u k)) := by
    have he : G.force t k = fun i => -(leray k (advection G.modes u k) i) := rfl
    rw [he, nrm_neg]
  have htwo : (2 : ℝ) * nrm (leray k (advection G.modes u k))
      ≤ ∑ p ∈ G.symFibre k, 2 * wlen k * (nrm (u p) * nrm (u (k - p))) := by
    have hL : leray k (fun i => (2 : ℂ) * (advection G.modes u k) i)
        = fun i => ∑ p ∈ G.symFibre k, leray k (pairAdvection p (k - p) (u p) (u (k - p))) i := by
      rw [hadv, hdouble, leray_sum]
    have hnormL : nrm (fun i => (2 : ℂ) * (advection G.modes u k) i)
        = 2 * nrm (advection G.modes u k) := by
      rw [nrm_const_mul]
      simp
    have h1 : (2 : ℝ) * nrm (leray k (advection G.modes u k))
        = nrm (leray k (fun i => (2 : ℂ) * (advection G.modes u k) i)) := by
      rw [leray_smul, nrm_const_mul]
      simp
    rw [h1, hL]
    refine le_trans (nrm_sum_le _ _) ?_
    exact Finset.sum_le_sum hpair
  have hsym : ∑ p ∈ G.symFibre k, 2 * wlen k * (nrm (u p) * nrm (u (k - p)))
      = ∑ p ∈ G.modes, 2 * wlen k * (nrm (u p) * nrm (u (k - p))) := by
    refine (Finset.sum_subset (G.modes_subset_symFibre k) ?_).symm
    intro p _ hp
    have h0 : u p = 0 := G.support t p hp
    have : nrm (u p) = 0 := by
      rw [h0]
      simp [nrm, nsq]
    rw [this]
    ring
  rw [hforce]
  have hfin : ∑ p ∈ G.modes, 2 * wlen k * (nrm (u p) * nrm (u (k - p)))
      = 2 * (wlen k * cellMajorant G.modes (fun a => nrm (u a)) k) := by
    rw [cellMajorant, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsym, hfin] at htwo
  linarith

/-- **The critical absorption on the physical carrier, unconditionally.**  No
gain hypothesis: the low-output gain is proved above from incompressibility. -/
theorem abs_critProd_le_wiener_absorption_of_flow (t : ℝ) {theta : ℝ} (hth : 0 < theta) :
    |G.critProd t| ≤ theta * G.critDiss t
      + (1 / theta) * ((∑ a ∈ G.modes, nrm (G.u t a)) ^ 2
          * (∑ a ∈ G.modes, wlen a * nrm (G.u t a) ^ 2)) :=
  G.abs_critProd_le_wiener_absorption t hth
    (fun _ hk => G.nrm_force_le_output_gain t (G.wsq_ne_zero_of_mem hk))

end GalerkinFlow

end ClayNS.Waleffe

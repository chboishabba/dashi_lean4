/-
# Feeding the paid remainder budget into the signed Gram flux consumer

`ResolventGramFlux.ns_signed_gram_integral_bound` is the checked consumer of the
resolvent/flux architecture: for a family of two-leg cells obeying the literal
damped tangent `dA_α = −ν(|p|²+|q|²) A_α + F_α`, it bounds the signed integrated
Gram debt by

  `2·resForm(A(t₀)) + ε·∫ resForm(A,A) + (4/ε)·∫ resForm(F,F)`,

leaving exactly one unpaid object, the *spacetime remainder resolvent energy*
`∫_t resForm(F(t),F(t))`.

`SignedRemainderResolventBudget.lean` pays that object on the literal physical
carrier.  This file performs the wiring, at one output frequency and then summed
over the outputs:

* `resForm_outCells_eq_integral` — the *same-object receipt*: the abstract
  resolvent energy of the outer cell family at output `k`, at the literal
  viscous pair rates, **is** `∫_0^∞ ‖F_s(k)‖² ds`.  No new representation is
  introduced: this is `PSDForm.resForm_eq_integral` composed with
  `Fs_eq_heatCombo`.
* `sum_resForm_outCells_le_wiener` — hence the total remainder resolvent energy
  over all outputs is at most `9‖u‖_A⁴E/(2ν)`, cutoff-uniformly.
* `sum_gram_debt_le_wiener` — the assembled statement: summed over the outputs,
  the signed integrated Gram debt is bounded by the initial resolvent energy, an
  arbitrarily small multiple of the integrated resolvent energy of the cells,
  and `(4/ε)·9M(t₁−t₀)/(2ν)`, where `M` bounds the Wiener–energy product
  `‖u(t)‖_A⁴E(t)` on the time interval.  Every constant is explicit and none
  depends on the Galerkin truncation.

The remaining input is exactly the spacetime Wiener quantity `M`, which
`WaleffeWienerSupercritical.wiener_norm_not_controlled_by_energy` shows is not
available from the energy inequality.  Package A and the literal Clay periodic
target are not closed.
-/
import RequestProject.NavierStokes.SignedRemainderResolventBudget
import RequestProject.NavierStokes.WaleffeWienerSupercritical

noncomputable section

open MeasureTheory Set

namespace ClayNS.TTStar

open ClayNS.Waleffe ClayNS.Resolvent

/-- The literal viscous pair rates of the inner fibre at a fixed output `k`. -/
def outRate (nu : ℝ) (modes : Finset Wave) (k : Wave) : ↥modes → ℝ :=
  fun p => viscousPairRate nu (p : Wave) (k - (p : Wave))

/-- The outer cell family at a fixed output `k`, indexed by the inner fibre. -/
def outCells (N u : Wave → Fin 3 → ℂ) (modes : Finset Wave) (k : Wave) :
    ↥modes → Fin 3 → ℂ :=
  fun p => outerCellVec N u k (p : Wave)

theorem outRate_pos {nu : ℝ} (hnu : 0 < nu) {modes : Finset Wave} {k : Wave}
    (hp : ∀ p ∈ modes, wsq p ≠ 0) : ∀ i : ↥modes, 0 < outRate nu modes k i := by
  intro i
  have h1 : 0 < wsq (i : Wave) :=
    lt_of_le_of_ne (wsq_nonneg' _) (Ne.symm (hp (i : Wave) i.2))
  have h2 : 0 ≤ wsq (k - (i : Wave)) := wsq_nonneg' _
  rw [outRate, viscousPairRate]
  have : 0 < wsq (i : Wave) + wsq (k - (i : Wave)) := by linarith
  exact mul_pos hnu this

/-- **The same-object receipt.**  The abstract resolvent energy of the outer cell
family at output `k` is literally the heat-parameter integral of the squared
signed remainder at that output. -/
theorem resForm_outCells_eq_integral {nu : ℝ} (hnu : 0 < nu) (modes : Finset Wave)
    (N u : Wave → Fin 3 → ℂ) (k : Wave) (hp : ∀ p ∈ modes, wsq p ≠ 0) :
    nsPSD.resForm (outRate nu modes k) (outCells N u modes k) (outCells N u modes k)
      = ∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes N u k) := by
  rw [PSDForm.resForm_eq_integral nsPSD (outRate nu modes k) (outRate_pos hnu hp)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
  rw [Fs_eq_heatCombo nu s modes N u k]
  simp only [nsPSD_form, nsq_eq_herm_re]
  rfl

/-- The total remainder resolvent energy over all outputs is paid by the Wiener
norm and the energy, cutoff-uniformly. -/
theorem sum_resForm_outCells_le_wiener {nu : ℝ} (hnu : 0 < nu)
    (modes outs : Finset Wave) (u : Wave → Fin 3 → ℂ)
    (hk : ∀ k ∈ outs, wsq k ≠ 0) (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hdiv : ∀ c : Wave, dotb (wC c) (u c) = 0)
    (hsupp : ∀ b ∉ modes, u b = fun _ => 0) :
    ∑ k ∈ outs, nsPSD.resForm (outRate nu modes k)
        (outCells (innerForcing modes u) u modes k)
        (outCells (innerForcing modes u) u modes k)
      ≤ 9 * wienerA modes u ^ 4 * energy modes u / (2 * nu) := by
  have hrw : ∀ k ∈ outs, nsPSD.resForm (outRate nu modes k)
        (outCells (innerForcing modes u) u modes k)
        (outCells (innerForcing modes u) u modes k)
      = ∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes (innerForcing modes u) u k) :=
    fun k _ => resForm_outCells_eq_integral hnu modes (innerForcing modes u) u k hp
  rw [Finset.sum_congr rfl hrw]
  exact sum_integral_nsq_Fs_le_wiener hnu modes outs u hk hp hdiv hsupp

/-- **The assembled signed Gram bound on a Wiener input.**  Summed over the
outputs, the signed integrated Gram debt of the cell families is bounded by the
initial resolvent energy, an arbitrarily small multiple of the integrated
resolvent energy of the cells, and an explicit multiple of the spacetime Wiener
budget `M`.  The whole remainder lane is paid; nothing here depends on the
Galerkin truncation. -/
theorem sum_gram_debt_le_wiener {nu : ℝ} (hnu : 0 < nu)
    (modes outs : Finset Wave) (u : ℝ → Wave → Fin 3 → ℂ)
    (A : Wave → ℝ → ↥modes → Fin 3 → ℂ) (t₀ t₁ M : ℝ) (ht : t₀ ≤ t₁)
    {ε : ℝ} (hε : 0 < ε)
    (hk : ∀ k ∈ outs, wsq k ≠ 0) (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hdiv : ∀ t : ℝ, ∀ c : Wave, dotb (wC c) (u t c) = 0)
    (hsupp : ∀ t : ℝ, ∀ b ∉ modes, u t b = fun _ => 0)
    (hM : ∀ t ∈ Set.Icc t₀ t₁, wienerA modes (u t) ^ 4 * energy modes (u t) ≤ M)
    (hcell : ∀ k ∈ outs, ∀ t ∈ uIcc t₀ t₁, ∀ (i : ↥modes) (c : Fin 3),
      HasDerivAt (fun t => A k t i c)
        (-(outRate nu modes k i : ℂ) * A k t i c
          + outCells (innerForcing modes (u t)) (u t) modes k i c) t)
    (hrem : ∀ k ∈ outs, ∀ i j, IntervalIntegrable
      (fun t => nsPSD.gramRemainder (A k t)
        (outCells (innerForcing modes (u t)) (u t) modes k) i j) volume t₀ t₁)
    (hMint : ∀ k ∈ outs, IntervalIntegrable
      (fun t => nsPSD.resForm (outRate nu modes k) (A k t)
        (outCells (innerForcing modes (u t)) (u t) modes k)) volume t₀ t₁)
    (hAint : ∀ k ∈ outs, IntervalIntegrable
      (fun t => nsPSD.resForm (outRate nu modes k) (A k t) (A k t)) volume t₀ t₁)
    (hFint : ∀ k ∈ outs, IntervalIntegrable
      (fun t => nsPSD.resForm (outRate nu modes k)
        (outCells (innerForcing modes (u t)) (u t) modes k)
        (outCells (innerForcing modes (u t)) (u t) modes k)) volume t₀ t₁) :
    ∑ k ∈ outs, ∫ t in t₀..t₁, nsPSD.gramDebt (A k t)
      ≤ (∑ k ∈ outs, 2 * nsPSD.resForm (outRate nu modes k) (A k t₀) (A k t₀))
        + ε * (∑ k ∈ outs, ∫ t in t₀..t₁,
            nsPSD.resForm (outRate nu modes k) (A k t) (A k t))
        + (4 / ε) * (9 * M * (t₁ - t₀) / (2 * nu)) := by
  classical
  set F : Wave → ℝ → ↥modes → Fin 3 → ℂ :=
    fun k t => outCells (innerForcing modes (u t)) (u t) modes k with hFdef
  -- (i) the consumer, at each output
  have hone : ∀ k ∈ outs, (∫ t in t₀..t₁, nsPSD.gramDebt (A k t))
      ≤ 2 * nsPSD.resForm (outRate nu modes k) (A k t₀) (A k t₀)
        + ε * (∫ t in t₀..t₁, nsPSD.resForm (outRate nu modes k) (A k t) (A k t))
        + (4 / ε) * ∫ t in t₀..t₁,
            nsPSD.resForm (outRate nu modes k) (F k t) (F k t) := by
    intro k hkm
    refine ns_signed_gram_integral_bound (fun i : ↥modes => ((i : Wave), k - (i : Wave)))
      hnu (fun i => hp (i : Wave) i.2) (A k) (F k) t₀ t₁ ht hε
      (outRate nu modes k) (fun i => rfl) (hcell k hkm) (hrem k hkm) (hMint k hkm)
      (hAint k hkm) (hFint k hkm)
  have hsum1 : ∑ k ∈ outs, (∫ t in t₀..t₁, nsPSD.gramDebt (A k t))
      ≤ ∑ k ∈ outs, (2 * nsPSD.resForm (outRate nu modes k) (A k t₀) (A k t₀)
        + ε * (∫ t in t₀..t₁, nsPSD.resForm (outRate nu modes k) (A k t) (A k t))
        + (4 / ε) * ∫ t in t₀..t₁,
            nsPSD.resForm (outRate nu modes k) (F k t) (F k t)) :=
    Finset.sum_le_sum hone
  -- (ii) the remainder lane, paid
  have hFsum : ∑ k ∈ outs, (∫ t in t₀..t₁,
      nsPSD.resForm (outRate nu modes k) (F k t) (F k t))
      ≤ 9 * M * (t₁ - t₀) / (2 * nu) := by
    have hswap : ∑ k ∈ outs, (∫ t in t₀..t₁,
        nsPSD.resForm (outRate nu modes k) (F k t) (F k t))
        = ∫ t in t₀..t₁, ∑ k ∈ outs,
            nsPSD.resForm (outRate nu modes k) (F k t) (F k t) :=
      (intervalIntegral.integral_finset_sum (fun k hkm => hFint k hkm)).symm
    have hintsum : IntervalIntegrable
        (fun t => ∑ k ∈ outs, nsPSD.resForm (outRate nu modes k) (F k t) (F k t))
        volume t₀ t₁ :=
      by
        have h := IntervalIntegrable.sum outs (fun k hkm => hFint k hkm)
        have hfun : (∑ i ∈ outs, fun t =>
            nsPSD.resForm (outRate nu modes i) (F i t) (F i t))
            = fun t => ∑ k ∈ outs, nsPSD.resForm (outRate nu modes k) (F k t) (F k t) := by
          funext t
          simp [Finset.sum_apply]
        rwa [hfun] at h
    have h2nu : 0 < 2 * nu := by linarith
    have hptwise : ∀ t ∈ Set.Icc t₀ t₁,
        (∑ k ∈ outs, nsPSD.resForm (outRate nu modes k) (F k t) (F k t))
          ≤ 9 * M / (2 * nu) := by
      intro t htm
      have h1 := sum_resForm_outCells_le_wiener hnu modes outs (u t) hk hp (hdiv t) (hsupp t)
      have h2 : 9 * wienerA modes (u t) ^ 4 * energy modes (u t) / (2 * nu)
          ≤ 9 * M / (2 * nu) := by
        refine (div_le_div_iff_of_pos_right h2nu).mpr ?_
        have := hM t htm
        linarith
      simpa [hFdef] using le_trans h1 h2
    have hmono := intervalIntegral.integral_mono_on ht hintsum
      (intervalIntegrable_const (c := 9 * M / (2 * nu))) hptwise
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have heq : (t₁ - t₀) * (9 * M / (2 * nu)) = 9 * M * (t₁ - t₀) / (2 * nu) := by ring
    rw [hswap]
    linarith [hmono, heq.le, heq.ge]
  -- (iii) split the sum of the three-term bounds
  have hsplit : ∑ k ∈ outs, (2 * nsPSD.resForm (outRate nu modes k) (A k t₀) (A k t₀)
        + ε * (∫ t in t₀..t₁, nsPSD.resForm (outRate nu modes k) (A k t) (A k t))
        + (4 / ε) * ∫ t in t₀..t₁,
            nsPSD.resForm (outRate nu modes k) (F k t) (F k t))
      = (∑ k ∈ outs, 2 * nsPSD.resForm (outRate nu modes k) (A k t₀) (A k t₀))
        + ε * (∑ k ∈ outs, ∫ t in t₀..t₁,
            nsPSD.resForm (outRate nu modes k) (A k t) (A k t))
        + (4 / ε) * ∑ k ∈ outs, ∫ t in t₀..t₁,
            nsPSD.resForm (outRate nu modes k) (F k t) (F k t) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
  have hεpos : 0 < 4 / ε := by positivity
  have hlast : (4 / ε) * ∑ k ∈ outs, (∫ t in t₀..t₁,
      nsPSD.resForm (outRate nu modes k) (F k t) (F k t))
      ≤ (4 / ε) * (9 * M * (t₁ - t₀) / (2 * nu)) :=
    mul_le_mul_of_nonneg_left hFsum hεpos.le
  linarith [hsum1, hsplit.le, hsplit.ge, hlast]

/-- **The remaining input is not energy-controlled.**  For every `M` there is a
kinematically admissible field (supported on finitely many nonzero modes,
transverse to every wavevector) of unit energy whose Wiener–energy budget
`‖u‖_A⁴ E` exceeds `M`.  So the spacetime quantity that `sum_gram_debt_le_wiener`
still requires cannot be extracted from the energy inequality: it is a genuinely
supercritical input, exactly the one already isolated for the network-forcing
wall. -/
theorem wiener_energy_budget_not_controlled_by_energy (M : ℝ) :
    ∃ (modes : Finset Wave) (u : Wave → Fin 3 → ℂ),
      (0 : Wave) ∉ modes ∧
      (∀ k, herm (wC k) (u k) = 0) ∧
      (∀ m, m ∉ modes → u m = 0) ∧
      energy modes u = 1 ∧
      M ≤ wienerA modes u ^ 4 * energy modes u := by
  obtain ⟨modes, u, hzero, htrans, hsupp, hE, hW⟩ :=
    wiener_norm_not_controlled_by_energy (max M 1)
  refine ⟨modes, u, hzero, htrans, hsupp, hE, ?_⟩
  have h1 : (1 : ℝ) ≤ wienerA modes u := le_trans (le_max_right M 1) hW
  have h2 : M ≤ wienerA modes u := le_trans (le_max_left M 1) hW
  have h3 : wienerA modes u ≤ wienerA modes u ^ 4 := by
    nlinarith [h1, sq_nonneg (wienerA modes u), sq_nonneg (wienerA modes u - 1)]
  have hEeq : energy modes u = 1 := hE
  rw [hEeq, mul_one]
  linarith [h2, h3]

end ClayNS.TTStar

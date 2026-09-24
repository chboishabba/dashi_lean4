/-
# The last lossy step, isolated and replaced: almost-orthogonality (Schur) in
# place of `Re⟪G_p, G_{p'}⟫ ≤ ‖G_p‖‖G_{p'}‖`

`SignedRemainderTTStar.lean` proved the exact signed `TT*` identity

  `∫_0^∞ ‖F_s(k)‖² ds = ∑_{p,p'} Re⟪G_p, G_{p'}⟫ / (λ_p + λ_{p'})`,

and `SignedRemainderResolventBudget.lean` paid the whole form — diagonal *and*
off-diagonal — at the price of one Cauchy–Schwarz step per pair,

  `Re⟪G_p, G_{p'}⟫ ≤ ‖G_p‖ ‖G_{p'}‖`,

which turns the Gram sum into a *square of an ℓ¹ sum* and produces the
supercritical spacetime input `∫ ‖u‖_A⁴ E dt`.  That single step is the only
place on this route where phase information is discarded.

This file does three things.

1. **Locates the loss exactly.**  `herm_re_eq_sub_defect` is the identity

     `Re⟪x,y⟫ = ‖x‖‖y‖ − ‖ ‖y‖x − ‖x‖y ‖² / (2‖x‖‖y‖)`,

   so the Cauchy–Schwarz defect is *the* squared collinearity defect of the two
   cells; the estimate is an equality precisely for perfectly coherent cells.

2. **Replaces the step by a Schur test.**  `AlmostOrthogonal modes G A` says the
   pairwise coherence of the cells is dominated by a symmetric nonnegative
   kernel with row sums `≤ A`.  `sum_sum_le_schur` is the Schur test, and
   `resForm_le_schur` converts the whole signed resolvent Gram form into an
   *ℓ² sum* of the frequency-normalized cell masses:

     `∑_{p,p'} Re⟪G_p,G_{p'}⟫/(λ_p+λ_{p'}) ≤ A · ∑_p ‖G_p‖²/|p|² / (2ν)`.

3. **Computes what that buys on the literal physical carrier.**  With the
   relocated inner kernel and the physical inner forcing,

     `∑_k ∫_0^∞ ‖F_s(k)‖² ds ≤ 9 A ‖u‖_A² E² / (2ν)`   (`sum_integral_nsq_Fs_le_schur_wiener`)

   in place of `9 ‖u‖_A⁴ E / (2ν)`.  Two powers of the Wiener norm have been
   traded for two powers of the energy.  Since the energy is bounded along the
   flow, the resulting spacetime demand is
   `∫ ‖u‖_A² dt` — the *critical* Wiener quantity — rather than the
   supercritical `∫ ‖u‖_A⁴E dt` (`spacetime_remainder_le_critical`).

4. **Books the difference exactly.**  `resForm_eq_cs_sub_defect`: the signed
   resolvent Gram form *equals* its Cauchy–Schwarz majorant minus the
   resolvent-weighted total collinearity defect, so every possible improvement
   over the unconditional route is exactly a lower bound on that defect sum.

5. **Wires the gain into the existing consumer.**  `sum_gram_debt_le_schur` is
   the assembled signed Gram bound of `SignedGramWienerAssembly` with the
   spacetime budget now controlling `‖u‖_A²E²` instead of `‖u‖_A⁴E`; no other
   hypothesis of the consumer changes.

**Honest status.**  `AlmostOrthogonal modes G A` with an `A` uniform in the
truncation is an *input*, not a theorem: nothing here proves that the physical
outer cells are almost orthogonal.  The two consistency results
`almostOrthogonal_one` and `card_le_of_almostOrthogonal_coherent` show the scale
of what is being asked: the trivial kernel always works with `A = card modes`
(which is exactly the old, cardinality-laden bound), and a *perfectly coherent*
cell family forces `A ≥ card modes`.  So the improvement is precisely and only a
phase-cancellation statement about the outer fibre.  Package A and the literal
Clay periodic target are not closed and nothing is claimed for them.
-/
import RequestProject.NavierStokes.SignedGramWienerAssembly

noncomputable section

open MeasureTheory Set

namespace ClayNS.Schur

open ClayNS.Waleffe ClayNS.Resolvent ClayNS.TTStar

/-! ## 1.  The exact Cauchy–Schwarz defect -/

/-- The collinearity defect `‖y‖ x − ‖x‖ y` of two cells. -/
def csDefect (x y : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i => ((nrm y : ℝ) : ℂ) * x i - ((nrm x : ℝ) : ℂ) * y i

/-- The squared defect is exactly twice the Cauchy–Schwarz gap. -/
theorem nsq_csDefect_eq (x y : Fin 3 → ℂ) :
    nsq (csDefect x y) = 2 * (nrm x * nrm y) * (nrm x * nrm y - (herm x y).re) := by
  have hcomp : ∀ i : Fin 3, Complex.normSq (csDefect x y i)
      = nrm y ^ 2 * Complex.normSq (x i) + nrm x ^ 2 * Complex.normSq (y i)
        - 2 * (nrm x * nrm y) * (((starRingEnd ℂ) (x i)) * y i).re := by
    intro i
    have hx : nsq x = nrm x ^ 2 := (nrm_sq x).symm
    have hy : nsq y = nrm y ^ 2 := (nrm_sq y).symm
    simp [csDefect, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im]
    rw [hx, hy]
    ring
  have hre : (herm x y).re = ∑ i, (((starRingEnd ℂ) (x i)) * y i).re := by
    simp [herm, Complex.re_sum]
  have hexp : nsq (csDefect x y)
      = nrm y ^ 2 * nsq x + nrm x ^ 2 * nsq y - 2 * (nrm x * nrm y) * (herm x y).re := by
    rw [nsq, hre]
    rw [Finset.sum_congr rfl (fun i _ => hcomp i)]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
    rfl
  rw [hexp, nrm_sq, nrm_sq]
  have hx : nrm x ^ 2 = nsq x := nrm_sq x
  have hy : nrm y ^ 2 = nsq y := nrm_sq y
  nlinarith [hx, hy]

/-- **The loss, exactly.**  Cauchy–Schwarz for the real part of the Hermitian
form is an identity up to the squared collinearity defect of the two cells; in
particular it is an equality precisely when the cells are perfectly coherent. -/
theorem herm_re_eq_sub_defect {x y : Fin 3 → ℂ} (hx : nrm x ≠ 0) (hy : nrm y ≠ 0) :
    (herm x y).re = nrm x * nrm y - nsq (csDefect x y) / (2 * (nrm x * nrm y)) := by
  have hpos : 0 < nrm x * nrm y := by
    have h1 : 0 < nrm x := lt_of_le_of_ne (nrm_nonneg x) (Ne.symm hx)
    have h2 : 0 < nrm y := lt_of_le_of_ne (nrm_nonneg y) (Ne.symm hy)
    exact mul_pos h1 h2
  have h := nsq_csDefect_eq x y
  field_simp
  nlinarith [h]

/-! ## 2.  The Schur test -/

/-- **Schur test.**  A double sum whose entries are dominated by a symmetric
nonnegative kernel times a rank-one profile is bounded by the row-sum ceiling of
the kernel times the *ℓ²* mass of the profile — not the square of its ℓ¹ mass. -/
theorem sum_sum_le_schur {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ι → ℝ)
    (a : ι → ℝ) (g : ι → ι → ℝ) (K A : ℝ) (hK : 0 ≤ K)
    (hgnn : ∀ i j, 0 ≤ g i j) (hgsym : ∀ i j, g i j = g j i)
    (hc : ∀ i ∈ s, ∀ j ∈ s, c i j ≤ K * (g i j * (a i * a j)))
    (hrow : ∀ i ∈ s, ∑ j ∈ s, g i j ≤ A) :
    ∑ i ∈ s, ∑ j ∈ s, c i j ≤ K * (A * ∑ i ∈ s, a i ^ 2) := by
  have hstep : ∀ i ∈ s, ∀ j ∈ s, c i j ≤ K * (g i j * ((a i ^ 2 + a j ^ 2) / 2)) := by
    intro i hi j hj
    refine le_trans (hc i hi j hj) ?_
    have hamgm : a i * a j ≤ (a i ^ 2 + a j ^ 2) / 2 := by nlinarith [sq_nonneg (a i - a j)]
    have := mul_le_mul_of_nonneg_left hamgm (hgnn i j)
    exact mul_le_mul_of_nonneg_left this hK
  have h1 : ∑ i ∈ s, ∑ j ∈ s, c i j
      ≤ ∑ i ∈ s, ∑ j ∈ s, K * (g i j * ((a i ^ 2 + a j ^ 2) / 2)) :=
    Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hstep i hi j hj
  have hK2 : (0 : ℝ) ≤ K / 2 := by linarith
  have hrowi : ∀ i ∈ s, ∑ j ∈ s, c i j
      ≤ (K / 2 * a i ^ 2) * A + ∑ j ∈ s, (K / 2 * a j ^ 2) * g i j := by
    intro i hi
    have hbd : ∑ j ∈ s, c i j
        ≤ ∑ j ∈ s, ((K / 2 * a i ^ 2) * g i j + (K / 2 * a j ^ 2) * g i j) := by
      refine Finset.sum_le_sum fun j hj => ?_
      calc c i j ≤ K * (g i j * ((a i ^ 2 + a j ^ 2) / 2)) := hstep i hi j hj
        _ = (K / 2 * a i ^ 2) * g i j + (K / 2 * a j ^ 2) * g i j := by ring
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hbd
    have hcoef : 0 ≤ K / 2 * a i ^ 2 := mul_nonneg hK2 (sq_nonneg _)
    have hle : (K / 2 * a i ^ 2) * ∑ j ∈ s, g i j ≤ (K / 2 * a i ^ 2) * A :=
      mul_le_mul_of_nonneg_left (hrow i hi) hcoef
    linarith [hbd, hle]
  have hsum1 : ∑ i ∈ s, ∑ j ∈ s, c i j
      ≤ ∑ i ∈ s, ((K / 2 * a i ^ 2) * A + ∑ j ∈ s, (K / 2 * a j ^ 2) * g i j) :=
    Finset.sum_le_sum hrowi
  have hsplit : ∑ i ∈ s, ((K / 2 * a i ^ 2) * A + ∑ j ∈ s, (K / 2 * a j ^ 2) * g i j)
      = (∑ i ∈ s, (K / 2 * a i ^ 2) * A)
        + ∑ i ∈ s, ∑ j ∈ s, (K / 2 * a j ^ 2) * g i j := Finset.sum_add_distrib
  have hA1 : ∑ i ∈ s, (K / 2 * a i ^ 2) * A = K / 2 * A * ∑ i ∈ s, a i ^ 2 := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
  have hcol : ∑ i ∈ s, ∑ j ∈ s, (K / 2 * a j ^ 2) * g i j
      ≤ K / 2 * A * ∑ i ∈ s, a i ^ 2 := by
    rw [Finset.sum_comm]
    have hstep2 : ∀ j ∈ s, ∑ i ∈ s, (K / 2 * a j ^ 2) * g i j ≤ (K / 2 * a j ^ 2) * A := by
      intro j hj
      rw [← Finset.mul_sum]
      have hswap : ∑ i ∈ s, g i j = ∑ i ∈ s, g j i :=
        Finset.sum_congr rfl fun i _ => hgsym i j
      have hrowj : ∑ i ∈ s, g i j ≤ A := by rw [hswap]; exact hrow j hj
      exact mul_le_mul_of_nonneg_left hrowj (mul_nonneg hK2 (sq_nonneg _))
    calc ∑ j ∈ s, ∑ i ∈ s, (K / 2 * a j ^ 2) * g i j
        ≤ ∑ j ∈ s, (K / 2 * a j ^ 2) * A := Finset.sum_le_sum hstep2
      _ = K / 2 * A * ∑ i ∈ s, a i ^ 2 := by rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
  linarith [hsum1, hsplit.le, hsplit.ge, hA1.le, hA1.ge, hcol]

/-! ## 3.  Almost orthogonality of a cell family -/

/-- **Almost orthogonality with Schur constant `A`.**  The pairwise coherence of
the cells `G_p`, `p ∈ modes`, is dominated by a symmetric nonnegative kernel
whose row sums are at most `A`.  This is the exact hypothesis that replaces the
naked Cauchy–Schwarz step; `A = card modes` is always available (`almostOrthogonal_one`),
and any `A` smaller than that is a genuine phase-cancellation statement. -/
def AlmostOrthogonal (modes : Finset Wave) (G : Wave → Fin 3 → ℂ) (A : ℝ) : Prop :=
  ∃ g : Wave → Wave → ℝ,
    (∀ p p', 0 ≤ g p p') ∧ (∀ p p', g p p' = g p' p) ∧
    (∀ p ∈ modes, ∀ p' ∈ modes,
      |(herm (G p) (G p')).re| ≤ g p p' * (nrm (G p) * nrm (G p'))) ∧
    (∀ p ∈ modes, ∑ p' ∈ modes, g p p' ≤ A)

/-- The trivial kernel: every family is almost orthogonal with Schur constant
`card modes`.  This is exactly the naked Cauchy–Schwarz route, and the
cardinality is exactly what the earlier bound paid for. -/
theorem almostOrthogonal_one (modes : Finset Wave) (G : Wave → Fin 3 → ℂ) :
    AlmostOrthogonal modes G (modes.card : ℝ) := by
  refine ⟨fun _ _ => 1, fun _ _ => zero_le_one, fun _ _ => rfl, ?_, ?_⟩
  · intro p _ p' _
    have h1 : |(herm (G p) (G p')).re| ≤ nrm (G p) * nrm (G p') :=
      le_trans (Complex.abs_re_le_norm _) (norm_herm_le _ _)
    simpa using h1
  · intro p _
    simp

/-- **The coherent case forces the trivial Schur constant.**  If all cells are
one and the same nonzero vector — perfect coherence, the equality case of
Cauchy–Schwarz — then every admissible Schur constant is at least the cardinality
of the fibre.  So the improvement below is a statement about phase cancellation
and nothing else. -/
theorem card_le_of_almostOrthogonal_coherent {modes : Finset Wave} {v : Fin 3 → ℂ} {A : ℝ}
    (hv : nsq v ≠ 0) (hmodes : modes.Nonempty)
    (h : AlmostOrthogonal modes (fun _ => v) A) :
    (modes.card : ℝ) ≤ A := by
  obtain ⟨g, hgnn, _, hAO, hrow⟩ := h
  have hvpos : 0 < nsq v := lt_of_le_of_ne (nsq_nonneg v) (Ne.symm hv)
  have hnrm : nrm v * nrm v = nsq v := by
    have := nrm_sq v; nlinarith [this]
  have hge : ∀ p ∈ modes, ∀ p' ∈ modes, 1 ≤ g p p' := by
    intro p hp p' hp'
    have h1 := hAO p hp p' hp'
    have h2 : (herm v v).re = nsq v := (nsq_eq_herm_re v).symm
    rw [h2] at h1
    rw [hnrm] at h1
    have h3 : nsq v ≤ g p p' * nsq v := le_trans (le_abs_self _) h1
    nlinarith [h3, hvpos]
  obtain ⟨p, hp⟩ := hmodes
  have hrowge : (modes.card : ℝ) ≤ ∑ p' ∈ modes, g p p' := by
    have : ∑ p' ∈ modes, (1 : ℝ) ≤ ∑ p' ∈ modes, g p p' :=
      Finset.sum_le_sum fun p' hp' => hge p hp p' hp'
    simpa using this
  exact le_trans hrowge (hrow p hp)

/-! ## 4.  The signed resolvent Gram form under almost orthogonality -/

/-- **The Schur replacement of the last lossy step.**  Under almost
orthogonality with constant `A`, the whole signed resolvent Gram form —
diagonal and off-diagonal — is bounded by `A` times the *ℓ²* mass of the
frequency-normalized cells.  With `A = card modes` this is the old bound; with
`A` bounded it is a genuine gain of one ℓ¹→ℓ² step. -/
theorem resForm_le_schur {nu A : ℝ} (hnu : 0 < nu) (modes : Finset Wave)
    (G : Wave → Fin 3 → ℂ) (k : Wave) (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hAO : AlmostOrthogonal modes G A) :
    ∑ p ∈ modes, ∑ p' ∈ modes,
        (herm (G p) (G p')).re
          / (viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p'))
      ≤ A * (∑ p ∈ modes, nsq (G p) / wsq p) / (2 * nu) := by
  classical
  obtain ⟨g, hgnn, hgsym, hAOb, hrow⟩ := hAO
  set a : Wave → ℝ := fun p => nrm (G p) / wlen p with ha
  have hterm : ∀ p ∈ modes, ∀ p' ∈ modes,
      (herm (G p) (G p')).re
          / (viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p'))
        ≤ (1 / (2 * nu)) * (g p p' * (a p * a p')) := by
    intro p hpm p' hp'm
    have hlp : 0 < wlen p := wlen_pos_of_wsq_ne_zero (hp p hpm)
    have hlp' : 0 < wlen p' := wlen_pos_of_wsq_ne_zero (hp p' hp'm)
    have hden0 : 0 < 2 * nu * (wlen p * wlen p') := by positivity
    have hden : 2 * nu * (wlen p * wlen p')
        ≤ viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p') :=
      two_nu_wlen_mul_le_pairRate hnu.le k p p'
    have hpos : 0 < viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p') :=
      lt_of_lt_of_le hden0 hden
    have habs : |(herm (G p) (G p')).re| ≤ g p p' * (nrm (G p) * nrm (G p')) :=
      hAOb p hpm p' hp'm
    have hnum : (herm (G p) (G p')).re ≤ g p p' * (nrm (G p) * nrm (G p')) :=
      le_trans (le_abs_self _) habs
    have hnumnn : 0 ≤ g p p' * (nrm (G p) * nrm (G p')) :=
      mul_nonneg (hgnn p p') (mul_nonneg (nrm_nonneg _) (nrm_nonneg _))
    have hstep1 : (herm (G p) (G p')).re
          / (viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p'))
        ≤ (g p p' * (nrm (G p) * nrm (G p')))
          / (viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p')) :=
      (div_le_div_iff_of_pos_right hpos).mpr hnum
    have hstep2 : (g p p' * (nrm (G p) * nrm (G p')))
          / (viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p'))
        ≤ (g p p' * (nrm (G p) * nrm (G p'))) / (2 * nu * (wlen p * wlen p')) :=
      div_le_div_of_nonneg_left hnumnn hden0 hden
    have heq : (g p p' * (nrm (G p) * nrm (G p'))) / (2 * nu * (wlen p * wlen p'))
        = (1 / (2 * nu)) * (g p p' * (a p * a p')) := by
      rw [ha]; field_simp
    linarith [hstep1, hstep2, heq.le, heq.ge]
  have hschur := sum_sum_le_schur (s := modes)
    (c := fun p p' => (herm (G p) (G p')).re
      / (viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p')))
    (a := a) (g := g) (K := 1 / (2 * nu)) (A := A)
    (by positivity) hgnn hgsym hterm hrow
  have hsq : ∀ p ∈ modes, a p ^ 2 = nsq (G p) / wsq p := by
    intro p hpm
    have hlp : 0 < wlen p := wlen_pos_of_wsq_ne_zero (hp p hpm)
    rw [ha]
    rw [div_pow, nrm_sq, wlen_sq]
  have hsum : ∑ p ∈ modes, a p ^ 2 = ∑ p ∈ modes, nsq (G p) / wsq p :=
    Finset.sum_congr rfl hsq
  rw [hsum] at hschur
  have hfin : 1 / (2 * nu) * (A * ∑ p ∈ modes, nsq (G p) / wsq p)
      = A * (∑ p ∈ modes, nsq (G p) / wsq p) / (2 * nu) := by
    field_simp
  linarith [hschur, hfin.le, hfin.ge]

/-! ## 5.  The physical carrier: one output, then all outputs -/

/-- The frequency-normalized outer cell mass, squared: the `|p|²` of the
relocated inner kernel is cancelled, and what survives is the ℓ² profile. -/
theorem cell_ratio_sq_le {N u : Wave → Fin 3 → ℂ} {k p : Wave} (B : Wave → ℝ)
    (hk : wsq k ≠ 0) (hp : wsq p ≠ 0)
    (hN : nrm (N p) ≤ 3 * wlen p * B p) :
    nsq (outerCellVec N u k p) / wsq p ≤ 9 * (B p ^ 2 * nsq (u (k - p))) := by
  have hlp : 0 < wlen p := wlen_pos_of_wsq_ne_zero hp
  have hratio : nrm (outerCellVec N u k p) / wlen p ≤ 3 * (B p * nrm (u (k - p))) :=
    cell_ratio_le B hk hp hN
  have hnn : 0 ≤ nrm (outerCellVec N u k p) / wlen p :=
    div_nonneg (nrm_nonneg _) hlp.le
  have hsq : (nrm (outerCellVec N u k p) / wlen p) ^ 2
      ≤ (3 * (B p * nrm (u (k - p)))) ^ 2 := by nlinarith [hratio, hnn]
  have hl : (nrm (outerCellVec N u k p) / wlen p) ^ 2
      = nsq (outerCellVec N u k p) / wsq p := by
    rw [div_pow, nrm_sq, wlen_sq]
  have hr : (3 * (B p * nrm (u (k - p)))) ^ 2 = 9 * (B p ^ 2 * nsq (u (k - p))) := by
    have : nrm (u (k - p)) ^ 2 = nsq (u (k - p)) := nrm_sq _
    nlinarith [this]
  linarith [hsq, hl.le, hl.ge, hr.le, hr.ge]

/-- **The remainder budget at one output, under almost orthogonality.**  The
whole `s`-integral of the squared signed remainder is bounded by `A` times an
ℓ² convolution profile — no square of an ℓ¹ sum. -/
theorem integral_nsq_Fs_le_schur {nu A : ℝ} (hnu : 0 < nu) (modes : Finset Wave)
    (N u : Wave → Fin 3 → ℂ) (k : Wave) (B : Wave → ℝ)
    (hk : wsq k ≠ 0) (hp : ∀ p ∈ modes, wsq p ≠ 0) (hA : 0 ≤ A)
    (hN : ∀ p ∈ modes, nrm (N p) ≤ 3 * wlen p * B p)
    (hAO : AlmostOrthogonal modes (fun p => outerCellVec N u k p) A) :
    (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes N u k))
      ≤ 9 * A * (∑ p ∈ modes, B p ^ 2 * nsq (u (k - p))) / (2 * nu) := by
  have hrate : ∀ p ∈ modes, 0 < viscousPairRate nu p (k - p) := by
    intro p hpm
    rw [viscousPairRate]
    have h1 : 0 < wsq p := lt_of_le_of_ne (wsq_nonneg' p) (Ne.symm (hp p hpm))
    have h2 : 0 ≤ wsq (k - p) := wsq_nonneg' (k - p)
    exact mul_pos hnu (by linarith)
  rw [integral_nsq_Fs_eq_resForm modes N u k hrate]
  have hgram := resForm_le_schur hnu modes (fun p => outerCellVec N u k p) k hp hAO
  have hprofile : ∑ p ∈ modes, nsq (outerCellVec N u k p) / wsq p
      ≤ ∑ p ∈ modes, 9 * (B p ^ 2 * nsq (u (k - p))) :=
    Finset.sum_le_sum fun p hpm => cell_ratio_sq_le B hk (hp p hpm) (hN p hpm)
  have hfac : ∑ p ∈ modes, 9 * (B p ^ 2 * nsq (u (k - p)))
      = 9 * ∑ p ∈ modes, B p ^ 2 * nsq (u (k - p)) := by rw [Finset.mul_sum]
  have h2nu : 0 < 2 * nu := by linarith
  have hstep : A * (∑ p ∈ modes, nsq (outerCellVec N u k p) / wsq p) / (2 * nu)
      ≤ 9 * A * (∑ p ∈ modes, B p ^ 2 * nsq (u (k - p))) / (2 * nu) := by
    refine (div_le_div_iff_of_pos_right h2nu).mpr ?_
    have := mul_le_mul_of_nonneg_left hprofile hA
    rw [hfac] at this
    linarith [this]
  linarith [hgram, hstep]

/-- **The summed remainder budget under almost orthogonality.**  Summing over the
outputs costs a shift of the energy sum only: no output cardinality, no shell
multiplicity, no cutoff dependence. -/
theorem sum_integral_nsq_Fs_le_schur {nu A : ℝ} (hnu : 0 < nu)
    (modes outs : Finset Wave) (N u : Wave → Fin 3 → ℂ) (B : Wave → ℝ)
    (hk : ∀ k ∈ outs, wsq k ≠ 0) (hp : ∀ p ∈ modes, wsq p ≠ 0) (hA : 0 ≤ A)
    (hN : ∀ p ∈ modes, nrm (N p) ≤ 3 * wlen p * B p)
    (hsupp : ∀ b ∉ modes, u b = fun _ => 0)
    (hAO : ∀ k ∈ outs, AlmostOrthogonal modes (fun p => outerCellVec N u k p) A) :
    ∑ k ∈ outs, (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes N u k))
      ≤ 9 * A * ((∑ p ∈ modes, B p ^ 2) * energy modes u) / (2 * nu) := by
  classical
  have h2nu : 0 < 2 * nu := by linarith
  have hpt : ∑ k ∈ outs, (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes N u k))
      ≤ ∑ k ∈ outs, 9 * A * (∑ p ∈ modes, B p ^ 2 * nsq (u (k - p))) / (2 * nu) :=
    Finset.sum_le_sum fun k hkm =>
      integral_nsq_Fs_le_schur hnu modes N u k B (hk k hkm) hp hA hN (hAO k hkm)
  have hswap : ∑ k ∈ outs, (∑ p ∈ modes, B p ^ 2 * nsq (u (k - p)))
      = ∑ p ∈ modes, B p ^ 2 * ∑ k ∈ outs, nsq (u (k - p)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => by rw [Finset.mul_sum]
  have hshift : ∀ p : Wave, ∑ k ∈ outs, nsq (u (k - p)) ≤ energy modes u := by
    intro p
    have := sum_shift_le modes outs (fun q => nsq (u q)) (fun q => nsq_nonneg _)
      (by intro q hq; simp [hsupp q hq, nsq]) p
    simpa [energy] using this
  have htail : ∑ p ∈ modes, B p ^ 2 * ∑ k ∈ outs, nsq (u (k - p))
      ≤ (∑ p ∈ modes, B p ^ 2) * energy modes u := by
    have : ∑ p ∈ modes, B p ^ 2 * ∑ k ∈ outs, nsq (u (k - p))
        ≤ ∑ p ∈ modes, B p ^ 2 * energy modes u :=
      Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hshift p) (sq_nonneg _)
    calc ∑ p ∈ modes, B p ^ 2 * ∑ k ∈ outs, nsq (u (k - p))
        ≤ ∑ p ∈ modes, B p ^ 2 * energy modes u := this
      _ = (∑ p ∈ modes, B p ^ 2) * energy modes u := by rw [← Finset.sum_mul]
  have hcollect : ∑ k ∈ outs, 9 * A * (∑ p ∈ modes, B p ^ 2 * nsq (u (k - p))) / (2 * nu)
      = 9 * A * (∑ k ∈ outs, (∑ p ∈ modes, B p ^ 2 * nsq (u (k - p)))) / (2 * nu) := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
  have hfin : 9 * A * (∑ k ∈ outs, (∑ p ∈ modes, B p ^ 2 * nsq (u (k - p)))) / (2 * nu)
      ≤ 9 * A * ((∑ p ∈ modes, B p ^ 2) * energy modes u) / (2 * nu) := by
    refine (div_le_div_iff_of_pos_right h2nu).mpr ?_
    rw [hswap]
    have h9A : 0 ≤ 9 * A := by linarith
    exact mul_le_mul_of_nonneg_left htail h9A
  linarith [hpt, hcollect.le, hcollect.ge, hfin]

/-! ## 6.  The literal physical inner forcing: `‖u‖_A² E²` in place of `‖u‖_A⁴ E` -/

/-- The ℓ² mass of the leg-norm convolution profile: discrete Young in ℓ²,
`‖f∗f‖_{ℓ²}² ≤ ‖f‖_{ℓ¹}²‖f‖_{ℓ²}²`. -/
theorem sum_sq_conv_le_wiener_energy (modes : Finset Wave) (u : Wave → Fin 3 → ℂ)
    (hsupp : ∀ b ∉ modes, u b = fun _ => 0) :
    ∑ p ∈ modes, (∑ a ∈ modes, nrm (u a) * nrm (u (p - a))) ^ 2
      ≤ wienerA modes u ^ 2 * energy modes u := by
  classical
  have hyoung := sum_sq_conv_le modes modes (fun q => nrm (u q)) (fun q => nrm (u q))
    (fun q => nrm_nonneg _) (by intro q hq; simp [hsupp q hq, nrm, nsq])
  have hgsum : ∑ q ∈ modes, nrm (u q) ^ 2 = energy modes u := by
    simp [energy, nrm_sq]
  have hf : (∑ q ∈ modes, nrm (u q)) = wienerA modes u := rfl
  rw [hgsum, hf] at hyoung
  exact hyoung

/-- **The physical consequence.**  For the literal carrier — inner forcing
`N_p = ∑_{a+b=p}` of relocated pure commutators, outer Leray-projected
commutator with the remaining leg, heat weights at the literal viscous pair rate
— almost orthogonality of the outer cells with a truncation-uniform Schur
constant `A` gives

  `∑_k ∫_0^∞ ‖F_s(k)‖² ds ≤ 9 A ‖u‖_A² E² / (2ν)`,

two powers of the Wiener norm less than the unconditional bound
`9 ‖u‖_A⁴ E/(2ν)` of `sum_integral_nsq_Fs_le_wiener`. -/
theorem sum_integral_nsq_Fs_le_schur_wiener {nu A : ℝ} (hnu : 0 < nu)
    (modes outs : Finset Wave) (u : Wave → Fin 3 → ℂ)
    (hk : ∀ k ∈ outs, wsq k ≠ 0) (hp : ∀ p ∈ modes, wsq p ≠ 0) (hA : 0 ≤ A)
    (hdiv : ∀ c : Wave, dotb (wC c) (u c) = 0)
    (hsupp : ∀ b ∉ modes, u b = fun _ => 0)
    (hAO : ∀ k ∈ outs,
      AlmostOrthogonal modes (fun p => outerCellVec (innerForcing modes u) u k p) A) :
    ∑ k ∈ outs, (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes (innerForcing modes u) u k))
      ≤ 9 * A * (wienerA modes u ^ 2 * energy modes u ^ 2) / (2 * nu) := by
  classical
  set B : Wave → ℝ := fun p => ∑ a ∈ modes, nrm (u a) * nrm (u (p - a)) with hBdef
  have hN : ∀ p ∈ modes, nrm (innerForcing modes u p) ≤ 3 * wlen p * B p := by
    intro p hpm
    exact nrm_innerForcing_le_conv modes (hp p hpm) hdiv
  have hmain := sum_integral_nsq_Fs_le_schur hnu modes outs (innerForcing modes u) u B
    hk hp hA hN hsupp hAO
  have hB2 : ∑ p ∈ modes, B p ^ 2 ≤ wienerA modes u ^ 2 * energy modes u :=
    sum_sq_conv_le_wiener_energy modes u hsupp
  have hE : 0 ≤ energy modes u := energy_nonneg modes u
  have h2nu : 0 < 2 * nu := by linarith
  have hstep : 9 * A * ((∑ p ∈ modes, B p ^ 2) * energy modes u) / (2 * nu)
      ≤ 9 * A * (wienerA modes u ^ 2 * energy modes u ^ 2) / (2 * nu) := by
    refine (div_le_div_iff_of_pos_right h2nu).mpr ?_
    have h1 : (∑ p ∈ modes, B p ^ 2) * energy modes u
        ≤ (wienerA modes u ^ 2 * energy modes u) * energy modes u :=
      mul_le_mul_of_nonneg_right hB2 hE
    have h2 : (wienerA modes u ^ 2 * energy modes u) * energy modes u
        = wienerA modes u ^ 2 * energy modes u ^ 2 := by ring
    nlinarith [h1, h2.le, h2.ge, hA]
  linarith [hmain, hstep]

/-! ## 7.  The spacetime form: a *critical* demand -/

/-- **The spacetime remainder under almost orthogonality is critical.**  On a
time interval on which the energy is bounded by `E₀`, the spacetime remainder
energy of the signed heat-weighted family is bounded by a constant times the
*critical* Wiener quantity `∫ ‖u(t)‖_A² dt` — not by the supercritical
`∫ ‖u(t)‖_A⁴E(t) dt` that the unconditional route demands.  This is exactly the
gain that a truncation-uniform Schur constant would buy. -/
theorem spacetime_remainder_le_critical {nu A E₀ : ℝ} (hnu : 0 < nu)
    (modes outs : Finset Wave) (u : ℝ → Wave → Fin 3 → ℂ) (t₀ t₁ : ℝ)
    (ht : t₀ ≤ t₁) (hA : 0 ≤ A) (hE₀ : 0 ≤ E₀)
    (hk : ∀ k ∈ outs, wsq k ≠ 0) (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hdiv : ∀ t : ℝ, ∀ c : Wave, dotb (wC c) (u t c) = 0)
    (hsupp : ∀ t : ℝ, ∀ b ∉ modes, u t b = fun _ => 0)
    (hAO : ∀ t ∈ Set.Icc t₀ t₁, ∀ k ∈ outs,
      AlmostOrthogonal modes
        (fun p => outerCellVec (innerForcing modes (u t)) (u t) k p) A)
    (hEbd : ∀ t ∈ Set.Icc t₀ t₁, energy modes (u t) ≤ E₀)
    (hint : IntervalIntegrable
      (fun t => ∑ k ∈ outs,
        (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes (innerForcing modes (u t)) (u t) k)))
      volume t₀ t₁)
    (hintW : IntervalIntegrable (fun t => wienerA modes (u t) ^ 2) volume t₀ t₁) :
    (∫ t in t₀..t₁, ∑ k ∈ outs,
        (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes (innerForcing modes (u t)) (u t) k)))
      ≤ 9 * A * E₀ ^ 2 / (2 * nu) * ∫ t in t₀..t₁, wienerA modes (u t) ^ 2 := by
  have h2nu : 0 < 2 * nu := by linarith
  have hbound : ∀ t ∈ Set.Icc t₀ t₁,
      (∑ k ∈ outs,
        (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes (innerForcing modes (u t)) (u t) k)))
        ≤ 9 * A * E₀ ^ 2 / (2 * nu) * wienerA modes (u t) ^ 2 := by
    intro t htm
    have h1 := sum_integral_nsq_Fs_le_schur_wiener hnu modes outs (u t) hk hp hA
      (hdiv t) (hsupp t) (hAO t htm)
    have hEnn : 0 ≤ energy modes (u t) := energy_nonneg modes (u t)
    have hWnn : 0 ≤ wienerA modes (u t) ^ 2 := sq_nonneg _
    have h2 : 9 * A * (wienerA modes (u t) ^ 2 * energy modes (u t) ^ 2) / (2 * nu)
        ≤ 9 * A * E₀ ^ 2 / (2 * nu) * wienerA modes (u t) ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right h2nu]
      have hsqE : energy modes (u t) ^ 2 ≤ E₀ ^ 2 := by
        nlinarith [hEbd t htm, hEnn, hE₀]
      have hprod : 0 ≤ (9 * A) * (wienerA modes (u t) ^ 2 * (E₀ ^ 2 - energy modes (u t) ^ 2)) :=
        mul_nonneg (by linarith) (mul_nonneg hWnn (by linarith))
      nlinarith [hprod]
    linarith [h1, h2]
  have hmono := intervalIntegral.integral_mono_on ht hint
    (hintW.const_mul (9 * A * E₀ ^ 2 / (2 * nu))) hbound
  rwa [intervalIntegral.integral_const_mul] at hmono

/-! ## 8.  The exactly orthogonal case: Schur constant one -/

/-- A cell family whose distinct members have orthogonal real parts is almost
orthogonal with Schur constant `1`. -/
theorem almostOrthogonal_of_orthogonal (modes : Finset Wave) (G : Wave → Fin 3 → ℂ)
    (horth : ∀ p ∈ modes, ∀ p' ∈ modes, p ≠ p' → (herm (G p) (G p')).re = 0) :
    AlmostOrthogonal modes G 1 := by
  classical
  refine ⟨fun p p' => if p = p' then 1 else 0, ?_, ?_, ?_, ?_⟩
  · intro p p'
    by_cases h : p = p' <;> simp [h]
  · intro p p'
    by_cases h : p = p'
    · simp [h]
    · simp [h, Ne.symm h]
  · intro p hp p' hp'
    by_cases h : p = p'
    · subst h
      have hns : (herm (G p) (G p)).re = nsq (G p) := (nsq_eq_herm_re (G p)).symm
      have hnn : (0 : ℝ) ≤ nsq (G p) := nsq_nonneg _
      have hsq : nrm (G p) * nrm (G p) = nsq (G p) := by
        have := nrm_sq (G p); nlinarith [this]
      rw [hns, abs_of_nonneg hnn]
      simp [hsq]
    · rw [horth p hp p' hp' h]
      simp [h]
  · intro p hp
    simp [Finset.sum_ite_eq, hp]

/-- **The target constant.**  If the outer cells at each retained output are
exactly orthogonal, the spacetime remainder budget is
`9 ‖u‖_A²E²/(2ν)` — two powers of the Wiener norm below the unconditional
bound, hence a critical rather than supercritical demand. -/
theorem sum_integral_nsq_Fs_le_orthogonal_wiener {nu : ℝ} (hnu : 0 < nu)
    (modes outs : Finset Wave) (u : Wave → Fin 3 → ℂ)
    (hk : ∀ k ∈ outs, wsq k ≠ 0) (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hdiv : ∀ c : Wave, dotb (wC c) (u c) = 0)
    (hsupp : ∀ b ∉ modes, u b = fun _ => 0)
    (horth : ∀ k ∈ outs, ∀ p ∈ modes, ∀ p' ∈ modes, p ≠ p' →
      (herm (outerCellVec (innerForcing modes u) u k p)
        (outerCellVec (innerForcing modes u) u k p')).re = 0) :
    ∑ k ∈ outs, (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes (innerForcing modes u) u k))
      ≤ 9 * (wienerA modes u ^ 2 * energy modes u ^ 2) / (2 * nu) := by
  have h := sum_integral_nsq_Fs_le_schur_wiener (A := 1) hnu modes outs u hk hp zero_le_one
    hdiv hsupp (fun k hkm =>
      almostOrthogonal_of_orthogonal modes _ (fun p hpm p' hp'm hne =>
        horth k hkm p hpm p' hp'm hne))
  simpa using h

/-! ## 9.  Sharpness: a coherent family attains the ℓ¹ square exactly -/

/-- The Hermitian form of two real multiples of vectors. -/
theorem herm_real_pair (a b : ℝ) (v w : Fin 3 → ℂ) :
    herm (fun i => (a : ℂ) * v i) (fun i => (b : ℂ) * w i)
      = ((a * b : ℝ) : ℂ) * herm v w := by
  simp only [herm, map_mul, Complex.conj_ofReal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by push_cast; ring

/-- **The Cauchy–Schwarz route is sharp on a coherent family.**  If all cells are
nonnegative real multiples of one and the same vector, and the pair rates are
constant, the signed resolvent Gram form is *exactly* the square of the ℓ¹ mass
of the cells.  So no rearrangement of the estimate can improve the unconditional
bound: any gain must come from genuine phase cancellation between the cells,
which is precisely what `AlmostOrthogonal` with a small `A` asserts. -/
theorem resForm_coherent_eq (lam : ℝ) (modes : Finset Wave)
    (c : Wave → ℝ) (v : Fin 3 → ℂ) :
    ∑ p ∈ modes, ∑ p' ∈ modes,
        (herm (fun i => ((c p : ℝ) : ℂ) * v i) (fun i => ((c p' : ℝ) : ℂ) * v i)).re
          / (lam + lam)
      = (∑ p ∈ modes, c p) ^ 2 * nsq v / (2 * lam) := by
  have hentry : ∀ p p' : Wave,
      (herm (fun i => ((c p : ℝ) : ℂ) * v i) (fun i => ((c p' : ℝ) : ℂ) * v i)).re
          / (lam + lam)
        = c p * c p' * (nsq v / (2 * lam)) := by
    intro p p'
    rw [herm_real_pair]
    have hre : (((c p * c p' : ℝ) : ℂ) * herm v v).re = (c p * c p') * (herm v v).re := by
      simp [Complex.mul_re]
    rw [hre, ← nsq_eq_herm_re]
    have h2 : lam + lam = 2 * lam := by ring
    rw [h2]
    field_simp
  calc ∑ p ∈ modes, ∑ p' ∈ modes,
        (herm (fun i => ((c p : ℝ) : ℂ) * v i) (fun i => ((c p' : ℝ) : ℂ) * v i)).re
          / (lam + lam)
      = ∑ p ∈ modes, ∑ p' ∈ modes, c p * c p' * (nsq v / (2 * lam)) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => hentry p p'
    _ = (∑ p ∈ modes, c p) ^ 2 * nsq v / (2 * lam) := by
        rw [sq, Finset.sum_mul_sum]
        rw [Finset.sum_mul, Finset.sum_div]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_mul, Finset.sum_div]
        exact Finset.sum_congr rfl fun p' _ => by ring

/-! ## 10.  The exact ledger of the unconditional route -/

/-- **What the unconditional route throws away, exactly.**  The signed resolvent
Gram form equals its Cauchy–Schwarz majorant minus the resolvent-weighted total
collinearity defect of the cells.  Every possible improvement over
`resForm_le_sq` is therefore *exactly* a lower bound on that defect sum: this is
the signed bookkeeping of the last lossy step, with no estimate taken. -/
theorem resForm_eq_cs_sub_defect {nu : ℝ} (modes : Finset Wave) (G : Wave → Fin 3 → ℂ)
    (k : Wave) (hG : ∀ p ∈ modes, nrm (G p) ≠ 0) :
    ∑ p ∈ modes, ∑ p' ∈ modes,
        (herm (G p) (G p')).re
          / (viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p'))
      = (∑ p ∈ modes, ∑ p' ∈ modes,
          (nrm (G p) * nrm (G p'))
            / (viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p')))
        - ∑ p ∈ modes, ∑ p' ∈ modes,
            nsq (csDefect (G p) (G p')) / (2 * (nrm (G p) * nrm (G p')))
              / (viscousPairRate nu p (k - p) + viscousPairRate nu p' (k - p')) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hpm => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p' hp'm => ?_
  rw [herm_re_eq_sub_defect (hG p hpm) (hG p' hp'm), sub_div]

/-! ## 10b.  The Schur bound is never worse than the unconditional one -/

/-- The Galerkin energy is dominated by the square of the Wiener norm. -/
theorem energy_le_wienerA_sq (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) :
    energy modes u ≤ wienerA modes u ^ 2 := by
  have h : ∑ a ∈ modes, nrm (u a) ^ 2 ≤ (∑ a ∈ modes, nrm (u a)) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun a _ => nrm_nonneg _)
  have he : ∑ a ∈ modes, nrm (u a) ^ 2 = energy modes u := by simp [energy, nrm_sq]
  have hw : (∑ a ∈ modes, nrm (u a)) = wienerA modes u := rfl
  rw [he, hw] at h
  exact h

/-- **Consistency.**  With Schur constant `1` the conditional budget is never
worse than the unconditional one: `‖u‖_A²E² ≤ ‖u‖_A⁴E`.  The gain is genuine
whenever the field is spread out, i.e. exactly when `E ≪ ‖u‖_A²`. -/
theorem schur_budget_le_wiener_budget (modes : Finset Wave) (u : Wave → Fin 3 → ℂ) :
    wienerA modes u ^ 2 * energy modes u ^ 2 ≤ wienerA modes u ^ 4 * energy modes u := by
  have hE : 0 ≤ energy modes u := energy_nonneg modes u
  have hW : 0 ≤ wienerA modes u ^ 2 := sq_nonneg _
  have h := energy_le_wienerA_sq modes u
  have hkey : 0 ≤ wienerA modes u ^ 2 * energy modes u * (wienerA modes u ^ 2 - energy modes u) :=
    mul_nonneg (mul_nonneg hW hE) (by linarith)
  nlinarith [hkey]

/-- **The gain is critical, not free.**  Even the improved budget `‖u‖_A²E²` is
not controlled by the energy at a fixed time: for every `M` there is a
transverse, finitely supported field of unit energy whose Schur budget exceeds
`M`.  So the almost-orthogonality route still needs a genuine critical input
(`∫‖u‖_A²dt`), not the energy inequality alone. -/
theorem schur_budget_not_controlled_by_energy (M : ℝ) :
    ∃ (modes : Finset Wave) (u : Wave → Fin 3 → ℂ),
      (0 : Wave) ∉ modes ∧
      (∀ k, herm (wC k) (u k) = 0) ∧
      (∀ m, m ∉ modes → u m = 0) ∧
      energy modes u = 1 ∧
      M ≤ wienerA modes u ^ 2 * energy modes u ^ 2 := by
  obtain ⟨modes, u, h0, hdiv, hsupp, hE, hW⟩ :=
    wiener_norm_not_controlled_by_energy (max M 1)
  refine ⟨modes, u, h0, hdiv, hsupp, hE, ?_⟩
  have hM1 : (1 : ℝ) ≤ max M 1 := le_max_right _ _
  have hMM : M ≤ max M 1 := le_max_left _ _
  have hE' : energy modes u = 1 := hE
  rw [hE']
  nlinarith [hW, hM1, hMM]

/-! ## 11.  The assembled consumer, with the Schur remainder -/

/-- The total remainder resolvent energy over all outputs, under almost
orthogonality: the same-object receipt of `resForm_outCells_eq_integral`
composed with the Schur budget. -/
theorem sum_resForm_outCells_le_schur {nu A : ℝ} (hnu : 0 < nu)
    (modes outs : Finset Wave) (u : Wave → Fin 3 → ℂ)
    (hk : ∀ k ∈ outs, wsq k ≠ 0) (hp : ∀ p ∈ modes, wsq p ≠ 0) (hA : 0 ≤ A)
    (hdiv : ∀ c : Wave, dotb (wC c) (u c) = 0)
    (hsupp : ∀ b ∉ modes, u b = fun _ => 0)
    (hAO : ∀ k ∈ outs,
      AlmostOrthogonal modes (fun p => outerCellVec (innerForcing modes u) u k p) A) :
    ∑ k ∈ outs, nsPSD.resForm (outRate nu modes k)
        (outCells (innerForcing modes u) u modes k)
        (outCells (innerForcing modes u) u modes k)
      ≤ 9 * A * (wienerA modes u ^ 2 * energy modes u ^ 2) / (2 * nu) := by
  have hrw : ∀ k ∈ outs, nsPSD.resForm (outRate nu modes k)
        (outCells (innerForcing modes u) u modes k)
        (outCells (innerForcing modes u) u modes k)
      = ∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes (innerForcing modes u) u k) :=
    fun k _ => resForm_outCells_eq_integral hnu modes (innerForcing modes u) u k hp
  rw [Finset.sum_congr rfl hrw]
  exact sum_integral_nsq_Fs_le_schur_wiener hnu modes outs u hk hp hA hdiv hsupp hAO

/-- **The assembled signed Gram bound under almost orthogonality.**  Exactly the
consumer statement of `sum_gram_debt_le_wiener`, with the spacetime budget `M`
now controlling `‖u‖_A²E²` rather than `‖u‖_A⁴E`: with the energy bounded along
the flow this is a critical demand.  No other hypothesis of the consumer is
changed. -/
theorem sum_gram_debt_le_schur {nu A : ℝ} (hnu : 0 < nu)
    (modes outs : Finset Wave) (u : ℝ → Wave → Fin 3 → ℂ)
    (Acell : Wave → ℝ → ↥modes → Fin 3 → ℂ) (t₀ t₁ M : ℝ) (ht : t₀ ≤ t₁)
    {ε : ℝ} (hε : 0 < ε) (hA : 0 ≤ A)
    (hk : ∀ k ∈ outs, wsq k ≠ 0) (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hdiv : ∀ t : ℝ, ∀ c : Wave, dotb (wC c) (u t c) = 0)
    (hsupp : ∀ t : ℝ, ∀ b ∉ modes, u t b = fun _ => 0)
    (hAO : ∀ t ∈ Set.Icc t₀ t₁, ∀ k ∈ outs,
      AlmostOrthogonal modes
        (fun p => outerCellVec (innerForcing modes (u t)) (u t) k p) A)
    (hM : ∀ t ∈ Set.Icc t₀ t₁, wienerA modes (u t) ^ 2 * energy modes (u t) ^ 2 ≤ M)
    (hcell : ∀ k ∈ outs, ∀ t ∈ uIcc t₀ t₁, ∀ (i : ↥modes) (c : Fin 3),
      HasDerivAt (fun t => Acell k t i c)
        (-(outRate nu modes k i : ℂ) * Acell k t i c
          + outCells (innerForcing modes (u t)) (u t) modes k i c) t)
    (hrem : ∀ k ∈ outs, ∀ i j, IntervalIntegrable
      (fun t => nsPSD.gramRemainder (Acell k t)
        (outCells (innerForcing modes (u t)) (u t) modes k) i j) volume t₀ t₁)
    (hMint : ∀ k ∈ outs, IntervalIntegrable
      (fun t => nsPSD.resForm (outRate nu modes k) (Acell k t)
        (outCells (innerForcing modes (u t)) (u t) modes k)) volume t₀ t₁)
    (hAint : ∀ k ∈ outs, IntervalIntegrable
      (fun t => nsPSD.resForm (outRate nu modes k) (Acell k t) (Acell k t)) volume t₀ t₁)
    (hFint : ∀ k ∈ outs, IntervalIntegrable
      (fun t => nsPSD.resForm (outRate nu modes k)
        (outCells (innerForcing modes (u t)) (u t) modes k)
        (outCells (innerForcing modes (u t)) (u t) modes k)) volume t₀ t₁) :
    ∑ k ∈ outs, ∫ t in t₀..t₁, nsPSD.gramDebt (Acell k t)
      ≤ (∑ k ∈ outs, 2 * nsPSD.resForm (outRate nu modes k) (Acell k t₀) (Acell k t₀))
        + ε * (∑ k ∈ outs, ∫ t in t₀..t₁,
            nsPSD.resForm (outRate nu modes k) (Acell k t) (Acell k t))
        + (4 / ε) * (9 * A * M * (t₁ - t₀) / (2 * nu)) := by
  classical
  set F : Wave → ℝ → ↥modes → Fin 3 → ℂ :=
    fun k t => outCells (innerForcing modes (u t)) (u t) modes k with hFdef
  have hone : ∀ k ∈ outs, (∫ t in t₀..t₁, nsPSD.gramDebt (Acell k t))
      ≤ 2 * nsPSD.resForm (outRate nu modes k) (Acell k t₀) (Acell k t₀)
        + ε * (∫ t in t₀..t₁, nsPSD.resForm (outRate nu modes k) (Acell k t) (Acell k t))
        + (4 / ε) * ∫ t in t₀..t₁,
            nsPSD.resForm (outRate nu modes k) (F k t) (F k t) := by
    intro k hkm
    exact ns_signed_gram_integral_bound (fun i : ↥modes => ((i : Wave), k - (i : Wave)))
      hnu (fun i => hp (i : Wave) i.2) (Acell k) (F k) t₀ t₁ ht hε
      (outRate nu modes k) (fun i => rfl) (hcell k hkm) (hrem k hkm) (hMint k hkm)
      (hAint k hkm) (hFint k hkm)
  have hsum1 : ∑ k ∈ outs, (∫ t in t₀..t₁, nsPSD.gramDebt (Acell k t))
      ≤ ∑ k ∈ outs, (2 * nsPSD.resForm (outRate nu modes k) (Acell k t₀) (Acell k t₀)
        + ε * (∫ t in t₀..t₁, nsPSD.resForm (outRate nu modes k) (Acell k t) (Acell k t))
        + (4 / ε) * ∫ t in t₀..t₁,
            nsPSD.resForm (outRate nu modes k) (F k t) (F k t)) :=
    Finset.sum_le_sum hone
  have hFsum : ∑ k ∈ outs, (∫ t in t₀..t₁,
      nsPSD.resForm (outRate nu modes k) (F k t) (F k t))
      ≤ 9 * A * M * (t₁ - t₀) / (2 * nu) := by
    have hswap : ∑ k ∈ outs, (∫ t in t₀..t₁,
        nsPSD.resForm (outRate nu modes k) (F k t) (F k t))
        = ∫ t in t₀..t₁, ∑ k ∈ outs,
            nsPSD.resForm (outRate nu modes k) (F k t) (F k t) :=
      (intervalIntegral.integral_finset_sum (fun k hkm => hFint k hkm)).symm
    have hintsum : IntervalIntegrable
        (fun t => ∑ k ∈ outs, nsPSD.resForm (outRate nu modes k) (F k t) (F k t))
        volume t₀ t₁ := by
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
          ≤ 9 * A * M / (2 * nu) := by
      intro t htm
      have h1 := sum_resForm_outCells_le_schur hnu modes outs (u t) hk hp hA (hdiv t)
        (hsupp t) (hAO t htm)
      have h2 : 9 * A * (wienerA modes (u t) ^ 2 * energy modes (u t) ^ 2) / (2 * nu)
          ≤ 9 * A * M / (2 * nu) := by
        refine (div_le_div_iff_of_pos_right h2nu).mpr ?_
        have hmt := hM t htm
        nlinarith [hmt, hA]
      simpa [hFdef] using le_trans h1 h2
    have hmono := intervalIntegral.integral_mono_on ht hintsum
      (intervalIntegrable_const (c := 9 * A * M / (2 * nu))) hptwise
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have heq : (t₁ - t₀) * (9 * A * M / (2 * nu)) = 9 * A * M * (t₁ - t₀) / (2 * nu) := by ring
    rw [hswap]
    linarith [hmono, heq.le, heq.ge]
  have hsplit : ∑ k ∈ outs, (2 * nsPSD.resForm (outRate nu modes k) (Acell k t₀) (Acell k t₀)
        + ε * (∫ t in t₀..t₁, nsPSD.resForm (outRate nu modes k) (Acell k t) (Acell k t))
        + (4 / ε) * ∫ t in t₀..t₁,
            nsPSD.resForm (outRate nu modes k) (F k t) (F k t))
      = (∑ k ∈ outs, 2 * nsPSD.resForm (outRate nu modes k) (Acell k t₀) (Acell k t₀))
        + ε * (∑ k ∈ outs, ∫ t in t₀..t₁,
            nsPSD.resForm (outRate nu modes k) (Acell k t) (Acell k t))
        + (4 / ε) * ∑ k ∈ outs, ∫ t in t₀..t₁,
            nsPSD.resForm (outRate nu modes k) (F k t) (F k t) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
  have hεpos : 0 < 4 / ε := by positivity
  have hlast : (4 / ε) * ∑ k ∈ outs, (∫ t in t₀..t₁,
      nsPSD.resForm (outRate nu modes k) (F k t) (F k t))
      ≤ (4 / ε) * (9 * A * M * (t₁ - t₀) / (2 * nu)) :=
    mul_le_mul_of_nonneg_left hFsum hεpos.le
  linarith [hsum1, hsplit.le, hsplit.ge, hlast]

end ClayNS.Schur

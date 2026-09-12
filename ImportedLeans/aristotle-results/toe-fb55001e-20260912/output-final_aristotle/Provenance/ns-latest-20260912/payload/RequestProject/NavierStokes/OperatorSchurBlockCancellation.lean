/-
# From data-Schur to operator-Schur, and from absolute row sums to blocks

`AlmostOrthogonalGramSchur.lean` closed the following chain: the exact
Cauchy–Schwarz/collinearity-defect identity, a finite Schur compiler, and the
critical spacetime consumer

  `∫ remainder ≤ (9AE₀²/(2ν)) ∫ ‖u(t)‖_A² dt`,

conditionally on `AlmostOrthogonal modes G A` — a Schur (uniform absolute row
sum) condition on the *realized* cell family `G_p = P_k(N_p × u_{k−p})`.

Three things about that hypothesis deserved to be sharpened, and this file
sharpens all three.

1. **`AlmostOrthogonal` is a property of one snapshot.**  Its object is the
   already-realized family, so the constant `A` is in principle allowed to
   depend on accidentally favourable phase relations of a single solution.
   `dataSchur_snapshot_dependent` shows this is not a hypothetical worry: for a
   fixed (linear) family of maps `T_p`, one input gives Schur constant `1` and
   another forces `A ≥ card`.  `OperatorSchur` is the structural replacement —
   a `T_p^*T_q`-style kernel bound together with a uniform lower frame bound —
   and `almostOrthogonal_of_operatorSchur` is the promised realization seam

     `OperatorSchur T A ⟹ ∀ x, AlmostOrthogonal (p ↦ T_p x) A`,

   with `A` independent of `x`.  `spacetime_remainder_le_critical_of_operatorSchur`
   runs it straight into the existing critical consumer.

2. **The defect ledger needed support surgery.**  `herm_re_eq_sub_defect`
   required both cells to have nonzero norm.  `herm_re_eq_sub_defect'` and
   `resForm_eq_cs_sub_defect'` are the zero-safe versions (the identity is true
   verbatim, because a zero cell kills both sides), and
   `two_nrm_mul_herm_re_eq` is the division-free form.

3. **Absolute row sums are a producer, not the phenomenon.**  Two results
   delimit this.  `exists_signed_family_resForm_zero_with_maximal_schur`
   exhibits a family whose *signed* resolvent Gram form vanishes identically
   while every admissible absolute Schur constant is at least the cardinality:
   so a failure of uniform absolute row-summability does **not** kill the
   resolvent route.  And `sum_sum_le_block_schur` / `resForm_le_block_schur`
   compile the weaker *block* hypothesis into the same conclusion, with
   `blockAlmostOrthogonal_of_almostOrthogonal` showing the pointwise condition
   is the singleton-block special case and
   `blockSchur_strictly_weaker_than_absolute_schur` showing the inclusion is
   strict.  Taking a single block, `BlockAlmostOrthogonal` with `A = 1` *is*
   the statement that the physical outer-cell Gram operator has a
   truncation-uniform `ℓ² → ℓ²` bound at the retained output — i.e. exactly the
   operator-level question, now expressible as a hypothesis of the same
   compiler.

Nothing here proves the physical family satisfies any of these hypotheses.
Package A and the literal periodic Clay target are not closed and nothing is
claimed for them; no axiom, postulate or placeholder is introduced.
-/
import RequestProject.NavierStokes.AlmostOrthogonalGramSchur

noncomputable section

open MeasureTheory Set

namespace ClayNS.Schur

open ClayNS.Waleffe ClayNS.Resolvent ClayNS.TTStar

/-! ## 1.  The zero-safe collinearity ledger -/

/-- A cell of vanishing norm vanishes. -/
theorem vec_eq_zero_of_nrm_eq_zero {x : Fin 3 → ℂ} (h : nrm x = 0) (i : Fin 3) : x i = 0 := by
  have h0 : nsq x = 0 := by rw [← nrm_sq x, h]; ring
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (f := fun i => Complex.normSq (x i)) (s := (Finset.univ : Finset (Fin 3)))
    (fun i _ => Complex.normSq_nonneg _)).mp h0 i (Finset.mem_univ i)
  simpa [Complex.normSq_eq_zero] using hi

/-- **Zero-safe defect identity.**  `herm_re_eq_sub_defect` without the
nonvanishing hypotheses: if either cell is zero both sides vanish, so no support
surgery is needed before applying the ledger. -/
theorem herm_re_eq_sub_defect' (x y : Fin 3 → ℂ) :
    (herm x y).re = nrm x * nrm y - nsq (csDefect x y) / (2 * (nrm x * nrm y)) := by
  by_cases hx : nrm x = 0
  · have hz : ∀ i, x i = 0 := vec_eq_zero_of_nrm_eq_zero hx
    have hzero : herm x y = 0 := by simp [herm, hz]
    simp [hzero, hx]
  · by_cases hy : nrm y = 0
    · have hz : ∀ i, y i = 0 := vec_eq_zero_of_nrm_eq_zero hy
      have hzero : herm x y = 0 := by simp [herm, hz]
      simp [hzero, hy]
    · exact herm_re_eq_sub_defect hx hy

/-- The division-free form of the same ledger. -/
theorem two_nrm_mul_herm_re_eq (x y : Fin 3 → ℂ) :
    2 * (nrm x * nrm y) * (herm x y).re
      = 2 * (nrm x * nrm y) ^ 2 - nsq (csDefect x y) := by
  have h := nsq_csDefect_eq x y
  nlinarith [h]

/-- **Zero-safe exact ledger of the unconditional route.**  `resForm_eq_cs_sub_defect`
with its nonvanishing hypothesis removed: the signed resolvent Gram form equals
its Cauchy–Schwarz majorant minus the resolvent-weighted total collinearity
defect, for *every* cell family. -/
theorem resForm_eq_cs_sub_defect' {nu : ℝ} (modes : Finset Wave) (G : Wave → Fin 3 → ℂ)
    (k : Wave) :
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
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p' _ => ?_
  rw [herm_re_eq_sub_defect' (G p) (G p'), sub_div]

/-! ## 2.  Operator-level almost orthogonality -/

/-- **Operator Schur condition.**  A family of maps `T_p : X → ℂ³` is
operator-almost-orthogonal with constant `A` when there are

* a symmetric nonnegative kernel `c` with `|Re⟪T_p x, T_q x⟫| ≤ c(p,q)‖x‖²`
  for *every* input `x` — the `‖T_p^*T_q‖`-style hypothesis, and
* a uniform lower frame bound `b_p‖x‖ ≤ ‖T_p x‖`,

such that the normalized kernel `c(p,q)/(b_p b_q)` has row sums at most `A`.
Unlike `AlmostOrthogonal`, this is a property of the *maps*: `A` cannot depend
on a particular realized snapshot. -/
def OperatorSchur {X : Type*} (modes : Finset Wave) (T : Wave → X → (Fin 3 → ℂ))
    (nX : X → ℝ) (A : ℝ) : Prop :=
  ∃ (c : Wave → Wave → ℝ) (b : Wave → ℝ),
    (∀ x, 0 ≤ nX x) ∧
    (∀ p, 0 < b p) ∧
    (∀ p q, 0 ≤ c p q) ∧ (∀ p q, c p q = c q p) ∧
    (∀ p ∈ modes, ∀ q ∈ modes, ∀ x : X,
      |(herm (T p x) (T q x)).re| ≤ c p q * nX x ^ 2) ∧
    (∀ p ∈ modes, ∀ x : X, b p * nX x ≤ nrm (T p x)) ∧
    (∀ p ∈ modes, ∑ q ∈ modes, c p q / (b p * b q) ≤ A)

/-- **The realization seam.**  An operator-level Schur bound produces the
data-level Schur bound at every admissible input, with the *same* constant. -/
theorem almostOrthogonal_of_operatorSchur {X : Type*} {modes : Finset Wave}
    {T : Wave → X → (Fin 3 → ℂ)} {nX : X → ℝ} {A : ℝ}
    (h : OperatorSchur modes T nX A) (x : X) :
    AlmostOrthogonal modes (fun p => T p x) A := by
  obtain ⟨c, b, hnX, hb, hcnn, hcsym, hker, hlow, hrow⟩ := h
  refine ⟨fun p q => c p q / (b p * b q), ?_, ?_, ?_, hrow⟩
  · intro p q
    exact div_nonneg (hcnn p q) (le_of_lt (mul_pos (hb p) (hb q)))
  · intro p q
    show c p q / (b p * b q) = c q p / (b q * b p)
    rw [hcsym p q, mul_comm (b p) (b q)]
  · intro p hp q hq
    show |(herm (T p x) (T q x)).re| ≤ c p q / (b p * b q) * (nrm (T p x) * nrm (T q x))
    have h1 : |(herm (T p x) (T q x)).re| ≤ c p q * nX x ^ 2 := hker p hp q hq x
    have hbp := hb p
    have hbq := hb q
    have heq : c p q * nX x ^ 2
        = (c p q / (b p * b q)) * ((b p * nX x) * (b q * nX x)) := by
      field_simp
    have hmono : (c p q / (b p * b q)) * ((b p * nX x) * (b q * nX x))
        ≤ (c p q / (b p * b q)) * (nrm (T p x) * nrm (T q x)) := by
      have hgnn : 0 ≤ c p q / (b p * b q) :=
        div_nonneg (hcnn p q) (le_of_lt (mul_pos hbp hbq))
      have h1' : 0 ≤ b p * nX x := mul_nonneg hbp.le (hnX x)
      have h2' : 0 ≤ b q * nX x := mul_nonneg hbq.le (hnX x)
      have hp1 : b p * nX x ≤ nrm (T p x) := hlow p hp x
      have hq1 : b q * nX x ≤ nrm (T q x) := hlow q hq x
      have hmm : (b p * nX x) * (b q * nX x) ≤ nrm (T p x) * nrm (T q x) :=
        mul_le_mul hp1 hq1 h2' (le_trans h1' hp1)
      exact mul_le_mul_of_nonneg_left hmm hgnn
    calc |(herm (T p x) (T q x)).re| ≤ c p q * nX x ^ 2 := h1
      _ = (c p q / (b p * b q)) * ((b p * nX x) * (b q * nX x)) := heq
      _ ≤ (c p q / (b p * b q)) * (nrm (T p x) * nrm (T q x)) := hmono

/-- **The critical consumer, fed by an operator-level hypothesis.**  Identical
to `spacetime_remainder_le_critical` except that the almost-orthogonality input
is now a property of the outer-cell *maps* at each retained output, quantified
over all admissible fields, rather than of the realized family at each time. -/
theorem spacetime_remainder_le_critical_of_operatorSchur {nu A E₀ : ℝ} (hnu : 0 < nu)
    (modes outs : Finset Wave) (u : ℝ → Wave → Fin 3 → ℂ) (t₀ t₁ : ℝ)
    (ht : t₀ ≤ t₁) (hA : 0 ≤ A) (hE₀ : 0 ≤ E₀)
    (hk : ∀ k ∈ outs, wsq k ≠ 0) (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hdiv : ∀ t : ℝ, ∀ c : Wave, dotb (wC c) (u t c) = 0)
    (hsupp : ∀ t : ℝ, ∀ b ∉ modes, u t b = fun _ => 0)
    (hOS : ∀ k ∈ outs, OperatorSchur modes
      (fun p x => outerCellVec (innerForcing modes x) x k p) (wienerA modes) A)
    (hEbd : ∀ t ∈ Set.Icc t₀ t₁, energy modes (u t) ≤ E₀)
    (hint : IntervalIntegrable
      (fun t => ∑ k ∈ outs,
        (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes (innerForcing modes (u t)) (u t) k)))
      volume t₀ t₁)
    (hintW : IntervalIntegrable (fun t => wienerA modes (u t) ^ 2) volume t₀ t₁) :
    (∫ t in t₀..t₁, ∑ k ∈ outs,
        (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes (innerForcing modes (u t)) (u t) k)))
      ≤ 9 * A * E₀ ^ 2 / (2 * nu) * ∫ t in t₀..t₁, wienerA modes (u t) ^ 2 :=
  spacetime_remainder_le_critical hnu modes outs u t₀ t₁ ht hA hE₀ hk hp hdiv hsupp
    (fun t _ k hkm => almostOrthogonal_of_operatorSchur (hOS k hkm) (u t)) hEbd hint hintW

/-! ## 3.  Why the distinction is not cosmetic: data-Schur is snapshot dependent -/

/-- The first coordinate vector of `ℂ³`. -/
def e0 : Fin 3 → ℂ := fun i => if i = 0 then 1 else 0

/-- The second coordinate vector of `ℂ³`. -/
def e1 : Fin 3 → ℂ := fun i => if i = 1 then 1 else 0

/-- The zero lattice vector, used as a mode label. -/
def wa : Wave := fun _ => 0

/-- The all-ones lattice vector, used as a second mode label. -/
def wb : Wave := fun _ => 1

theorem wa_ne_wb : wa ≠ wb := by
  intro h
  have h0 := congrFun h 0
  simp [wa, wb] at h0

/-- **`AlmostOrthogonal` is a property of the snapshot, not of the maps.**  For
one fixed family of (linear, indeed coordinate-projection) maps `T_p`, one input
realizes Schur constant `1` and another forces the trivial constant `card modes`.
So a Clay-scale argument cannot rest on a data-level Schur constant unless it is
produced by something like `OperatorSchur`, which quantifies over inputs. -/
theorem dataSchur_snapshot_dependent :
    ∃ (modes : Finset Wave) (T : Wave → (Wave → Fin 3 → ℂ) → (Fin 3 → ℂ))
      (x y : Wave → Fin 3 → ℂ),
      (modes.card : ℝ) = 2 ∧
      (∀ p z, T p z = z p) ∧
      AlmostOrthogonal modes (fun p => T p x) 1 ∧
      (∀ A : ℝ, AlmostOrthogonal modes (fun p => T p y) A → (2 : ℝ) ≤ A) := by
  classical
  have hba : wb ≠ wa := Ne.symm wa_ne_wb
  refine ⟨{wa, wb}, fun p z => z p, fun p => if p = wa then e0 else e1, fun _ => e0,
    by rw [Finset.card_pair wa_ne_wb]; norm_num, fun _ _ => rfl, ?_, ?_⟩
  · refine almostOrthogonal_of_orthogonal _ _ ?_
    intro p hp p' hp' hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hp'
    rcases hp with rfl | rfl <;> rcases hp' with rfl | rfl
    · exact absurd rfl hne
    · simp [herm, e0, e1, hba]
    · simp [herm, e0, e1, hba]
    · exact absurd rfl hne
  · intro A hA
    have hv : nsq e0 ≠ 0 := by simp [nsq, e0]
    have hc := card_le_of_almostOrthogonal_coherent (modes := {wa, wb}) (v := e0) hv
      ⟨wa, by simp⟩ hA
    rwa [Finset.card_pair wa_ne_wb, show ((2 : ℕ) : ℝ) = 2 from by norm_num] at hc

/-! ## 4.  Absolute row sums are a producer, not the phenomenon -/

/-- A real multiple of a fixed cell. -/
def realScale (a : ℝ) (v : Fin 3 → ℂ) : Fin 3 → ℂ := fun i => ((a : ℝ) : ℂ) * v i

theorem nsq_realScale (a : ℝ) (v : Fin 3 → ℂ) : nsq (realScale a v) = a ^ 2 * nsq v := by
  simp [nsq, realScale, Complex.normSq_mul, Finset.mul_sum, Complex.normSq_ofReal, sq]

theorem nrm_realScale (a : ℝ) (v : Fin 3 → ℂ) : nrm (realScale a v) = |a| * nrm v := by
  rw [nrm, nrm, nsq_realScale, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

theorem herm_realScale (a b : ℝ) (v : Fin 3 → ℂ) :
    (herm (realScale a v) (realScale b v)).re = a * b * nsq v := by
  show (herm (fun i => ((a : ℝ) : ℂ) * v i) (fun i => ((b : ℝ) : ℂ) * v i)).re = _
  rw [herm_real_pair]
  simp [Complex.mul_re, ← nsq_eq_herm_re]

/-- The signed resolvent Gram form of a family of real multiples of one cell, at
constant pair rate: it is the *square of the signed sum*, so it is small exactly
when the signs cancel. -/
theorem resForm_realScale_eq (lam : ℝ) (modes : Finset Wave) (c : Wave → ℝ) (v : Fin 3 → ℂ) :
    ∑ p ∈ modes, ∑ p' ∈ modes,
        (herm (realScale (c p) v) (realScale (c p') v)).re / (lam + lam)
      = (∑ p ∈ modes, c p) ^ 2 * nsq v / (2 * lam) :=
  resForm_coherent_eq lam modes c v

/-- **A unimodular family still forces the trivial Schur constant.**  Absolute
coherence does not see the signs: if every cell is `±v`, every admissible
absolute Schur constant is at least the cardinality of the fibre. -/
theorem card_le_of_almostOrthogonal_unimodular {modes : Finset Wave} {v : Fin 3 → ℂ}
    {c : Wave → ℝ} {A : ℝ} (hv : nsq v ≠ 0) (hmodes : modes.Nonempty)
    (hc : ∀ p ∈ modes, |c p| = 1)
    (h : AlmostOrthogonal modes (fun p => realScale (c p) v) A) :
    (modes.card : ℝ) ≤ A := by
  obtain ⟨g, hgnn, _, hAO, hrow⟩ := h
  have hvpos : 0 < nsq v := lt_of_le_of_ne (nsq_nonneg v) (Ne.symm hv)
  have hnrm : nrm v * nrm v = nsq v := by have := nrm_sq v; nlinarith [this]
  have hge : ∀ p ∈ modes, ∀ p' ∈ modes, 1 ≤ g p p' := by
    intro p hp p' hp'
    have h1 := hAO p hp p' hp'
    rw [herm_realScale, nrm_realScale, nrm_realScale, hc p hp, hc p' hp'] at h1
    rw [abs_mul, abs_mul, hc p hp, hc p' hp', abs_of_nonneg hvpos.le] at h1
    simp only [one_mul] at h1
    rw [hnrm] at h1
    nlinarith [h1, hvpos]
  obtain ⟨p, hp⟩ := hmodes
  have hrowge : (modes.card : ℝ) ≤ ∑ p' ∈ modes, g p p' := by
    have hs : ∑ _p' ∈ modes, (1 : ℝ) ≤ ∑ p' ∈ modes, g p p' :=
      Finset.sum_le_sum fun p' hp' => hge p hp p' hp'
    simpa using hs
  exact le_trans hrowge (hrow p hp)

/-- **Large absolute row sums do not kill the resolvent route.**  There is a
cell family whose *signed* resolvent Gram form vanishes identically — so the
remainder it produces is zero — while every admissible absolute Schur constant
is at least the cardinality of the fibre.  Hence a failure of uniform absolute
row-summability is not a no-go for the signed route; it only rules out this
particular producer. -/
theorem exists_signed_family_resForm_zero_with_maximal_schur (lam : ℝ) :
    ∃ (modes : Finset Wave) (v : Fin 3 → ℂ) (c : Wave → ℝ),
      (modes.card : ℝ) = 2 ∧ nsq v ≠ 0 ∧ (∀ p, |c p| = 1) ∧
      (∑ p ∈ modes, ∑ p' ∈ modes,
        (herm (realScale (c p) v) (realScale (c p') v)).re / (lam + lam)) = 0 ∧
      (∀ A : ℝ, AlmostOrthogonal modes (fun p => realScale (c p) v) A → (2 : ℝ) ≤ A) := by
  classical
  have hba : wb ≠ wa := Ne.symm wa_ne_wb
  have hv : nsq e0 ≠ 0 := by simp [nsq, e0]
  have hcard : (({wa, wb} : Finset Wave).card : ℝ) = 2 := by
    rw [Finset.card_pair wa_ne_wb]; norm_num
  refine ⟨{wa, wb}, e0, fun p => if p = wa then 1 else -1, hcard, hv, ?_, ?_, ?_⟩
  · intro p; by_cases h : p = wa <;> simp [h]
  · rw [resForm_realScale_eq]
    have hsum : ∑ p ∈ ({wa, wb} : Finset Wave), (if p = wa then (1 : ℝ) else -1) = 0 := by
      rw [Finset.sum_pair wa_ne_wb]
      simp [hba]
    rw [hsum]
    simp
  · intro A hA
    have hc := card_le_of_almostOrthogonal_unimodular (modes := {wa, wb}) (v := e0)
      (c := fun p => if p = wa then 1 else -1) hv ⟨wa, by simp⟩
      (fun p _ => by by_cases h : p = wa <;> simp [h]) hA
    rwa [hcard] at hc

/-! ## 5.  The block Schur compiler -/

/-- **Block Schur test.**  If the index set is partitioned by `blk` into blocks
listed by `Bl`, and the *aggregated* block sums are dominated by a symmetric
nonnegative block kernel with row sums `≤ A` against a block profile `a`, then
the full double sum is bounded by the ℓ² mass of that profile.  Setting `blk`
to the identity recovers `sum_sum_le_schur`. -/
theorem sum_sum_le_block_schur {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (s : Finset ι) (Bl : Finset β) (blk : ι → β) (hmaps : ∀ i ∈ s, blk i ∈ Bl)
    (c : ι → ι → ℝ) (a : β → ℝ) (g : β → β → ℝ) (K A : ℝ) (hK : 0 ≤ K)
    (hgnn : ∀ P Q, 0 ≤ g P Q) (hgsym : ∀ P Q, g P Q = g Q P)
    (hc : ∀ P ∈ Bl, ∀ Q ∈ Bl,
      (∑ i ∈ s with blk i = P, ∑ j ∈ s with blk j = Q, c i j) ≤ K * (g P Q * (a P * a Q)))
    (hrow : ∀ P ∈ Bl, ∑ Q ∈ Bl, g P Q ≤ A) :
    ∑ i ∈ s, ∑ j ∈ s, c i j ≤ K * (A * ∑ P ∈ Bl, a P ^ 2) := by
  classical
  have hexp : ∑ P ∈ Bl, ∑ Q ∈ Bl, (∑ i ∈ s with blk i = P, ∑ j ∈ s with blk j = Q, c i j)
      = ∑ i ∈ s, ∑ j ∈ s, c i j := by
    have h1 : ∀ P ∈ Bl, ∑ Q ∈ Bl, (∑ i ∈ s with blk i = P, ∑ j ∈ s with blk j = Q, c i j)
        = ∑ i ∈ s with blk i = P, ∑ j ∈ s, c i j := by
      intro P _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact Finset.sum_fiberwise_of_maps_to hmaps (fun j => c i j)
    rw [Finset.sum_congr rfl h1]
    exact Finset.sum_fiberwise_of_maps_to hmaps (fun i => ∑ j ∈ s, c i j)
  rw [← hexp]
  exact sum_sum_le_schur Bl
    (fun P Q => ∑ i ∈ s with blk i = P, ∑ j ∈ s with blk j = Q, c i j) a g K A hK hgnn hgsym
    hc hrow

/-- The ℓ² mass of the frequency-normalized cells inside one block. -/
def blockMass {β : Type*} [DecidableEq β] (modes : Finset Wave) (blk : Wave → β)
    (G : Wave → Fin 3 → ℂ) (P : β) : ℝ :=
  Real.sqrt (∑ p ∈ modes with blk p = P, nsq (G p) / wsq p)

theorem sq_blockMass {β : Type*} [DecidableEq β] (modes : Finset Wave) (blk : Wave → β)
    (G : Wave → Fin 3 → ℂ) (P : β) :
    blockMass modes blk G P ^ 2 = ∑ p ∈ modes with blk p = P, nsq (G p) / wsq p := by
  rw [blockMass, Real.sq_sqrt]
  exact Finset.sum_nonneg fun p _ => div_nonneg (nsq_nonneg _) (wsq_nonneg _)

theorem blockMass_singleton (modes : Finset Wave) (G : Wave → Fin 3 → ℂ) {P : Wave}
    (hP : P ∈ modes) : blockMass modes id G P = nrm (G P) / wlen P := by
  classical
  rw [blockMass]
  have hfil : {p ∈ modes | id p = P} = ({P} : Finset Wave) := by
    simpa using (by rw [Finset.filter_eq' modes P, if_pos hP] :
      {p ∈ modes | p = P} = ({P} : Finset Wave))
  rw [hfil, Finset.sum_singleton, Real.sqrt_div (nsq_nonneg _), nrm, wlen]

/-- **Block almost orthogonality.**  Only the *aggregated* interaction between
two blocks is required to be small, measured against the ℓ² masses of the
blocks; the pointwise entries inside a block are unconstrained.  With singleton
blocks this is `AlmostOrthogonal` (`blockAlmostOrthogonal_of_almostOrthogonal`);
with a single block containing every retained cell it is exactly the statement
that the outer-cell Gram operator at the output `k` is bounded on `ℓ²` with
constant `A`. -/
def BlockAlmostOrthogonal {β : Type*} [DecidableEq β] (nu : ℝ) (modes : Finset Wave)
    (Bl : Finset β) (blk : Wave → β) (G : Wave → Fin 3 → ℂ) (k : Wave) (A : ℝ) : Prop :=
  (∀ p ∈ modes, blk p ∈ Bl) ∧
  ∃ g : β → β → ℝ, (∀ P Q, 0 ≤ g P Q) ∧ (∀ P Q, g P Q = g Q P) ∧
    (∀ P ∈ Bl, ∀ Q ∈ Bl,
      (∑ p ∈ modes with blk p = P, ∑ q ∈ modes with blk q = Q,
        (herm (G p) (G q)).re
          / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q)))
        ≤ (1 / (2 * nu)) * (g P Q * (blockMass modes blk G P * blockMass modes blk G Q))) ∧
    (∀ P ∈ Bl, ∑ Q ∈ Bl, g P Q ≤ A)

/-- **The block Schur compiler.**  The weaker block hypothesis buys exactly the
same conclusion as `resForm_le_schur`: the whole signed resolvent Gram form is
bounded by `A` times the ℓ² mass of the frequency-normalized cells. -/
theorem resForm_le_block_schur {β : Type*} [DecidableEq β] {nu A : ℝ} (hnu : 0 < nu)
    (modes : Finset Wave) (Bl : Finset β) (blk : Wave → β)
    (G : Wave → Fin 3 → ℂ) (k : Wave)
    (hAO : BlockAlmostOrthogonal nu modes Bl blk G k A) :
    ∑ p ∈ modes, ∑ q ∈ modes,
        (herm (G p) (G q)).re
          / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))
      ≤ A * (∑ p ∈ modes, nsq (G p) / wsq p) / (2 * nu) := by
  classical
  obtain ⟨hmaps, g, hgnn, hgsym, hblk, hrow⟩ := hAO
  have hK : (0 : ℝ) ≤ 1 / (2 * nu) := by positivity
  have h := sum_sum_le_block_schur (s := modes) (Bl := Bl) (blk := blk) hmaps
    (c := fun p q => (herm (G p) (G q)).re
      / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q)))
    (a := blockMass modes blk G) (g := g) (K := 1 / (2 * nu)) (A := A) hK hgnn hgsym hblk hrow
  have hmass : ∑ P ∈ Bl, blockMass modes blk G P ^ 2 = ∑ p ∈ modes, nsq (G p) / wsq p := by
    rw [Finset.sum_congr rfl (fun P _ => sq_blockMass modes blk G P)]
    exact Finset.sum_fiberwise_of_maps_to hmaps _
  rw [hmass] at h
  have hfin : 1 / (2 * nu) * (A * ∑ p ∈ modes, nsq (G p) / wsq p)
      = A * (∑ p ∈ modes, nsq (G p) / wsq p) / (2 * nu) := by field_simp
  linarith [h, hfin.le, hfin.ge]

/-- One pair of the resolvent form under a coherence bound: the viscous pair
rate cancels the two output derivatives and leaves the frequency-normalized
masses.  This is the pointwise step of `resForm_le_schur`, isolated. -/
theorem resTerm_le_of_coherence {nu : ℝ} (hnu : 0 < nu) (k p q : Wave) {x y : Fin 3 → ℂ}
    {gpq : ℝ} (hp : wsq p ≠ 0) (hq : wsq q ≠ 0) (hgnn : 0 ≤ gpq)
    (hb : |(herm x y).re| ≤ gpq * (nrm x * nrm y)) :
    (herm x y).re / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))
      ≤ (1 / (2 * nu)) * (gpq * ((nrm x / wlen p) * (nrm y / wlen q))) := by
  have hlp : 0 < wlen p := wlen_pos_of_wsq_ne_zero hp
  have hlq : 0 < wlen q := wlen_pos_of_wsq_ne_zero hq
  have hden0 : 0 < 2 * nu * (wlen p * wlen q) := by positivity
  have hden : 2 * nu * (wlen p * wlen q)
      ≤ viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q) :=
    two_nu_wlen_mul_le_pairRate hnu.le k p q
  have hpos : 0 < viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q) :=
    lt_of_lt_of_le hden0 hden
  have hnum : (herm x y).re ≤ gpq * (nrm x * nrm y) := le_trans (le_abs_self _) hb
  have hnumnn : 0 ≤ gpq * (nrm x * nrm y) :=
    mul_nonneg hgnn (mul_nonneg (nrm_nonneg _) (nrm_nonneg _))
  have hstep1 : (herm x y).re / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))
      ≤ (gpq * (nrm x * nrm y))
        / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q)) :=
    (div_le_div_iff_of_pos_right hpos).mpr hnum
  have hstep2 : (gpq * (nrm x * nrm y))
        / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))
      ≤ (gpq * (nrm x * nrm y)) / (2 * nu * (wlen p * wlen q)) :=
    div_le_div_of_nonneg_left hnumnn hden0 hden
  have heq : (gpq * (nrm x * nrm y)) / (2 * nu * (wlen p * wlen q))
      = (1 / (2 * nu)) * (gpq * ((nrm x / wlen p) * (nrm y / wlen q))) := by
    field_simp
  linarith [hstep1, hstep2, heq.le, heq.ge]

/-- **Absolute Schur is the singleton-block case.**  So the block hypothesis is
never stronger than the pointwise one. -/
theorem blockAlmostOrthogonal_of_almostOrthogonal {nu A : ℝ} (hnu : 0 < nu)
    (modes : Finset Wave) (G : Wave → Fin 3 → ℂ) (k : Wave)
    (hp : ∀ p ∈ modes, wsq p ≠ 0) (hAO : AlmostOrthogonal modes G A) :
    BlockAlmostOrthogonal nu modes modes id G k A := by
  classical
  obtain ⟨g, hgnn, hgsym, hb, hrow⟩ := hAO
  refine ⟨fun p hpm => hpm, g, hgnn, hgsym, ?_, hrow⟩
  intro P hP Q hQ
  have hfilP : {p ∈ modes | id p = P} = ({P} : Finset Wave) := by
    simpa using (by rw [Finset.filter_eq' modes P, if_pos hP] :
      {p ∈ modes | p = P} = ({P} : Finset Wave))
  have hfilQ : {q ∈ modes | id q = Q} = ({Q} : Finset Wave) := by
    simpa using (by rw [Finset.filter_eq' modes Q, if_pos hQ] :
      {q ∈ modes | q = Q} = ({Q} : Finset Wave))
  rw [hfilP, Finset.sum_singleton, hfilQ, Finset.sum_singleton,
    blockMass_singleton modes G hP, blockMass_singleton modes G hQ]
  exact resTerm_le_of_coherence hnu k P Q (hp P hP) (hq := hp Q hQ) (hgnn P Q) (hb P hP Q hQ)

/-! ## 6.  The inclusion is strict -/

/-- The lattice vector `(1,0,0)`. -/
def wp1 : Wave := fun i => if i = 0 then 1 else 0

/-- The lattice vector `(−1,0,0)`. -/
def wm1 : Wave := fun i => if i = 0 then -1 else 0

theorem wp1_ne_wm1 : wp1 ≠ wm1 := by
  intro h
  have h0 := congrFun h 0
  simp [wp1, wm1] at h0

theorem wsq_wp1 : wsq wp1 = 1 := by simp [wsq, wp1]

theorem wsq_wm1 : wsq wm1 = 1 := by simp [wsq, wm1]

/-- **Block Schur is strictly weaker than absolute Schur.**  At the output
`k = 0` the two cells `±v` on the modes `(±1,0,0)` have equal viscous pair
rates, so their signed Gram form vanishes: a single block certifies
`BlockAlmostOrthogonal` with constant `1`, while every absolute Schur constant
for the same family is at least `2`.  So if a uniform pointwise coherence row
bound fails, the block route is still open. -/
theorem blockSchur_strictly_weaker_than_absolute_schur {nu : ℝ} (hnu : 0 < nu) :
    ∃ (modes : Finset Wave) (G : Wave → Fin 3 → ℂ) (Bl : Finset Unit) (blk : Wave → Unit),
      BlockAlmostOrthogonal nu modes Bl blk G 0 1 ∧
      (∀ A : ℝ, AlmostOrthogonal modes G A → (2 : ℝ) ≤ A) := by
  classical
  set c : Wave → ℝ := fun p => if p = wp1 then 1 else -1 with hc
  set G : Wave → Fin 3 → ℂ := fun p => realScale (c p) e0 with hG
  have hmw : wm1 ≠ wp1 := Ne.symm wp1_ne_wm1
  have hv : nsq e0 ≠ 0 := by simp [nsq, e0]
  have hrate : ∀ p : Wave, wsq p = 1 →
      viscousPairRate nu p ((0 : Wave) - p) = 2 * nu := by
    intro p hpsq
    have hsub : wsq ((0 : Wave) - p) = wsq p := by
      simp [wsq, Fin.sum_univ_three]
    rw [viscousPairRate, hsub, hpsq]
    ring
  refine ⟨{wp1, wm1}, G, {()}, fun _ => (), ⟨fun _ _ => Finset.mem_singleton_self _,
    fun _ _ => 1, fun _ _ => zero_le_one, fun _ _ => rfl, ?_, ?_⟩, ?_⟩
  · intro P _ Q _
    have hfil : {p ∈ ({wp1, wm1} : Finset Wave) | (fun _ => ()) p = P}
        = ({wp1, wm1} : Finset Wave) := by
      refine Finset.filter_true_of_mem fun p _ => ?_
      exact Subsingleton.elim _ _
    rw [hfil]
    have hzero : ∑ p ∈ ({wp1, wm1} : Finset Wave), ∑ q ∈ ({wp1, wm1} : Finset Wave),
        (herm (G p) (G q)).re
          / (viscousPairRate nu p ((0 : Wave) - p) + viscousPairRate nu q ((0 : Wave) - q))
        = 0 := by
      rw [Finset.sum_pair wp1_ne_wm1, Finset.sum_pair wp1_ne_wm1, Finset.sum_pair wp1_ne_wm1]
      rw [hrate wp1 wsq_wp1, hrate wm1 wsq_wm1]
      rw [hG]
      simp only [herm_realScale, hc]
      simp [hmw]
      ring
    rw [hzero]
    have hnn : 0 ≤ (1 / (2 * nu)) * ((1 : ℝ) *
        (blockMass ({wp1, wm1} : Finset Wave) (fun _ => ()) G P *
          blockMass ({wp1, wm1} : Finset Wave) (fun _ => ()) G Q)) := by
      have h1 : 0 ≤ blockMass ({wp1, wm1} : Finset Wave) (fun _ => ()) G P :=
        Real.sqrt_nonneg _
      have h2 : 0 ≤ blockMass ({wp1, wm1} : Finset Wave) (fun _ => ()) G Q :=
        Real.sqrt_nonneg _
      have h3 : 0 ≤ 1 / (2 * nu) := by positivity
      positivity
    exact hnn
  · intro P _
    simp
  · intro A hA
    have hcard : (({wp1, wm1} : Finset Wave).card : ℝ) = 2 := by
      rw [Finset.card_pair wp1_ne_wm1]; norm_num
    have hres := card_le_of_almostOrthogonal_unimodular (modes := {wp1, wm1}) (v := e0)
      (c := c) hv ⟨wp1, by simp⟩ (fun p _ => by rw [hc]; by_cases h : p = wp1 <;> simp [h]) hA
    rwa [hcard] at hres

/-! ## 7.  The weakest hypothesis the consumer actually needs

Every producer above — pointwise absolute Schur, block Schur, and the
operator-level condition — is used only through one scalar inequality: that the
signed resolvent Gram form of the cells at the output `k` is bounded by `A`
times the ℓ² mass of the frequency-normalized cells.  That inequality is
exactly the truncation-uniform `ℓ² → ℓ²` bound for the outer-cell Gram operator.
This section isolates it and reruns the whole physical chain from it, so that
any future producer — angular, helical, phase/Cotlar–Stein, signed or block —
can be plugged in without touching the consumer. -/

/-- **The operator bound at one output.**  The signed resolvent Gram form of the
cells is bounded by `A` times the ℓ² mass of the frequency-normalized cells. -/
def GramOperatorBound (nu : ℝ) (modes : Finset Wave) (G : Wave → Fin 3 → ℂ)
    (k : Wave) (A : ℝ) : Prop :=
  ∑ p ∈ modes, ∑ q ∈ modes,
      (herm (G p) (G q)).re
        / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))
    ≤ A * (∑ p ∈ modes, nsq (G p) / wsq p) / (2 * nu)

/-- Producer 1: pointwise absolute Schur. -/
theorem gramOperatorBound_of_almostOrthogonal {nu A : ℝ} (hnu : 0 < nu) (modes : Finset Wave)
    (G : Wave → Fin 3 → ℂ) (k : Wave) (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hAO : AlmostOrthogonal modes G A) :
    GramOperatorBound nu modes G k A :=
  resForm_le_schur hnu modes G k hp hAO

/-- Producer 2: block Schur. -/
theorem gramOperatorBound_of_blockAlmostOrthogonal {β : Type*} [DecidableEq β] {nu A : ℝ}
    (hnu : 0 < nu) (modes : Finset Wave) (Bl : Finset β) (blk : Wave → β)
    (G : Wave → Fin 3 → ℂ) (k : Wave)
    (hAO : BlockAlmostOrthogonal nu modes Bl blk G k A) :
    GramOperatorBound nu modes G k A :=
  resForm_le_block_schur hnu modes Bl blk G k hAO

/-- Producer 3: the operator-level condition, at every admissible input. -/
theorem gramOperatorBound_of_operatorSchur {X : Type*} {nu A : ℝ} (hnu : 0 < nu)
    (modes : Finset Wave) {T : Wave → X → (Fin 3 → ℂ)} {nX : X → ℝ} (k : Wave)
    (hp : ∀ p ∈ modes, wsq p ≠ 0) (h : OperatorSchur modes T nX A) (x : X) :
    GramOperatorBound nu modes (fun p => T p x) k A :=
  resForm_le_schur hnu modes _ k hp (almostOrthogonal_of_operatorSchur h x)

/-- **Single-block Schur is exactly the operator bound.**  So the block
compiler, taken at its coarsest partition, asks for nothing more and nothing
less than a truncation-uniform `ℓ² → ℓ²` bound on the outer-cell Gram operator
at the retained output. -/
theorem blockAlmostOrthogonal_single_iff {nu A : ℝ} (hnu : 0 < nu) (hA : 0 ≤ A)
    (modes : Finset Wave) (G : Wave → Fin 3 → ℂ) (k : Wave) :
    BlockAlmostOrthogonal nu modes ({()} : Finset Unit) (fun _ => ()) G k A
      ↔ GramOperatorBound nu modes G k A := by
  classical
  have hfil : {p ∈ modes | (fun _ => ()) p = ()} = modes :=
    Finset.filter_true_of_mem fun p _ => rfl
  have hmass : blockMass modes (fun _ => ()) G () ^ 2 = ∑ p ∈ modes, nsq (G p) / wsq p := by
    rw [sq_blockMass, hfil]
  have hmassnn : 0 ≤ blockMass modes (fun _ => ()) G () := Real.sqrt_nonneg _
  have hprod : blockMass modes (fun _ => ()) G () * blockMass modes (fun _ => ()) G ()
      = ∑ p ∈ modes, nsq (G p) / wsq p := by
    rw [← sq, hmass]
  constructor
  · intro h
    exact gramOperatorBound_of_blockAlmostOrthogonal hnu modes _ _ G k h
  · intro h
    refine ⟨fun _ _ => Finset.mem_singleton_self _, fun _ _ => A, fun _ _ => hA,
      fun _ _ => rfl, ?_, ?_⟩
    · intro P _ Q _
      have hP : P = () := rfl
      have hQ : Q = () := rfl
      rw [hfil]
      have heq : (1 / (2 * nu)) * (A * (blockMass modes (fun _ => ()) G P *
          blockMass modes (fun _ => ()) G Q))
          = A * (∑ p ∈ modes, nsq (G p) / wsq p) / (2 * nu) := by
        rw [hP, hQ, hprod]
        field_simp
      rw [heq]
      exact h
    · intro P _
      simp

/-- The remainder budget at one output, from the operator bound alone. -/
theorem integral_nsq_Fs_le_gramBound {nu A : ℝ} (hnu : 0 < nu) (modes : Finset Wave)
    (N u : Wave → Fin 3 → ℂ) (k : Wave) (B : Wave → ℝ)
    (hk : wsq k ≠ 0) (hp : ∀ p ∈ modes, wsq p ≠ 0) (hA : 0 ≤ A)
    (hN : ∀ p ∈ modes, nrm (N p) ≤ 3 * wlen p * B p)
    (hGB : GramOperatorBound nu modes (fun p => outerCellVec N u k p) k A) :
    (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes N u k))
      ≤ 9 * A * (∑ p ∈ modes, B p ^ 2 * nsq (u (k - p))) / (2 * nu) := by
  have hrate : ∀ p ∈ modes, 0 < viscousPairRate nu p (k - p) := by
    intro p hpm
    rw [viscousPairRate]
    have h1 : 0 < wsq p := lt_of_le_of_ne (wsq_nonneg' p) (Ne.symm (hp p hpm))
    have h2 : 0 ≤ wsq (k - p) := wsq_nonneg' (k - p)
    exact mul_pos hnu (by linarith)
  rw [integral_nsq_Fs_eq_resForm modes N u k hrate]
  have hprofile : ∑ p ∈ modes, nsq (outerCellVec N u k p) / wsq p
      ≤ ∑ p ∈ modes, 9 * (B p ^ 2 * nsq (u (k - p))) :=
    Finset.sum_le_sum fun p hpm => cell_ratio_sq_le B hk (hp p hpm) (hN p hpm)
  have hfac : ∑ p ∈ modes, 9 * (B p ^ 2 * nsq (u (k - p)))
      = 9 * ∑ p ∈ modes, B p ^ 2 * nsq (u (k - p)) := by rw [Finset.mul_sum]
  have h2nu : 0 < 2 * nu := by linarith
  have hstep : A * (∑ p ∈ modes, nsq (outerCellVec N u k p) / wsq p) / (2 * nu)
      ≤ 9 * A * (∑ p ∈ modes, B p ^ 2 * nsq (u (k - p))) / (2 * nu) := by
    refine (div_le_div_iff_of_pos_right h2nu).mpr ?_
    have hml := mul_le_mul_of_nonneg_left hprofile hA
    rw [hfac] at hml
    linarith [hml]
  have hGB' : ∑ p ∈ modes, ∑ q ∈ modes,
      (herm (outerCellVec N u k p) (outerCellVec N u k q)).re
        / (viscousPairRate nu p (k - p) + viscousPairRate nu q (k - q))
      ≤ A * (∑ p ∈ modes, nsq (outerCellVec N u k p) / wsq p) / (2 * nu) := hGB
  linarith [hGB', hstep]

/-- The summed remainder budget, from the operator bound at each output. -/
theorem sum_integral_nsq_Fs_le_gramBound {nu A : ℝ} (hnu : 0 < nu)
    (modes outs : Finset Wave) (N u : Wave → Fin 3 → ℂ) (B : Wave → ℝ)
    (hk : ∀ k ∈ outs, wsq k ≠ 0) (hp : ∀ p ∈ modes, wsq p ≠ 0) (hA : 0 ≤ A)
    (hN : ∀ p ∈ modes, nrm (N p) ≤ 3 * wlen p * B p)
    (hsupp : ∀ b ∉ modes, u b = fun _ => 0)
    (hGB : ∀ k ∈ outs, GramOperatorBound nu modes (fun p => outerCellVec N u k p) k A) :
    ∑ k ∈ outs, (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes N u k))
      ≤ 9 * A * ((∑ p ∈ modes, B p ^ 2) * energy modes u) / (2 * nu) := by
  classical
  have h2nu : 0 < 2 * nu := by linarith
  have hpt : ∑ k ∈ outs, (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes N u k))
      ≤ ∑ k ∈ outs, 9 * A * (∑ p ∈ modes, B p ^ 2 * nsq (u (k - p))) / (2 * nu) :=
    Finset.sum_le_sum fun k hkm =>
      integral_nsq_Fs_le_gramBound hnu modes N u k B (hk k hkm) hp hA hN (hGB k hkm)
  have hswap : ∑ k ∈ outs, (∑ p ∈ modes, B p ^ 2 * nsq (u (k - p)))
      = ∑ p ∈ modes, B p ^ 2 * ∑ k ∈ outs, nsq (u (k - p)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => by rw [Finset.mul_sum]
  have hshift : ∀ p : Wave, ∑ k ∈ outs, nsq (u (k - p)) ≤ energy modes u := by
    intro p
    have hs := sum_shift_le modes outs (fun q => nsq (u q)) (fun q => nsq_nonneg _)
      (by intro q hq; simp [hsupp q hq, nsq]) p
    simpa [energy] using hs
  have htail : ∑ p ∈ modes, B p ^ 2 * ∑ k ∈ outs, nsq (u (k - p))
      ≤ (∑ p ∈ modes, B p ^ 2) * energy modes u := by
    have hle : ∑ p ∈ modes, B p ^ 2 * ∑ k ∈ outs, nsq (u (k - p))
        ≤ ∑ p ∈ modes, B p ^ 2 * energy modes u :=
      Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hshift p) (sq_nonneg _)
    calc ∑ p ∈ modes, B p ^ 2 * ∑ k ∈ outs, nsq (u (k - p))
        ≤ ∑ p ∈ modes, B p ^ 2 * energy modes u := hle
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

/-- The physical `‖u‖_A²E²` remainder bound, from the operator bound alone. -/
theorem sum_integral_nsq_Fs_le_gramBound_wiener {nu A : ℝ} (hnu : 0 < nu)
    (modes outs : Finset Wave) (u : Wave → Fin 3 → ℂ)
    (hk : ∀ k ∈ outs, wsq k ≠ 0) (hp : ∀ p ∈ modes, wsq p ≠ 0) (hA : 0 ≤ A)
    (hdiv : ∀ c : Wave, dotb (wC c) (u c) = 0)
    (hsupp : ∀ b ∉ modes, u b = fun _ => 0)
    (hGB : ∀ k ∈ outs, GramOperatorBound nu modes
      (fun p => outerCellVec (innerForcing modes u) u k p) k A) :
    ∑ k ∈ outs, (∫ s in Ioi (0 : ℝ), nsq (Fs nu s modes (innerForcing modes u) u k))
      ≤ 9 * A * (wienerA modes u ^ 2 * energy modes u ^ 2) / (2 * nu) := by
  classical
  set B : Wave → ℝ := fun p => ∑ a ∈ modes, nrm (u a) * nrm (u (p - a)) with hBdef
  have hN : ∀ p ∈ modes, nrm (innerForcing modes u p) ≤ 3 * wlen p * B p := by
    intro p hpm
    exact nrm_innerForcing_le_conv modes (hp p hpm) hdiv
  have hmain := sum_integral_nsq_Fs_le_gramBound hnu modes outs (innerForcing modes u) u B
    hk hp hA hN hsupp hGB
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

/-- **The critical spacetime consumer, from the operator bound alone.**  This is
the final form of the conditional result: the only analytic input is a
truncation-uniform `ℓ² → ℓ²` bound for the outer-cell Gram operator at each
retained output, and the conclusion is the critical Wiener budget. -/
theorem spacetime_remainder_le_critical_of_gramBound {nu A E₀ : ℝ} (hnu : 0 < nu)
    (modes outs : Finset Wave) (u : ℝ → Wave → Fin 3 → ℂ) (t₀ t₁ : ℝ)
    (ht : t₀ ≤ t₁) (hA : 0 ≤ A) (hE₀ : 0 ≤ E₀)
    (hk : ∀ k ∈ outs, wsq k ≠ 0) (hp : ∀ p ∈ modes, wsq p ≠ 0)
    (hdiv : ∀ t : ℝ, ∀ c : Wave, dotb (wC c) (u t c) = 0)
    (hsupp : ∀ t : ℝ, ∀ b ∉ modes, u t b = fun _ => 0)
    (hGB : ∀ t ∈ Set.Icc t₀ t₁, ∀ k ∈ outs, GramOperatorBound nu modes
      (fun p => outerCellVec (innerForcing modes (u t)) (u t) k p) k A)
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
    have h1 := sum_integral_nsq_Fs_le_gramBound_wiener hnu modes outs (u t) hk hp hA
      (hdiv t) (hsupp t) (hGB t htm)
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

/-! ## 8.  What a physical producer must supply, and what will not do

Two complementary results delimit the shape of an admissible producer of the
operator bound.  Negatively: comparable-shell (dyadic collar) localization alone
never yields a constant, because a collar contains arbitrarily many modes and a
coherent family on them forces the trivial Schur constant — so a producer must
supply *decay* in some further geometric coordinate, not merely finite overlap.
Positively: decay in the difference variable is enough, and it is enough
uniformly in the truncation: a translation-invariant coherence kernel with
finite total mass produces the Schur condition with `A` its total mass. -/

/-- The lattice vector `(a,0,0)`. -/
def axisWave (a : ℤ) : Wave := fun i => if i = 0 then a else 0

theorem axisWave_injective : Function.Injective axisWave := by
  intro a b h
  have h0 := congrFun h 0
  simpa [axisWave] using h0

theorem wsq_axisWave (a : ℤ) : wsq (axisWave a) = (a : ℝ) ^ 2 := by
  simp [wsq, axisWave]

/-- **Comparable-shell localization alone is insufficient.**  For every `N`
there is a family of at least `N` nonzero modes whose lengths are pairwise
comparable (`|p|² ≤ 4|q|²`, i.e. all inside one dyadic collar) and whose cells
are perfectly coherent, so every admissible Schur constant is at least `N`.
A producer therefore has to exhibit decay in a coordinate beyond the shell. -/
theorem comparable_shell_localization_insufficient (N : ℕ) :
    ∃ (modes : Finset Wave) (v : Fin 3 → ℂ),
      N ≤ modes.card ∧ nsq v ≠ 0 ∧ (0 : Wave) ∉ modes ∧
      (∀ p ∈ modes, ∀ q ∈ modes, wsq p ≤ 4 * wsq q) ∧
      (∀ A : ℝ, AlmostOrthogonal modes (fun _ => v) A → (N : ℝ) ≤ A) := by
  classical
  set n : ℤ := (N : ℤ) + 1 with hn
  set modes : Finset Wave := (Finset.Icc n (2 * n)).image axisWave with hmodes
  have hnpos : 0 < n := by positivity
  have hmem : ∀ p ∈ modes, ∃ a : ℤ, n ≤ a ∧ a ≤ 2 * n ∧ p = axisWave a := by
    intro p hp
    rw [hmodes, Finset.mem_image] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    rw [Finset.mem_Icc] at ha
    exact ⟨a, ha.1, ha.2, rfl⟩
  have hcard : modes.card = N + 2 := by
    rw [hmodes, Finset.card_image_of_injective _ axisWave_injective, Int.card_Icc, hn]
    simp
    omega
  have hne : modes.Nonempty := by
    refine ⟨axisWave n, ?_⟩
    rw [hmodes, Finset.mem_image]
    exact ⟨n, by rw [Finset.mem_Icc]; omega, rfl⟩
  refine ⟨modes, e0, by omega, by simp [nsq, e0], ?_, ?_, ?_⟩
  · intro h0
    obtain ⟨a, ha1, _, ha3⟩ := hmem 0 h0
    have hz : (0 : Wave) 0 = a := by rw [ha3]; simp [axisWave]
    simp at hz
    omega
  · intro p hp q hq
    obtain ⟨a, ha1, ha2, rfl⟩ := hmem p hp
    obtain ⟨b, hb1, hb2, rfl⟩ := hmem q hq
    rw [wsq_axisWave, wsq_axisWave]
    have h1 : (a : ℝ) ≤ 2 * (b : ℝ) := by
      have hab : a ≤ 2 * b := le_trans ha2 (by omega)
      exact_mod_cast hab
    have h2 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb1.trans_lt' hnpos
    have h3 : (0 : ℝ) ≤ (a : ℝ) := by
      have ha : (0 : ℤ) ≤ a := le_of_lt (hnpos.trans_le ha1)
      exact_mod_cast ha
    nlinarith
  · intro A hA
    have hc := card_le_of_almostOrthogonal_coherent (modes := modes) (v := e0)
      (by simp [nsq, e0]) hne hA
    rw [hcard] at hc
    have hNle : (N : ℝ) ≤ ((N + 2 : ℕ) : ℝ) := by push_cast; linarith
    linarith

/-- **A producer template: decay in the difference variable.**  If the pairwise
coherence of the cells is dominated by a symmetric, nonnegative kernel of the
difference `p − q` supported in a finite set `D` of total mass at most `A`, then
the family is almost orthogonal with constant `A` — and `A` depends only on the
kernel, not on the mode set, hence not on the truncation.  This is the shape a
physical angular, helical or phase producer has to deliver: not finite overlap,
but a summable profile in an extra coordinate. -/
theorem almostOrthogonal_of_shiftInvariant_kernel (modes D : Finset Wave)
    (G : Wave → Fin 3 → ℂ) (w : Wave → ℝ) (A : ℝ)
    (hwnn : ∀ d, 0 ≤ w d) (hwsym : ∀ d, w (-d) = w d) (hwsupp : ∀ d ∉ D, w d = 0)
    (hsum : ∑ d ∈ D, w d ≤ A)
    (hcoh : ∀ p ∈ modes, ∀ q ∈ modes,
      |(herm (G p) (G q)).re| ≤ w (p - q) * (nrm (G p) * nrm (G q))) :
    AlmostOrthogonal modes G A := by
  have hsw : ∀ p q : Wave, w (p - q) = w (q - p) := by
    intro p q
    have hneg : -(q - p) = p - q := by abel
    rw [← hwsym (q - p), hneg]
  refine ⟨fun p q => w (p - q), fun p q => hwnn _, ?_, hcoh, ?_⟩
  · intro p q
    show w (p - q) = w (q - p)
    exact hsw p q
  · intro p _
    have hshift := sum_shift_le D modes w hwnn hwsupp p
    have hcongr : ∑ q ∈ modes, w (p - q) = ∑ q ∈ modes, w (q - p) :=
      Finset.sum_congr rfl fun q _ => hsw p q
    rw [hcongr]
    exact le_trans hshift hsum

end ClayNS.Schur

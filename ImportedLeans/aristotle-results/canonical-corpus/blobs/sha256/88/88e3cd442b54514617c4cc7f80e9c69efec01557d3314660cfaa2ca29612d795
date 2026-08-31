/-
# Row A1a — the shell coefficient from the *literal* one-loop trace

Everything upstream of this file bounds the Gaussian sector through a hypothesis
of the shape

    |V_{αβ;ρ}(q)|² / 2  ≤  I_j(q)                                        (†)

with `I_j` the one-loop integrand, left abstract.  This file replaces `I_j` by
the literal object — the CMP109-shaped one-loop trace

    I(q) = betaTrace G(q) V(q) V(q) S(q) = ½Tr(GVGV) − ½Tr(GS)

built on the *constrained* lattice propagator `G(q) = (q̂²)⁻¹P(q)` of
`TransverseSymbol.constrainedPropagator_rankOne` and on a seagull `S = −WᵀW`
(the paramagnetic sign, `SeagullSign`) — and asks what survives.

Two things come out, and the first one is negative.

* **(†) is false for the literal integrand on the mixed-component patch.**
  `mixedPatch_entry_hypothesis_fails` exhibits a point of `mixedPatch (1/16)` —
  the point `x = (1/4, 0, 1/2, 1/2)`, which lies in the box for every admissible
  half-width — at which the literal one-loop integrand *vanishes identically*
  while the mixed component of the first variation is at least `1/5`.  The
  reason is the lattice Ward identity of `WardTransverseVertex`: the constrained
  propagator conjugates the vertex with the transverse projector, and
  `P V P = sin(2πx_ρ)·P` vanishes at `x_ρ = 0`, which is exactly where the
  mixed-component patch sits.  So the mixed-component route, correct as an
  estimate for the symbol itself, cannot be fed into the literal Gaussian
  coefficient.  This is a source-identification obstruction, not an estimate
  that can be improved.

* **The Ward identity supplies a different, working patch.**  The same identity
  says the transverse conjugate is `sin(2πx_ρ)·P` plus the Lorentz-diagonal
  averaging/projection contribution.  Choosing the momentum box `wardPatch`,
  where `sin(2πx_1) ≥ 1/2` and the projector's `(0,0)` entry is at least `1/2`,
  gives a *computed* floor for the literal one-loop integrand,
  `I(q) ≥ 1/32768`, and hence the shell floor

      β_j(g) ≥ 1/16777216 > 0

  for every shell index and admissible history (`A1_beta_pos_ward`).

**Honest status — Row A1 is not closed.**  The remaining hypotheses of
`A1_beta_pos_ward` are: integrability of the literal one-loop integrand on the
cell; a bound `d ≤ 1/4` on the *Lorentz-diagonal* entries of the averaging and
constrained-projection background variations (these do not vanish — only their
mixed entries do — and they enter the transverse conjugate); and the five
remainder-channel majorants.  None of them is an identification of one object
with another, and none is a postulate; the diagonal bound `d ≤ 1/4` is a genuine
analytic obligation on Bałaban's averaging operator.  The scoreboard is
unchanged: `A, B, C, D` open, frozen research count 4.
-/
import RequestProject.YangMills.WardTransverseVertex
import RequestProject.YangMills.A1SourceObjects

namespace YangMills

open Real Matrix Finset MeasureTheory Set

/-! ## 1. The literal one-loop integrand -/

/-- **The literal one-loop integrand.**  The propagator is the constrained
lattice symbol, the two first variations are the source matrix `Vm`, and the
seagull is `−WᵀW` — the paramagnetic shape, built into the definition rather
than assumed. -/
noncomputable def literalOneLoopIntegrand (Vm Wm : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (q : Fin 4 → ℝ) : ℝ :=
  betaTrace (latticeSymbolOf q) (Vm q) (Vm q) (-((Wm q)ᵀ * Wm q))

/-- **Any entry of the reduced bubble kernel is a floor for the literal
integrand.** -/
theorem literalOneLoopIntegrand_ge_entry_sq
    {Vm Wm : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {q : Fin 4 → ℝ}
    (hq : phatSq q ≠ 0) (hV : (Vm q)ᵀ = Vm q) (i j : Fin 4) :
    1 / 2 * ((latticeGramFactor q * Vm q * (latticeGramFactor q)ᵀ) i j) ^ 2
      ≤ literalOneLoopIntegrand Vm Wm q :=
  betaTrace_ge_entry_sq (latticeSymbol_eq_gram q hq) hV rfl i j

/-- **The literal integrand is nonnegative** wherever the propagator exists:
the bubble is a sum of squares and the seagull has the paramagnetic sign. -/
theorem literalOneLoopIntegrand_nonneg
    {Vm Wm : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {q : Fin 4 → ℝ}
    (hq : phatSq q ≠ 0) (hV : (Vm q)ᵀ = Vm q) :
    0 ≤ literalOneLoopIntegrand Vm Wm q := by
  have h := literalOneLoopIntegrand_ge_entry_sq (Vm := Vm) (Wm := Wm) hq hV 0 0
  nlinarith [sq_nonneg ((latticeGramFactor q * Vm q * (latticeGramFactor q)ᵀ) 0 0)]

/-! ## 2. The source first-variation matrix -/

/-- A matrix with no off-diagonal entries is symmetric. -/
theorem transpose_of_offdiag_zero {n : Type*} {D : Matrix n n ℝ}
    (hD : ∀ a b, a ≠ b → D a b = 0) : Dᵀ = D := by
  ext a b
  rcases eq_or_ne a b with h | h
  · rw [h]; rfl
  · rw [Matrix.transpose_apply, hD b a (Ne.symm h), hD a b h]

theorem wilsonBgZeroMatrix_transpose (x : Fin 4 → ℝ) (rho : Fin 4) :
    (wilsonBgZeroMatrix x rho)ᵀ = wilsonBgZeroMatrix x rho := by
  rw [wilsonBgZeroMatrix_eq]
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.transpose_add, vecMulVec_transpose_swap]
  rw [add_comm (Matrix.vecMulVec (basisVec rho) (phatVec x))]

theorem gaugeVariationMatrix_transpose (f : ℝ) (k : Fin 4 → ℝ) (rho : Fin 4) :
    (gaugeVariationMatrix f k rho)ᵀ = gaugeVariationMatrix f k rho := by
  rw [gaugeVariationMatrix_eq]
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_add,
    vecMulVec_transpose_swap]
  rw [add_comm (Matrix.vecMulVec (basisVec rho) k)]

/-- **The literal constrained first variation as a Lorentz matrix.**  The Wilson
cubic vertex, the computed gauge-projection variation, and the Lorentz-diagonal
averaging/constrained-projection variation `D`. -/
noncomputable def sourceVariationMatrix (f : ℝ) (rho : Fin 4)
    (D : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  wilsonBgZeroMatrix x rho + gaugeVariationMatrix f (phatVec x) rho + D x

theorem sourceVariationMatrix_transpose {f : ℝ} {rho : Fin 4}
    {D : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    (hD : ∀ x a b, a ≠ b → D x a b = 0) (x : Fin 4 → ℝ) :
    (sourceVariationMatrix f rho D x)ᵀ = sourceVariationMatrix f rho D x := by
  rw [sourceVariationMatrix, Matrix.transpose_add, Matrix.transpose_add,
    wilsonBgZeroMatrix_transpose, gaugeVariationMatrix_transpose,
    transpose_of_offdiag_zero (hD x)]

/-- The `(0,1)` entry of the source variation matrix is the mixed component of
`MixedComponentPatch`, when the diagonal piece is absent there. -/
theorem sourceVariationMatrix_mixed_entry (f : ℝ)
    {D : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    (hD : ∀ x a b, a ≠ b → D x a b = 0) (x : Fin 4 → ℝ) :
    sourceVariationMatrix f 1 D x 0 1 = mixedConstrainedSymbol f x 0 1 := by
  simp only [sourceVariationMatrix, Matrix.add_apply, wilsonBgZeroMatrix, gaugeVariationMatrix,
    Matrix.of_apply, hD x 0 1 (by decide), add_zero, mixedConstrainedSymbol]
  rfl

/-! ## 3. The reduced bubble entry of the source variation -/

theorem transverseProjector_diag (u : Fin 4 → ℝ) (i : Fin 4) :
    transverseProjector u i i = 1 - (normSqVec u)⁻¹ * (u i * u i) := by
  simp [transverseProjector, Matrix.vecMulVec_apply]

/-- **The reduced bubble entry of the literal source variation.**  Combining the
Gram form of the constrained symbol with the Ward identity: the `(i,i)` entry of
`C V Cᵀ` is `(q̂²)⁻¹` times the transverse conjugate, which is at least
`P_{ii}(sin(2πx_ρ) − d)`. -/
theorem sourceVariation_bubble_entry_ge {f d : ℝ} {rho : Fin 4}
    {D : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    (hD : ∀ x a b, a ≠ b → D x a b = 0) (hd : ∀ x a, |D x a a| ≤ d)
    {x : Fin 4 → ℝ} (hx : phatSq x ≠ 0) (hx0 : 0 < phatSq x) (i : Fin 4) :
    (phatSq x)⁻¹ * ((transverseProjector (phatVec x)) i i * (sinAtom (2 * x rho) - d))
      ≤ (latticeGramFactor x * sourceVariationMatrix f rho D x
          * (latticeGramFactor x)ᵀ) i i := by
  rw [latticeReducedBubble_eq x hx0.le]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hmain := transverseConjugate_diag_ge (x := x) hx rho (f := f) (d := d) (D := D x)
    (hD x) (hd x) i
  have hinv : 0 < (phatSq x)⁻¹ := inv_pos.mpr hx0
  exact mul_le_mul_of_nonneg_left hmain hinv.le

/-! ## 4. The Ward patch -/

/-- **The Ward patch.**  The background direction `ρ = 1` carries a normalised
momentum in `[1/8, 1/4]`, where `sin(2πx_1) ≥ 1/2`; the direction `0` carries a
smaller momentum, which keeps the transverse projector's `(0,0)` entry above
`1/2`; the two spectator directions are free. -/
def wardPatch : Set (Fin 4 → ℝ) :=
  Set.univ.pi fun mu => if mu = 0 then Icc (0 : ℝ) (1 / 8)
    else if mu = 1 then Icc (1 / 8 : ℝ) (1 / 4) else Icc (0 : ℝ) (1 / 2)

theorem measurableSet_wardPatch : MeasurableSet wardPatch := by
  refine MeasurableSet.univ_pi fun mu => ?_
  by_cases h0 : mu = 0
  · simp [h0, measurableSet_Icc]
  · by_cases h1 : mu = 1 <;> simp [h0, h1, measurableSet_Icc]

theorem wardPatch_mem_zero {x : Fin 4 → ℝ} (hx : x ∈ wardPatch) :
    x 0 ∈ Icc (0 : ℝ) (1 / 8) := by simpa [wardPatch] using hx 0 (mem_univ 0)

theorem wardPatch_mem_one {x : Fin 4 → ℝ} (hx : x ∈ wardPatch) :
    x 1 ∈ Icc (1 / 8 : ℝ) (1 / 4) := by simpa [wardPatch] using hx 1 (mem_univ 1)

theorem wardPatch_mem_spectator {x : Fin 4 → ℝ} (hx : x ∈ wardPatch) (mu : Fin 4)
    (h0 : mu ≠ 0) (h1 : mu ≠ 1) : x mu ∈ Icc (0 : ℝ) (1 / 2) := by
  simpa [wardPatch, h0, h1] using hx mu (mem_univ mu)

theorem wardPatch_subset_momentumCell : wardPatch ⊆ momentumCell := by
  refine Set.pi_mono fun mu _ => ?_
  by_cases hz : mu = 0
  · simp only [hz]
    exact Icc_subset_Icc le_rfl (by norm_num)
  · by_cases ho : mu = 1
    · simp only [ho, if_neg (by decide : ¬((1 : Fin 4) = 0))]
      exact Icc_subset_Icc (by norm_num) (by norm_num)
    · simp only [if_neg hz, if_neg ho]
      exact subset_rfl

theorem wardPatch_subset_puncturedCell : wardPatch ⊆ puncturedCell := by
  intro x hx
  refine ⟨wardPatch_subset_momentumCell hx, ?_⟩
  intro hzero
  have hx1 : x 1 ∈ Icc (1 / 8 : ℝ) (1 / 4) := wardPatch_mem_one hx
  have h0 : x 1 = 0 := by
    have : x = (0 : Fin 4 → ℝ) := hzero
    rw [this]; rfl
  have := hx1.1
  rw [h0] at this
  linarith

theorem wardPatch_volume : volume wardPatch = ENNReal.ofReal (1 / 256 : ℝ) := by
  rw [wardPatch, volume_pi_pi, Fin.prod_univ_four]
  rw [if_pos rfl, if_neg (by decide : ¬((1 : Fin 4) = 0)), if_pos rfl,
    if_neg (by decide : ¬((2 : Fin 4) = 0)), if_neg (by decide : ¬((2 : Fin 4) = 1)),
    if_neg (by decide : ¬((3 : Fin 4) = 0)), if_neg (by decide : ¬((3 : Fin 4) = 1))]
  simp only [Real.volume_Icc]
  rw [show (1 / 8 - 0 : ℝ) = 1 / 8 by ring, show (1 / 4 - 1 / 8 : ℝ) = 1 / 8 by ring,
    show (1 / 2 - 0 : ℝ) = 1 / 2 by ring]
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1 / 8),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1 / 8 * (1 / 8)),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1 / 8 * (1 / 8) * (1 / 2))]
  norm_num

theorem wardPatch_volume_real : (volume wardPatch).toReal = 1 / 256 := by
  rw [wardPatch_volume, ENNReal.toReal_ofReal (by norm_num)]

theorem wardPatch_volume_ne_top : volume wardPatch ≠ ⊤ := by
  rw [wardPatch_volume]; exact ENNReal.ofReal_ne_top

/-! ## 5. The estimates on the Ward patch -/

theorem sinAtom_mono {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    sinAtom a ≤ sinAtom b := by
  have hpi := Real.pi_pos
  refine Real.strictMonoOn_sin.monotoneOn ⟨by nlinarith, by nlinarith⟩
    ⟨by nlinarith, by nlinarith⟩ (by nlinarith)

/-- On the Ward patch the Ward factor is at least `1/2`. -/
theorem wardPatch_sinAtom_ge {x : Fin 4 → ℝ} (hx : x ∈ wardPatch) :
    (1 : ℝ) / 2 ≤ sinAtom (2 * x 1) := by
  obtain ⟨hl, hu⟩ := wardPatch_mem_one hx
  have h := two_mul_le_sinAtom (x := 2 * x 1) (by linarith) (by linarith)
  linarith

/-- On the Ward patch the lattice momentum square is positive. -/
theorem wardPatch_phatSq_pos {x : Fin 4 → ℝ} (hx : x ∈ wardPatch) : 0 < phatSq x := by
  obtain ⟨hl, hu⟩ := wardPatch_mem_one hx
  have h := two_mul_le_sinAtom (x := x 1) (by linarith) (by linarith)
  have hp : (1 : ℝ) / 2 ≤ phat (x 1) := by rw [phat]; linarith
  have hterm : (0 : ℝ) < (phat (x 1)) ^ 2 := by nlinarith
  have hsum : phatSq x = (phat (x 0)) ^ 2 + (phat (x 1)) ^ 2 + (phat (x 2)) ^ 2
      + (phat (x 3)) ^ 2 := by rw [phatSq, Fin.sum_univ_four]
  rw [hsum]
  nlinarith [sq_nonneg (phat (x 0)), sq_nonneg (phat (x 2)), sq_nonneg (phat (x 3))]

/-- On the Ward patch the lattice momentum square is at most `16`. -/
theorem wardPatch_phatSq_le (x : Fin 4 → ℝ) : phatSq x ≤ 16 := by
  have hb : ∀ mu : Fin 4, (phat (x mu)) ^ 2 ≤ 4 := by
    intro mu
    have h1 : |Real.sin (π * x mu)| ≤ 1 := Real.abs_sin_le_one _
    have : (Real.sin (π * x mu)) ^ 2 ≤ 1 := by
      nlinarith [abs_nonneg (Real.sin (π * x mu)), sq_abs (Real.sin (π * x mu))]
    rw [phat, sinAtom]
    nlinarith
  have hsum : phatSq x = (phat (x 0)) ^ 2 + (phat (x 1)) ^ 2 + (phat (x 2)) ^ 2
      + (phat (x 3)) ^ 2 := by rw [phatSq, Fin.sum_univ_four]
  rw [hsum]
  have := hb 0; have := hb 1; have := hb 2; have := hb 3
  linarith

/-- On the Ward patch the transverse projector's `(0,0)` entry is at least
`1/2`: the direction `0` carries less momentum than the direction `1`. -/
theorem wardPatch_projector_diag_ge {x : Fin 4 → ℝ} (hx : x ∈ wardPatch) :
    (1 : ℝ) / 2 ≤ (transverseProjector (phatVec x)) 0 0 := by
  obtain ⟨h0l, h0u⟩ := wardPatch_mem_zero hx
  obtain ⟨h1l, h1u⟩ := wardPatch_mem_one hx
  have hmono : sinAtom (x 0) ≤ sinAtom (x 1) :=
    sinAtom_mono h0l (by linarith) (by linarith)
  have hnn : 0 ≤ sinAtom (x 0) := by
    have := two_mul_le_sinAtom (x := x 0) h0l (by linarith)
    linarith
  have hsq : (phat (x 0)) ^ 2 ≤ (phat (x 1)) ^ 2 := by
    rw [phat, phat]; nlinarith
  have hpos := wardPatch_phatSq_pos hx
  have hsum : phatSq x = (phat (x 0)) ^ 2 + (phat (x 1)) ^ 2 + (phat (x 2)) ^ 2
      + (phat (x 3)) ^ 2 := by rw [phatSq, Fin.sum_univ_four]
  have hhalf : 2 * (phat (x 0)) ^ 2 ≤ phatSq x := by
    rw [hsum]; nlinarith [sq_nonneg (phat (x 2)), sq_nonneg (phat (x 3))]
  rw [transverseProjector_diag, normSqVec_phatVec]
  have hentry : phatVec x 0 * phatVec x 0 = (phat (x 0)) ^ 2 := by
    simp [phatVec]; ring
  rw [hentry]
  have hle : (phatSq x)⁻¹ * (phat (x 0)) ^ 2 ≤ 1 / 2 := by
    have h2 : (phat (x 0)) ^ 2 ≤ phatSq x * (1 / 2) := by linarith
    calc (phatSq x)⁻¹ * (phat (x 0)) ^ 2
        ≤ (phatSq x)⁻¹ * (phatSq x * (1 / 2)) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hpos.le)
      _ = 1 / 2 := by field_simp
  linarith

/-! ## 6. The floor for the literal integrand on the Ward patch -/

/-- **The computed floor for the literal one-loop integrand.**  No entry bound
is assumed: the Wilson piece enters through the Ward identity, the gauge piece is
annihilated by the transverse projector, and the Lorentz-diagonal averaging and
constrained-projection variations are paid for by `d ≤ 1/4`. -/
theorem literalOneLoopIntegrand_wardPatch_floor {f d : ℝ}
    {D : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {Wm : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    (hD : ∀ x a b, a ≠ b → D x a b = 0) (hd : ∀ x a, |D x a a| ≤ d) (hd4 : d ≤ 1 / 4)
    {x : Fin 4 → ℝ} (hx : x ∈ wardPatch) :
    (1 : ℝ) / 32768 ≤ literalOneLoopIntegrand (sourceVariationMatrix f 1 D) Wm x := by
  have hpos := wardPatch_phatSq_pos hx
  have hne : phatSq x ≠ 0 := ne_of_gt hpos
  have hle16 := wardPatch_phatSq_le x
  have hP := wardPatch_projector_diag_ge hx
  have hsin := wardPatch_sinAtom_ge hx
  have hentry := sourceVariation_bubble_entry_ge (f := f) (d := d) (rho := 1) hD hd hne hpos 0
  -- the transverse conjugate is at least `1/8`
  have hbig : (1 : ℝ) / 8
      ≤ (transverseProjector (phatVec x)) 0 0 * (sinAtom (2 * x 1) - d) := by
    nlinarith
  have hinv : (1 : ℝ) / 16 ≤ (phatSq x)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hpos]
    linarith
  have hprod : (1 : ℝ) / 128
      ≤ (phatSq x)⁻¹ * ((transverseProjector (phatVec x)) 0 0 * (sinAtom (2 * x 1) - d)) := by
    have hnn : (0 : ℝ) ≤ (transverseProjector (phatVec x)) 0 0 * (sinAtom (2 * x 1) - d) := by
      linarith
    nlinarith
  have hE : (1 : ℝ) / 128
      ≤ (latticeGramFactor x * sourceVariationMatrix f 1 D x * (latticeGramFactor x)ᵀ) 0 0 :=
    le_trans hprod hentry
  have hmain := literalOneLoopIntegrand_ge_entry_sq (Vm := sourceVariationMatrix f 1 D)
    (Wm := Wm) hne (sourceVariationMatrix_transpose hD x) 0 0
  nlinarith

/-! ## 7. The obstruction: the mixed-component patch is invisible to the literal
integrand -/

/-- The point of the mixed-component patch at which the Ward factor vanishes. -/
noncomputable def wardDegeneratePoint : Fin 4 → ℝ :=
  fun mu => if mu = 0 then 1 / 4 else if mu = 1 then 0 else 1 / 2

theorem wardDegeneratePoint_mem_mixedPatch {delta : ℝ} (h0 : 0 ≤ delta) :
    wardDegeneratePoint ∈ mixedPatch delta := by
  intro mu _
  by_cases hz : mu = 0
  · simp only [hz, wardDegeneratePoint]
    constructor <;> norm_num <;> linarith
  · by_cases ho : mu = 1
    · simp only [ho, if_neg (by decide : ¬((1 : Fin 4) = 0)), wardDegeneratePoint]
      norm_num
      exact h0
    · simp only [if_neg hz, if_neg ho, wardDegeneratePoint]
      norm_num
      exact h0

theorem phatSq_wardDegeneratePoint : phatSq wardDegeneratePoint = 10 := by
  have e0 : wardDegeneratePoint 0 = 1 / 4 := by simp [wardDegeneratePoint]
  have e1 : wardDegeneratePoint 1 = 0 := by simp [wardDegeneratePoint]
  have e2 : wardDegeneratePoint 2 = 1 / 2 := by simp [wardDegeneratePoint]
  have e3 : wardDegeneratePoint 3 = 1 / 2 := by simp [wardDegeneratePoint]
  have h0 : phat (wardDegeneratePoint 0) = Real.sqrt 2 := by
    rw [phat, sinAtom, e0, show π * (1 / 4 : ℝ) = π / 4 by ring, Real.sin_pi_div_four]
    ring
  have h1 : phat (wardDegeneratePoint 1) = 0 := by
    rw [phat, sinAtom, e1]; simp
  have h2 : phat (wardDegeneratePoint 2) = 2 := by
    rw [phat, sinAtom, e2, show π * (1 / 2 : ℝ) = π / 2 by ring, Real.sin_pi_div_two, mul_one]
  have h3 : phat (wardDegeneratePoint 3) = 2 := by
    rw [phat, sinAtom, e3, show π * (1 / 2 : ℝ) = π / 2 by ring, Real.sin_pi_div_two, mul_one]
  rw [phatSq, Fin.sum_univ_four, h0, h1, h2, h3]
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- **The literal one-loop integrand vanishes at the degenerate point.**  With
no Lorentz-diagonal contribution and no seagull, the transverse conjugate of the
first variation is `sin(2π·0)·P = 0`, so the whole bubble vanishes. -/
theorem literalOneLoopIntegrand_wardDegeneratePoint_eq_zero (f : ℝ) :
    literalOneLoopIntegrand (sourceVariationMatrix f 1 (fun _ => 0)) (fun _ => 0)
      wardDegeneratePoint = 0 := by
  set x := wardDegeneratePoint with hxdef
  have hne : phatSq x ≠ 0 := by rw [phatSq_wardDegeneratePoint]; norm_num
  have hV : (sourceVariationMatrix f 1 (fun _ => 0) x)ᵀ
      = sourceVariationMatrix f 1 (fun _ => 0) x :=
    sourceVariationMatrix_transpose (fun _ a b _ => rfl) x
  have hsin : sinAtom (2 * x 1) = 0 := by
    simp [hxdef, wardDegeneratePoint, sinAtom]
  have hconj : transverseProjector (phatVec x) * sourceVariationMatrix f 1 (fun _ => 0) x
      * transverseProjector (phatVec x) = 0 := by
    have hsplit : transverseProjector (phatVec x) * sourceVariationMatrix f 1 (fun _ => 0) x
        * transverseProjector (phatVec x)
        = transverseProjector (phatVec x) * wilsonBgZeroMatrix x 1 * transverseProjector (phatVec x)
          + transverseProjector (phatVec x) * gaugeVariationMatrix f (phatVec x) 1
              * transverseProjector (phatVec x)
          + transverseProjector (phatVec x) * (0 : Matrix (Fin 4) (Fin 4) ℝ)
              * transverseProjector (phatVec x) := by
      simp only [sourceVariationMatrix, Matrix.mul_add, Matrix.add_mul]
    rw [hsplit, transverseProjector_conj_wilsonBgZeroMatrix x 1 hne,
      transverseProjector_conj_gaugeVariationMatrix f x 1 hne, hsin]
    simp
  have hred : latticeGramFactor x * sourceVariationMatrix f 1 (fun _ => 0) x
      * (latticeGramFactor x)ᵀ = 0 := by
    have hnn : (0 : ℝ) ≤ phatSq x := by rw [phatSq]; positivity
    rw [latticeReducedBubble_eq x hnn, hconj, smul_zero]
  have hG : latticeSymbolOf x = (latticeGramFactor x)ᵀ * latticeGramFactor x :=
    latticeSymbol_eq_gram x hne
  have hbub := bubble_eq_frobenius (G := latticeSymbolOf x)
    (V := sourceVariationMatrix f 1 (fun _ => 0) x) (C := latticeGramFactor x) hG hV
  rw [literalOneLoopIntegrand, betaTrace, hbub, hred]
  simp

/-- **The entry hypothesis `(†)` fails for the literal one-loop integrand.**  At
the degenerate point of the mixed-component patch the literal integrand is zero
while the mixed component of the constrained first variation is at least `1/5`.
So no choice of source data of this shape can satisfy

    |V_{01;1}(q)|²/2 ≤ I(q)   on   mixedPatch (1/16),

and the mixed-component route cannot feed the literal Gaussian coefficient. -/
theorem mixedPatch_entry_hypothesis_fails {f : ℝ} (hf : |f| ≤ 1) :
    ∃ x ∈ mixedPatch (1 / 16 : ℝ),
      literalOneLoopIntegrand (sourceVariationMatrix f 1 (fun _ => 0)) (fun _ => 0) x = 0 ∧
      ¬ (|sourceVariationMatrix f 1 (fun _ => 0) x 0 1| ^ 2 / 2
          ≤ literalOneLoopIntegrand (sourceVariationMatrix f 1 (fun _ => 0)) (fun _ => 0) x) := by
  refine ⟨wardDegeneratePoint, wardDegeneratePoint_mem_mixedPatch (by norm_num),
    literalOneLoopIntegrand_wardDegeneratePoint_eq_zero f, ?_⟩
  rw [literalOneLoopIntegrand_wardDegeneratePoint_eq_zero f]
  rw [sourceVariationMatrix_mixed_entry (D := fun _ => 0) f (fun _ a b _ => rfl)]
  have hfloor := mixedPatch_floor_concrete hf
    (wardDegeneratePoint_mem_mixedPatch (delta := 1 / 16) (by norm_num))
  intro hcon
  nlinarith

/-! ## 8. The shell floor from the Ward patch -/

/-- **The Gaussian floor produced by the Ward patch.** -/
theorem cellGaussianFloor_of_wardPatch {I : (Fin 4 → ℝ) → ℝ} {c : ℝ}
    (hint : IntegrableOn I puncturedCell)
    (hnonneg : ∀ q ∈ puncturedCell, 0 ≤ I q)
    (hpatch : ∀ q ∈ wardPatch, c ≤ I q) :
    1 / 256 * c ≤ cellGaussianCoefficient I := by
  have hmain := setIntegral_ge_patch measurableSet_wardPatch
    wardPatch_subset_puncturedCell wardPatch_volume_ne_top hint
    measurableSet_puncturedCell hpatch (fun q hq => hnonneg q hq.1)
  rw [Measure.real, wardPatch_volume_real] at hmain
  rw [cellGaussianCoefficient, ← setIntegral_puncturedCell]
  exact hmain

/-- **Row A1a from the literal one-loop trace.**  The Gaussian sector is the
literal CMP109-shaped one-loop trace on the constrained lattice propagator; its
floor is computed from the lattice Ward identity, not assumed; the debt sector is
the computed five-channel sum.  For every shell index and admissible history,

    β_j(g) ≥ 1/16777216 > 0. -/
theorem A1_beta_pos_ward
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {Adm : (ℕ → ℝ) → Prop} {g : ℕ → ℝ} {f d : ℝ}
    {Dm : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {Wm : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {lamDet : ℕ → (ℕ → ℝ) → ι → ℝ} {lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ}
    {aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    {AInt AChart ALoc : ℕ → ℝ} {N : ℕ} {LamDet LamGauge theta : ℝ}
    (hD : ∀ j h x a b, a ≠ b → Dm j h x a b = 0)
    (hd : ∀ j h x a, |Dm j h x a a| ≤ d) (hd4 : d ≤ 1 / 4)
    (hintg : ∀ j h, IntegrableOn
      (literalOneLoopIntegrand (sourceVariationMatrix f 1 (Dm j h)) (Wm j h)) puncturedCell)
    (hLd : ∀ j h i, |lamDet j h i| ≤ LamDet)
    (hLg : ∀ j h i, |lamGauge j h i| ≤ LamGauge)
    (hAInt : ∀ j h n, |aInt j h n| ≤ AInt n)
    (hAChart : ∀ j h n, |aChart j h n| ≤ AChart n)
    (hALoc : ∀ j h n, |aLoc j h n| ≤ ALoc n)
    (hsmall : ∀ j h, Adm h → 0 ≤ h j ∧ h j ≤ theta ∧
        h j * LamDet ≤ theta ∧ h j * LamGauge ≤ theta)
    (hth : theta < 1) (hth0 : 0 ≤ theta)
    (hadm : Adm g) (hg0 : ∀ j, 0 ≤ g j)
    (hgg : ∀ j, g j ≤ criticalCoupling (1 / 8388608 : ℝ)
      (Cbeta (sourceChannelCoefficient (Fintype.card ι) (Fintype.card κ)
        LamDet LamGauge theta AInt AChart ALoc N)))
    (j : ℕ) :
    (1 : ℝ) / 16777216 ≤ shellBetaOfSources
      (fun j' h => literalOneLoopIntegrand (sourceVariationMatrix f 1 (Dm j' h)) (Wm j' h))
      lamDet lamGauge aInt aChart aLoc N j g := by
  have hfloor : HistoryUniformFloor (shellGaussianOfIntegrand
      (fun j' h => literalOneLoopIntegrand (sourceVariationMatrix f 1 (Dm j' h)) (Wm j' h)))
      Adm (1 / 8388608 : ℝ) := by
    intro j' h _
    have hnonneg : ∀ q ∈ puncturedCell,
        0 ≤ literalOneLoopIntegrand (sourceVariationMatrix f 1 (Dm j' h)) (Wm j' h) q := by
      intro q hq
      exact literalOneLoopIntegrand_nonneg (phatSq_ne_zero_of_mem_puncturedCell hq)
        (sourceVariationMatrix_transpose (hD j' h) q)
    have hpatch : ∀ q ∈ wardPatch,
        (1 : ℝ) / 32768
          ≤ literalOneLoopIntegrand (sourceVariationMatrix f 1 (Dm j' h)) (Wm j' h) q :=
      fun q hq => literalOneLoopIntegrand_wardPatch_floor (hD j' h) (hd j' h) hd4 hq
    have := cellGaussianFloor_of_wardPatch (hintg j' h) hnonneg hpatch
    rw [shellGaussianOfIntegrand]
    calc (1 : ℝ) / 8388608 = 1 / 256 * (1 / 32768) := by norm_num
      _ ≤ _ := this
  have hmain := A1_historyUniform_half_floor (bpatch := 1 / 8388608)
    (beta := shellBetaOfSources
      (fun j' h => literalOneLoopIntegrand (sourceVariationMatrix f 1 (Dm j' h)) (Wm j' h))
      lamDet lamGauge aInt aChart aLoc N)
    (betaZ := shellGaussianOfIntegrand
      (fun j' h => literalOneLoopIntegrand (sourceVariationMatrix f 1 (Dm j' h)) (Wm j' h)))
    (betaInt := shellInteractionOfChannels lamDet lamGauge aInt aChart aLoc N)
    (by norm_num) (fun _ _ => rfl) hfloor
    (historyUniformQuartic_of_sourceChannels (fun _ _ _ => rfl)
      hLd hLg hAInt hAChart hALoc hsmall hth)
    (fun k => sourceChannelCoefficient_nonneg hth hth0 k) hadm hg0 hgg j
  have hval : (1 / 8388608 : ℝ) / 2 = 1 / 16777216 := by norm_num
  rw [hval] at hmain
  exact hmain

end YangMills

/-
# Row A1: the margin `b_Z − C_int γ^ρ − D·B > 0` in fully reduced form

This module assembles the three reduced source data of the preceding modules
into the single Row A1 statement, and records exactly which numbers of the
literal Bałaban construction are still needed.

The three inputs are now:

1. **Gaussian floor (A1a).**  One diagonal entry of the *literal first background
   variation*, at the corner lattice momentum `q = (0,1/2,0,0)`:
   `|V_j(0,0)| ≥ v > 0` uniformly in the scale — together with the paramagnetic
   sign datum `S_j = −W_jᵀW_j`.  `TransverseBubbleEntry` turns this into
   `b_Z = v²/32`, with no Brillouin-zone integral: the reduced bubble entry is
   exactly `V_j(0,0)/p̂²` and `p̂² = 4` there.
2. **Interaction debt.**  A Cauchy majorant `|a_{j,m}| ≤ A·K^m` on the nonlinear
   fluctuation coefficients, on a trajectory with `0 ≤ g_j ≤ γ`, `Kγ < 1`.
   `InteractionDebt` turns this into `C_int = A/(1 − Kγ)`.
3. **History debt.**  Uniform summability `∑_{k<j}|R_{j,k}| ≤ D` of the literal
   response kernel, over a displacement budget `B`.  `HistorySummabilityCriteria`
   supplies three different sufficient producers.

`A1_reduced_lower_bound` proves, from exactly these, the uniform bound

    β_j(g) ≥ v²/32 − (A/(1 − Kγ))·γ^ρ − D·B          for every shell index `j`,

with no dependence on the number of scales, the volume or the cutoff, and
`A1_reduced_beta_pos` converts a positive margin into strict positivity of every
shell coefficient.

`A1_reduced_margin_pos_of_smallCoupling` is the literal numerical inequality in
the form in which it will be checked once the six numbers `(v, A, K, γ, D, B)`
are extracted, and `A1_reduced_margin_example` exhibits a concrete admissible
sextuple, so the target inequality is not empty.

**Honest status.**  Nothing here asserts a value for any of `v, A, K, γ, D, B`
for Bałaban's construction.  Row A1 is therefore *not* closed; what is closed is
everything downstream of those six numbers.
-/
import RequestProject.YangMills.TransverseBubbleEntry
import RequestProject.YangMills.InteractionDebt
import RequestProject.YangMills.HistorySummabilityCriteria

namespace YangMills

open Matrix Finset

/-- The literal lattice constrained symbol at the corner momentum. -/
noncomputable def cornerSymbol : Matrix (Fin 4) (Fin 4) ℝ :=
  latticeSymbolOf cornerMomentum

/-- The Row A1 margin in reduced variables:
`b_Z − C_int γ^ρ − D·B` with `b_Z = v²/32` and `C_int = A/(1 − Kγ)`. -/
noncomputable def reducedMargin (v A K gamma D B : ℝ) (rho : ℕ) : ℝ :=
  v ^ 2 / 32 - (A / (1 - K * gamma)) * gamma ^ rho - D * B

/-- **Row A1 from an abstract Gaussian floor plus the two debt data.**  The
Gaussian input is isolated as `v²/32 ≤ βZ_j(g_ref)`; the two producers of that
input on the literal lattice symbol are `latticeUniformFloor_corner` (one entry
of the first background variation) and `latticeBetaTrace_corner_block` (the
whole transverse block). -/
theorem A1_reduced_lower_bound_of_floor
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {R : ℕ → ℕ → ℝ}
    {a : ℕ → ℕ → ℝ} {g gref : ℕ → ℝ}
    {v A K gamma D B : ℝ} {rho : ℕ}
    (hZ : ∀ j, v ^ 2 / 32 ≤ betaZ j gref)
    (hsplit : ∀ j g, beta j g = betaZ j g + betaInt j g)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hg0 : ∀ j, 0 ≤ g j) (hgg : ∀ j, g j ≤ gamma)
    (hKgamma : K * gamma < 1)
    (ha : ∀ j m, |a j m| ≤ A * K ^ m)
    (hbetaInt : ∀ j, betaInt j g = ∑' m, a j m * (g j) ^ (m + rho))
    (hresp : HasHistoryResponse betaZ R)
    (hsum : ∀ j, ∑ k ∈ range j, |R j k| ≤ D)
    (hB : ∀ k, |g k - gref k| ≤ B)
    (j : ℕ) :
    reducedMargin v A K gamma D B rho ≤ beta j g := by
  have hden : 0 < 1 - K * gamma := by linarith
  have hCint : 0 ≤ A / (1 - K * gamma) := by positivity
  have hInt : |betaInt j g| ≤ (A / (1 - K * gamma)) * gamma ^ rho := by
    have h1 : |betaInt j g| ≤ (A / (1 - K * gamma)) * (g j) ^ rho :=
      interactionDebt_of_geometricMajorant hA hK (hg0 j) (hgg j) hKgamma (ha j)
        (hbetaInt j)
    have h2 : (g j) ^ rho ≤ gamma ^ rho := pow_le_pow_left₀ (hg0 j) (hgg j) rho
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hCint)
  exact A1_lower_bound_of_summableKernel hsplit hresp hsum hB (hZ j) hInt

/-- **Row A1 with the Gaussian floor supplied by the whole transverse block of
the first background variation at the corner momentum.**  This is the weakest
Gaussian datum produced in this development: the `3×3` transverse block of `V_j`
need only have Frobenius norm at least `v`, uniformly in the scale. -/
theorem A1_reduced_lower_bound_block
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {R : ℕ → ℕ → ℝ}
    {V S W : ℕ → Matrix (Fin 4) (Fin 4) ℝ}
    {a : ℕ → ℕ → ℝ} {g gref : ℕ → ℝ}
    {v A K gamma D B : ℝ} {rho : ℕ}
    (hV : ∀ j, (V j)ᵀ = V j) (hS : ∀ j, S j = -((W j)ᵀ * W j))
    (hblock : ∀ j, v ^ 2 ≤ ∑ x ∈ ({0, 2, 3} : Finset (Fin 4)),
      ∑ y ∈ ({0, 2, 3} : Finset (Fin 4)), (V j x y) ^ 2)
    (hident : ∀ j, betaZ j gref = betaTrace cornerSymbol (V j) (V j) (S j))
    (hsplit : ∀ j g, beta j g = betaZ j g + betaInt j g)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hg0 : ∀ j, 0 ≤ g j) (hgg : ∀ j, g j ≤ gamma)
    (hKgamma : K * gamma < 1)
    (ha : ∀ j m, |a j m| ≤ A * K ^ m)
    (hbetaInt : ∀ j, betaInt j g = ∑' m, a j m * (g j) ^ (m + rho))
    (hresp : HasHistoryResponse betaZ R)
    (hsum : ∀ j, ∑ k ∈ range j, |R j k| ≤ D)
    (hB : ∀ k, |g k - gref k| ≤ B)
    (j : ℕ) :
    reducedMargin v A K gamma D B rho ≤ beta j g := by
  refine A1_reduced_lower_bound_of_floor (fun j' => ?_) hsplit hA hK hg0 hgg hKgamma
    ha hbetaInt hresp hsum hB j
  rw [hident j']
  refine le_trans ?_ (latticeBetaTrace_corner_block (V j') (S j') (W j') (hV j') (hS j'))
  exact div_le_div_of_nonneg_right (hblock j') (by norm_num)

/-- **Row A1 with the Gaussian floor supplied by the full Brillouin sum.**  This
is the faithful shape of the Gaussian input: `βZ_j` is the finite Brillouin sum
of the one-loop integrand over the (rescaled, hence scale-independent) lattice
momenta, and the only quantitative datum used is one entry of the first
background variation at the corner momentum.  The rest of the Brillouin zone is
controlled by the paramagnetic sign alone. -/
theorem A1_reduced_lower_bound_brillouin
    {iota : Type*} [Fintype iota]
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {R : ℕ → ℕ → ℝ}
    {V S W : ℕ → iota → Matrix (Fin 4) (Fin 4) ℝ}
    {a : ℕ → ℕ → ℝ} {g gref : ℕ → ℝ}
    {v A K gamma D B : ℝ} {rho : ℕ}
    (p : iota → (Fin 4 → ℝ)) (hp : ∀ q, phatSq (p q) ≠ 0)
    (q₀ : iota) (hq₀ : p q₀ = cornerMomentum)
    (hV : ∀ j q, (V j q)ᵀ = V j q) (hS : ∀ j q, S j q = -((W j q)ᵀ * W j q))
    (hv : 0 ≤ v) (hdiag : ∀ j, v ≤ |V j q₀ 0 0|)
    (hident : ∀ j, betaZ j gref
      = ∑ q, brillouinIntegrand (latticeSymbolOf (p q)) (V j q) (V j q) (S j q))
    (hsplit : ∀ j g, beta j g = betaZ j g + betaInt j g)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hg0 : ∀ j, 0 ≤ g j) (hgg : ∀ j, g j ≤ gamma)
    (hKgamma : K * gamma < 1)
    (ha : ∀ j m, |a j m| ≤ A * K ^ m)
    (hbetaInt : ∀ j, betaInt j g = ∑' m, a j m * (g j) ^ (m + rho))
    (hresp : HasHistoryResponse betaZ R)
    (hsum : ∀ j, ∑ k ∈ range j, |R j k| ≤ D)
    (hB : ∀ k, |g k - gref k| ≤ B)
    (j : ℕ) :
    reducedMargin v A K gamma D B rho ≤ beta j g := by
  refine A1_reduced_lower_bound_of_floor (fun j' => ?_) hsplit hA hK hg0 hgg hKgamma
    ha hbetaInt hresp hsum hB j
  rw [hident j']
  exact latticeBrillouinFloor_corner p hp (V j') (S j') (W j') (hV j') (hS j') q₀ hq₀
    hv (hdiag j')

/-- **Row A1 from the three reduced source data.** -/
theorem A1_reduced_lower_bound
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {R : ℕ → ℕ → ℝ}
    {V S W : ℕ → Matrix (Fin 4) (Fin 4) ℝ}
    {a : ℕ → ℕ → ℝ} {g gref : ℕ → ℝ}
    {v A K gamma D B : ℝ} {rho : ℕ}
    (hV : ∀ j, (V j)ᵀ = V j) (hS : ∀ j, S j = -((W j)ᵀ * W j))
    (hv : 0 ≤ v) (hdiag : ∀ j, v ≤ |V j 0 0|)
    (hident : ∀ j, betaZ j gref = betaTrace cornerSymbol (V j) (V j) (S j))
    (hsplit : ∀ j g, beta j g = betaZ j g + betaInt j g)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hg0 : ∀ j, 0 ≤ g j) (hgg : ∀ j, g j ≤ gamma)
    (hKgamma : K * gamma < 1)
    (ha : ∀ j m, |a j m| ≤ A * K ^ m)
    (hbetaInt : ∀ j, betaInt j g = ∑' m, a j m * (g j) ^ (m + rho))
    (hresp : HasHistoryResponse betaZ R)
    (hsum : ∀ j, ∑ k ∈ range j, |R j k| ≤ D)
    (hB : ∀ k, |g k - gref k| ≤ B)
    (j : ℕ) :
    reducedMargin v A K gamma D B rho ≤ beta j g := by
  refine A1_reduced_lower_bound_of_floor (fun j' => ?_) hsplit hA hK hg0 hgg hKgamma
    ha hbetaInt hresp hsum hB j
  rw [hident j']
  exact latticeUniformFloor_corner V S W hV hS hv hdiag j'

/-- **Positivity of every shell coefficient once the margin is positive.** -/
theorem A1_reduced_beta_pos
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {R : ℕ → ℕ → ℝ}
    {V S W : ℕ → Matrix (Fin 4) (Fin 4) ℝ}
    {a : ℕ → ℕ → ℝ} {g gref : ℕ → ℝ}
    {v A K gamma D B : ℝ} {rho : ℕ}
    (hV : ∀ j, (V j)ᵀ = V j) (hS : ∀ j, S j = -((W j)ᵀ * W j))
    (hv : 0 ≤ v) (hdiag : ∀ j, v ≤ |V j 0 0|)
    (hident : ∀ j, betaZ j gref = betaTrace cornerSymbol (V j) (V j) (S j))
    (hsplit : ∀ j g, beta j g = betaZ j g + betaInt j g)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hg0 : ∀ j, 0 ≤ g j) (hgg : ∀ j, g j ≤ gamma)
    (hKgamma : K * gamma < 1)
    (ha : ∀ j m, |a j m| ≤ A * K ^ m)
    (hbetaInt : ∀ j, betaInt j g = ∑' m, a j m * (g j) ^ (m + rho))
    (hresp : HasHistoryResponse betaZ R)
    (hsum : ∀ j, ∑ k ∈ range j, |R j k| ≤ D)
    (hB : ∀ k, |g k - gref k| ≤ B)
    (hmargin : 0 < reducedMargin v A K gamma D B rho)
    (j : ℕ) :
    0 < beta j g :=
  lt_of_lt_of_le hmargin
    (A1_reduced_lower_bound hV hS hv hdiag hident hsplit hA hK hg0 hgg hKgamma ha
      hbetaInt hresp hsum hB j)

/-! ## The literal numerical inequality -/

/-- **The target inequality, in the form in which it will be checked.**
Positivity of the margin is exactly
`v²/32 > (A/(1−Kγ))·γ^ρ + D·B`. -/
theorem A1_reduced_margin_pos_iff (v A K gamma D B : ℝ) (rho : ℕ) :
    0 < reducedMargin v A K gamma D B rho
      ↔ (A / (1 - K * gamma)) * gamma ^ rho + D * B < v ^ 2 / 32 := by
  rw [reducedMargin]
  constructor <;> intro h <;> linarith

/-- **A sufficient smallness criterion.**  If the trajectory bound `γ` and the
history debt `D·B` are small compared with the Gaussian floor, the margin is
positive. -/
theorem A1_reduced_margin_pos_of_smallCoupling
    {v A K gamma D B : ℝ} {rho : ℕ}
    (hint : (A / (1 - K * gamma)) * gamma ^ rho < v ^ 2 / 64)
    (hhist : D * B < v ^ 2 / 64) :
    0 < reducedMargin v A K gamma D B rho := by
  rw [reducedMargin]
  linarith

/-- **The target inequality is satisfiable.**  With
`v = 1, A = 1, K = 1, γ = 1/10, ρ = 2, D = 1/100, B = 1/100` the margin is
`1/32 − 1/90 − 1/10000 > 0`. -/
theorem A1_reduced_margin_example :
    0 < reducedMargin 1 1 1 (1/10) (1/100) (1/100) 2 := by
  rw [reducedMargin]
  norm_num

/-- The same example, spelled out: the margin exceeds `1/50`. -/
theorem A1_reduced_margin_example_value :
    reducedMargin 1 1 1 (1/10) (1/100) (1/100) 2 = 1/32 - 1/90 - 1/10000 := by
  rw [reducedMargin]
  norm_num

/-! ## What remains -/

/-- **The residual A1 obligation, stated as a proposition.**  Row A1 closes as
soon as the literal Bałaban data inhabit this predicate: the shell coefficient
splits into a Gaussian Brillouin sum plus a nonlinear part; the second background
variation is paramagnetic; one entry of the first background variation at the
corner momentum is bounded below uniformly in the scale; the nonlinear
coefficients obey a Cauchy majorant on a small-coupling trajectory; the response
kernel is uniformly summable over the displacement budget; and the numerical
inequality holds. -/
def A1ResidualObligation {iota : Type*} [Fintype iota]
    (p : iota → (Fin 4 → ℝ)) (q₀ : iota)
    (betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ) (R : ℕ → ℕ → ℝ)
    (V S W : ℕ → iota → Matrix (Fin 4) (Fin 4) ℝ) (a : ℕ → ℕ → ℝ) (g gref : ℕ → ℝ)
    (v A K gamma D B : ℝ) (rho : ℕ) : Prop :=
  (∀ q, phatSq (p q) ≠ 0) ∧ p q₀ = cornerMomentum ∧
  (∀ j q, (V j q)ᵀ = V j q) ∧ (∀ j q, S j q = -((W j q)ᵀ * W j q)) ∧ 0 ≤ v ∧
  (∀ j, v ≤ |V j q₀ 0 0|) ∧
  (∀ j, betaZ j gref
    = ∑ q, brillouinIntegrand (latticeSymbolOf (p q)) (V j q) (V j q) (S j q)) ∧
  0 ≤ A ∧ 0 ≤ K ∧ (∀ j, 0 ≤ g j) ∧ (∀ j, g j ≤ gamma) ∧ K * gamma < 1 ∧
  (∀ j m, |a j m| ≤ A * K ^ m) ∧
  (∀ j, betaInt j g = ∑' m, a j m * (g j) ^ (m + rho)) ∧
  HasHistoryResponse betaZ R ∧ (∀ j, ∑ k ∈ range j, |R j k| ≤ D) ∧
  (∀ k, |g k - gref k| ≤ B) ∧ 0 < reducedMargin v A K gamma D B rho

/-- **The residual obligation suffices.**  Any inhabitant of
`A1ResidualObligation` makes every shell coefficient strictly positive,
uniformly in the scale, the volume and the cutoff. -/
theorem A1_of_residualObligation {iota : Type*} [Fintype iota]
    {p : iota → (Fin 4 → ℝ)} {q₀ : iota}
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {R : ℕ → ℕ → ℝ}
    {V S W : ℕ → iota → Matrix (Fin 4) (Fin 4) ℝ} {a : ℕ → ℕ → ℝ} {g gref : ℕ → ℝ}
    {v A K gamma D B : ℝ} {rho : ℕ}
    (hsplit : ∀ j g, beta j g = betaZ j g + betaInt j g)
    (h : A1ResidualObligation p q₀ betaZ betaInt R V S W a g gref v A K gamma D B rho)
    (j : ℕ) :
    0 < beta j g := by
  obtain ⟨hp, hq₀, hV, hS, hv, hdiag, hident, hA, hK, hg0, hgg, hKgamma, ha,
    hbetaInt, hresp, hsum, hB, hmargin⟩ := h
  exact lt_of_lt_of_le hmargin
    (A1_reduced_lower_bound_brillouin p hp q₀ hq₀ hV hS hv hdiag hident hsplit hA hK
      hg0 hgg hKgamma ha hbetaInt hresp hsum hB j)

/-! ## Non-vacuity of the residual obligation -/

section NonVacuity

/-- The one-momentum Gaussian part of the witness. -/
noncomputable def witnessBetaZ : ℝ :=
  ∑ _q : Fin 1, brillouinIntegrand (latticeSymbolOf cornerMomentum)
    (1 : Matrix (Fin 4) (Fin 4) ℝ) 1 0

/-- Trivial data satisfying every clause of the residual obligation: a
one-momentum Brillouin sum at the corner momentum, the identity first variation,
vanishing second variation, vanishing nonlinear coefficients, vanishing response
kernel, and the numerical sextuple of `A1_reduced_margin_example`.  So the
residual obligation is consistent. -/
theorem A1ResidualObligation_nonvacuous :
    A1ResidualObligation (fun _ : Fin 1 => cornerMomentum) 0
      (fun _ _ => witnessBetaZ) (fun _ _ => 0) (fun _ _ => 0)
      (fun _ _ => (1 : Matrix (Fin 4) (Fin 4) ℝ)) (fun _ _ => 0) (fun _ _ => 0)
      (fun _ _ => 0) (fun _ => 1/10) (fun _ => 1/10)
      1 1 1 (1/10) (1/100) (1/100) 2 := by
  refine ⟨fun _ => ne_of_gt phatSq_cornerMomentum_pos, rfl,
    fun _ _ => Matrix.transpose_one, fun _ _ => by simp, by norm_num,
    fun _ => by simp, fun _ => rfl, by norm_num, by norm_num,
    fun _ => by norm_num, fun _ => le_refl _, by norm_num, fun _ _ => by norm_num,
    fun _ => by simp, ?_, fun _ => by simp, fun _ => by norm_num,
    A1_reduced_margin_example⟩
  intro j g g'
  have hzero : |witnessBetaZ - witnessBetaZ| = 0 := by simp
  rw [hzero]
  exact Finset.sum_nonneg (fun k _ => by positivity)

/-- Consequently the assembled Row A1 conclusion is inhabited on that data: the
shell coefficient of the witness is strictly positive. -/
theorem A1_reduced_witness_pos (j : ℕ) : 0 < witnessBetaZ + 0 :=
  A1_of_residualObligation (beta := fun _ _ => witnessBetaZ + 0)
    (fun _ _ => rfl) A1ResidualObligation_nonvacuous j

end NonVacuity

end YangMills

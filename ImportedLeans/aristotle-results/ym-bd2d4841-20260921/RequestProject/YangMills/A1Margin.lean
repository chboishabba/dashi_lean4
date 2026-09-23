/-
# The Row A1 margin: three numbers, one inequality

The recut of Row A1 asks for exactly three quantitative inputs

    (1)  β Z_j ≥ b_Z                       (Gaussian/constrained-determinant part)
    (2)  |β Int_j| ≤ C_int γ^ρ             (nonlinear fluctuation part, ρ > 0)
    (3)  |R_{j,k}| ≤ C_R θ^{j−k}, θ < 1    (history response)

and closes as soon as

    b_− = b_Z − C_int γ^ρ − C_R B θ/(1−θ) > 0.

This module proves the consumer side of that statement, and two structural
results that the recut asks for explicitly.

* `A1_margin_lower_bound` / `A1_margin_positive` — the boxed inequality:
  from (1), (2), (3) the shell coefficient on *any* admissible history is at
  least `b_−`, uniformly in the shell index `j` (hence in the number of scales,
  the volume and the cutoff, none of which enter), and positive as soon as
  `b_− > 0`.

* `sharedExpansion_lower_bound` — *one* perturbative expansion delivers both A1a
  and A1b.  If

        β_j(g) = β_* + ∑_{k<j} R_{j,k}(g_k − g_*) + Rem_j(g),   |Rem_j| ≤ ε,

  then the constant term and the historical derivatives are read off the same
  expansion and give `β_j(g) ≥ β_* − C_R B θ/(1−θ) − ε`.  A1a and A1b are then
  not two independent source hunts but two questions asked of one expansion.

* `responseDecay_of_irrelevance` — the decay hypothesis (3) *derived from
  renormalisation-group irrelevance* rather than postulated: if the earlier
  coupling `g_k` reaches the shell `j` only through an operator of scaling
  dimension `ω > 0`, so that `|∂β_j/∂g_k| ≤ C L^{−ω(j−k)}` with `L > 1`, then
  the geometric decay holds with `θ = L^{−ω} ∈ (0,1)`, and
  `irrelevantRatio_lt_one` records that this `θ` is genuinely `< 1`.

No numerical value of `b_Z`, `C_int`, `ρ`, `C_R`, `θ` is asserted anywhere here;
this file proves what such constants buy.
-/
import RequestProject.YangMills.BetaHistoryResponse

namespace YangMills

open Finset

/-- The Row A1 margin `b_− = b_Z − Rint − C_R B θ/(1−θ)`, where `Rint` is the
bound on the nonlinear fluctuation part. -/
noncomputable def a1Margin (bZ Rint CR B theta : ℝ) : ℝ :=
  bZ - Rint - CR * B * (theta / (1 - theta))

/-- **The Row A1 margin bound.**  With the source-native split
`β_j = βZ_j + βInt_j`, a floor `b_Z` for the Gaussian part at the reference
history, a bound `Rint` for the nonlinear part, and geometric history response
with ratio `θ < 1` over a displacement budget `B`, the shell coefficient obeys

    β_j(g) ≥ b_Z − Rint − C_R B θ/(1−θ) = b_−,

uniformly in `j`. -/
theorem A1_margin_lower_bound
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {R : ℕ → ℕ → ℝ}
    {bZ Rint CR theta B : ℝ}
    (hsplit : ∀ j g, beta j g = betaZ j g + betaInt j g)
    (hresp : HasHistoryResponse betaZ R) (hdec : HasResponseDecay R CR theta)
    (hCR : 0 ≤ CR) (h0 : 0 ≤ theta) (h1 : theta < 1)
    {g gref : ℕ → ℝ} (hB : ∀ k, |g k - gref k| ≤ B)
    (hZ : bZ ≤ betaZ j gref) (hInt : |betaInt j g| ≤ Rint) :
    a1Margin bZ Rint CR B theta ≤ beta j g := by
  have hhist : |betaZ j g - betaZ j gref| ≤ CR * B * (theta / (1 - theta)) :=
    historyResponse_bound hresp hdec hCR h0 h1 hB j
  have h1' := (abs_le.mp hhist).1
  have h2' := (abs_le.mp hInt).1
  rw [hsplit j g, a1Margin]
  linarith

/-- **Row A1 closes when the margin is positive.** -/
theorem A1_margin_positive
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {R : ℕ → ℕ → ℝ}
    {bZ Rint CR theta B : ℝ}
    (hsplit : ∀ j g, beta j g = betaZ j g + betaInt j g)
    (hresp : HasHistoryResponse betaZ R) (hdec : HasResponseDecay R CR theta)
    (hCR : 0 ≤ CR) (h0 : 0 ≤ theta) (h1 : theta < 1)
    {g gref : ℕ → ℝ} (hB : ∀ k, |g k - gref k| ≤ B)
    (hZ : bZ ≤ betaZ j gref) (hInt : |betaInt j g| ≤ Rint)
    (hmargin : 0 < a1Margin bZ Rint CR B theta) :
    0 < beta j g :=
  lt_of_lt_of_le hmargin
    (A1_margin_lower_bound hsplit hresp hdec hCR h0 h1 hB hZ hInt)

/-- **One expansion for both halves of A1.**  If the shell coefficient has the
perturbative expansion

    β_j(g) = β_* + ∑_{k<j} R_{j,k}(g_k − g_*) + Rem_j(g)

with a uniformly small remainder and geometrically decaying response kernel,
then the constant term (A1a) and the historical derivatives (A1b) come from the
*same* expansion, and

    β_j(g) ≥ β_* − C_R B θ/(1−θ) − ε. -/
theorem sharedExpansion_lower_bound
    {beta Rem : ℕ → (ℕ → ℝ) → ℝ} {R : ℕ → ℕ → ℝ}
    {betaStar CR theta B eps : ℝ} {gstar g : ℕ → ℝ} {j : ℕ}
    (hexp : ∀ j g, beta j g
      = betaStar + ∑ k ∈ range j, R j k * (g k - gstar k) + Rem j g)
    (hdec : HasResponseDecay R CR theta) (hCR : 0 ≤ CR)
    (h0 : 0 ≤ theta) (h1 : theta < 1) (hB0 : 0 ≤ B)
    (hB : ∀ k, |g k - gstar k| ≤ B) (hRem : |Rem j g| ≤ eps) :
    betaStar - CR * B * (theta / (1 - theta)) - eps ≤ beta j g := by
  have hsum : |∑ k ∈ range j, R j k * (g k - gstar k)|
      ≤ CR * B * (theta / (1 - theta)) := by
    have hterm : ∀ k ∈ range j, |R j k * (g k - gstar k)| ≤ CR * B * theta ^ (j - k) := by
      intro k hk
      have hkj : k < j := Finset.mem_range.mp hk
      have hR := hdec j k hkj
      have hg := hB k
      calc |R j k * (g k - gstar k)| = |R j k| * |g k - gstar k| := abs_mul _ _
        _ ≤ (CR * theta ^ (j - k)) * B := by
            refine mul_le_mul hR hg (abs_nonneg _) ?_
            exact mul_nonneg hCR (pow_nonneg h0 _)
        _ = CR * B * theta ^ (j - k) := by ring
    calc |∑ k ∈ range j, R j k * (g k - gstar k)|
        ≤ ∑ k ∈ range j, |R j k * (g k - gstar k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range j, CR * B * theta ^ (j - k) := Finset.sum_le_sum hterm
      _ = CR * B * ∑ k ∈ range j, theta ^ (j - k) := by rw [Finset.mul_sum]
      _ ≤ CR * B * (theta / (1 - theta)) :=
          mul_le_mul_of_nonneg_left (responseSum_le h0 h1 j) (mul_nonneg hCR hB0)
  have h1' := (abs_le.mp hsum).1
  have h2' := (abs_le.mp hRem).1
  rw [hexp j g]
  linarith

section Irrelevance

/-- The irrelevant ratio `θ = L^{−ω}` attached to an operator of scaling
dimension `ω > 0` at rescaling factor `L > 1`. -/
noncomputable def irrelevantRatio (L omega : ℝ) : ℝ := L ^ (-omega)

theorem irrelevantRatio_nonneg {L omega : ℝ} (hL : 0 < L) :
    0 ≤ irrelevantRatio L omega :=
  le_of_lt (Real.rpow_pos_of_pos hL _)

/-- Irrelevance really does give a contraction ratio: `L^{−ω} < 1` for `L > 1`
and `ω > 0`. -/
theorem irrelevantRatio_lt_one {L omega : ℝ} (hL : 1 < L) (homega : 0 < omega) :
    irrelevantRatio L omega < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hL (neg_neg_iff_pos.mpr homega)

/-- **Geometric response decay derived from renormalisation-group
irrelevance.**  If the response of the shell coefficient to an earlier coupling
is suppressed by the scaling dimension of an irrelevant operator,

    |R_{j,k}| ≤ C · L^{−ω(j−k)},   L > 1, ω > 0,

then the kernel has geometric decay with ratio `θ = L^{−ω} < 1`, which is
exactly the hypothesis the history budget consumes. -/
theorem responseDecay_of_irrelevance {R : ℕ → ℕ → ℝ} {C L omega : ℝ}
    (hL : 0 < L) (hR : ∀ j k, k < j → |R j k| ≤ C * L ^ (-(omega * (j - k : ℕ)))) :
    HasResponseDecay R C (irrelevantRatio L omega) := by
  intro j k hkj
  have hpow : (irrelevantRatio L omega) ^ (j - k) = L ^ (-(omega * (j - k : ℕ))) := by
    rw [irrelevantRatio, ← Real.rpow_natCast (L ^ (-omega)) (j - k),
      ← Real.rpow_mul (le_of_lt hL)]
    ring_nf
  rw [hpow]
  exact hR j k hkj

end Irrelevance

section NonVacuity

/-- **Non-vacuity of the margin package.**  The hypotheses of
`A1_margin_positive` are jointly satisfiable by an actual coefficient family, so
the conclusion is not reached through a contradictory hypothesis set: take the
Gaussian part constant `1`, no nonlinear part, and a vanishing response kernel;
the margin is then `1 > 0`. -/
theorem A1_margin_nonvacuous :
    0 < (fun (_ : ℕ) (_ : ℕ → ℝ) => (1 : ℝ)) 0 (fun _ => 0) := by
  refine A1_margin_positive (beta := fun _ _ => (1 : ℝ))
    (betaZ := fun _ _ => (1 : ℝ)) (betaInt := fun _ _ => 0) (R := fun _ _ => 0)
    (bZ := 1) (Rint := 0) (CR := 0) (theta := 0) (B := 0) (j := 0)
    (fun j g => by ring) ?_ ?_ le_rfl le_rfl (by norm_num)
    (g := fun _ => 0) (gref := fun _ => 0) (fun k => by simp) le_rfl (by simp) ?_
  · intro j g g'
    simp
  · intro j k _; simp
  · simp [a1Margin]

/-- **The irrelevance route is non-vacuous**: at `L = 2`, `ω = 1` the derived
ratio is `1/2 < 1`. -/
theorem irrelevantRatio_two_one : irrelevantRatio 2 1 = 1 / 2 := by
  rw [irrelevantRatio]
  rw [show (-1 : ℝ) = ((-1 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
  norm_num

end NonVacuity

end YangMills

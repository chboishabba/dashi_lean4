/-
# Row A1 — history-uniform remainder control, and why the history debt must
# then *not* be subtracted again

In the source organisation of the beta chain, `β_j` is projected from the
**current** effective interaction `E^{(j+1)}`, and that current effective
interaction already carries the dependence on the preceding couplings.  So if
the five-channel remainder estimate

    β_Int ≥ −C_β g⁴

is available *uniformly over the admissible preceding-coupling history* — i.e.
the constant `C_β` does not depend on which admissible history produced the
current effective interaction — and the Gaussian floor `β_Z ≥ b_patch` is
likewise uniform over admissible histories, then the history displacement has
already been accounted for.  Subtracting a separate memory debt
`(C_H γ/2 + H_marg)·B` on top of that would **double-count** the history.

This file proves that route and separates it cleanly from the fallback route of
`A1CorrectedMargin`.

* `HistoryUniformFloor`, `HistoryUniformQuartic` : the two uniformity
  hypotheses, quantified over an explicit set of admissible histories.
* `A1_historyUniform_lower_bound` : the anti-double-counting conclusion
  `b_patch − C_β γ⁴ ≤ β_j`, with no memory term at all.
* `correctedMargin_le_historyUniformMargin` : the fallback margin is never
  larger — the explicit history debts are a strictly weaker statement whenever
  the debt is positive (`historyUniform_strictly_stronger`).
* `historyUniformFloor_is_a_real_hypothesis` : a Gaussian coefficient with a
  floor along one reference trajectory but **no** uniform floor over histories.
  So history-uniformity may not be assumed for free; it is exactly the source
  obligation this route trades the memory debt for.
* `A1_historyUniform_half_floor` / `A1_historyUniform_beta_pos` : combined with
  the constructive coupling `γ_*` of `SmallCouplingAbsorption`, any finite `C_β`
  and any floor `b_patch > 0` give `β_j ≥ b_patch/2 > 0`.

Nothing here asserts `b_patch` or `C_β` for Bałaban's construction.
-/
import RequestProject.YangMills.A1CorrectedMargin
import RequestProject.YangMills.SmallCouplingAbsorption

namespace YangMills

open Finset

/-- The Gaussian floor, uniformly over the admissible preceding-coupling
histories `Adm`. -/
def HistoryUniformFloor (betaZ : ℕ → (ℕ → ℝ) → ℝ) (Adm : (ℕ → ℝ) → Prop) (b : ℝ) : Prop :=
  ∀ j h, Adm h → b ≤ betaZ j h

/-- The five-channel quartic remainder, uniformly over admissible histories:
for every admissible history the current effective interaction splits into the
five channels with the *same* coefficients `c k`. -/
def HistoryUniformQuartic (betaInt : ℕ → (ℕ → ℝ) → ℝ) (Adm : (ℕ → ℝ) → Prop)
    (c : BetaChannel → ℝ) : Prop :=
  ∀ j h, Adm h → ∃ ch : BetaChannel → ℝ,
    betaInt j h = ∑ k, ch k ∧ ∀ k, |ch k| ≤ c k * (h j) ^ 4

/-- The history-uniform margin: floor minus quartic debt, **no memory term**. -/
noncomputable def historyUniformMargin (bpatch Cb gamma : ℝ) : ℝ :=
  bpatch - Cb * gamma ^ 4

/-- **The anti-double-counting estimate.**  If both the Gaussian floor and the
five-channel quartic remainder hold uniformly over admissible histories, then
the shell coefficient of *any* admissible trajectory obeys
`β_j ≥ b_patch − C_β γ⁴`, uniformly in the shell index, the number of scales,
the volume and the cutoff — with no history debt subtracted. -/
theorem A1_historyUniform_lower_bound
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {Adm : (ℕ → ℝ) → Prop}
    {c : BetaChannel → ℝ} {bpatch gamma : ℝ} {g : ℕ → ℝ}
    (hsplit : ∀ j h, beta j h = betaZ j h + betaInt j h)
    (hfloor : HistoryUniformFloor betaZ Adm bpatch)
    (hquart : HistoryUniformQuartic betaInt Adm c)
    (hc : ∀ k, 0 ≤ c k) (hadm : Adm g) (hg0 : ∀ j, 0 ≤ g j) (hgg : ∀ j, g j ≤ gamma)
    (j : ℕ) :
    historyUniformMargin bpatch (Cbeta c) gamma ≤ beta j g := by
  obtain ⟨ch, hch, hmaj⟩ := hquart j g hadm
  have hInt : -(Cbeta c) * gamma ^ 4 ≤ betaInt j g :=
    betaInt_ge_on_trajectory (betaInt := fun _ => betaInt j g) (ch := fun k _ => ch k)
      (c := c) (g := g j) (gamma := gamma) (by simpa using hch) (fun k => hmaj k) hc
      (hg0 j) (hgg j)
  have hZ : bpatch ≤ betaZ j g := hfloor j g hadm
  rw [hsplit j g, historyUniformMargin]
  linarith

/-- The fallback margin of `A1CorrectedMargin` is never larger than the
history-uniform margin. -/
theorem correctedMargin_le_historyUniformMargin
    {bpatch Cb CHconst gamma Hmarg B : ℝ}
    (hdebt : 0 ≤ (CHconst * gamma / 2 + Hmarg) * B) :
    correctedMargin bpatch Cb CHconst gamma Hmarg B
      ≤ historyUniformMargin bpatch Cb gamma := by
  unfold correctedMargin historyUniformMargin
  linarith

/-- …and strictly smaller as soon as the memory debt is positive: re-subtracting
the history is a real loss, not a harmless conservatism. -/
theorem historyUniform_strictly_stronger
    {bpatch Cb CHconst gamma Hmarg B : ℝ}
    (hdebt : 0 < (CHconst * gamma / 2 + Hmarg) * B) :
    correctedMargin bpatch Cb CHconst gamma Hmarg B
      < historyUniformMargin bpatch Cb gamma := by
  unfold correctedMargin historyUniformMargin
  linarith

/-- The two routes agree exactly when there is no memory debt. -/
theorem correctedMargin_eq_historyUniformMargin_of_no_debt
    (bpatch Cb CHconst gamma : ℝ) :
    correctedMargin bpatch Cb CHconst gamma 0 0
      = historyUniformMargin bpatch Cb gamma := by
  unfold correctedMargin historyUniformMargin; ring

/-! ## History-uniformity is a genuine hypothesis -/

/-- **Boundary test.**  There is a Gaussian coefficient with a strictly positive
floor along the zero reference history and *no* positive floor uniform over
histories: `betaZ j h = 1 − h 0` has `betaZ j 0 = 1` but is arbitrarily negative
on other histories.  So `HistoryUniformFloor` cannot be inferred from a floor at
one reference trajectory; it is exactly the additional source obligation that
the anti-double-counting route buys the memory debt with. -/
theorem historyUniformFloor_is_a_real_hypothesis :
    ∃ betaZ : ℕ → (ℕ → ℝ) → ℝ,
      (∀ j, (1 : ℝ) ≤ betaZ j (fun _ => 0)) ∧
      ∀ b : ℝ, 0 < b → ¬ HistoryUniformFloor betaZ (fun _ => True) b := by
  refine ⟨fun _ h => 1 - h 0, fun j => by norm_num, ?_⟩
  intro b hb hU
  have h := hU 0 (fun _ => 1 - b + 1) trivial
  simp at h
  linarith

/-- The history-uniform hypothesis package is inhabited: a constant Gaussian
coefficient with a genuinely nonzero quartic remainder. -/
theorem historyUniform_nonvacuous :
    ∃ (betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ) (c : BetaChannel → ℝ),
      HistoryUniformFloor betaZ (fun h => ∀ j, 0 ≤ h j ∧ h j ≤ 1 / 10) (1 / 2) ∧
      HistoryUniformQuartic betaInt (fun h => ∀ j, 0 ≤ h j ∧ h j ≤ 1 / 10) c ∧
      (∀ k, 0 ≤ c k) ∧ (∀ j h, betaInt j h = -(h j) ^ 4) := by
  refine ⟨fun _ _ => 1 / 2, fun j h => -(h j) ^ 4, fun _ => 1, fun _ _ _ => le_rfl,
    ?_, fun _ => zero_le_one, fun _ _ => rfl⟩
  intro j h _
  refine ⟨fun k => if k = BetaChannel.determinant then -(h j) ^ 4 else 0, by simp, ?_⟩
  intro k
  have h4 : (0 : ℝ) ≤ (h j) ^ 4 := by positivity
  by_cases hk : k = BetaChannel.determinant
  · subst hk
    simp [abs_of_nonneg h4]
  · simp [hk, h4]

/-! ## The closure step, with no numerical constant -/

/-- **The dream-closure assembly.**  History-uniform Gaussian floor
`b_patch > 0`, history-uniform five-channel quartic remainder with *any* finite
`C_β`, and the constructive coupling `γ_* = (1/2)·b_patch/(C_β + b_patch)` give
`β_j ≥ b_patch/2` for every shell index. -/
theorem A1_historyUniform_half_floor
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {Adm : (ℕ → ℝ) → Prop}
    {c : BetaChannel → ℝ} {bpatch : ℝ} {g : ℕ → ℝ}
    (hb : 0 < bpatch)
    (hsplit : ∀ j h, beta j h = betaZ j h + betaInt j h)
    (hfloor : HistoryUniformFloor betaZ Adm bpatch)
    (hquart : HistoryUniformQuartic betaInt Adm c)
    (hc : ∀ k, 0 ≤ c k) (hadm : Adm g) (hg0 : ∀ j, 0 ≤ g j)
    (hgg : ∀ j, g j ≤ criticalCoupling bpatch (Cbeta c))
    (j : ℕ) :
    bpatch / 2 ≤ beta j g := by
  obtain ⟨ch, hch, hmaj⟩ := hquart j g hadm
  have hInt : -(Cbeta c * (g j) ^ 4) ≤ betaInt j g := by
    have := betaInt_ge_of_channelMajorants (betaInt := fun _ => betaInt j g)
      (ch := fun k _ => ch k) (c := c) (g := g j) (by simpa using hch) (fun k => hmaj k)
    simpa [neg_mul] using this
  have hZ : bpatch ≤ betaZ j g := hfloor j g hadm
  have := half_floor_of_smallCoupling (betaZ := betaZ j g) (betaInt := betaInt j g)
    hb (Cbeta_nonneg hc) hZ hInt (hg0 j) (hgg j)
  rw [hsplit j g]
  exact this

/-- Hence strict positivity of every shell coefficient. -/
theorem A1_historyUniform_beta_pos
    {beta betaZ betaInt : ℕ → (ℕ → ℝ) → ℝ} {Adm : (ℕ → ℝ) → Prop}
    {c : BetaChannel → ℝ} {bpatch : ℝ} {g : ℕ → ℝ}
    (hb : 0 < bpatch)
    (hsplit : ∀ j h, beta j h = betaZ j h + betaInt j h)
    (hfloor : HistoryUniformFloor betaZ Adm bpatch)
    (hquart : HistoryUniformQuartic betaInt Adm c)
    (hc : ∀ k, 0 ≤ c k) (hadm : Adm g) (hg0 : ∀ j, 0 ≤ g j)
    (hgg : ∀ j, g j ≤ criticalCoupling bpatch (Cbeta c))
    (j : ℕ) :
    0 < beta j g :=
  lt_of_lt_of_le (by linarith)
    (A1_historyUniform_half_floor hb hsplit hfloor hquart hc hadm hg0 hgg j)

end YangMills

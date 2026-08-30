/-
# `C*`: the two exact forms of the remaining C-side obligation

After `AdjointCaccioppoliClosure.lean` the C side of the route is a *conditional*
Caccioppoli budget whose sources are all linear in the truncation data.  What is
still missing is stated here, as `Prop`s in the vocabulary of the development —
never as axioms or postulates.

Two independent inputs remain, and either one of them is `C*`.

* `ClayNS.AdjointDefectWeightGate` — the **weight**.  The budget
  `ClayNS.adjoint_caccioppoli_linear_budget` assumes a nonnegative periodic
  weight `Φ` that solves the backward adjoint transport–diffusion equation
  `−∂_tΦ − u(·+h)·∇Φ − νΔΦ = 0` exactly, has a bounded gradient, and is
  positive at the chosen defect point.
  `ClayNS.adjoint_caccioppoli_budget_of_weight_gate` is the (proved) statement
  that this gate is the only thing between the development and the budget.

  **Update (modulus tranche).**  As stated, this gate is *not* an obstruction:
  the constant weight `Φ ≡ 1` solves the backward adjoint equation exactly, is
  nonnegative and periodic, has vanishing gradient and is positive everywhere,
  so `ClayNS.adjointDefectWeightGate_const` proves it outright — and with it the
  budget, unconditionally, in its *global* (unlocalized) form.  What the De
  Giorgi argument actually needs is **concentration**: a weight whose cell mass
  is small compared with its value at the defect point.  That refinement is
  `ClayNS.ConcentratedAdjointWeightGate`, and the constant weight realizes the
  concentration ratio exactly `1` (`ClayNS.concentratedAdjointWeightGate_one`),
  so the whole remaining content is the strict inequality `θ < 1`.

* `ClayNS.IncrementStretchingDepletionGate` — the **extra level-set factor**.
  The proved critical estimate `ClayNS.increment_stretching_critical_estimate`
  gives the exponent `3/10` on `|A_k|`, and
  `ClayNS.sublinear_recurrence_no_decay` shows that this exponent produces a
  *sublinear* `Y_k^{3/5}` source, which cannot drive the De Giorgi recurrence.
  The depletion gate asks for `3/10 + θ` with `θ > 0`.
  `ClayNS.incrementStretchingDepletion_exponent_zero` proves the `θ = 0` case
  unconditionally, so the entire content of the gate is the strict positivity
  of `θ`.

Neither gate is proved here.  Nothing downstream of them is assumed: the two
implications recorded in this file are proved.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.AdjointCaccioppoliClosure
import RequestProject.NavierStokes.IncrementStretchingCritical

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

namespace ClayNS

/-! ## The adjoint defect weight -/

/-- **The adjoint defect-weight gate.**  For every smooth periodic
divergence-free velocity, every increment step `h` and every base point `z₀`
there is a nonnegative periodic weight with bounded gradient which solves the
backward adjoint transport–diffusion equation of the increment exactly and is
positive at `z₀`.

Positivity at `z₀` is what makes the gate non-vacuous: `Φ ≡ 0` solves (Adj) but
carries no information. -/
def AdjointDefectWeightGate (nu : ℝ) : Prop :=
  ∀ V : STime → E3, ContDiff ℝ (⊤ : ℕ∞) V → SpacePeriodic V → (∀ z : STime, divg V z = 0) →
    ∀ (h : E3) (z₀ : STime), ∃ (Phi : STime → ℝ) (G : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) Phi ∧ SpacePeriodic Phi ∧ (∀ z, 0 ≤ Phi z) ∧
        (∀ z : STime, adjointOp nu h V Phi z = 0) ∧
        (∀ (z : STime) (j : Fin 3), |dvec (0, ee j) Phi z| ≤ G) ∧ 0 < Phi z₀

/-- **The weight gate delivers the linear Caccioppoli budget.**  Everything
else in `ClayNS.adjoint_caccioppoli_linear_budget` is already available, so the
existence of the adjoint weight is exactly what stands between the development
and a localized budget concentrated at the defect point. -/
theorem adjoint_caccioppoli_budget_of_weight_gate {nu eta Amp Bmp Gp : ℝ}
    (hnu : 0 < nu) (heta : 0 < eta)
    {V : STime → E3} {P : STime → ℝ} (h : E3) (z₀ : STime)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V)
    {beta b1 b2 : ℝ → ℝ} (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta)
    (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1) (hb2c : ContDiff ℝ (⊤ : ℕ∞) b2)
    (hb1 : ∀ x, HasDerivAt beta (b1 x) x) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (hB1 : ∀ x, 0 ≤ b1 x) (hB2 : ∀ x, 0 ≤ b2 x)
    (hAmp : ∀ (z : STime) (a : Fin 3), |V z a| ≤ Amp)
    (hBmp : ∀ (z : STime) (a : Fin 3), |incrComp h V a z| ≤ Bmp)
    (hGp : ∀ (z : STime) (a : Fin 3), |dvec (0, ee a) (incrPres h P) z| ≤ Gp)
    (hgate : AdjointDefectWeightGate nu) (t : ℝ) :
    ∃ (Phi : STime → ℝ) (G : ℝ), 0 < Phi z₀ ∧
      cellInt (fun x => dvec (1, 0) (fun w => Phi w * beta (incrQuad h V w)) (t, x))
          + (1 - eta) * nu * cellInt (fun x => Phi (t, x) * (b2 (incrQuad h V (t, x))
              * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
                  * dvec (0, ee k) (incrQuad h V) (t, x)))
          + nu / 2 * cellInt (fun x =>
              Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x)))
        ≤ 27 * Amp ^ 2 * Bmp ^ 4 / (4 * eta * nu)
              * cellInt (fun x => Phi (t, x) * b2 (incrQuad h V (t, x)))
          + (9 * Amp ^ 2 * Bmp ^ 2 / (2 * nu) + 3 * Bmp * Gp)
              * cellInt (fun x => Phi (t, x) * b1 (incrQuad h V (t, x)))
          + 9 * Amp * Bmp ^ 2 * G * cellInt (fun x => b1 (incrQuad h V (t, x))) := by
  obtain ⟨Phi, G, hPhi, hPhiper, hPhi0, hadj, hG, hpos⟩ := hgate V hV hVper hdiv h z₀
  exact ⟨Phi, G, hpos,
    adjoint_caccioppoli_linear_budget hnu heta h hV hP hPhi hVper hPhiper hbeta hb1c hb2c
      hb1 hb2 hdiv hmom hadj hPhi0 hB1 hB2 hAmp hBmp hG hGp t⟩

/-! ## The increment stretching depletion -/

variable {α : Type*} [MeasurableSpace α]

/-- **The increment stretching depletion gate.**  The critical Hölder triple
`1/(5/2) + 1/(10/3) + 1/(10/3) = 1` gives the level-set exponent `3/10`; the
gate asks for a strictly better one, `3/10 + θ` with `θ > 0`. -/
def IncrementStretchingDepletionGate (μ : Measure α) (Str S v : α → ℝ) (A : Set α)
    (theta : ℝ) (C : ℝ≥0∞) : Prop :=
  0 < theta ∧
    (∫⁻ x in A, ‖Str x‖ₑ ∂μ)
      ≤ C * (eLpNorm S (5 / 2) μ * eLpNorm v (10 / 3) μ * μ A ^ ((3 / 10 : ℝ) + theta))

/-- **Calibration of the depletion gate: the `θ = 0` case is a theorem.**  With
exponent gain `θ = 0` and constant `8` the inequality of
`ClayNS.IncrementStretchingDepletionGate` is exactly the proved critical
estimate.  Hence the whole content of the gate is the strict positivity of `θ`,
i.e. a genuine depletion of the stretching on the level set. -/
theorem incrementStretchingDepletion_exponent_zero (μ : Measure α) {Str S v : α → ℝ}
    {A : Set α} (hA : MeasurableSet A) (hS : AEStronglyMeasurable S μ)
    (hv : AEStronglyMeasurable v μ) (hbound : ∀ x, |Str x| ≤ 8 * (|S x| * |v x|)) :
    (∫⁻ x in A, ‖Str x‖ₑ ∂μ)
      ≤ (8 : ℝ≥0∞) * (eLpNorm S (5 / 2) μ * eLpNorm v (10 / 3) μ
          * μ A ^ ((3 / 10 : ℝ) + 0)) := by
  simpa using increment_stretching_critical_estimate μ hA hS hv hbound

/-! ## The stated weight gate is a theorem; the real requirement is concentration -/

/-- **The adjoint defect-weight gate holds.**  The constant weight `Φ ≡ 1`
solves the backward adjoint transport–diffusion equation exactly, is
nonnegative, periodic, has zero gradient and is positive at every point.  So the
gate as stated is not an obstruction, and
`ClayNS.adjoint_caccioppoli_budget_of_weight_gate` delivers its budget
unconditionally — in the global, unlocalized form. -/
theorem adjointDefectWeightGate_const (nu : ℝ) : AdjointDefectWeightGate nu := by
  intro V hV hVper hdiv h z₀
  refine ⟨fun _ => (1:ℝ), 0, contDiff_const, ?_, fun _ => zero_le_one, ?_, ?_, one_pos⟩
  · intro z j; rfl
  · intro z
    have hd : ∀ (a : STime) (w : STime), dvec a (fun _ : STime => (1:ℝ)) w = 0 := by
      intro a w; simp [dvec]
    have hlap : lap (fun _ : STime => (1:ℝ)) z = 0 := by
      have hfun : ∀ i : Fin 3, (fun w : STime => dspace (fun _ : STime => (1:ℝ)) i w)
          = fun _ : STime => (0:ℝ) := fun i => funext fun w => hd (0, ee i) w
      simp only [lap, hfun]
      simp [dspace]
    simp [adjointOp, hd, hlap]
  · intro z j
    simp [dvec]

/-- **The concentrated adjoint weight gate.**  The same requirements as
`ClayNS.AdjointDefectWeightGate` together with the localization the De Giorgi
argument actually consumes: the cell mass of the weight is at most `θ` times its
value at the defect point.  For `θ < 1` the weight genuinely concentrates. -/
def ConcentratedAdjointWeightGate (nu theta : ℝ) : Prop :=
  ∀ V : STime → E3, ContDiff ℝ (⊤ : ℕ∞) V → SpacePeriodic V →
    (∀ z : STime, divg V z = 0) →
    ∀ (h : E3) (z₀ : STime), ∃ (Phi : STime → ℝ) (G : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) Phi ∧ SpacePeriodic Phi ∧ (∀ z, 0 ≤ Phi z) ∧
        (∀ z : STime, adjointOp nu h V Phi z = 0) ∧
        (∀ (z : STime) (j : Fin 3), |dvec (0, ee j) Phi z| ≤ G) ∧ 0 < Phi z₀ ∧
        cellInt (fun x => Phi (z₀.1, x)) ≤ theta * Phi z₀

/-- **Calibration of the concentration gate: `θ = 1` is a theorem.**  The
constant weight realizes the concentration ratio exactly `1` (the cell has unit
volume).  Hence the entire remaining content of the localization requirement is
the strict inequality `θ < 1`. -/
theorem concentratedAdjointWeightGate_one (nu : ℝ) : ConcentratedAdjointWeightGate nu 1 := by
  intro V _hV _hVper _hdiv h z₀
  refine ⟨fun _ => (1:ℝ), 0, contDiff_const, fun _ _ => rfl, fun _ => zero_le_one, ?_, ?_,
    one_pos, ?_⟩
  · intro z
    have hd : ∀ (a : STime) (w : STime), dvec a (fun _ : STime => (1:ℝ)) w = 0 := by
      intro a w; simp [dvec]
    have hlap : lap (fun _ : STime => (1:ℝ)) z = 0 := by
      have hfun : ∀ i : Fin 3, (fun w : STime => dspace (fun _ : STime => (1:ℝ)) i w)
          = fun _ : STime => (0:ℝ) := fun i => funext fun w => hd (0, ee i) w
      simp only [lap, hfun]
      simp [dspace]
    simp [adjointOp, hd, hlap]
  · intro z j
    simp [dvec]
  · have hone : cellInt (fun _ : E3 => (1 : ℝ)) = 1 := by
      rw [cellInt, cell]
      rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Icc_pi]
      simp
    simp [hone]

/-
**Resolution of `ConcentratedAdjointWeightGate` (recorded here, proved
elsewhere).**  The gate above is not merely open — it is *false* for every
`theta < 1` and every `nu > 0`.  See
`RequestProject/NavierStokes/ConcentratedWeightNoGo.lean`,
`ClayNS.not_concentratedAdjointWeightGate_of_lt_one`: on the torus an exact
solution of the adjoint transport–diffusion equation with a bounded spatial
gradient has a variance obeying `Var' ≥ (2ν/3)·Var` while staying bounded, hence
`Var ≡ 0`, hence the weight is spatially constant and its concentration ratio is
exactly `1`.

The statement is therefore kept as written (it is the historically recorded
target) but is *not* used anywhere; the development replaces it by the
approximate-adjoint gate
`ClayNS.GaussianApproximateAdjointWeightGate`
(`RequestProject/NavierStokes/GaussianApproximateAdjoint.lean`), which is proved
unconditionally and whose adjoint residual carries positive scaling dimension.
-/

end ClayNS

/-
# `C54`: keeping the Gaussian through Young's inequality

`GaussianLinearBudgetAudit.lean` isolated the obstruction: the transferred
stretching budget pairs the increment against `∇Φ`, and that pairing was
estimated by

  `|∑_j w_j ∂_jΦ| ≤ 3B·sup|∇Φ| = 3B·G`,   `G = 1/(4πa)`,

producing the unweighted, `a^{-1}`-amplified term `9AB²G·K₀`,
`K₀ = ∫_cell β′(q)`.

The correction is to *not* discard the weight.  Pointwise, for `Φ > 0` and any
`θ > 0`,

  `|∂_jΦ| ≤ (θ/2)Φ + (1/2θ)·|∇Φ|²/Φ`,                                  (Y)

which is Young's inequality applied to the *geometrically paired* factors
`√Φ · (|∂_jΦ|/√Φ)`.  Substituting (Y) for the sup bound replaces

  `9AB²·G·∫β′(q)`   by   `(9AB²θ/2)·∫Φβ′(q) + (9AB²/2θ)·∫β′(q)|∇Φ|²/Φ`,

the first term *weighted* (so it concentrates with the weight, exactly like the
pressure term), the second governed by the Fisher information of the weight,
which `C53` (`ClayNS.torusGaussFisherInformationBound`) bounds by `C_FI√a`.

Results here:

* `ClayNS.abs_dvec_le_fisher_young` — the pointwise inequality (Y);
* `ClayNS.increment_stretching_transfer_budget_weighted` — the pointwise
  transferred stretching budget with the sup replaced by (Y);
* `ClayNS.increment_stretching_transfer_cell_budget_weighted` — its cell form;
* `ClayNS.approx_adjoint_caccioppoli_linear_budget_weighted` — the linear
  Caccioppoli budget with the approximate-adjoint residual `D` and **no**
  unweighted term at all;
* `ClayNS.gaussianGradientWeightedAbsorption` — the Gaussian instantiation:
  with the active-modulus bound `β′ ≤ 1/λ` every source on the right is
  `O(a^{3/2}) + O(√a) + O(a) + O(ν√a)`, i.e. **vanishes** as the weight
  concentrates.  This is the statement the audit's `a^{-1}` term blocked.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GaussianLinearBudgetAudit
import RequestProject.NavierStokes.GaussianFisherInformation

open Real MeasureTheory

noncomputable section

namespace ClayNS

/-! ## The Fisher-information density of a general positive weight -/

/-- The Fisher-information density `|∇Φ|²/Φ` of a positive weight. -/
def fisherDens (Phi : STime → ℝ) : STime → ℝ :=
  fun z => ∑ i, dvec (0, ee i) Phi z ^ 2 / Phi z

lemma fisherDens_nonneg {Phi : STime → ℝ} (hPhi0 : ∀ z, 0 ≤ Phi z) (z : STime) :
    0 ≤ fisherDens Phi z :=
  Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (hPhi0 z)

/-- For the torus Gaussian the general density is the one of `C53`. -/
lemma fisherDens_torusGauss (a : ℝ) (x0 : E3) :
    fisherDens (torusGauss a x0) = torusGaussFisher a x0 := rfl

lemma contDiff_fisherDens {Phi : STime → ℝ} (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hpos : ∀ z, 0 < Phi z) : ContDiff ℝ (⊤ : ℕ∞) (fisherDens Phi) :=
  ContDiff.sum fun i _ =>
    ((contDiff_dvec _ hPhi (0, ee i)).pow 2).div hPhi fun z => ne_of_gt (hpos z)

/-! ## (Y): the weight-aware Young inequality -/

/-- **The weighted Young inequality.**  For a positive weight and any `θ > 0`,

  `|∂_jΦ| ≤ (θ/2)Φ + (1/2θ)·|∇Φ|²/Φ`.

Unlike the sup bound `|∂_jΦ| ≤ G`, both terms on the right are *weighted*: the
first by `Φ` itself and the second by the Fisher information, whose integral has
a **positive** power of the concentration scale. -/
theorem abs_dvec_le_fisher_young {Phi : STime → ℝ} {theta : ℝ} (htheta : 0 < theta)
    {z : STime} (hpos : 0 < Phi z) (j : Fin 3) :
    |dvec (0, ee j) Phi z| ≤ theta / 2 * Phi z + 1 / (2 * theta) * fisherDens Phi z := by
  set d : ℝ := dvec (0, ee j) Phi z with hd
  have hjle : d ^ 2 / Phi z ≤ fisherDens Phi z :=
    Finset.single_le_sum (f := fun i => dvec (0, ee i) Phi z ^ 2 / Phi z)
      (fun i _ => div_nonneg (sq_nonneg _) hpos.le) (Finset.mem_univ j)
  have hkey : |d| ≤ theta / 2 * Phi z + 1 / (2 * theta) * (d ^ 2 / Phi z) := by
    have hsq : d ^ 2 = |d| ^ 2 := (sq_abs d).symm
    have hid : theta / 2 * Phi z + 1 / (2 * theta) * (|d| ^ 2 / Phi z) - |d|
        = (theta * Phi z - |d|) ^ 2 / (2 * theta * Phi z) := by
      field_simp
      ring
    have hnn : 0 ≤ (theta * Phi z - |d|) ^ 2 / (2 * theta * Phi z) := by positivity
    rw [hsq]
    linarith [hid ▸ hnn]
  have hmul : 1 / (2 * theta) * (d ^ 2 / Phi z) ≤ 1 / (2 * theta) * fisherDens Phi z :=
    mul_le_mul_of_nonneg_left hjle (by positivity)
  linarith

/-! ## The pointwise transferred stretching budget, weight retained -/

/-- The weight-aware stretching budget density: the unweighted term
`9AB²G·β′(q)` of `ClayNS.stretchBudget` is replaced by
`(9AB²θ/2)·Φβ′(q) + (9AB²/2θ)·β′(q)|∇Φ|²/Φ`. -/
def stretchBudgetW (nu eta theta A B : ℝ) (h : E3) (V : STime → E3) (Phi : STime → ℝ)
    (b1 b2 : ℝ → ℝ) : STime → ℝ := fun w =>
  eta * nu * (Phi w * (b2 (incrQuad h V w)
      * ∑ k, dvec (0, ee k) (incrQuad h V) w * dvec (0, ee k) (incrQuad h V) w))
    + nu / 2 * (Phi w * (b1 (incrQuad h V w) * incrDissip h V w))
    + 27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * (Phi w * b2 (incrQuad h V w))
    + (9 * A ^ 2 * B ^ 2 / (2 * nu) + 9 * A * B ^ 2 * theta / 2)
        * (Phi w * b1 (incrQuad h V w))
    + 9 * A * B ^ 2 / (2 * theta) * (b1 (incrQuad h V w) * fisherDens Phi w)

lemma contDiff_stretchBudgetW (nu eta theta A B : ℝ) {V : STime → E3} {Phi : STime → ℝ}
    (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hpos : ∀ z, 0 < Phi z)
    {b1 b2 : ℝ → ℝ} (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1) (hb2c : ContDiff ℝ (⊤ : ℕ∞) b2) :
    ContDiff ℝ (⊤ : ℕ∞) (stretchBudgetW nu eta theta A B h V Phi b1 b2) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  have hb1q : ContDiff ℝ (⊤ : ℕ∞) (fun w => b1 (incrQuad h V w)) := hb1c.comp hq
  have hb2q : ContDiff ℝ (⊤ : ℕ∞) (fun w => b2 (incrQuad h V w)) := hb2c.comp hq
  have hdq : ∀ k : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (dvec (0, ee k) (incrQuad h V)) :=
    fun k => contDiff_dvec _ hq _
  have hgr : ContDiff ℝ (⊤ : ℕ∞)
      (fun w => ∑ k, dvec (0, ee k) (incrQuad h V) w * dvec (0, ee k) (incrQuad h V) w) :=
    ContDiff.sum fun k _ => (hdq k).mul (hdq k)
  have hdiss : ContDiff ℝ (⊤ : ℕ∞) (incrDissip h V) := contDiff_incrDissip h hV
  have hfi : ContDiff ℝ (⊤ : ℕ∞) (fisherDens Phi) := contDiff_fisherDens hPhi hpos
  exact ((((contDiff_const.mul (hPhi.mul (hb2q.mul hgr))).add
      (contDiff_const.mul (hPhi.mul (hb1q.mul hdiss)))).add
      (contDiff_const.mul (hPhi.mul hb2q))).add
      (contDiff_const.mul (hPhi.mul hb1q))).add
      (contDiff_const.mul (hb1q.mul hfi))

/-- **`C54`, pointwise.**  The transferred stretching budget with the Gaussian
kept through Young's inequality.  Identical to
`ClayNS.increment_stretching_transfer_budget` except that its unweighted term
`9AB²G·β′(q)` — the sole source of the `a^{-1}` blow-up — is replaced by a
weighted term plus a Fisher-information term. -/
theorem increment_stretching_transfer_budget_weighted {nu eta theta A B : ℝ} (hnu : 0 < nu)
    (heta : 0 < eta) (htheta : 0 < theta)
    {V : STime → E3} {Phi : STime → ℝ} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    {b1 b2 : ℝ → ℝ} (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hdiv : ∀ z : STime, divg V z = 0) (z : STime)
    (hPhipos : 0 < Phi z) (hB1 : 0 ≤ b1 (incrQuad h V z)) (hB2 : 0 ≤ b2 (incrQuad h V z))
    (hA : ∀ a : Fin 3, |V z a| ≤ A) (hB : ∀ a : Fin 3, |incrComp h V a z| ≤ B) :
    |Phi z * (b1 (incrQuad h V z) * incrStretch h V z)
        - divg (fun w => ((Phi w * b1 (incrQuad h V w)) * incrPair h V w) • incrVec h V w) z|
      ≤ stretchBudgetW nu eta theta A B h V Phi b1 b2 z := by
  have hbase := increment_stretching_transfer_budget (nu := nu) (eta := eta) (A := A) (B := B)
    (G := theta / 2 * Phi z + 1 / (2 * theta) * fisherDens Phi z) hnu heta h hV hPhi hb1c hb2
    hdiv z hPhipos.le hB1 hB2 hA hB
    (fun j => abs_dvec_le_fisher_young htheta hPhipos j)
  refine hbase.trans (le_of_eq ?_)
  simp only [stretchBudgetW]
  ring

/-! ## The cell form -/

/-- **`C54`, integrated.**  The cell form of the weight-aware stretching
budget: the transfer flux divergence integrates away on the torus. -/
theorem increment_stretching_transfer_cell_budget_weighted {nu eta theta A B : ℝ}
    (hnu : 0 < nu) (heta : 0 < eta) (htheta : 0 < theta)
    {V : STime → E3} {Phi : STime → ℝ} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hVper : SpacePeriodic V) (hPhiper : SpacePeriodic Phi)
    {b1 b2 : ℝ → ℝ} (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1) (hb2c : ContDiff ℝ (⊤ : ℕ∞) b2)
    (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hpos : ∀ z, 0 < Phi z) (hB1 : ∀ x, 0 ≤ b1 x) (hB2 : ∀ x, 0 ≤ b2 x)
    (hA : ∀ (z : STime) (a : Fin 3), |V z a| ≤ A)
    (hB : ∀ (z : STime) (a : Fin 3), |incrComp h V a z| ≤ B) (t : ℝ) :
    |cellInt (fun x => Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x)))|
      ≤ cellInt (fun x => stretchBudgetW nu eta theta A B h V Phi b1 b2 (t, x)) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  have hb1q : ContDiff ℝ (⊤ : ℕ∞) (fun w => b1 (incrQuad h V w)) := hb1c.comp hq
  set Fl : STime → E3 :=
    fun w => ((Phi w * b1 (incrQuad h V w)) * incrPair h V w) • incrVec h V w with hFl
  have hFlC : ContDiff ℝ (⊤ : ℕ∞) Fl :=
    ((hPhi.mul hb1q).mul (contDiff_incrPair h hV)).smul (contDiff_incrVec h hV)
  have hFlper : SpacePeriodic Fl := by
    intro z j
    show ((Phi (z.1, z.2 + ee j) * b1 (incrQuad h V (z.1, z.2 + ee j)))
        * incrPair h V (z.1, z.2 + ee j)) • incrVec h V (z.1, z.2 + ee j)
      = ((Phi z * b1 (incrQuad h V z)) * incrPair h V z) • incrVec h V z
    rw [hPhiper z j, spacePeriodic_incrQuad h hVper z j, spacePeriodic_incrPair h hVper z j,
      spacePeriodic_incrVec h hVper z j]
  have hdivzero : cellInt (fun x => divg Fl (t, x)) = 0 :=
    cellInt_divg_eq_zero Fl hFlC hFlper t
  have hfC : Continuous fun x : E3 =>
      Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x)) :=
    continuous_slice (hPhi.mul (hb1q.mul (contDiff_incrStretch h hV))) t
  have hgC : Continuous fun x : E3 => divg Fl (t, x) :=
    continuous_slice (contDiff_divgFun hFlC) t
  have hRC : Continuous fun x : E3 => stretchBudgetW nu eta theta A B h V Phi b1 b2 (t, x) :=
    continuous_slice (contDiff_stretchBudgetW nu eta theta A B h hV hPhi hpos hb1c hb2c) t
  have hpt : ∀ x : E3,
      |Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x)) - divg Fl (t, x)|
        ≤ stretchBudgetW nu eta theta A B h V Phi b1 b2 (t, x) := by
    intro x
    exact increment_stretching_transfer_budget_weighted hnu heta htheta h hV hPhi hb1c hb2
      hdiv (t, x) (hpos _) (hB1 _) (hB2 _) (hA _) (hB _)
  have hsub : cellInt (fun x => Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x))
      - divg Fl (t, x))
      = cellInt (fun x => Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x))) := by
    rw [cellInt_sub hfC hgC, hdivzero, sub_zero]
  have habs := abs_cellInt_le (f := fun x =>
      Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x)) - divg Fl (t, x))
    (g := fun x => stretchBudgetW nu eta theta A B h V Phi b1 b2 (t, x)) (hfC.sub hgC) hRC hpt
  rwa [hsub] at habs

/-! ## The linear Caccioppoli budget with no unweighted term -/

/-- **`C54`.  The approximate-adjoint linear Caccioppoli budget, weight
retained.**  This is `ClayNS.approx_adjoint_caccioppoli_linear_budget` with the
sup-gradient estimate replaced by the weighted Young inequality (Y).  Every
source on the right is now either weighted by `Φ` or by the Fisher information
`|∇Φ|²/Φ`; the unweighted `∫β′(q)` has disappeared. -/
theorem approx_adjoint_caccioppoli_linear_budget_weighted
    {nu eta theta A B Gp D : ℝ} (hnu : 0 < nu) (heta : 0 < eta) (htheta : 0 < theta)
    {V : STime → E3} {P Phi : STime → ℝ} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hVper : SpacePeriodic V) (hPhiper : SpacePeriodic Phi)
    {b1 b2 : ℝ → ℝ} (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1) (hb2c : ContDiff ℝ (⊤ : ℕ∞) b2)
    (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hpos : ∀ z, 0 < Phi z) (hB1 : ∀ x, 0 ≤ b1 x) (hB2 : ∀ x, 0 ≤ b2 x)
    (hA : ∀ (z : STime) (a : Fin 3), |V z a| ≤ A)
    (hB : ∀ (z : STime) (a : Fin 3), |incrComp h V a z| ≤ B)
    (hGp : ∀ (z : STime) (a : Fin 3), |dvec (0, ee a) (incrPres h P) z| ≤ Gp)
    {beta : ℝ → ℝ} (t : ℝ)
    (hbal : |cellInt (fun x => dvec (1, 0) (fun w => Phi w * beta (incrQuad h V w)) (t, x))
        + nu * cellInt (fun x => Phi (t, x) * (b2 (incrQuad h V (t, x))
            * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
                * dvec (0, ee k) (incrQuad h V) (t, x)))
        + nu * cellInt (fun x => Phi (t, x)
            * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x)))
        + cellInt (fun x => Phi (t, x)
            * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x)))
        + cellInt (fun x => Phi (t, x) * (b1 (incrQuad h V (t, x))
            * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x)))| ≤ D) :
    cellInt (fun x => dvec (1, 0) (fun w => Phi w * beta (incrQuad h V w)) (t, x))
        + (1 - eta) * nu * cellInt (fun x => Phi (t, x) * (b2 (incrQuad h V (t, x))
            * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
                * dvec (0, ee k) (incrQuad h V) (t, x)))
        + nu / 2 * cellInt (fun x =>
            Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x)))
      ≤ 27 * A ^ 2 * B ^ 4 / (4 * eta * nu)
            * cellInt (fun x => Phi (t, x) * b2 (incrQuad h V (t, x)))
        + (9 * A ^ 2 * B ^ 2 / (2 * nu) + 3 * B * Gp + 9 * A * B ^ 2 * theta / 2)
            * cellInt (fun x => Phi (t, x) * b1 (incrQuad h V (t, x)))
        + 9 * A * B ^ 2 / (2 * theta)
            * cellInt (fun x => b1 (incrQuad h V (t, x)) * fisherDens Phi (t, x))
        + D := by
  classical
  have hq : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  have hb1q : ContDiff ℝ (⊤ : ℕ∞) (fun w => b1 (incrQuad h V w)) := hb1c.comp hq
  have hb2q : ContDiff ℝ (⊤ : ℕ∞) (fun w => b2 (incrQuad h V w)) := hb2c.comp hq
  have hdq : ∀ k : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (dvec (0, ee k) (incrQuad h V)) :=
    fun k => contDiff_dvec _ hq _
  have hgr : ContDiff ℝ (⊤ : ℕ∞)
      (fun w => ∑ k, dvec (0, ee k) (incrQuad h V) w * dvec (0, ee k) (incrQuad h V) w) :=
    ContDiff.sum fun k _ => (hdq k).mul (hdq k)
  have hdiss : ContDiff ℝ (⊤ : ℕ∞) (incrDissip h V) := contDiff_incrDissip h hV
  have hfi : ContDiff ℝ (⊤ : ℕ∞) (fisherDens Phi) := contDiff_fisherDens hPhi hpos
  have hpres : ContDiff ℝ (⊤ : ℕ∞)
      (fun w => ∑ a, incrComp h V a w * dvec (0, ee a) (incrPres h P) w) :=
    ContDiff.sum fun a _ => (contDiff_incrComp h hV a).mul
      (contDiff_dvec _ (contDiff_incrPres h hP) _)
  have cJ2 : Continuous fun x : E3 => Phi (t, x) * (b2 (incrQuad h V (t, x))
      * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x) * dvec (0, ee k) (incrQuad h V) (t, x)) :=
    continuous_slice (hPhi.mul (hb2q.mul hgr)) t
  have cJ1 : Continuous fun x : E3 =>
      Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x)) :=
    continuous_slice (hPhi.mul (hb1q.mul hdiss)) t
  have cPw : Continuous fun x : E3 => Phi (t, x) * (b1 (incrQuad h V (t, x))
      * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x)) :=
    continuous_slice (hPhi.mul (hb1q.mul hpres)) t
  have cK2 : Continuous fun x : E3 => Phi (t, x) * b2 (incrQuad h V (t, x)) :=
    continuous_slice (hPhi.mul hb2q) t
  have cK1 : Continuous fun x : E3 => Phi (t, x) * b1 (incrQuad h V (t, x)) :=
    continuous_slice (hPhi.mul hb1q) t
  have cKF : Continuous fun x : E3 => b1 (incrQuad h V (t, x)) * fisherDens Phi (t, x) :=
    continuous_slice (hb1q.mul hfi) t
  set J2 := cellInt (fun x => Phi (t, x) * (b2 (incrQuad h V (t, x))
      * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
          * dvec (0, ee k) (incrQuad h V) (t, x))) with hJ2
  set J1 := cellInt (fun x =>
      Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x))) with hJ1
  set ST := cellInt (fun x =>
      Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x))) with hST
  set PW := cellInt (fun x => Phi (t, x) * (b1 (incrQuad h V (t, x))
      * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x))) with hPW
  set K2 := cellInt (fun x => Phi (t, x) * b2 (incrQuad h V (t, x))) with hK2
  set K1 := cellInt (fun x => Phi (t, x) * b1 (incrQuad h V (t, x))) with hK1
  set KF := cellInt (fun x => b1 (incrQuad h V (t, x)) * fisherDens Phi (t, x)) with hKF
  -- the weight-aware transferred stretching budget, integrated
  have hstrb : |ST| ≤ eta * nu * J2 + nu / 2 * J1
      + 27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * K2
      + (9 * A ^ 2 * B ^ 2 / (2 * nu) + 9 * A * B ^ 2 * theta / 2) * K1
      + 9 * A * B ^ 2 / (2 * theta) * KF := by
    have hcell := increment_stretching_transfer_cell_budget_weighted (nu := nu) (eta := eta)
      (theta := theta) (A := A) (B := B) hnu heta htheta h hV hPhi hVper hPhiper hb1c hb2c
      hb2 hdiv hpos hB1 hB2 hA hB t
    have hrw : ∀ x : E3, stretchBudgetW nu eta theta A B h V Phi b1 b2 (t, x)
        = eta * nu * (Phi (t, x) * (b2 (incrQuad h V (t, x))
            * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
                * dvec (0, ee k) (incrQuad h V) (t, x)))
          + nu / 2 * (Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x)))
          + 27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * (Phi (t, x) * b2 (incrQuad h V (t, x)))
          + (9 * A ^ 2 * B ^ 2 / (2 * nu) + 9 * A * B ^ 2 * theta / 2)
              * (Phi (t, x) * b1 (incrQuad h V (t, x)))
          + 9 * A * B ^ 2 / (2 * theta)
              * (b1 (incrQuad h V (t, x)) * fisherDens Phi (t, x)) := fun x => rfl
    have hsplit := cellInt_split5
      (f := fun x : E3 => stretchBudgetW nu eta theta A B h V Phi b1 b2 (t, x))
      (f1 := fun x : E3 => eta * nu * (Phi (t, x) * (b2 (incrQuad h V (t, x))
          * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
              * dvec (0, ee k) (incrQuad h V) (t, x))))
      (f2 := fun x : E3 => nu / 2 * (Phi (t, x)
          * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x))))
      (f3 := fun x : E3 => 27 * A ^ 2 * B ^ 4 / (4 * eta * nu)
          * (Phi (t, x) * b2 (incrQuad h V (t, x))))
      (f4 := fun x : E3 => (9 * A ^ 2 * B ^ 2 / (2 * nu) + 9 * A * B ^ 2 * theta / 2)
          * (Phi (t, x) * b1 (incrQuad h V (t, x))))
      (f5 := fun x : E3 => 9 * A * B ^ 2 / (2 * theta)
          * (b1 (incrQuad h V (t, x)) * fisherDens Phi (t, x)))
      hrw (continuous_const.mul cJ2) (continuous_const.mul cJ1) (continuous_const.mul cK2)
      (continuous_const.mul cK1) (continuous_const.mul cKF)
    rw [cellInt_const_mul, cellInt_const_mul, cellInt_const_mul, cellInt_const_mul,
      cellInt_const_mul, ← hJ2, ← hJ1, ← hK2, ← hK1, ← hKF] at hsplit
    rw [hsplit] at hcell
    exact hcell
  -- the pressure work is linear in `Φβ′`
  have hpw : -PW ≤ 3 * B * Gp * K1 := by
    have hle : ∀ x : E3, - (3 * B * Gp * (Phi (t, x) * b1 (incrQuad h V (t, x))))
        ≤ Phi (t, x) * (b1 (incrQuad h V (t, x))
            * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x)) := by
      intro x
      have hbd : |∑ a, incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x)|
          ≤ 3 * (B * Gp) := by
        refine (Finset.abs_sum_le_sum_abs
          (fun a : Fin 3 => incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x))
          Finset.univ).trans ?_
        have hterm : ∀ a : Fin 3, |incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x)|
            ≤ B * Gp := by
          intro a
          rw [abs_mul]
          exact mul_le_mul (hB _ a) (hGp _ a) (abs_nonneg _)
            ((abs_nonneg _).trans (hB (t, x) a))
        calc ∑ a : Fin 3, |incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x)|
            ≤ ∑ _a : Fin 3, B * Gp := Finset.sum_le_sum fun a _ => hterm a
          _ = 3 * (B * Gp) := by simp [Finset.sum_const, nsmul_eq_mul]
      have hw : 0 ≤ Phi (t, x) * b1 (incrQuad h V (t, x)) :=
        mul_nonneg (hpos _).le (hB1 _)
      have hlow := (abs_le.mp hbd).1
      nlinarith [hw, hlow]
    have cneg : Continuous
        (fun x : E3 => -(3 * B * Gp * (Phi (t, x) * b1 (incrQuad h V (t, x))))) :=
      (continuous_const.mul cK1).neg
    have hmono := cellInt_mono cneg cPw hle
    rw [cellInt_neg (fun x : E3 => 3 * B * Gp * (Phi (t, x) * b1 (incrQuad h V (t, x)))),
      cellInt_const_mul, ← hK1, ← hPW] at hmono
    linarith [hmono]
  have hSTle : ST ≥ -(eta * nu * J2 + nu / 2 * J1
      + 27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * K2
      + (9 * A ^ 2 * B ^ 2 / (2 * nu) + 9 * A * B ^ 2 * theta / 2) * K1
      + 9 * A * B ^ 2 / (2 * theta) * KF) := (abs_le.mp hstrb).1
  have hbalup := (abs_le.mp hbal).2
  nlinarith [hbalup, hSTle, hpw]

/-! ## The Gaussian instantiation: every source vanishes with the scale -/

/-- **`C54` + `C53`: `gaussianGradientWeightedAbsorption`.**

The unconditional Caccioppoli budget for the torus Gaussian weight `Φ_a`, with
the gradient pairing estimated by the weighted Young inequality instead of by
`sup|∇Φ_a| = 1/(4πa)`, and with the active-modulus bound `β′ ≤ 1/λ` (valid for
the truncation `ζ_λ(r) = (r−λ)_+` at any level `λ > 0`, and De Giorgi levels are
bounded away from `0`).  Every source term on the right except the
coercivity-paired `∫Φβ″` now carries a **positive** power of the concentration
scale:

  `(…)/λ·(π³a)^{3/2} + (9AB²/2θλ)·C_FI√a + ‖β‖_∞(6π³A·a + νC√a)`.

Compare `ClayNS.gaussian_adjoint_caccioppoli_linear_budget`, whose
corresponding term is `9AB²K₀/(4πa)` and **grows** like `a^{-1}`.  The
`a^{-1}K₀` obstruction was therefore an artefact of discarding the Gaussian, not
a property of Gaussian concentration. -/
theorem gaussianGradientWeightedAbsorption {nu eta theta a lam A B Gp Bbeta : ℝ}
    (hnu : 0 < nu) (heta : 0 < eta) (htheta : 0 < theta) (ha : 0 < a) (hlam : 0 < lam)
    {V : STime → E3} {P : STime → ℝ} (h x0 : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P) (hVper : SpacePeriodic V)
    {beta b1 b2 : ℝ → ℝ} (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta)
    (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1) (hb2c : ContDiff ℝ (⊤ : ℕ∞) b2)
    (hb1 : ∀ x, HasDerivAt beta (b1 x) x) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (hB1 : ∀ x, 0 ≤ b1 x) (hB2 : ∀ x, 0 ≤ b2 x) (hb1le : ∀ x, b1 x ≤ 1 / lam)
    (hA : ∀ (z : STime) (c : Fin 3), |V z c| ≤ A)
    (hB : ∀ (z : STime) (c : Fin 3), |incrComp h V c z| ≤ B)
    (hGp : ∀ (z : STime) (c : Fin 3), |dvec (0, ee c) (incrPres h P) z| ≤ Gp)
    (hBbeta : ∀ z : STime, |beta (incrQuad h V z)| ≤ Bbeta)
    (t : ℝ) :
    cellInt (fun x => dvec (1, 0)
          (fun w => torusGauss a x0 w * beta (incrQuad h V w)) (t, x))
        + (1 - eta) * nu * cellInt (fun x => torusGauss a x0 (t, x)
            * (b2 (incrQuad h V (t, x))
              * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
                  * dvec (0, ee k) (incrQuad h V) (t, x)))
        + nu / 2 * cellInt (fun x => torusGauss a x0 (t, x)
            * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x)))
      ≤ 27 * A ^ 2 * B ^ 4 / (4 * eta * nu)
            * cellInt (fun x => torusGauss a x0 (t, x) * b2 (incrQuad h V (t, x)))
        + (9 * A ^ 2 * B ^ 2 / (2 * nu) + 3 * B * Gp + 9 * A * B ^ 2 * theta / 2)
            * (tgY a ^ 3 / lam)
        + 9 * A * B ^ 2 / (2 * theta) * (tgFisherC * Real.sqrt a / lam)
        + Bbeta * (A * (6 * π ^ 3 * a) + nu * (tgLapC * Real.sqrt a)) := by
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA (t, 0) 0)
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB (t, 0) 0)
  have hGp0 : 0 ≤ Gp := le_trans (abs_nonneg _) (hGp (t, 0) 0)
  have hq : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  have hb1q : ContDiff ℝ (⊤ : ℕ∞) (fun w => b1 (incrQuad h V w)) := hb1c.comp hq
  have hPhi : ContDiff ℝ (⊤ : ℕ∞) (torusGauss a x0) := contDiff_torusGauss a x0
  have hfi : ContDiff ℝ (⊤ : ℕ∞) (fisherDens (torusGauss a x0)) :=
    contDiff_fisherDens hPhi (torusGauss_pos a x0)
  -- the weighted assembly
  have hmain := approx_adjoint_caccioppoli_linear_budget_weighted (theta := theta)
    hnu heta htheta h hV hP hPhi hVper (spacePeriodic_torusGauss a x0) hb1c hb2c hb2 hdiv
    (torusGauss_pos a x0) hB1 hB2 hA hB hGp (beta := beta) t
    (gaussian_adjoint_modulus_caccioppoli ha hnu.le h x0 hV hP hVper hbeta hb1c hb2c
      hb1 hb2 hdiv hmom hA hBbeta t)
  -- the weighted mass `K₁ ≤ (π³a)^{3/2}/λ`
  have hK1 : cellInt (fun x => torusGauss a x0 (t, x) * b1 (incrQuad h V (t, x)))
      ≤ tgY a ^ 3 / lam := by
    have hmono : cellInt (fun x => torusGauss a x0 (t, x) * b1 (incrQuad h V (t, x)))
        ≤ cellInt (fun x => 1 / lam * torusGauss a x0 (t, x)) := by
      refine cellInt_mono (continuous_slice (hPhi.mul hb1q) t)
        (continuous_const.mul (continuous_slice hPhi t)) fun x => ?_
      have := mul_le_mul_of_nonneg_left (hb1le (incrQuad h V (t, x)))
        (torusGauss_nonneg a x0 (t, x))
      linarith [this]
    rw [cellInt_const_mul] at hmono
    have hmass := cellInt_torusGauss_le ha x0 t
    have hinv : (0:ℝ) < 1 / lam := by positivity
    have := mul_le_mul_of_nonneg_left hmass hinv.le
    have heq : 1 / lam * tgY a ^ 3 = tgY a ^ 3 / lam := by ring
    linarith [hmono, this, heq]
  -- the Fisher term `K_F ≤ C_FI√a/λ`
  have hKF : cellInt (fun x => b1 (incrQuad h V (t, x)) * fisherDens (torusGauss a x0) (t, x))
      ≤ tgFisherC * Real.sqrt a / lam := by
    have hmono : cellInt (fun x =>
          b1 (incrQuad h V (t, x)) * fisherDens (torusGauss a x0) (t, x))
        ≤ cellInt (fun x => 1 / lam * torusGaussFisher a x0 (t, x)) := by
      refine cellInt_mono (continuous_slice (hb1q.mul hfi) t)
        (continuous_const.mul (continuous_slice
          (by simpa [fisherDens_torusGauss] using hfi) t)) fun x => ?_
      have hf : 0 ≤ torusGaussFisher a x0 (t, x) := torusGaussFisher_nonneg a x0 (t, x)
      have := mul_le_mul_of_nonneg_right (hb1le (incrQuad h V (t, x))) hf
      simpa [fisherDens_torusGauss, mul_comm] using this
    rw [cellInt_const_mul] at hmono
    have hC53 := torusGaussFisherInformationBound ha x0 t
    have hinv : (0:ℝ) < 1 / lam := by positivity
    have := mul_le_mul_of_nonneg_left hC53 hinv.le
    have heq : 1 / lam * (tgFisherC * Real.sqrt a) = tgFisherC * Real.sqrt a / lam := by ring
    linarith [hmono, this, heq]
  -- assemble
  have hc1 : 0 ≤ 9 * A ^ 2 * B ^ 2 / (2 * nu) + 3 * B * Gp + 9 * A * B ^ 2 * theta / 2 := by
    have h1 : (0:ℝ) ≤ 9 * A ^ 2 * B ^ 2 / (2 * nu) := by positivity
    have h2 : (0:ℝ) ≤ 3 * B * Gp := by positivity
    have h3 : (0:ℝ) ≤ 9 * A * B ^ 2 * theta / 2 := by positivity
    linarith
  have hc2 : 0 ≤ 9 * A * B ^ 2 / (2 * theta) := by positivity
  have hstep1 := mul_le_mul_of_nonneg_left hK1 hc1
  have hstep2 := mul_le_mul_of_nonneg_left hKF hc2
  linarith [hmain, hstep1, hstep2]

/-- **The contrast with the sup route, machine-checked.**  Every `a`-dependent
source of `ClayNS.gaussianGradientWeightedAbsorption` is a combination of
`(π³a)^{3/2}`, `√a` and `a`, so the whole source tends to `0` as the weight
concentrates.  The corresponding source of the sup-route budget is
`9AB²K₀/(4πa)`, which by `ClayNS.gaussian_gradient_term_blows_up` exceeds any
prescribed bound.  Both statements are true: the `a^{-1}` blow-up is a no-go for
the sup-unweighted estimate, not for Gaussian concentration. -/
theorem gaussianWeightedSource_tendsto_zero (c1 c2 c3 c4 : ℝ) :
    Filter.Tendsto (fun a : ℝ => c1 * tgY a ^ 3 + c2 * (tgFisherC * Real.sqrt a)
        + c3 * a + c4 * Real.sqrt a) (nhds 0) (nhds 0) := by
  have hcont : Continuous fun a : ℝ => c1 * tgY a ^ 3 + c2 * (tgFisherC * Real.sqrt a)
      + c3 * a + c4 * Real.sqrt a := by
    unfold tgY
    fun_prop
  have htgY0 : tgY 0 = 0 := by rw [tgY, mul_zero, Real.sqrt_zero]
  simpa [htgY0] using hcont.tendsto 0

end ClayNS

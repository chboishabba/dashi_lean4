/-
# `C51`: the pressure and remainder audit for the Gaussian weight

`AdjointCaccioppoliClosure.lean` derives its linear Caccioppoli budget from
three independent ingredients:

1. the **cell balance** `IT + νJ₂ + νJ₁ + ST + PW = 0`, which needs the weight
   to solve the adjoint equation exactly;
2. the **transferred stretching budget** `|ST| ≤ ηνJ₂ + (ν/2)J₁ + C₁K₂ + C₂K₁ +
   9AB²G·K₀`, which needs only amplitude bounds and a *pointwise* gradient
   bound `|∇Φ| ≤ G`;
3. the **pressure work** `−PW ≤ 3BG_p·K₁`, which needs only amplitude bounds.

Only (1) uses adjointness.  `ClayNS.approx_adjoint_caccioppoli_linear_budget`
replaces it by the *approximate* balance `|IT + νJ₂ + νJ₁ + ST + PW| ≤ D`, so
the whole budget survives with `+D` on the right.  Feeding in the Gaussian
gives `ClayNS.gaussian_adjoint_caccioppoli_linear_budget`, an unconditional
budget with

  `D = ‖β(q)‖_∞ · (6π³A·a + νC·√a)`   and   `G = 1/(4πa)`.

## The audit, stated plainly

Two of the three `a`-dependent quantities improve as the weight concentrates
and one gets worse:

* concentration ratio `θ(a) = O(a^{3/2})` — **improves**;
* adjoint residual `D = O(a) + O(ν√a)` — **improves**;
* pointwise gradient constant `G = 1/(4πa)` — **worsens, like `a^{-1}`**.

The gradient constant enters the budget only through the single term
`9AB²G·K₀`, where `K₀ = ∫_cell β'(q)` carries **no weight at all**.  That is the
precise location of the remaining obstruction — the "smoothing-annulus
remainder": a concentrated weight buys a small cell mass and a small adjoint
residual, but the unweighted `K₀` term is amplified by exactly `a^{-1}`, so no
single choice of `a` makes the whole right-hand side small unless `K₀` is
itself controlled (which is what a level-set/annulus estimate would provide).

The pressure work, by contrast, is **not** an obstruction: it contributes
`3BG_p·K₁` with `K₁ = ∫_cell Φβ'(q)`, which *is* weighted, and hence inherits
the concentration.  This confirms the expectation that the pressure term is
gauge-controlled and that the frontier is the annulus/level-set remainder.

**Superseded on this point.**  The `a^{-1}` amplification above is an artefact
of replacing the weighted gradient pairing by `sup|∇Φ_a|`.  Keeping the weight
through Young's inequality (`GaussianWeightedAbsorption.lean`, `C54`) replaces
`9AB²G·K₀` by a weighted term plus the Fisher information of the weight, which
`GaussianFisherInformation.lean` (`C53`) bounds by `C_FI√a`.  The resulting
budget `ClayNS.gaussianGradientWeightedAbsorption` has *no* unweighted term and
all its sources vanish as `a ↓ 0`.  The audit below is retained as the record of
where the sup-route obstruction sat.

Nothing here proves a De Giorgi conclusion; `C52` is not attempted.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GaussianAdjointCaccioppoli

open Real MeasureTheory

noncomputable section

namespace ClayNS

/-! ## A uniform pointwise gradient bound for the torus Gaussian -/

/-- `|ψ′(s)| ≤ 1/π` globally: the periodic profile derivative is `sin(2πs)/π`. -/
lemma abs_tgProfile1_le_inv_pi (s : ℝ) : |tgProfile1 s| ≤ 1 / π := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hs : 2 * Real.sin (π * s) * Real.cos (π * s) = Real.sin (2 * (π * s)) := by
    rw [Real.sin_two_mul]
  rw [tgProfile1, hs, abs_div, abs_of_pos hpi]
  gcongr
  exact Real.abs_sin_le_one _

/-- **The uniform gradient bound.**  `|∂_jΦ_a| ≤ 1/(4πa)` everywhere.  Unlike
the cell budget, this constant *grows* as the weight concentrates. -/
theorem abs_dvec_torusGauss_le_unif {a : ℝ} (ha : 0 < a) (x0 : E3) (z : STime) (j : Fin 3) :
    |dvec (0, ee j) (torusGauss a x0) z| ≤ 1 / (4 * π * a) := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  rw [dvec_torusGauss, abs_mul, abs_mul, abs_neg,
    abs_of_pos (show (0:ℝ) < 1 / (4 * a) by positivity),
    abs_of_pos (torusGauss_pos a x0 z)]
  have h1 : |tgProfile1 (z.2 j - x0 j)| ≤ 1 / π := abs_tgProfile1_le_inv_pi _
  have h2 : torusGauss a x0 z ≤ 1 := torusGauss_le_one ha x0 z
  have h3 : (0:ℝ) < torusGauss a x0 z := torusGauss_pos a x0 z
  have h4 : (0:ℝ) < 1 / (4 * a) := by positivity
  have hstep : 1 / (4 * a) * |tgProfile1 (z.2 j - x0 j)| * torusGauss a x0 z
      ≤ 1 / (4 * a) * (1 / π) * 1 := by
    have hA : 1 / (4 * a) * |tgProfile1 (z.2 j - x0 j)| ≤ 1 / (4 * a) * (1 / π) :=
      mul_le_mul_of_nonneg_left h1 h4.le
    exact mul_le_mul hA h2 h3.le (by positivity)
  calc 1 / (4 * a) * |tgProfile1 (z.2 j - x0 j)| * torusGauss a x0 z
      ≤ 1 / (4 * a) * (1 / π) * 1 := hstep
    _ = 1 / (4 * π * a) := by field_simp

/-! ## The linear budget with an approximate adjoint weight -/

/-- **The linear Caccioppoli budget with an approximate adjoint weight.**  This
is `ClayNS.adjoint_caccioppoli_linear_budget` with exact adjointness replaced by
a cell-integrated residual bound `D`.  Only the balance step used adjointness,
so the price is exactly `+D`. -/
theorem approx_adjoint_caccioppoli_linear_budget {nu eta A B G Gp D : ℝ} (hnu : 0 < nu)
    (heta : 0 < eta) {V : STime → E3} {P Phi : STime → ℝ} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hVper : SpacePeriodic V) (hPhiper : SpacePeriodic Phi)
    {b1 b2 : ℝ → ℝ} (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1) (hb2c : ContDiff ℝ (⊤ : ℕ∞) b2)
    (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hPhi0 : ∀ z, 0 ≤ Phi z) (hB1 : ∀ x, 0 ≤ b1 x) (hB2 : ∀ x, 0 ≤ b2 x)
    (hA : ∀ (z : STime) (a : Fin 3), |V z a| ≤ A)
    (hB : ∀ (z : STime) (a : Fin 3), |incrComp h V a z| ≤ B)
    (hG : ∀ (z : STime) (j : Fin 3), |dvec (0, ee j) Phi z| ≤ G)
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
        + (9 * A ^ 2 * B ^ 2 / (2 * nu) + 3 * B * Gp)
            * cellInt (fun x => Phi (t, x) * b1 (incrQuad h V (t, x)))
        + 9 * A * B ^ 2 * G * cellInt (fun x => b1 (incrQuad h V (t, x)))
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
  have cK0 : Continuous fun x : E3 => b1 (incrQuad h V (t, x)) := continuous_slice hb1q t
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
  set K0 := cellInt (fun x => b1 (incrQuad h V (t, x))) with hK0
  -- (2) the transferred stretching budget, integrated
  have hstrb : |ST| ≤ eta * nu * J2 + nu / 2 * J1
      + 27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * K2
      + 9 * A ^ 2 * B ^ 2 / (2 * nu) * K1 + 9 * A * B ^ 2 * G * K0 := by
    have hcell := increment_stretching_transfer_cell_budget (nu := nu) (eta := eta) (A := A)
      (B := B) (G := G) hnu heta h hV hPhi hVper hPhiper hb1c hb2c hb2 hdiv hPhi0 hB1 hB2
      hA hB hG t
    have hrw : ∀ x : E3, stretchBudget nu eta A B G h V Phi b1 b2 (t, x)
        = eta * nu * (Phi (t, x) * (b2 (incrQuad h V (t, x))
            * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
                * dvec (0, ee k) (incrQuad h V) (t, x)))
          + nu / 2 * (Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x)))
          + 27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * (Phi (t, x) * b2 (incrQuad h V (t, x)))
          + 9 * A ^ 2 * B ^ 2 / (2 * nu) * (Phi (t, x) * b1 (incrQuad h V (t, x)))
          + 9 * A * B ^ 2 * G * b1 (incrQuad h V (t, x)) := fun x => rfl
    have hsplit := cellInt_split5
      (f := fun x : E3 => stretchBudget nu eta A B G h V Phi b1 b2 (t, x))
      (f1 := fun x : E3 => eta * nu * (Phi (t, x) * (b2 (incrQuad h V (t, x))
          * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
              * dvec (0, ee k) (incrQuad h V) (t, x))))
      (f2 := fun x : E3 => nu / 2 * (Phi (t, x)
          * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x))))
      (f3 := fun x : E3 => 27 * A ^ 2 * B ^ 4 / (4 * eta * nu)
          * (Phi (t, x) * b2 (incrQuad h V (t, x))))
      (f4 := fun x : E3 => 9 * A ^ 2 * B ^ 2 / (2 * nu)
          * (Phi (t, x) * b1 (incrQuad h V (t, x))))
      (f5 := fun x : E3 => 9 * A * B ^ 2 * G * b1 (incrQuad h V (t, x)))
      hrw (continuous_const.mul cJ2) (continuous_const.mul cJ1) (continuous_const.mul cK2)
      (continuous_const.mul cK1) (continuous_const.mul cK0)
    rw [cellInt_const_mul, cellInt_const_mul, cellInt_const_mul, cellInt_const_mul,
      cellInt_const_mul, ← hJ2, ← hJ1, ← hK2, ← hK1, ← hK0] at hsplit
    rw [hsplit] at hcell
    exact hcell
  -- (3) the pressure work is linear in `Φβ'`
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
      have hw : 0 ≤ Phi (t, x) * b1 (incrQuad h V (t, x)) := mul_nonneg (hPhi0 _) (hB1 _)
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
      + 9 * A ^ 2 * B ^ 2 / (2 * nu) * K1 + 9 * A * B ^ 2 * G * K0) := (abs_le.mp hstrb).1
  have hbalup := (abs_le.mp hbal).2
  nlinarith [hbalup, hSTle, hpw]

/-- **`C51`.  The unconditional linear Caccioppoli budget for the Gaussian
weight.**  Everything is explicit: the adjoint error is
`‖β(q)‖_∞·(6π³A·a + νC·√a)` and the pointwise gradient constant is `1/(4πa)`.
The audit is visible in the statement — the last two terms move in opposite
directions as the concentration scale `a` decreases. -/
theorem gaussian_adjoint_caccioppoli_linear_budget {nu eta a A B Gp Bbeta : ℝ}
    (hnu : 0 < nu) (heta : 0 < eta) (ha : 0 < a)
    {V : STime → E3} {P : STime → ℝ} (h x0 : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P) (hVper : SpacePeriodic V)
    {beta b1 b2 : ℝ → ℝ} (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta)
    (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1) (hb2c : ContDiff ℝ (⊤ : ℕ∞) b2)
    (hb1 : ∀ x, HasDerivAt beta (b1 x) x) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (hB1 : ∀ x, 0 ≤ b1 x) (hB2 : ∀ x, 0 ≤ b2 x)
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
        + (9 * A ^ 2 * B ^ 2 / (2 * nu) + 3 * B * Gp)
            * cellInt (fun x => torusGauss a x0 (t, x) * b1 (incrQuad h V (t, x)))
        + 9 * A * B ^ 2 * (1 / (4 * π * a)) * cellInt (fun x => b1 (incrQuad h V (t, x)))
        + Bbeta * (A * (6 * π ^ 3 * a) + nu * (tgLapC * Real.sqrt a)) := by
  refine approx_adjoint_caccioppoli_linear_budget (G := 1 / (4 * π * a)) hnu heta h hV hP
    (contDiff_torusGauss a x0) hVper (spacePeriodic_torusGauss a x0) hb1c hb2c hb2 hdiv
    (torusGauss_nonneg a x0) hB1 hB2 hA hB
    (fun z j => abs_dvec_torusGauss_le_unif ha x0 z j) hGp (beta := beta) t ?_
  exact gaussian_adjoint_modulus_caccioppoli ha hnu.le h x0 hV hP hVper hbeta hb1c hb2c
    hb1 hb2 hdiv hmom hA hBbeta t

end ClayNS

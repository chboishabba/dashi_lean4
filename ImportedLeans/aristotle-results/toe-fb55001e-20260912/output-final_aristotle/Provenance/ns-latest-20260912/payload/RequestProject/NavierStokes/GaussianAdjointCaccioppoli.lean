/-
# `C50`: the Gaussian-weighted adjoint modulus Caccioppoli budget

This is the cell-integrated form of `ClayNS.adjoint_localized_increment_residual`
with the concentrated weight of `GaussianApproximateAdjoint.lean` inserted.

Integrating the localized increment identity over the periodicity cell kills
the flux divergence exactly (`ClayNS.cellInt_divg_eq_zero`), so what survives is
the balance

```
∫ ∂_t(Φβ(q)) + ν∫ Φβ''(q)|∇q|² + ν∫ Φβ'(q)|∇δ_hu|²
    + ∫ Φβ'(q)·(stretching) + ∫ Φβ'(q)·(pressure work)
```

which for an *exact* adjoint weight is identically `0`.  For the Gaussian it is
not zero — but its size is bounded by `sup|β(q)|` times the cell adjoint
residual, and that residual was shown to be

```
∫_cell |L*_hΦ_a| ≤ 6π³A·a + νC·√a,      a = ντ.
```

So the entire cost of abandoning exact adjointness is

```
E_adjoint ≤ ‖β(q)‖_∞ · (6π³A·a + νC·√a)  →  0     as a ↓ 0,
```

*simultaneously* with the concentration ratio `θ(a) = O(a^{3/2})`.  That is the
"positive scaling dimension residual" the tranche asked for: the error is
irrelevant in the renormalization-group sense, and the weight concentrates.

`ClayNS.gaussian_adjoint_modulus_caccioppoli_le` is the rearranged Caccioppoli
form.  Note what it does **not** do: it does not bound the stretching or the
pressure work.  Those two terms remain exactly where the development left them
(`C51`), and no De Giorgi conclusion is drawn here (`C52`).

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GaussianApproximateAdjoint
import RequestProject.NavierStokes.AdjointCaccioppoliClosure

open Real MeasureTheory

noncomputable section

namespace ClayNS

/-- **`C50`.  The Gaussian-weighted adjoint modulus Caccioppoli balance.**  With
the concentrated weight `Φ_a`, the cell-integrated localized increment balance
fails to vanish by at most `Bβ` times the cell adjoint residual, which is
`O(a) + O(ν√a)`. -/
theorem gaussian_adjoint_modulus_caccioppoli {nu a Amp Bbeta : ℝ} (ha : 0 < a) (hnu : 0 ≤ nu)
    {V : STime → E3} {P : STime → ℝ} (h x0 : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P) (hVper : SpacePeriodic V)
    {beta b1 b2 : ℝ → ℝ} (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta)
    (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1) (hb2c : ContDiff ℝ (⊤ : ℕ∞) b2)
    (hb1 : ∀ x, HasDerivAt beta (b1 x) x) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (hAmp : ∀ (z : STime) (b : Fin 3), |V z b| ≤ Amp)
    (hBbeta : ∀ z : STime, |beta (incrQuad h V z)| ≤ Bbeta)
    (t : ℝ) :
    |cellInt (fun x => dvec (1, 0)
          (fun w => torusGauss a x0 w * beta (incrQuad h V w)) (t, x))
        + nu * cellInt (fun x => torusGauss a x0 (t, x) * (b2 (incrQuad h V (t, x))
            * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
                * dvec (0, ee k) (incrQuad h V) (t, x)))
        + nu * cellInt (fun x => torusGauss a x0 (t, x)
            * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x)))
        + cellInt (fun x => torusGauss a x0 (t, x)
            * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x)))
        + cellInt (fun x => torusGauss a x0 (t, x) * (b1 (incrQuad h V (t, x))
            * ∑ b, incrComp h V b (t, x) * dvec (0, ee b) (incrPres h P) (t, x)))|
      ≤ Bbeta * (Amp * (6 * π ^ 3 * a) + nu * (tgLapC * Real.sqrt a)) := by
  classical
  set Phi : STime → ℝ := torusGauss a x0 with hPhidef
  have hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi := contDiff_torusGauss a x0
  have hPhiper : SpacePeriodic Phi := spacePeriodic_torusGauss a x0
  have hB0 : 0 ≤ Bbeta := le_trans (abs_nonneg _) (hBbeta (t, x0))
  -- regularity of the ingredients
  have hq : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  have hbq : ContDiff ℝ (⊤ : ℕ∞) (fun w => beta (incrQuad h V w)) := hbeta.comp hq
  have hb1q : ContDiff ℝ (⊤ : ℕ∞) (fun w => b1 (incrQuad h V w)) := hb1c.comp hq
  have hb2q : ContDiff ℝ (⊤ : ℕ∞) (fun w => b2 (incrQuad h V w)) := hb2c.comp hq
  have hdq : ∀ k : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (dvec (0, ee k) (incrQuad h V)) :=
    fun k => contDiff_dvec _ hq _
  have hgr : ContDiff ℝ (⊤ : ℕ∞)
      (fun w => ∑ k, dvec (0, ee k) (incrQuad h V) w * dvec (0, ee k) (incrQuad h V) w) :=
    ContDiff.sum fun k _ => (hdq k).mul (hdq k)
  have hdiss : ContDiff ℝ (⊤ : ℕ∞) (incrDissip h V) := contDiff_incrDissip h hV
  have hstr : ContDiff ℝ (⊤ : ℕ∞) (incrStretch h V) := contDiff_incrStretch h hV
  have hpres : ContDiff ℝ (⊤ : ℕ∞)
      (fun w => ∑ b, incrComp h V b w * dvec (0, ee b) (incrPres h P) w) :=
    ContDiff.sum fun b _ => (contDiff_incrComp h hV b).mul
      (contDiff_dvec _ (contDiff_incrPres h hP) _)
  set F : STime → E3 := incrBetaLocFlux nu beta h V Phi with hFdef
  have hFC : ContDiff ℝ (⊤ : ℕ∞) F := contDiff_incrBetaLocFlux nu h hV hPhi hbeta
  have hFper : SpacePeriodic F :=
    spacePeriodic_incrBetaLocFlux nu h hV hPhi hbeta hVper hPhiper
  have hFzero : cellInt (fun x => divg F (t, x)) = 0 := cellInt_divg_eq_zero F hFC hFper t
  -- slice continuity
  have cT : Continuous fun x : E3 =>
      dvec (1, 0) (fun w => Phi w * beta (incrQuad h V w)) (t, x) :=
    continuous_slice (contDiff_dvec _ (hPhi.mul hbq) _) t
  have cF : Continuous fun x : E3 => divg F (t, x) := continuous_slice (contDiff_divgFun hFC) t
  have cJ2 : Continuous fun x : E3 => Phi (t, x) * (b2 (incrQuad h V (t, x))
      * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x) * dvec (0, ee k) (incrQuad h V) (t, x)) :=
    continuous_slice (hPhi.mul (hb2q.mul hgr)) t
  have cJ1 : Continuous fun x : E3 =>
      Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x)) :=
    continuous_slice (hPhi.mul (hb1q.mul hdiss)) t
  have cSt : Continuous fun x : E3 =>
      Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x)) :=
    continuous_slice (hPhi.mul (hb1q.mul hstr)) t
  have cPw : Continuous fun x : E3 => Phi (t, x) * (b1 (incrQuad h V (t, x))
      * ∑ b, incrComp h V b (t, x) * dvec (0, ee b) (incrPres h P) (t, x)) :=
    continuous_slice (hPhi.mul (hb1q.mul hpres)) t
  have cRes : Continuous fun x : E3 => Bbeta * |adjointOp nu h V Phi (t, x)| :=
    continuous_const.mul ((continuous_slice (contDiff_adjointOp_torusGauss nu a h hV x0) t).abs)
  -- the balance field
  set E : E3 → ℝ := fun x =>
    dvec (1, 0) (fun w => Phi w * beta (incrQuad h V w)) (t, x)
      + divg F (t, x)
      + nu * (Phi (t, x) * (b2 (incrQuad h V (t, x))
          * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
              * dvec (0, ee k) (incrQuad h V) (t, x)))
      + nu * (Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x)))
      + Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x))
      + Phi (t, x) * (b1 (incrQuad h V (t, x))
          * ∑ b, incrComp h V b (t, x) * dvec (0, ee b) (incrPres h P) (t, x)) with hEdef
  have cE : Continuous E := by
    refine ((((cT.add cF).add (continuous_const.mul cJ2)).add
      (continuous_const.mul cJ1)).add cSt).add cPw
  -- pointwise residual bound
  have hpt : ∀ x : E3, |E x| ≤ Bbeta * |adjointOp nu h V Phi (t, x)| := by
    intro x
    have hres := adjoint_localized_increment_residual nu V P Phi h hV hP hPhi hdiv hmom
      hbeta hb1 hb2 (t, x) (R := |adjointOp nu h V Phi (t, x)|) le_rfl
    have hsrc : incrSource nu h V P (t, x) = - incrStretch h V (t, x)
        - (∑ b, incrComp h V b (t, x) * dvec (0, ee b) (incrPres h P) (t, x))
        - nu * incrDissip h V (t, x) := rfl
    have heq : dvec (1, 0) (fun w => Phi w * beta (incrQuad h V w)) (t, x)
        + divg (incrBetaLocFlux nu beta h V Phi) (t, x)
        - (- nu * Phi (t, x) * (b2 (incrQuad h V (t, x))
              * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
                  * dvec (0, ee k) (incrQuad h V) (t, x))
            + Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrSource nu h V P (t, x)))
          = E x := by
      rw [hsrc, hEdef, hFdef]
      ring
    rw [heq] at hres
    exact hres.trans (mul_le_mul_of_nonneg_right (hBbeta (t, x)) (abs_nonneg _))
  -- integrate
  have hint : |cellInt E| ≤ cellInt (fun x => Bbeta * |adjointOp nu h V Phi (t, x)|) :=
    abs_cellInt_le cE cRes hpt
  have hsplit : cellInt E
      = cellInt (fun x : E3 => dvec (1, 0) (fun w => Phi w * beta (incrQuad h V w)) (t, x))
        + cellInt (fun x : E3 => divg F (t, x))
        + cellInt (fun x : E3 => nu * (Phi (t, x) * (b2 (incrQuad h V (t, x))
            * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
                * dvec (0, ee k) (incrQuad h V) (t, x))))
        + cellInt (fun x : E3 => nu * (Phi (t, x)
            * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x))))
        + cellInt (fun x : E3 => Phi (t, x)
            * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x)))
        + cellInt (fun x : E3 => Phi (t, x) * (b1 (incrQuad h V (t, x))
            * ∑ b, incrComp h V b (t, x) * dvec (0, ee b) (incrPres h P) (t, x))) :=
    cellInt_split6 (fun _ => rfl) cT cF (continuous_const.mul cJ2)
      (continuous_const.mul cJ1) cSt cPw
  rw [hsplit, hFzero, cellInt_const_mul, cellInt_const_mul] at hint
  have hres := cellInt_abs_adjointOp_torusGauss_le ha hnu hV hAmp h x0 t
  have hfin : cellInt (fun x : E3 => Bbeta * |adjointOp nu h V Phi (t, x)|)
      ≤ Bbeta * (Amp * (6 * π ^ 3 * a) + nu * (tgLapC * Real.sqrt a)) := by
    rw [cellInt_const_mul]
    exact mul_le_mul_of_nonneg_left hres hB0
  have hgoal : |cellInt (fun x : E3 =>
        dvec (1, 0) (fun w => Phi w * beta (incrQuad h V w)) (t, x))
      + 0
      + nu * cellInt (fun x : E3 => Phi (t, x) * (b2 (incrQuad h V (t, x))
          * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
              * dvec (0, ee k) (incrQuad h V) (t, x)))
      + nu * cellInt (fun x : E3 => Phi (t, x)
          * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x)))
      + cellInt (fun x : E3 => Phi (t, x)
          * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x)))
      + cellInt (fun x : E3 => Phi (t, x) * (b1 (incrQuad h V (t, x))
          * ∑ b, incrComp h V b (t, x) * dvec (0, ee b) (incrPres h P) (t, x)))|
      ≤ Bbeta * (Amp * (6 * π ^ 3 * a) + nu * (tgLapC * Real.sqrt a)) := le_trans hint hfin
  simpa using hgoal

/-- **`C50`, Caccioppoli form.**  Rearranged, with the adjoint error moved to
the right-hand side: the two good terms and the time derivative are controlled
by the stretching, the pressure work, and an error that vanishes with the
concentration scale. -/
theorem gaussian_adjoint_modulus_caccioppoli_le {nu a Amp Bbeta : ℝ} (ha : 0 < a)
    (hnu : 0 ≤ nu) {V : STime → E3} {P : STime → ℝ} (h x0 : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P) (hVper : SpacePeriodic V)
    {beta b1 b2 : ℝ → ℝ} (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta)
    (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1) (hb2c : ContDiff ℝ (⊤ : ℕ∞) b2)
    (hb1 : ∀ x, HasDerivAt beta (b1 x) x) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (hAmp : ∀ (z : STime) (b : Fin 3), |V z b| ≤ Amp)
    (hBbeta : ∀ z : STime, |beta (incrQuad h V z)| ≤ Bbeta)
    (t : ℝ) :
    cellInt (fun x => dvec (1, 0)
          (fun w => torusGauss a x0 w * beta (incrQuad h V w)) (t, x))
        + nu * cellInt (fun x => torusGauss a x0 (t, x) * (b2 (incrQuad h V (t, x))
            * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
                * dvec (0, ee k) (incrQuad h V) (t, x)))
        + nu * cellInt (fun x => torusGauss a x0 (t, x)
            * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x)))
      ≤ - cellInt (fun x => torusGauss a x0 (t, x)
            * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x)))
        - cellInt (fun x => torusGauss a x0 (t, x) * (b1 (incrQuad h V (t, x))
            * ∑ b, incrComp h V b (t, x) * dvec (0, ee b) (incrPres h P) (t, x)))
        + Bbeta * (Amp * (6 * π ^ 3 * a) + nu * (tgLapC * Real.sqrt a)) := by
  have h := gaussian_adjoint_modulus_caccioppoli ha hnu h x0 hV hP hVper hbeta hb1c hb2c
    hb1 hb2 hdiv hmom hAmp hBbeta t
  have h2 := (abs_le.1 h).2
  linarith

end ClayNS

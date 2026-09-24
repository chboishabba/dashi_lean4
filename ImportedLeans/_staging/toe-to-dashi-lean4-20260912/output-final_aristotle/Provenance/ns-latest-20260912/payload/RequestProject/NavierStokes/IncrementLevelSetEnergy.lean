/-
# The integrated level-set energy inequality for the increment density

`IncrementConvexSubsolution.lean` proves the *pointwise* half of `C_b`: for
`ν ≥ 0` and every smooth convex `β`, the composed increment density `β(q)`,
`q = ½|δ_h u|²`, is a subsolution,

`∂_t β(q) + u(·+h)·∇β(q) ≤ νΔβ(q) + β'(q)·(source)`.

This file integrates that inequality over the periodic cell.  Both structural
terms disappear exactly: the Laplacian is a divergence of a periodic field, and
the transport term is `div(β(q)·u(·+h))` because the shifted velocity is
divergence free.  What is left is the **level-set energy inequality**

`d/dt ∫_cell β(q) ≤ ∫_cell β'(q)·( −δ_h u·(δ_h u·∇)u − δ_h u·∇δ_h p − ν|∇δ_h u|² )`,

valid for *every* smooth convex `β` simultaneously — the truncation family the
De Giorgi iteration consumes.

## What is proved here

* `ClayNS.incrBetaEnergy`, `ClayNS.incrBetaSource` — the level quantity and its
  source.
* `ClayNS.hasDerivAt_incrBetaEnergy` — differentiation under the cell integral:
  `d/dt ∫β(q) = ∫∂_t β(q)`.
* `ClayNS.cellInt_dtBeta_le_source` — the integrated subsolution inequality.
* `ClayNS.deriv_incrBetaEnergy_le` — the two combined: the derivative of the
  level energy exists and is bounded by the source.
* `ClayNS.deriv_incrBetaEnergy_le_potential` — the potential form: with an
  entrywise strain bound `K` on the cell and `β' ≥ 0`, the stretching part of
  the source is dominated by `6K·∫β'(q)q`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.IncrementEnergyPeriodic
import RequestProject.NavierStokes.IncrementConvexSubsolution

open scoped BigOperators

noncomputable section

namespace ClayNS

/-- The cell integral of a convex composition of the increment energy density:
the De Giorgi level quantity. -/
def incrBetaEnergy (beta : ℝ → ℝ) (h : E3) (V : STime → E3) (t : ℝ) : ℝ :=
  cellInt (fun x => beta (incrQuad h V (t, x)))

/-- The interior source of the increment density: stretching, pressure work and
dissipation. -/
def incrSource (nu : ℝ) (h : E3) (V : STime → E3) (P : STime → ℝ) : STime → ℝ :=
  fun z => - incrStretch h V z
    - (∑ a, incrComp h V a z * dvec (0, ee a) (incrPres h P) z)
    - nu * incrDissip h V z

/-- The source of the level quantity: the interior source weighted by `β'(q)`. -/
def incrBetaSource (b1 : ℝ → ℝ) (nu : ℝ) (h : E3) (V : STime → E3) (P : STime → ℝ)
    (t : ℝ) : ℝ :=
  cellInt (fun x => b1 (incrQuad h V (t, x)) * incrSource nu h V P (t, x))

lemma contDiff_incrSource (nu : ℝ) {V : STime → E3} {P : STime → ℝ} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P) :
    ContDiff ℝ (⊤ : ℕ∞) (incrSource nu h V P) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (incrStretch h V) := contDiff_incrStretch h hV
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun w => ∑ a, incrComp h V a w * dvec (0, ee a) (incrPres h P) w) :=
    ContDiff.sum fun a _ =>
      (contDiff_incrComp h hV a).mul (contDiff_dvec _ (contDiff_incrPres h hP) _)
  have h3 : ContDiff ℝ (⊤ : ℕ∞) (incrDissip h V) := contDiff_incrDissip h hV
  exact ((h1.neg.sub h2).sub (contDiff_const.mul h3))

lemma spacePeriodic_comp_scalar {f : STime → ℝ} (beta : ℝ → ℝ) (hper : SpacePeriodic f) :
    SpacePeriodic (fun w => beta (f w)) := fun z j => by
  show beta (f (z.1, z.2 + ee j)) = beta (f z)
  rw [hper z j]

lemma spacePeriodic_betaFlux {beta : ℝ → ℝ} {V : STime → E3} (h : E3)
    (hVper : SpacePeriodic V) :
    SpacePeriodic (fun w => beta (incrQuad h V w) • shift h V w) := fun z j => by
  show beta (incrQuad h V (z.1, z.2 + ee j)) • shift h V (z.1, z.2 + ee j)
    = beta (incrQuad h V z) • shift h V z
  rw [spacePeriodic_incrQuad h hVper z j, spacePeriodic_shift h hVper z j]

/-- **Differentiation under the cell integral** for the level quantity. -/
theorem hasDerivAt_incrBetaEnergy {beta : ℝ → ℝ} (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta)
    {V : STime → E3} (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) :
    HasDerivAt (incrBetaEnergy beta h V)
      (cellInt (fun x => dvec (1, 0) (fun w => beta (incrQuad h V w)) (t, x))) t :=
  hasDerivAt_cellInt (fun w => beta (incrQuad h V w)) (hbeta.comp (contDiff_incrQuad h hV)) t

/-- **The integrated subsolution inequality.**  Both structural terms integrate
away, leaving the level-set energy inequality. -/
theorem cellInt_dtBeta_le_source (nu : ℝ) (hnu : 0 ≤ nu) (V : STime → E3) (P : STime → ℝ)
    (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    {beta b1 b2 : ℝ → ℝ} (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta) (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1)
    (hb1 : ∀ x, HasDerivAt beta (b1 x) x) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hconv : ∀ x, 0 ≤ b2 x) (t : ℝ) :
    cellInt (fun x => dvec (1, 0) (fun w => beta (incrQuad h V w)) (t, x))
      ≤ incrBetaSource b1 nu h V P t := by
  set Beta : STime → ℝ := fun w => beta (incrQuad h V w) with hBeta
  have hBetaC : ContDiff ℝ (⊤ : ℕ∞) Beta := hbeta.comp (contDiff_incrQuad h hV)
  have hflux : ContDiff ℝ (⊤ : ℕ∞) (fun w => Beta w • shift h V w) :=
    hBetaC.smul (contDiff_shift h hV)
  have hb1q : ContDiff ℝ (⊤ : ℕ∞) (fun w => b1 (incrQuad h V w)) :=
    hb1c.comp (contDiff_incrQuad h hV)
  have hsrc : ContDiff ℝ (⊤ : ℕ∞) (incrSource nu h V P) := contDiff_incrSource nu h hV hP
  -- the transport term is a divergence
  have htrans : ∀ x : E3,
      divg (fun w => Beta w • shift h V w) (t, x)
        = ∑ j, shift h V (t, x) j * dvec (0, ee j) Beta (t, x) :=
    fun x => pressure_work_divergence (shift h V) Beta (contDiff_shift h hV) hBetaC
      (shift_incompressible h hdiv) (t, x)
  -- pointwise bound on the time derivative
  have hpt : ∀ x : E3, dvec (1, 0) Beta (t, x)
      ≤ (nu * lap Beta (t, x) + b1 (incrQuad h V (t, x)) * incrSource nu h V P (t, x))
        - divg (fun w => Beta w • shift h V w) (t, x) := by
    intro x
    have hsub := increment_convex_subsolution nu hnu V P h hV hP hmom hb1 hb2 hconv (t, x)
    rw [htrans x]
    have hs : incrSource nu h V P (t, x) = - incrStretch h V (t, x)
        - (∑ a, incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x))
        - nu * incrDissip h V (t, x) := rfl
    rw [hs]
    linarith [hsub]
  -- continuity of both sides
  have hcont_dt : Continuous fun x : E3 => dvec (1, 0) Beta (t, x) :=
    continuous_slice (contDiff_dvec _ hBetaC _) t
  have hcont_lap : Continuous fun x : E3 => nu * lap Beta (t, x) :=
    continuous_const.mul (continuous_slice (contDiff_lapFun hBetaC) t)
  have hcont_src : Continuous fun x : E3 =>
      b1 (incrQuad h V (t, x)) * incrSource nu h V P (t, x) :=
    (continuous_slice hb1q t).mul (continuous_slice hsrc t)
  have hcont_div : Continuous fun x : E3 => divg (fun w => Beta w • shift h V w) (t, x) :=
    continuous_slice (contDiff_divgFun hflux) t
  have hmono := cellInt_mono hcont_dt ((hcont_lap.add hcont_src).sub hcont_div) hpt
  simp only [Pi.add_apply] at hmono
  -- the two structural integrals vanish
  have hlapzero : cellInt (fun x => lap Beta (t, x)) = 0 :=
    cellInt_lap_eq_zero Beta hBetaC (spacePeriodic_comp_scalar beta
      (spacePeriodic_incrQuad h hVper)) t
  have hdivzero : cellInt (fun x => divg (fun w => Beta w • shift h V w) (t, x)) = 0 :=
    cellInt_divg_eq_zero _ hflux (spacePeriodic_betaFlux h hVper) t
  have hsplit : cellInt (fun x =>
      (nu * lap Beta (t, x) + b1 (incrQuad h V (t, x)) * incrSource nu h V P (t, x))
        - divg (fun w => Beta w • shift h V w) (t, x))
      = incrBetaSource b1 nu h V P t := by
    have e1 := cellInt_sub
      (f := fun x : E3 => nu * lap Beta (t, x)
        + b1 (incrQuad h V (t, x)) * incrSource nu h V P (t, x))
      (g := fun x : E3 => divg (fun w => Beta w • shift h V w) (t, x))
      (hcont_lap.add hcont_src) hcont_div
    have e2 := cellInt_add
      (f := fun x : E3 => nu * lap Beta (t, x))
      (g := fun x : E3 => b1 (incrQuad h V (t, x)) * incrSource nu h V P (t, x))
      hcont_lap hcont_src
    have e3 := cellInt_const_mul nu (fun x : E3 => lap Beta (t, x))
    rw [e1, e2, e3, hlapzero, hdivzero]
    simp [incrBetaSource]
  rw [hsplit] at hmono
  exact hmono

/-- **The level-set energy inequality.**  The derivative of the level quantity
exists and is bounded by the source, for every smooth convex `β`. -/
theorem deriv_incrBetaEnergy_le (nu : ℝ) (hnu : 0 ≤ nu) (V : STime → E3) (P : STime → ℝ)
    (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    {beta b1 b2 : ℝ → ℝ} (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta) (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1)
    (hb1 : ∀ x, HasDerivAt beta (b1 x) x) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hconv : ∀ x, 0 ≤ b2 x) (t : ℝ) :
    ∃ D : ℝ, HasDerivAt (incrBetaEnergy beta h V) D t ∧ D ≤ incrBetaSource b1 nu h V P t :=
  ⟨_, hasDerivAt_incrBetaEnergy hbeta h hV t,
    cellInt_dtBeta_le_source nu hnu V P h hV hP hVper hdiv hmom hbeta hb1c hb1 hb2 hconv t⟩

/-- **Potential form of the level-set energy inequality.**  With an entrywise
bound `K` on `∇u` over the cell and `β' ≥ 0`, the stretching contribution to the
source is dominated by `6K·∫β'(q)q`, so the level energy obeys a linear
differential inequality with potential coefficient `6K`. -/
theorem deriv_incrBetaEnergy_le_potential (nu : ℝ) (hnu : 0 ≤ nu) (V : STime → E3)
    (P : STime → ℝ) (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    {beta b1 b2 : ℝ → ℝ} (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta) (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1)
    (hb1 : ∀ x, HasDerivAt beta (b1 x) x) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hconv : ∀ x, 0 ≤ b2 x) (hmono : ∀ x, 0 ≤ b1 x) {K : ℝ} (t : ℝ)
    (hK : ∀ x : E3, ∀ i a : Fin 3, |dvec (0, ee i) (fun w => V w a) (t, x)| ≤ K) :
    ∃ D : ℝ, HasDerivAt (incrBetaEnergy beta h V) D t ∧
      D ≤ cellInt (fun x => b1 (incrQuad h V (t, x)) *
        (6 * K * incrQuad h V (t, x)
          - (∑ a, incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x))
          - nu * incrDissip h V (t, x))) := by
  obtain ⟨D, hD, hle⟩ := deriv_incrBetaEnergy_le nu hnu V P h hV hP hVper hdiv hmom
    hbeta hb1c hb1 hb2 hconv t
  refine ⟨D, hD, hle.trans ?_⟩
  have hb1q : ContDiff ℝ (⊤ : ℕ∞) (fun w => b1 (incrQuad h V w)) :=
    hb1c.comp (contDiff_incrQuad h hV)
  have hsrc : ContDiff ℝ (⊤ : ℕ∞) (incrSource nu h V P) := contDiff_incrSource nu h hV hP
  have hpotC : ContDiff ℝ (⊤ : ℕ∞) (fun w => 6 * K * incrQuad h V w
      - (∑ a, incrComp h V a w * dvec (0, ee a) (incrPres h P) w)
      - nu * incrDissip h V w) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun w => 6 * K * incrQuad h V w) :=
      contDiff_const.mul (contDiff_incrQuad h hV)
    have h2 : ContDiff ℝ (⊤ : ℕ∞)
        (fun w => ∑ a, incrComp h V a w * dvec (0, ee a) (incrPres h P) w) :=
      ContDiff.sum fun a _ =>
        (contDiff_incrComp h hV a).mul (contDiff_dvec _ (contDiff_incrPres h hP) _)
    exact (h1.sub h2).sub (contDiff_const.mul (contDiff_incrDissip h hV))
  refine cellInt_mono ((continuous_slice hb1q t).mul (continuous_slice hsrc t))
    ((continuous_slice hb1q t).mul (continuous_slice hpotC t)) ?_
  intro x
  have hstr : |incrStretch h V (t, x)|
      ≤ 3 * K * ∑ a, incrComp h V a (t, x) * incrComp h V a (t, x) :=
    incrStretch_abs_le h V (t, x) K (hK x)
  have hquad : incrQuad h V (t, x)
      = (1 / 2 : ℝ) * ∑ a, incrComp h V a (t, x) * incrComp h V a (t, x) := rfl
  have hle' : - incrStretch h V (t, x) ≤ 6 * K * incrQuad h V (t, x) := by
    have := (abs_le.mp hstr).1
    rw [hquad]
    linarith
  have hsrcval : incrSource nu h V P (t, x) = - incrStretch h V (t, x)
      - (∑ a, incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x))
      - nu * incrDissip h V (t, x) := rfl
  rw [hsrcval]
  exact mul_le_mul_of_nonneg_left (by linarith) (hmono _)

end ClayNS

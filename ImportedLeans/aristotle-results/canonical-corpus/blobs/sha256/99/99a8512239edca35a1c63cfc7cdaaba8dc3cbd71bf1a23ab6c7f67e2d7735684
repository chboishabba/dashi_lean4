/-
# The localized Kármán–Howarth identity on the periodicity cell

`RequestProject/NavierStokes/IncrementLocalEnergy.lean` derives the *pointwise*
localized energy identity for the increment `δ_h u = u(·+h) − u`, and
`RequestProject/NavierStokes/StructureFunction.lean` builds the two-point
objects

* `S₂(h,t) = ∫_cell Φ(x)|δ_h u|² dx`,
* `F₃(h,t)_m = ∫_cell Φ(x) δ_h u_m|δ_h u|² dx`,

together with their derivatives in the *separation* variable `h`.  This file
puts the two together and derives the localized Kármán–Howarth identity with
every cutoff error term kept explicitly — no absolute values are taken:

`∂_t S₂ + ∇_h·F₃ = −2ν∫Φ|∇_x δ_h u|² + 2∫(∇Φ·F) + 2ν∫qΔΦ − 2∫q (δ_h u·∇Φ)`,

`q = ½|δ_h u|²`, `F = q·u(·+h) + δ_h p·δ_h u`.  In particular:

* the dissipation term is manifestly nonpositive;
* the pressure enters **only** through `∫ δ_h p (δ_h u·∇Φ)`, i.e. only against
  a derivative of the cutoff — there is no interior pressure term;
* every other error term carries a derivative of `Φ`, so it is supported where
  the cutoff varies.

The two ingredients are proved separately:

* `ClayNS.hasDerivAt_wIncrEnergy` — the cutoff-weighted increment energy
  balance (the time derivative), obtained by integrating the localized
  pointwise identity over the cell;
* `ClayNS.divH_strFlux_eq` — the separation divergence of the third-order flux,
  `∇_h·F₃ = 2∫Φ·δ_h u·(δ_h u·∇)u − 2∫|δ_h u|²(δ_h u·∇Φ)`, which is where the
  incompressibility of `u` at the shifted point is used.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.StructureFunction

open scoped BigOperators

noncomputable section

namespace ClayNS

/-! ## The cutoff-weighted increment energy and its balance -/

/-- The cutoff-weighted increment energy `∫_cell Φ q`, `q = ½|δ_h u|²`. -/
def wIncrEnergy (Phi : STime → ℝ) (h : E3) (V : STime → E3) (t : ℝ) : ℝ :=
  cellInt fun x => Phi (t, x) * incrQuad h V (t, x)

/-- The cutoff error produced by the increment energy flux, `∫ ∇Φ·F`. -/
def wCutoffFlux (Phi : STime → ℝ) (h : E3) (V : STime → E3) (P : STime → ℝ) (t : ℝ) : ℝ :=
  cellInt fun x => ∑ i, dvec (0, ee i) Phi (t, x) * incrFlux h V P (t, x) i

/-- The cutoff error produced by the viscous term, `ν∫qΔΦ`. -/
def wCutoffLap (nu : ℝ) (Phi : STime → ℝ) (h : E3) (V : STime → E3) (t : ℝ) : ℝ :=
  cellInt fun x => nu * incrQuad h V (t, x) * lap Phi (t, x)

/-- The weighted increment dissipation `ν∫Φ|∇δ_h u|²`. -/
def wDissip (nu : ℝ) (Phi : STime → ℝ) (h : E3) (V : STime → E3) (t : ℝ) : ℝ :=
  cellInt fun x => nu * Phi (t, x) * incrDissip h V (t, x)

/-- The weighted stretching term `∫Φ δ_h u·(δ_h u·∇)u`. -/
def wStretch (Phi : STime → ℝ) (h : E3) (V : STime → E3) (t : ℝ) : ℝ :=
  cellInt fun x => Phi (t, x) * incrStretch h V (t, x)

lemma spacePeriodic_grad {f : STime → ℝ} (hf : Differentiable ℝ f) (hper : SpacePeriodic f) :
    SpacePeriodic (fun w => grad f w) := by
  intro z j
  simp only [grad]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := spacePeriodic_dvec hf hper (0, ee i) z j
  simp only [dspace_eq_dvec]
  rw [show dvec (0, ee i) f (z.1, z.2 + ee j) = dvec (0, ee i) f z from this]

lemma spacePeriodic_incrLocFlux {nu : ℝ} {V : STime → E3} {P Phi : STime → ℝ} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P) (hPhiper : SpacePeriodic Phi) :
    SpacePeriodic (incrLocFlux nu h V P Phi) := by
  intro z j
  have hq := spacePeriodic_incrQuad h hVper z j
  have hF := spacePeriodic_incrFlux h hVper hPper z j
  have hgq : grad (incrQuad h V) (z.1, z.2 + ee j) = grad (incrQuad h V) z :=
    spacePeriodic_grad (differentiable_of_contDiffTop (contDiff_incrQuad h hV))
      (spacePeriodic_incrQuad h hVper) z j
  have hgPhi : grad Phi (z.1, z.2 + ee j) = grad Phi z :=
    spacePeriodic_grad (differentiable_of_contDiffTop hPhi) hPhiper z j
  have hPhi' := hPhiper z j
  show Phi (z.1, z.2 + ee j) • incrFlux h V P (z.1, z.2 + ee j)
      - nu • (Phi (z.1, z.2 + ee j) • grad (incrQuad h V) (z.1, z.2 + ee j)
        - incrQuad h V (z.1, z.2 + ee j) • grad Phi (z.1, z.2 + ee j))
    = Phi z • incrFlux h V P z
      - nu • (Phi z • grad (incrQuad h V) z - incrQuad h V z • grad Phi z)
  rw [hq, hF, hgq, hgPhi, hPhi']

lemma contDiff_incrLocFlux {nu : ℝ} {V : STime → E3} {P Phi : STime → ℝ} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P) (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) :
    ContDiff ℝ (⊤ : ℕ∞) (incrLocFlux nu h V P Phi) :=
  (hPhi.smul (contDiff_incrFlux h hV hP)).sub
    (((hPhi.smul (contDiff_grad (contDiff_incrQuad h hV))).sub
      ((contDiff_incrQuad h hV).smul (contDiff_grad hPhi))).const_smul nu)

/-- **The cutoff-weighted increment energy balance.**  Integrating the localized
pointwise identity over the periodicity cell removes the divergence and leaves

`d/dt ∫Φq = ∫∇Φ·F + ν∫qΔΦ − ν∫Φ|∇δ_h u|² − ∫Φ δ_h u·(δ_h u·∇)u`.

The pressure survives only inside `∫∇Φ·F`. -/
theorem hasDerivAt_wIncrEnergy (nu : ℝ) (V : STime → E3) (P Phi : STime → ℝ) (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P) (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hPhiT : ∀ z : STime, dvec (1, 0) Phi z = 0)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P) (hPhiper : SpacePeriodic Phi)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (t : ℝ) :
    HasDerivAt (wIncrEnergy Phi h V)
      (wCutoffFlux Phi h V P t + wCutoffLap nu Phi h V t
        - wDissip nu Phi h V t - wStretch Phi h V t) t := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  have hLF : ContDiff ℝ (⊤ : ℕ∞) (incrLocFlux nu h V P Phi) :=
    contDiff_incrLocFlux h hV hP hPhi
  have hbase := hasDerivAt_cellInt (fun w => Phi w * incrQuad h V w) (hPhi.mul hq) t
  have hpt : ∀ x : E3, dvec (1, 0) (fun w => Phi w * incrQuad h V w) (t, x)
      = (((∑ i, dvec (0, ee i) Phi (t, x) * incrFlux h V P (t, x) i)
            + nu * incrQuad h V (t, x) * lap Phi (t, x))
          - nu * Phi (t, x) * incrDissip h V (t, x)
          - Phi (t, x) * incrStretch h V (t, x))
        - divg (incrLocFlux nu h V P Phi) (t, x) := by
    intro x
    have := increment_localized_energy_identity nu V P Phi h hV hP hPhi hPhiT hdiv hmom (t, x)
    linarith [this]
  have c1 : Continuous fun x : E3 => ∑ i, dvec (0, ee i) Phi (t, x) * incrFlux h V P (t, x) i := by
    refine continuous_finset_sum _ fun i _ => ?_
    exact (continuous_slice (contDiff_dvec Phi hPhi (0, ee i)) t).mul
      (continuous_slice (contDiff_coord _ (contDiff_incrFlux h hV hP) i) t)
  have c2 : Continuous fun x : E3 => nu * incrQuad h V (t, x) * lap Phi (t, x) :=
    (continuous_const.mul (continuous_slice hq t)).mul
      (continuous_slice (contDiff_lapFun hPhi) t)
  have c3 : Continuous fun x : E3 => nu * Phi (t, x) * incrDissip h V (t, x) :=
    (continuous_const.mul (continuous_slice hPhi t)).mul
      (continuous_slice (contDiff_incrDissip h hV) t)
  have c4 : Continuous fun x : E3 => Phi (t, x) * incrStretch h V (t, x) :=
    (continuous_slice hPhi t).mul (continuous_slice (contDiff_incrStretch h hV) t)
  have c5 : Continuous fun x : E3 => divg (incrLocFlux nu h V P Phi) (t, x) :=
    continuous_slice (contDiff_divgFun hLF) t
  set A : E3 → ℝ := fun x => ∑ i, dvec (0, ee i) Phi (t, x) * incrFlux h V P (t, x) i with hAdef
  set Bq : E3 → ℝ := fun x => nu * incrQuad h V (t, x) * lap Phi (t, x) with hBdef
  set Cd : E3 → ℝ := fun x => nu * Phi (t, x) * incrDissip h V (t, x) with hCdef
  set Ds : E3 → ℝ := fun x => Phi (t, x) * incrStretch h V (t, x) with hDdef
  set Ef : E3 → ℝ := fun x => divg (incrLocFlux nu h V P Phi) (t, x) with hEdef
  have e1 : cellInt (fun x => A x + Bq x) = cellInt A + cellInt Bq := cellInt_add c1 c2
  have e2 : cellInt (fun x => A x + Bq x - Cd x) = cellInt (fun x => A x + Bq x) - cellInt Cd :=
    cellInt_sub (c1.add c2) c3
  have e3 : cellInt (fun x => A x + Bq x - Cd x - Ds x)
      = cellInt (fun x => A x + Bq x - Cd x) - cellInt Ds :=
    cellInt_sub ((c1.add c2).sub c3) c4
  have e4 : cellInt (fun x => A x + Bq x - Cd x - Ds x - Ef x)
      = cellInt (fun x => A x + Bq x - Cd x - Ds x) - cellInt Ef :=
    cellInt_sub (((c1.add c2).sub c3).sub c4) c5
  have hE0 : cellInt Ef = 0 :=
    cellInt_divg_eq_zero (incrLocFlux nu h V P Phi) hLF
      (spacePeriodic_incrLocFlux h hV hPhi hVper hPper hPhiper) t
  have hsplit : cellInt (fun x => dvec (1, 0) (fun w => Phi w * incrQuad h V w) (t, x))
      = wCutoffFlux Phi h V P t + wCutoffLap nu Phi h V t
        - wDissip nu Phi h V t - wStretch Phi h V t := by
    rw [cellInt_congr hpt, e4, e3, e2, e1, hE0]
    simp only [wCutoffFlux, wCutoffLap, wDissip, wStretch, hAdef, hBdef, hCdef, hDdef]
    ring
  rw [hsplit] at hbase
  exact hbase

/-! ## The separation divergence of the third-order structure flux -/

@[simp] lemma rayPt_zero_param (t : ℝ) (h : E3) (j : Fin 3) (x : E3) :
    rayPt t h j (0, x) = (t, x + h) := by
  simp

lemma rayIncrComp_at_zero_param (V : STime → E3) (t : ℝ) (h : E3) (j a : Fin 3) (x : E3) :
    rayIncrComp V t h j a (0, x) = incrComp h V a (t, x) := by
  simp [rayIncrComp, incrComp]

/-- The spatial derivative of the increment splits the two-point derivative. -/
lemma dvec_shifted_split {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (h : E3) (j a : Fin 3)
    (t : ℝ) (x : E3) :
    dvec (0, ee j) (fun w => V w a) (t, x + h)
      = dvec (0, ee j) (incrComp h V a) (t, x) + dvec (0, ee j) (fun w => V w a) (t, x) := by
  have hshift : dvec (0, ee j) (fun w : STime => shift h V w a) (t, x)
      = dvec (0, ee j) (fun w : STime => V w a) (t, x + h) := by
    have hfun : (fun w : STime => shift h V w a) = shift h (fun w : STime => V w a) := rfl
    rw [hfun, dvec_shift]
    congr 1
    simp
  have hd : dvec (0, ee j) (incrComp h V a) (t, x)
      = dvec (0, ee j) (fun w : STime => shift h V w a) (t, x)
        - dvec (0, ee j) (fun w : STime => V w a) (t, x) :=
    dvec_sub _ _ (t, x)
      (differentiable_of_contDiffTop (contDiff_coord _ (contDiff_shift h hV) a) (t, x))
      (differentiable_of_contDiffTop (contDiff_coord V hV a) (t, x)) (0, ee j)
  rw [hd, hshift]
  ring

/-- **The pointwise separation divergence of the third-order flux density.**
Incompressibility of `u` at the shifted point removes the first term, and the
remaining one splits into the stretching term and a pure transport term. -/
lemma sum_strFluxDensD_at_zero {Phi : STime → ℝ} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hdiv : ∀ z : STime, divg V z = 0) (t : ℝ) (h : E3) (x : E3) :
    ∑ j, strFluxDensD Phi V t h j j (0, x)
      = 2 * (Phi (t, x) * incrStretch h V (t, x))
        + 2 * (Phi (t, x)
            * ∑ j, incrComp h V j (t, x) * dvec (0, ee j) (incrQuad h V) (t, x)) := by
  have hW : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (incrComp h V a) := fun a => contDiff_incrComp h hV a
  have hval : ∀ j : Fin 3, strFluxDensD Phi V t h j j (0, x)
      = Phi (t, x) * (dvec (0, ee j) (fun w => V w j) (t, x + h)
          * ∑ a, incrComp h V a (t, x) * incrComp h V a (t, x)
        + incrComp h V j (t, x) * (2 * ∑ a, incrComp h V a (t, x)
            * dvec (0, ee j) (fun w => V w a) (t, x + h))) := by
    intro j
    simp only [strFluxDensD, rayPt_zero_param, slicePt_apply, rayIncrComp_at_zero_param]
  have hdiv0 : ∑ j, dvec (0, ee j) (fun w => V w j) (t, x + h) = 0 := by
    have := divg_eq_sum V hV (t, x + h)
    rw [← this]
    exact hdiv _
  have hquad : ∀ j : Fin 3, ∑ a, incrComp h V a (t, x) * dvec (0, ee j) (incrComp h V a) (t, x)
      = dvec (0, ee j) (incrQuad h V) (t, x) := fun j =>
    (dvec_quad (incrComp h V) hW (0, ee j) (t, x)).symm
  rw [Finset.sum_congr rfl fun j _ => hval j]
  simp only [dvec_shifted_split hV h _ _ t x, incrStretch] at hdiv0 ⊢
  simp only [Fin.sum_univ_three] at hdiv0 hquad ⊢
  linear_combination (Phi (t, x) * ((incrComp h V 0 (t, x) * incrComp h V 0 (t, x)
      + incrComp h V 1 (t, x) * incrComp h V 1 (t, x)
      + incrComp h V 2 (t, x) * incrComp h V 2 (t, x)))) * hdiv0
    + 2 * Phi (t, x) * (incrComp h V 0 (t, x) * hquad 0 + incrComp h V 1 (t, x) * hquad 1
      + incrComp h V 2 (t, x) * hquad 2)


/-! ## Transferring the transport derivative onto the cutoff -/

/-- The interior transport term `∫Φ δ_h u·∇q`, `q = ½|δ_h u|²`. -/
def wTransport (Phi : STime → ℝ) (h : E3) (V : STime → E3) (t : ℝ) : ℝ :=
  cellInt fun x => Phi (t, x) * ∑ j, incrComp h V j (t, x) * dvec (0, ee j) (incrQuad h V) (t, x)

/-- The cutoff error produced by the transport term, `∫q (δ_h u·∇Φ)`. -/
def wCutoffTransport (Phi : STime → ℝ) (h : E3) (V : STime → E3) (t : ℝ) : ℝ :=
  cellInt fun x => incrQuad h V (t, x) * ∑ j, incrComp h V j (t, x) * dvec (0, ee j) Phi (t, x)

/-- **Integration by parts in the transport term.**  Since `δ_h u` is divergence
free, `∫Φ δ_h u·∇q = −∫q (δ_h u·∇Φ)`: the interior transport term carries a
derivative of the cutoff, so it is supported where `Φ` varies. -/
theorem wTransport_eq_neg_wCutoffTransport {V : STime → E3} {Phi : STime → ℝ} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hVper : SpacePeriodic V) (hPhiper : SpacePeriodic Phi)
    (hdiv : ∀ z : STime, divg V z = 0) (t : ℝ) :
    wTransport Phi h V t = - wCutoffTransport Phi h V t := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  have hf : ContDiff ℝ (⊤ : ℕ∞) fun w : STime => Phi w * incrQuad h V w := hPhi.mul hq
  have hG : ContDiff ℝ (⊤ : ℕ∞) (incrVec h V) := contDiff_incrVec h hV
  have hC : ContDiff ℝ (⊤ : ℕ∞) fun w : STime => (Phi w * incrQuad h V w) • incrVec h V w :=
    hf.smul hG
  have hper : SpacePeriodic fun w : STime => (Phi w * incrQuad h V w) • incrVec h V w := by
    intro z j
    show (Phi (z.1, z.2 + ee j) * incrQuad h V (z.1, z.2 + ee j)) • incrVec h V (z.1, z.2 + ee j)
      = (Phi z * incrQuad h V z) • incrVec h V z
    rw [hPhiper z j, spacePeriodic_incrQuad h hVper z j, spacePeriodic_incrVec h hVper z j]
  have hpt : ∀ x : E3, divg (fun w : STime => (Phi w * incrQuad h V w) • incrVec h V w) (t, x)
      = Phi (t, x) * (∑ j, incrComp h V j (t, x) * dvec (0, ee j) (incrQuad h V) (t, x))
        + incrQuad h V (t, x) * ∑ j, incrComp h V j (t, x) * dvec (0, ee j) Phi (t, x) := by
    intro x
    rw [divg_smul (fun w : STime => Phi w * incrQuad h V w) (incrVec h V) hf hG (t, x),
      divg_incrVec h hV hdiv (t, x), mul_zero, add_zero]
    have hd : ∀ i : Fin 3, dvec (0, ee i) (fun w : STime => Phi w * incrQuad h V w) (t, x)
        = dvec (0, ee i) Phi (t, x) * incrQuad h V (t, x)
          + Phi (t, x) * dvec (0, ee i) (incrQuad h V) (t, x) := fun i =>
      dvec_mul Phi (incrQuad h V) (t, x) (differentiable_of_contDiffTop hPhi (t, x))
        (differentiable_of_contDiffTop hq (t, x)) (0, ee i)
    simp only [hd, incrVec_coord, Fin.sum_univ_three]
    ring
  have c1 : Continuous fun x : E3 =>
      Phi (t, x) * ∑ j, incrComp h V j (t, x) * dvec (0, ee j) (incrQuad h V) (t, x) :=
    (continuous_slice hPhi t).mul (continuous_finset_sum _ fun j _ =>
      (continuous_slice (contDiff_incrComp h hV j) t).mul
        (continuous_slice (contDiff_dvec _ hq (0, ee j)) t))
  have c2 : Continuous fun x : E3 =>
      incrQuad h V (t, x) * ∑ j, incrComp h V j (t, x) * dvec (0, ee j) Phi (t, x) :=
    (continuous_slice hq t).mul (continuous_finset_sum _ fun j _ =>
      (continuous_slice (contDiff_incrComp h hV j) t).mul
        (continuous_slice (contDiff_dvec _ hPhi (0, ee j)) t))
  have hzero := cellInt_divg_eq_zero _ hC hper t
  rw [cellInt_congr hpt, cellInt_add c1 c2] at hzero
  have : wTransport Phi h V t + wCutoffTransport Phi h V t = 0 := hzero
  linarith

/-! ## The separation divergence of the third-order flux -/

lemma contDiff_strFluxDensD {Phi : STime → ℝ} {V : STime → E3} (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) (h : E3) (j m : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (strFluxDensD Phi V t h j m) :=
  (contDiff_slicePhi hPhi t).mul
    (((contDiff_rayGrad hV t h j m).mul
        (ContDiff.sum fun a _ =>
          (contDiff_rayIncrComp hV t h j a).mul (contDiff_rayIncrComp hV t h j a))).add
      ((contDiff_rayIncrComp hV t h j m).mul (contDiff_const.mul
        (ContDiff.sum fun a _ =>
          (contDiff_rayIncrComp hV t h j a).mul (contDiff_rayGrad hV t h j a)))))

/-- The separation divergence `∇_h·F₃` of the third-order structure flux: the
sum over `j` of the derivatives `∂_{h_j} F₃(h)_j`, each of which is supplied by
`ClayNS.hasDerivAt_strFlux_ray`. -/
def strFluxDivH (Phi : STime → ℝ) (V : STime → E3) (t : ℝ) (h : E3) : ℝ :=
  ∑ j, cellInt fun x => strFluxDensD Phi V t h j j (0, x)

/-- Each summand of `strFluxDivH` really is a separation derivative of `F₃`. -/
theorem hasDerivAt_strFluxDivH_component {Phi : STime → ℝ} {V : STime → E3}
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) (h : E3) (j : Fin 3) :
    HasDerivAt (fun r : ℝ => strFlux Phi V t (h + r • ee j) j)
      (cellInt fun x => strFluxDensD Phi V t h j j (0, x)) 0 :=
  hasDerivAt_strFlux_ray hPhi hV t h j j 0

/-- **The separation divergence of the third-order flux.**  Incompressibility of
`u` at the shifted point kills the term with the divergence of `u(·+h)`, leaving
exactly twice the stretching term plus twice the transport term. -/
theorem divH_strFlux_eq {Phi : STime → ℝ} {V : STime → E3} (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hdiv : ∀ z : STime, divg V z = 0) (t : ℝ) (h : E3) :
    strFluxDivH Phi V t h = 2 * wStretch Phi h V t + 2 * wTransport Phi h V t := by
  set g : Fin 3 → E3 → ℝ := fun j x => strFluxDensD Phi V t h j j (0, x) with hg
  have hc : ∀ j, Continuous (g j) := fun j =>
    continuous_slice (contDiff_strFluxDensD hPhi hV t h j j) 0
  have hA : Continuous fun x : E3 => 2 * (Phi (t, x) * incrStretch h V (t, x)) :=
    continuous_const.mul ((continuous_slice hPhi t).mul
      (continuous_slice (contDiff_incrStretch h hV) t))
  have hB : Continuous fun x : E3 => 2 * (Phi (t, x)
      * ∑ j, incrComp h V j (t, x) * dvec (0, ee j) (incrQuad h V) (t, x)) :=
    continuous_const.mul ((continuous_slice hPhi t).mul
      (continuous_finset_sum _ fun j _ =>
        (continuous_slice (contDiff_incrComp h hV j) t).mul
          (continuous_slice (contDiff_dvec _ (contDiff_incrQuad h hV) (0, ee j)) t)))
  have e1 : cellInt (fun x => g 1 x + g 2 x) = cellInt (g 1) + cellInt (g 2) :=
    cellInt_add (hc 1) (hc 2)
  have e0 : cellInt (fun x => g 0 x + (g 1 x + g 2 x))
      = cellInt (g 0) + cellInt (fun x => g 1 x + g 2 x) :=
    cellInt_add (hc 0) ((hc 1).add (hc 2))
  have hsum : strFluxDivH Phi V t h = cellInt (fun x => g 0 x + (g 1 x + g 2 x)) := by
    rw [e0, e1, strFluxDivH, Fin.sum_univ_three, add_assoc]
  have hpt : ∀ x : E3, g 0 x + (g 1 x + g 2 x)
      = 2 * (Phi (t, x) * incrStretch h V (t, x))
        + 2 * (Phi (t, x)
            * ∑ j, incrComp h V j (t, x) * dvec (0, ee j) (incrQuad h V) (t, x)) := by
    intro x
    have := sum_strFluxDensD_at_zero (Phi := Phi) hV hdiv t h x
    rw [Fin.sum_univ_three] at this
    simp only [hg]
    linarith [this]
  rw [hsum, cellInt_congr hpt, cellInt_add hA hB, cellInt_const_mul, cellInt_const_mul]
  rfl

/-! ## The localized Kármán–Howarth identity -/

/-- The structure function is twice the cutoff-weighted increment energy. -/
lemma strFun_eq_two_wIncrEnergy (Phi : STime → ℝ) (V : STime → E3) (t : ℝ) (h : E3) :
    strFun Phi V t h = 2 * wIncrEnergy Phi h V t := by
  simp only [strFun, wIncrEnergy]
  rw [← cellInt_const_mul]
  refine cellInt_congr fun x => ?_
  simp only [incrQuad, quad, incrComp, shift_apply]
  ring

/-- **The localized Kármán–Howarth identity.**

For a smooth periodic solution `(u,p)` of the zero-force Navier–Stokes system
and a smooth time-independent periodic cutoff `Φ`, the cutoff-weighted
second-order structure function `S₂(h,t) = ∫Φ|δ_h u|²` and third-order flux
`F₃(h,t)_m = ∫Φ δ_h u_m|δ_h u|²` satisfy exactly

`∂_t S₂ + ∇_h·F₃ = −2ν∫Φ|∇_x δ_h u|² + 2∫∇Φ·F + 2ν∫qΔΦ − 2∫q(δ_h u·∇Φ)`

with `q = ½|δ_h u|²` and `F = q·u(·+h) + δ_h p·δ_h u`.  No absolute values are
taken anywhere: this is an identity, not an estimate.  Three structural facts
are visible on the right-hand side.

* The dissipation `−2ν∫Φ|∇_x δ_h u|²` is manifestly nonpositive.
* The pressure occurs **only** inside `∫∇Φ·F`, i.e. only paired with a
  derivative of the cutoff; there is no interior pressure term.
* Every error term other than the dissipation carries a derivative of `Φ`, so
  all of them are supported in the region where the cutoff varies.  On a cutoff
  adapted to a scale `R` they are the `E_cutoff + E_pressure` of the localized
  Kármán–Howarth–Monin balance. -/
theorem localized_karman_howarth (nu : ℝ) (V : STime → E3) (P Phi : STime → ℝ) (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P) (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hPhiT : ∀ z : STime, dvec (1, 0) Phi z = 0)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P) (hPhiper : SpacePeriodic Phi)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (t : ℝ) :
    HasDerivAt (fun r : ℝ => strFun Phi V r h)
      ((- (2 * wDissip nu Phi h V t) + 2 * wCutoffFlux Phi h V P t
          + 2 * wCutoffLap nu Phi h V t - 2 * wCutoffTransport Phi h V t)
        - strFluxDivH Phi V t h) t := by
  have hE := hasDerivAt_wIncrEnergy nu V P Phi h hV hP hPhi hPhiT hVper hPper hPhiper hdiv hmom t
  have hfun : (fun r : ℝ => strFun Phi V r h) = fun r : ℝ => 2 * wIncrEnergy Phi h V r :=
    funext fun r => strFun_eq_two_wIncrEnergy Phi V r h
  have hdivF := divH_strFlux_eq hPhi hV hdiv t h
  have hbp := wTransport_eq_neg_wCutoffTransport h hV hPhi hVper hPhiper hdiv t
  have hval : (- (2 * wDissip nu Phi h V t) + 2 * wCutoffFlux Phi h V P t
        + 2 * wCutoffLap nu Phi h V t - 2 * wCutoffTransport Phi h V t)
      - strFluxDivH Phi V t h
      = 2 * (wCutoffFlux Phi h V P t + wCutoffLap nu Phi h V t
          - wDissip nu Phi h V t - wStretch Phi h V t) := by
    rw [hdivF, hbp]; ring
  rw [hfun, hval]
  exact hE.const_mul 2

end ClayNS

/-
# The exact concentrated adjoint weight gate is **false** for every `θ < 1`.

`RequestProject/NavierStokes/FrontierGatesAdjoint.lean` records
`ClayNS.ConcentratedAdjointWeightGate nu theta`: the demand for a smooth,
periodic, nonnegative weight `Φ` with a bounded spatial gradient, solving the
backward adjoint transport–diffusion equation

  `−∂_tΦ − u(·+h)·∇Φ − νΔΦ = 0`   (`ClayNS.adjointOp nu h V Φ = 0`)

*exactly*, positive at the defect point, and **concentrated**:
`∫_cell Φ(t₀,·) ≤ θ·Φ(z₀)`.  The constant weight realizes `θ = 1`
(`ClayNS.concentratedAdjointWeightGate_one`), and the open question was whether
`θ < 1` is attainable.

It is not.  This file proves the gate **false** for every `θ < 1` and every
`ν > 0`, by an energy argument that needs nothing beyond the hypotheses the gate
itself supplies:

* `ClayNS.cellInt_dvec_time_eq_zero` — the cell mass of an exact adjoint weight
  has vanishing time derivative (advection and diffusion are both spatial
  divergences of periodic fields), so the mean `m = ∫_cell Φ(t,·)` is a
  *constant of the motion* (`ClayNS.cellInt_adjoint_weight_const`).

* `ClayNS.hasDerivAt_adjointWeightEnergy` — the adjoint equation is a
  transported quadratic with viscosity `−ν`, so
  `d/dt ∫_cell Φ² = +2ν ∫_cell |∇Φ|²`.  The `L²` variance
  `Var(t) = ∫_cell Φ² − m²` therefore *grows*.

* Poincaré on the cell (`ClayNS.cellInt_poincare`) turns this into the
  differential inequality `Var′ ≥ (2ν/3)·Var`, while the gate's own gradient
  bound `|∂_jΦ| ≤ G` caps the variance uniformly, `Var ≤ 9G²`
  (`ClayNS.adjointWeightVar_le`).

* A bounded solution of `Var′ ≥ c·Var` with `c > 0` must vanish
  (`ClayNS.adjointWeightVar_eq_zero`); hence `Φ(t,·)` is *constant in space*
  (`ClayNS.adjoint_weight_eq_cell_mean`), so its cell mean equals its value at
  the defect point and the concentration ratio is forced to be exactly `1`.

The conclusion, `ClayNS.not_concentratedAdjointWeightGate_of_lt_one`, is the
precise sense in which the frontier item cannot be closed as stated: an *exact*
adjoint weight on the torus with a bounded gradient is necessarily flat.  This
is why the development replaces it by the *approximate*-adjoint gate
`ClayNS.GaussianApproximateAdjointWeightGate`, whose residual carries positive
scaling dimension.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.FrontierGatesAdjoint
import RequestProject.NavierStokes.AncientLiouville
import RequestProject.NavierStokes.IncrementEnergyPeriodic
import RequestProject.NavierStokes.CellVanishing

open scoped BigOperators
open MeasureTheory Set

noncomputable section

namespace ClayNS

/-! ## Set-up: an exact adjoint weight -/

section Exact

variable {nu : ℝ} {h : E3} {V : STime → E3} {Phi : STime → ℝ}

/-- The `L²` cell energy of the weight. -/
def adjointWeightEnergy (Phi : STime → ℝ) (t : ℝ) : ℝ := cellInt (fun x => Phi (t, x) ^ 2)

/-- The cell Dirichlet energy of the weight. -/
def adjointWeightDissip (Phi : STime → ℝ) (t : ℝ) : ℝ :=
  cellInt (fun x => ∑ k, dvec (0, ee k) Phi (t, x) ^ 2)

/-- The adjoint equation, solved for the time derivative. -/
lemma dvec_time_of_adjointOp_eq_zero (hadj : ∀ z : STime, adjointOp nu h V Phi z = 0)
    (z : STime) :
    dvec (1, 0) Phi z
      = -(∑ j, shift h V z j * dvec (0, ee j) Phi z) - nu * lap Phi z := by
  have hz := hadj z
  rw [adjointOp] at hz
  linarith

/-- **The cell mass of an exact adjoint weight is stationary.**  Both the
advection term and the diffusion term are spatial divergences of periodic
fields, so the cell integral of `∂_tΦ` vanishes. -/
lemma cellInt_dvec_time_eq_zero (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVper : SpacePeriodic V)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (hPhiper : SpacePeriodic Phi)
    (hadj : ∀ z : STime, adjointOp nu h V Phi z = 0) (t : ℝ) :
    cellInt (fun x => dvec (1, 0) Phi (t, x)) = 0 := by
  have hU : ContDiff ℝ (⊤ : ℕ∞) (shift h V) := contDiff_shift h hV
  have hUper : SpacePeriodic (shift h V) := spacePeriodic_shift h hVper
  have hUdiv : ∀ z : STime, divg (shift h V) z = 0 := shift_incompressible h hdiv
  have hadvzero : cellInt (fun x => ∑ j, shift h V (t, x) j * dvec (0, ee j) Phi (t, x)) = 0 :=
    cellInt_pressure_work_eq_zero (shift h V) Phi hU hPhi hUper hPhiper hUdiv t
  have hlapzero : cellInt (fun x => lap Phi (t, x)) = 0 := cellInt_lap_eq_zero Phi hPhi hPhiper t
  have hAcont : Continuous
      (fun x : E3 => ∑ j, shift h V (t, x) j * dvec (0, ee j) Phi (t, x)) := by
    refine continuous_time_slice
      (f := fun w : STime => ∑ j, shift h V w j * dvec (0, ee j) Phi w) ?_ t
    exact continuous_finset_sum _ fun j _ =>
      (contDiff_coord _ hU j).continuous.mul (continuous_dvec Phi hPhi (0, ee j))
  have hLcont : Continuous (fun x : E3 => lap Phi (t, x)) := by
    refine continuous_time_slice (f := fun w : STime => lap Phi w) ?_ t
    exact continuous_finset_sum _ fun k _ =>
      continuous_dvec _ (contDiff_dvec Phi hPhi (0, ee k)) (0, ee k)
  have hpt : ∀ x : E3, dvec (1, 0) Phi (t, x)
      = -(∑ j, shift h V (t, x) j * dvec (0, ee j) Phi (t, x)) - nu * lap Phi (t, x) :=
    fun x => dvec_time_of_adjointOp_eq_zero hadj (t, x)
  rw [cellInt_congr hpt,
    cellInt_sub (f := fun x : E3 => -(∑ j, shift h V (t, x) j * dvec (0, ee j) Phi (t, x)))
      (g := fun x : E3 => nu * lap Phi (t, x)) hAcont.neg (continuous_const.mul hLcont),
    cellInt_neg, hadvzero, cellInt_const_mul, hlapzero]
  simp

/-- **The cell mean of an exact adjoint weight is a constant of the motion.** -/
theorem cellInt_adjoint_weight_const (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVper : SpacePeriodic V)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (hPhiper : SpacePeriodic Phi)
    (hadj : ∀ z : STime, adjointOp nu h V Phi z = 0) (s t : ℝ) :
    cellInt (fun x => Phi (s, x)) = cellInt (fun x => Phi (t, x)) := by
  have hder : ∀ r : ℝ, HasDerivAt (fun r' => cellInt (fun x => Phi (r', x))) 0 r := by
    intro r
    have hd := hasDerivAt_cellInt Phi hPhi r
    rwa [cellInt_dvec_time_eq_zero hV hVper hdiv hPhi hPhiper hadj r] at hd
  exact is_const_of_deriv_eq_zero (fun r => (hder r).differentiableAt)
    (fun r => (hder r).deriv) s t

/-- **The weight's `L²` energy grows.**  The adjoint equation is a transported
quadratic with viscosity `−ν`, so `d/dt ∫Φ² = +2ν∫|∇Φ|²`. -/
theorem hasDerivAt_adjointWeightEnergy (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVper : SpacePeriodic V)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (hPhiper : SpacePeriodic Phi)
    (hadj : ∀ z : STime, adjointOp nu h V Phi z = 0) (t : ℝ) :
    HasDerivAt (adjointWeightEnergy Phi) (2 * nu * adjointWeightDissip Phi t) t := by
  have hU : ContDiff ℝ (⊤ : ℕ∞) (shift h V) := contDiff_shift h hV
  have hUper : SpacePeriodic (shift h V) := spacePeriodic_shift h hVper
  have hUdiv : ∀ z : STime, divg (shift h V) z = 0 := shift_incompressible h hdiv
  have heq : ∀ (a : Fin 3) (z : STime),
      dvec (1, 0) Phi z + ∑ j, shift h V z j * dvec (0, ee j) Phi z
        = (0 : ℝ) + (-nu) * ∑ k, dvec (0, ee k) (dvec (0, ee k) Phi) z := by
    intro _ z
    have hz := dvec_time_of_adjointOp_eq_zero hadj z
    have hlap : lap Phi z = ∑ k, dvec (0, ee k) (dvec (0, ee k) Phi) z := rfl
    rw [hz, hlap]
    ring
  have hbal := global_quadratic_balance (-nu) (shift h V) (fun _ => Phi) (fun _ _ => 0)
    hU hUper hUdiv (fun _ => hPhi) (fun _ => hPhiper) heq t
  -- rewrite the source term away
  have hsrc : cellInt (fun x => ∑ _a : Fin 3, Phi (t, x) * (0 : ℝ)) = 0 := by
    rw [cellInt_congr (fun x => by simp : ∀ x : E3, (∑ _a : Fin 3, Phi (t, x) * (0 : ℝ)) = 0)]
    exact cellInt_const (0 : ℝ)
  -- the gradient-square density of the triple `(Φ,Φ,Φ)`
  have hgrad : cellInt (fun x => gradSq (fun _ : Fin 3 => Phi) (t, x))
      = 3 * adjointWeightDissip Phi t := by
    rw [adjointWeightDissip, ← cellInt_const_mul]
    refine cellInt_congr fun x => ?_
    simp only [gradSq]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fin.sum_univ_three]
    ring
  rw [hsrc, hgrad] at hbal
  -- `quad (Φ,Φ,Φ) = (3/2)Φ²`
  have hquad : (fun s => cellInt (fun x => quad (fun _ : Fin 3 => Phi) (s, x)))
      = fun s => (3 / 2 : ℝ) * adjointWeightEnergy Phi s := by
    funext s
    rw [adjointWeightEnergy, ← cellInt_const_mul]
    refine cellInt_congr fun x => ?_
    simp only [quad, Fin.sum_univ_three]
    ring
  rw [hquad] at hbal
  have h1 := hbal.const_mul (2 / 3 : ℝ)
  have h2 : (fun s => (2 / 3 : ℝ) * ((3 / 2 : ℝ) * adjointWeightEnergy Phi s))
      = adjointWeightEnergy Phi := by
    funext s; ring
  rw [h2] at h1
  convert h1 using 1
  ring

/-! ## Poincaré, the uniform variance cap, and the differential inequality -/

/-- Poincaré on the cell, in the vocabulary of the weight. -/
lemma adjointWeightVar_le_dissip (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (t : ℝ) :
    cellInt (fun x => (Phi (t, x) - cellInt (fun y => Phi (t, y))) ^ 2)
      ≤ 3 * adjointWeightDissip Phi t := by
  have hPhid : Differentiable ℝ Phi := hPhi.differentiable (by simp)
  have hslice : ContDiff ℝ 1 (fun y : E3 => Phi (t, y)) :=
    (contDiff_slice Phi hPhi t).of_le (by exact_mod_cast le_top)
  have hp := cellInt_poincare (fun y : E3 => Phi (t, y)) hslice
  have hconv : ∀ (i : Fin 3) (x : E3),
      fderiv ℝ (fun y : E3 => Phi (t, y)) x (ee i) = dvec (0, ee i) Phi (t, x) :=
    fun i x => fderiv_slice_apply Phi hPhid t x (ee i)
  simp only [hconv] at hp
  have hsum : ∑ i, cellInt (fun x => dvec (0, ee i) Phi (t, x) ^ 2)
      = adjointWeightDissip Phi t := by
    rw [adjointWeightDissip]
    refine (cellInt_finset_sum Finset.univ
      (fun (i : Fin 3) (x : E3) => dvec (0, ee i) Phi (t, x) ^ 2) fun i _ => ?_).symm
    exact ((continuous_dvec Phi hPhi (0, ee i)).comp
      (continuous_const.prodMk continuous_id)).pow 2
  rw [hsum] at hp
  exact hp

/-- The gate's own gradient bound caps the Dirichlet energy. -/
lemma adjointWeightDissip_le (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) {G : ℝ}
    (hG : ∀ (z : STime) (j : Fin 3), |dvec (0, ee j) Phi z| ≤ G) (t : ℝ) :
    adjointWeightDissip Phi t ≤ 3 * G ^ 2 := by
  have hcont : Continuous (fun x : E3 => ∑ k, dvec (0, ee k) Phi (t, x) ^ 2) := by
    refine continuous_time_slice
      (f := fun w : STime => ∑ k, dvec (0, ee k) Phi w ^ 2) ?_ t
    exact continuous_finset_sum _ fun k _ => (continuous_dvec Phi hPhi (0, ee k)).pow 2
  have hle : ∀ x : E3, (∑ k, dvec (0, ee k) Phi (t, x) ^ 2) ≤ 3 * G ^ 2 := by
    intro x
    have hk : ∀ k : Fin 3, dvec (0, ee k) Phi (t, x) ^ 2 ≤ G ^ 2 := by
      intro k
      have := hG (t, x) k
      nlinarith [abs_nonneg (dvec (0, ee k) Phi (t, x)), sq_abs (dvec (0, ee k) Phi (t, x))]
    rw [Fin.sum_univ_three]
    linarith [hk 0, hk 1, hk 2]
  calc cellInt (fun x => ∑ k, dvec (0, ee k) Phi (t, x) ^ 2)
      ≤ cellInt (fun _ : E3 => 3 * G ^ 2) :=
        cellInt_mono hcont continuous_const hle
    _ = 3 * G ^ 2 := cellInt_const _

/-- The variance of the weight equals `∫Φ² − m²`. -/
lemma adjointWeightVar_eq (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (t : ℝ) :
    cellInt (fun x => (Phi (t, x) - cellInt (fun y => Phi (t, y))) ^ 2)
      = adjointWeightEnergy Phi t - cellInt (fun y => Phi (t, y)) ^ 2 := by
  set m : ℝ := cellInt (fun y => Phi (t, y)) with hm
  have hcont : Continuous (fun x : E3 => Phi (t, x)) :=
    continuous_time_slice hPhi.continuous t
  have hpt : ∀ x : E3, (Phi (t, x) - m) ^ 2
      = (Phi (t, x) ^ 2 - (2 * m) * Phi (t, x)) + m ^ 2 := fun x => by ring
  rw [cellInt_congr hpt,
    cellInt_add (f := fun x : E3 => Phi (t, x) ^ 2 - (2 * m) * Phi (t, x))
      (g := fun _ : E3 => m ^ 2)
      ((hcont.pow 2).sub (continuous_const.mul hcont)) continuous_const,
    cellInt_sub (f := fun x : E3 => Phi (t, x) ^ 2) (g := fun x : E3 => (2 * m) * Phi (t, x))
      (hcont.pow 2) (continuous_const.mul hcont),
    cellInt_const_mul, cellInt_const, adjointWeightEnergy, ← hm]
  ring

/-! ## A bounded solution of `Var′ ≥ c·Var` vanishes -/

/-- If a differentiable nonnegative function is bounded above and satisfies
`f′ ≥ c f` with `c > 0`, then it vanishes identically. -/
theorem eq_zero_of_bounded_of_deriv_ge {f : ℝ → ℝ} {f' : ℝ → ℝ} {c B : ℝ} (hc : 0 < c)
    (hderiv : ∀ t, HasDerivAt f (f' t) t) (hineq : ∀ t, c * f t ≤ f' t)
    (hnn : ∀ t, 0 ≤ f t) (hbd : ∀ t, f t ≤ B) (t₀ : ℝ) : f t₀ = 0 := by
  -- `g t = f t · e^{−ct}` is monotone
  set g : ℝ → ℝ := fun t => f t * Real.exp (-(c * t)) with hg
  have hgder : ∀ t, HasDerivAt g
      (f' t * Real.exp (-(c * t)) + f t * (-c * Real.exp (-(c * t)))) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -(c * s)) (-c) t := by
      simpa using ((hasDerivAt_id t).const_mul c).neg
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-(c * s))) (-c * Real.exp (-(c * t))) t := by
      simpa [mul_comm] using h1.exp
    exact (hderiv t).mul h2
  have hmono : Monotone g := by
    refine monotone_of_deriv_nonneg (fun t => (hgder t).differentiableAt) fun t => ?_
    rw [(hgder t).deriv]
    have hpos : 0 < Real.exp (-(c * t)) := Real.exp_pos _
    nlinarith [hineq t]
  -- suppose `f t₀ > 0`; then `f` grows past its own bound
  by_contra hne
  have hpos : 0 < f t₀ := lt_of_le_of_ne (hnn t₀) (Ne.symm hne)
  have hB : 0 < B := lt_of_lt_of_le hpos (hbd t₀)
  set s : ℝ := B / (f t₀ * c) with hs
  have hs0 : 0 ≤ s := by positivity
  have hkey := hmono (le_add_of_nonneg_right hs0 : t₀ ≤ t₀ + s)
  -- unwind `g t₀ ≤ g (t₀ + s)`
  have hexp : Real.exp (-(c * t₀)) = Real.exp (-(c * (t₀ + s))) * Real.exp (c * s) := by
    rw [← Real.exp_add]; ring_nf
  have hgrow : f t₀ * Real.exp (c * s) ≤ f (t₀ + s) := by
    have hpe : 0 < Real.exp (-(c * (t₀ + s))) := Real.exp_pos _
    have h := hkey
    simp only [hg] at h
    rw [hexp] at h
    have h' : (f t₀ * Real.exp (c * s)) * Real.exp (-(c * (t₀ + s)))
        ≤ f (t₀ + s) * Real.exp (-(c * (t₀ + s))) := by nlinarith [h]
    exact le_of_mul_le_mul_right (by linarith [h']) hpe
  have hlin : 1 + c * s ≤ Real.exp (c * s) := by
    have := Real.add_one_le_exp (c * s)
    linarith
  have hcs : f t₀ * (c * s) = B := by
    rw [hs]; field_simp
  nlinarith [hbd (t₀ + s), hgrow, hlin, hpos]

/-! ## The weight is flat -/

/-- **An exact adjoint weight with bounded gradient is spatially constant.**
Its value at every point equals its cell mean. -/
theorem adjoint_weight_eq_cell_mean (hnu : 0 < nu)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVper : SpacePeriodic V)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (hPhiper : SpacePeriodic Phi)
    (hadj : ∀ z : STime, adjointOp nu h V Phi z = 0)
    {G : ℝ} (hG : ∀ (z : STime) (j : Fin 3), |dvec (0, ee j) Phi z| ≤ G)
    (z₀ : STime) :
    Phi z₀ = cellInt (fun x => Phi (z₀.1, x)) := by
  obtain ⟨t₀, x₀⟩ := z₀
  set m : ℝ := cellInt (fun y => Phi (t₀, y)) with hm
  have hmconst : ∀ t : ℝ, cellInt (fun y => Phi (t, y)) = m := fun t =>
    cellInt_adjoint_weight_const hV hVper hdiv hPhi hPhiper hadj t t₀
  -- the variance
  set Var : ℝ → ℝ := fun t => adjointWeightEnergy Phi t - m ^ 2 with hVar
  have hVareq : ∀ t : ℝ, Var t = cellInt (fun x => (Phi (t, x) - m) ^ 2) := by
    intro t
    have h := adjointWeightVar_eq (Phi := Phi) hPhi t
    rw [hmconst t] at h
    rw [hVar]
    exact h.symm
  have hVarnn : ∀ t, 0 ≤ Var t := by
    intro t; rw [hVareq t]; exact cellInt_nonneg fun x => sq_nonneg _
  have hderiv : ∀ t, HasDerivAt Var (2 * nu * adjointWeightDissip Phi t) t := fun t =>
    (hasDerivAt_adjointWeightEnergy hV hVper hdiv hPhi hPhiper hadj t).sub_const (m ^ 2)
  have hpoin : ∀ t, Var t ≤ 3 * adjointWeightDissip Phi t := by
    intro t
    rw [hVareq t]
    have h := adjointWeightVar_le_dissip (Phi := Phi) hPhi t
    rwa [hmconst t] at h
  have hineq : ∀ t, (2 * nu / 3) * Var t ≤ 2 * nu * adjointWeightDissip Phi t := by
    intro t
    nlinarith [hpoin t, hnu]
  have hbd : ∀ t, Var t ≤ 9 * G ^ 2 := by
    intro t
    have h1 := hpoin t
    have h2 := adjointWeightDissip_le (Phi := Phi) hPhi hG t
    linarith
  have hzero : Var t₀ = 0 :=
    eq_zero_of_bounded_of_deriv_ge (c := 2 * nu / 3) (B := 9 * G ^ 2) (by positivity)
      hderiv hineq hVarnn hbd t₀
  -- pointwise vanishing of `(Φ − m)²`
  have hcellzero : cellInt (fun x => (Phi (t₀, x) - m) ^ 2) = 0 := by
    rw [← hVareq t₀]; exact hzero
  have hcont : Continuous (fun x : E3 => (Phi (t₀, x) - m) ^ 2) :=
    ((continuous_time_slice hPhi.continuous t₀).sub continuous_const).pow 2
  have hper : ∀ (x : E3) (j : Fin 3),
      (Phi (t₀, x + ee j) - m) ^ 2 = (Phi (t₀, x) - m) ^ 2 := by
    intro x j
    rw [hPhiper (t₀, x) j]
  have hpt := eq_zero_of_cellInt_eq_zero hcont (fun x => sq_nonneg _) hper hcellzero x₀
  have : Phi (t₀, x₀) - m = 0 := by
    have := sq_eq_zero_iff.mp hpt
    exact this
  simpa [hm] using sub_eq_zero.mp this

end Exact

/-! ## The gate is false -/

/-- **The exact concentrated adjoint weight gate fails for every `θ < 1`.**
Taking the zero velocity field already suffices: any smooth periodic weight with
bounded gradient solving the adjoint equation exactly is spatially constant, so
its concentration ratio is exactly `1`. -/
theorem not_concentratedAdjointWeightGate_of_lt_one {nu theta : ℝ} (hnu : 0 < nu)
    (hth : theta < 1) : ¬ ConcentratedAdjointWeightGate nu theta := by
  intro hgate
  have hV : ContDiff ℝ (⊤ : ℕ∞) (fun _ : STime => (0 : E3)) := contDiff_const
  have hVper : SpacePeriodic (fun _ : STime => (0 : E3)) := fun _ _ => rfl
  have hdiv : ∀ z : STime, divg (fun _ : STime => (0 : E3)) z = 0 := by
    intro z
    simp [divg, dspace]
  obtain ⟨Phi, G, hPhi, hPhiper, _hnn, hadj, hG, hzpos, hconc⟩ :=
    hgate (fun _ : STime => (0 : E3)) hV hVper hdiv 0 (0, 0)
  have hflat := adjoint_weight_eq_cell_mean (nu := nu) (h := 0)
    (V := fun _ : STime => (0 : E3)) (Phi := Phi) hnu hV hVper hdiv hPhi hPhiper hadj hG (0, 0)
  rw [← hflat] at hconc
  nlinarith [hconc, hzpos, hth]

end ClayNS

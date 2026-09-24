/-
# The increment energy balance on the periodicity cell

`RequestProject/NavierStokes/IncrementLocalEnergy.lean` derives the *pointwise*
local energy identity for the increment `δ_h u = u(·+h) − u`,

  `∂_t q + div( q·u(·+h) + δ_h p·δ_h u ) = ν(Δq − |∇δ_h u|²) − δ_h u·(δ_h u·∇)u`,
  `q = ½|δ_h u|²`,

and the derivative transfer

  `δ_h u·(δ_h u·∇)u = div((u·δ_h u)δ_h u) − ∑_{a,j} u_a δ_h u_j ∂_j δ_h u_a`.

This file integrates both over the periodicity cell, where every divergence
disappears (`cellInt_dvec_divergence_eq_zero`).  The results are exact
*integrated* balances, not pointwise identities:

* `ClayNS.cellInt_divg_eq_zero`, `ClayNS.cellInt_lap_eq_zero` — the two
  divergence-theorem inputs;
* `ClayNS.hasDerivAt_incrEnergy` — **the increment energy balance**
  `d/dt ∫q = − ν∫|∇δ_h u|² − ∫δ_h u·(δ_h u·∇)u`.  Neither the pressure nor the
  transport term survives: both were fluxes.
* `ClayNS.incrStretchInt_eq_neg_transferInt` — after integration the stretching
  term equals `+∫∑ u_a δ_h u_j ∂_j δ_h u_a`, so it never needs a bound on `∇u`;
* `ClayNS.hasDerivAt_incrEnergy_transfer` and
  `ClayNS.incrEnergy_deriv_le_of_amplitude` — **the amplitude form**
  `d/dt ∫q ≤ −(ν/2)∫|∇δ_h u|² + (A²/ν)∫q` for any bound `A` on `|u(t,·)|`.
  Only the amplitude of the velocity enters: the modulus of continuity of a
  periodic solution, measured in `L²`, can grow at most at the rate `A²/ν`,
  with no gradient hypothesis at all.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.IncrementLocalEnergy
import RequestProject.NavierStokes.AncientLiouville

open scoped BigOperators

noncomputable section

namespace ClayNS

/-! ## Smoothness and periodicity of the derived fields -/

lemma continuous_slice {f : STime → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    Continuous fun x : E3 => f (t, x) :=
  hf.continuous.comp (continuous_const.prodMk continuous_id)

lemma contDiff_lapFun {f : STime → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w => lap f w) :=
  ContDiff.sum fun k _ => contDiff_dvec _ (contDiff_dvec f hf (0, ee k)) (0, ee k)

lemma contDiff_divgFun {F : STime → E3} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w => divg F w) :=
  ContDiff.sum fun i _ => contDiff_coord _ (contDiff_dvec F hF (0, ee i)) i

lemma contDiff_incrDissip {V : STime → E3} (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    ContDiff ℝ (⊤ : ℕ∞) (incrDissip h V) :=
  ContDiff.sum fun k _ => ContDiff.sum fun a _ =>
    (contDiff_dvec _ (contDiff_incrComp h hV a) (0, ee k)).mul
      (contDiff_dvec _ (contDiff_incrComp h hV a) (0, ee k))

lemma contDiff_incrStretch {V : STime → E3} (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    ContDiff ℝ (⊤ : ℕ∞) (incrStretch h V) :=
  ContDiff.sum fun a _ => (contDiff_incrComp h hV a).mul
    (ContDiff.sum fun j _ => (contDiff_incrComp h hV j).mul
      (contDiff_dvec _ (contDiff_coord V hV a) (0, ee j)))

lemma contDiff_incrTransfer {V : STime → E3} (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    ContDiff ℝ (⊤ : ℕ∞) (incrTransfer h V) :=
  ContDiff.sum fun a _ => ContDiff.sum fun j _ =>
    ((contDiff_coord V hV a).mul (contDiff_incrComp h hV j)).mul
      (contDiff_dvec _ (contDiff_incrComp h hV a) (0, ee j))

lemma contDiff_incrFlux {V : STime → E3} {P : STime → ℝ} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P) :
    ContDiff ℝ (⊤ : ℕ∞) (incrFlux h V P) :=
  ((contDiff_incrQuad h hV).smul (contDiff_shift h hV)).add
    ((contDiff_incrPres h hP).smul (contDiff_incrVec h hV))

lemma spacePeriodic_shift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : STime → F} (h : E3) (hper : SpacePeriodic V) : SpacePeriodic (shift h V) := by
  intro z j
  simp only [shift_apply]
  have hcomm : z.2 + ee j + h = z.2 + h + ee j := by abel
  rw [hcomm]
  exact hper (z.1, z.2 + h) j

lemma spacePeriodic_incrVec {V : STime → E3} (h : E3) (hper : SpacePeriodic V) :
    SpacePeriodic (incrVec h V) := by
  intro z j
  show shift h V (z.1, z.2 + ee j) - V (z.1, z.2 + ee j) = shift h V z - V z
  rw [spacePeriodic_shift h hper z j, hper z j]

lemma spacePeriodic_incrComp {V : STime → E3} (h : E3) (hper : SpacePeriodic V) (a : Fin 3) :
    SpacePeriodic (incrComp h V a) := fun z j => by
  have := spacePeriodic_incrVec h hper z j
  exact congrArg (fun v : E3 => v a) this

lemma spacePeriodic_incrQuad {V : STime → E3} (h : E3) (hper : SpacePeriodic V) :
    SpacePeriodic (incrQuad h V) := fun z j => by
  simp only [incrQuad, quad]
  exact congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
    (Finset.sum_congr rfl fun a _ => by rw [spacePeriodic_incrComp h hper a z j])

lemma spacePeriodic_incrPres {P : STime → ℝ} (h : E3) (hper : SpacePeriodic P) :
    SpacePeriodic (incrPres h P) := fun z j => by
  show shift h P (z.1, z.2 + ee j) - P (z.1, z.2 + ee j) = shift h P z - P z
  rw [spacePeriodic_shift h hper z j, hper z j]

lemma spacePeriodic_incrFlux {V : STime → E3} {P : STime → ℝ} (h : E3)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P) :
    SpacePeriodic (incrFlux h V P) := fun z j => by
  show incrQuad h V (z.1, z.2 + ee j) • shift h V (z.1, z.2 + ee j)
      + incrPres h P (z.1, z.2 + ee j) • incrVec h V (z.1, z.2 + ee j)
    = incrQuad h V z • shift h V z + incrPres h P z • incrVec h V z
  rw [spacePeriodic_incrQuad h hVper z j, spacePeriodic_shift h hVper z j,
    spacePeriodic_incrPres h hPper z j, spacePeriodic_incrVec h hVper z j]

lemma spacePeriodic_incrPair {V : STime → E3} (h : E3) (hper : SpacePeriodic V) :
    SpacePeriodic (incrPair h V) := fun z j => by
  simp only [incrPair]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [spacePeriodic_incrComp h hper a z j]
  exact congrArg (fun r : ℝ => r * incrComp h V a z) (spacePeriodic_coord hper a z j)

lemma spacePeriodic_pairFlux {V : STime → E3} (h : E3) (hper : SpacePeriodic V) :
    SpacePeriodic (fun w => incrPair h V w • incrVec h V w) := fun z j => by
  show incrPair h V (z.1, z.2 + ee j) • incrVec h V (z.1, z.2 + ee j)
    = incrPair h V z • incrVec h V z
  rw [spacePeriodic_incrPair h hper z j, spacePeriodic_incrVec h hper z j]

/-! ## The two divergence-theorem inputs -/

/-- **The cell integral of a divergence vanishes.** -/
theorem cellInt_divg_eq_zero (F : STime → E3) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hper : SpacePeriodic F) (t : ℝ) : cellInt (fun x => divg F (t, x)) = 0 := by
  have hcomp : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => F w i) :=
    fun i => contDiff_coord F hF i
  have hcper : ∀ i : Fin 3, SpacePeriodic (fun w => F w i) :=
    fun i => spacePeriodic_coord hper i
  have hzero := cellInt_dvec_divergence_eq_zero (fun i w => F w i) hcomp hcper t
  have hpt : ∀ x : E3, divg F (t, x) = ∑ i, dvec (0, ee i) (fun w => F w i) (t, x) :=
    fun x => divg_eq_sum F hF (t, x)
  rw [cellInt_congr hpt]
  exact hzero

/-- **The cell integral of a Laplacian vanishes.** -/
theorem cellInt_lap_eq_zero (f : STime → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hper : SpacePeriodic f) (t : ℝ) : cellInt (fun x => lap f (t, x)) = 0 := by
  have hd : ∀ k : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (dvec (0, ee k) f) :=
    fun k => contDiff_dvec f hf (0, ee k)
  have hdper : ∀ k : Fin 3, SpacePeriodic (dvec (0, ee k) f) :=
    fun k => spacePeriodic_dvec (differentiable_of_contDiffTop hf) hper (0, ee k)
  exact cellInt_dvec_divergence_eq_zero (fun k => dvec (0, ee k) f) hd hdper t

/-! ## The integrated increment quantities -/

/-- The increment energy `∫_cell ½|δ_h u|²`. -/
def incrEnergy (h : E3) (V : STime → E3) (t : ℝ) : ℝ := cellInt (fun x => incrQuad h V (t, x))

/-- The increment dissipation `∫_cell |∇δ_h u|²`. -/
def incrDissipInt (h : E3) (V : STime → E3) (t : ℝ) : ℝ :=
  cellInt (fun x => incrDissip h V (t, x))

/-- The integrated stretching term. -/
def incrStretchInt (h : E3) (V : STime → E3) (t : ℝ) : ℝ :=
  cellInt (fun x => incrStretch h V (t, x))

/-- The integrated transferred obstruction. -/
def incrTransferInt (h : E3) (V : STime → E3) (t : ℝ) : ℝ :=
  cellInt (fun x => incrTransfer h V (t, x))

/-! ## The increment energy balance -/

/-- **The increment energy balance on the torus.**  For a smooth periodic
divergence-free solution,

`d/dt ∫_cell ½|δ_h u|² = − ν ∫_cell |∇δ_h u|² − ∫_cell δ_h u·(δ_h u·∇)u`.

The pressure and the transport terms are fluxes and integrate away. -/
theorem hasDerivAt_incrEnergy (nu : ℝ) (V : STime → E3) (P : STime → ℝ) (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (t : ℝ) :
    HasDerivAt (incrEnergy h V)
      (- (nu * incrDissipInt h V t) - incrStretchInt h V t) t := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  have hF : ContDiff ℝ (⊤ : ℕ∞) (incrFlux h V P) := contDiff_incrFlux h hV hP
  have hbase := hasDerivAt_cellInt (incrQuad h V) hq t
  -- rewrite the time derivative pointwise
  have hpt : ∀ x : E3, dvec (1, 0) (incrQuad h V) (t, x)
      = ((nu * lap (incrQuad h V) (t, x) - nu * incrDissip h V (t, x))
          - incrStretch h V (t, x)) - divg (incrFlux h V P) (t, x) := by
    intro x
    have := increment_local_energy_identity nu V P h hV hP hdiv hmom (t, x)
    linarith [this]
  have hcont_lap : Continuous fun x : E3 => nu * lap (incrQuad h V) (t, x) :=
    continuous_const.mul (continuous_slice (contDiff_lapFun hq) t)
  have hcont_dis : Continuous fun x : E3 => nu * incrDissip h V (t, x) :=
    continuous_const.mul (continuous_slice (contDiff_incrDissip h hV) t)
  have hcont_str : Continuous fun x : E3 => incrStretch h V (t, x) :=
    continuous_slice (contDiff_incrStretch h hV) t
  have hcont_div : Continuous fun x : E3 => divg (incrFlux h V P) (t, x) :=
    continuous_slice (contDiff_divgFun hF) t
  have hsplit : cellInt (fun x => dvec (1, 0) (incrQuad h V) (t, x))
      = - (nu * incrDissipInt h V t) - incrStretchInt h V t := by
    rw [cellInt_congr hpt,
      cellInt_sub ((hcont_lap.sub hcont_dis).sub hcont_str) hcont_div,
      cellInt_sub (hcont_lap.sub hcont_dis) hcont_str,
      cellInt_sub hcont_lap hcont_dis,
      cellInt_const_mul nu (fun x => lap (incrQuad h V) (t, x)),
      cellInt_const_mul nu (fun x => incrDissip h V (t, x)),
      cellInt_lap_eq_zero (incrQuad h V) hq (spacePeriodic_incrQuad h hVper) t,
      cellInt_divg_eq_zero (incrFlux h V P) hF (spacePeriodic_incrFlux h hVper hPper) t]
    simp [incrDissipInt, incrStretchInt]
  rw [hsplit] at hbase
  exact hbase

/-- **After integration the stretching term needs no gradient bound.**  The
divergence produced by the derivative transfer integrates away, so
`∫ δ_h u·(δ_h u·∇)u = − ∫ ∑_{a,j} u_a δ_h u_j ∂_j δ_h u_a`. -/
theorem incrStretchInt_eq_neg_transferInt (V : STime → E3) (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVper : SpacePeriodic V)
    (hdiv : ∀ z : STime, divg V z = 0) (t : ℝ) :
    incrStretchInt h V t = - incrTransferInt h V t := by
  have hpair : ContDiff ℝ (⊤ : ℕ∞) (fun w => incrPair h V w • incrVec h V w) :=
    (contDiff_incrPair h hV).smul (contDiff_incrVec h hV)
  have hpt : ∀ x : E3, incrStretch h V (t, x)
      = divg (fun w => incrPair h V w • incrVec h V w) (t, x) - incrTransfer h V (t, x) :=
    fun x => incrStretch_divergence_transfer h hV hdiv (t, x)
  have hcont_div : Continuous fun x : E3 =>
      divg (fun w => incrPair h V w • incrVec h V w) (t, x) :=
    continuous_slice (contDiff_divgFun hpair) t
  have hcont_tr : Continuous fun x : E3 => incrTransfer h V (t, x) :=
    continuous_slice (contDiff_incrTransfer h hV) t
  rw [incrStretchInt, cellInt_congr hpt, cellInt_sub hcont_div hcont_tr,
    cellInt_divg_eq_zero _ hpair (spacePeriodic_pairFlux h hVper) t]
  simp [incrTransferInt]

/-- The increment energy balance in transferred form. -/
theorem hasDerivAt_incrEnergy_transfer (nu : ℝ) (V : STime → E3) (P : STime → ℝ) (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (t : ℝ) :
    HasDerivAt (incrEnergy h V)
      (- (nu * incrDissipInt h V t) + incrTransferInt h V t) t := by
  have hbal := hasDerivAt_incrEnergy nu V P h hV hP hVper hPper hdiv hmom t
  rwa [incrStretchInt_eq_neg_transferInt V h hV hVper hdiv t, sub_neg_eq_add] at hbal

/-- The integrated Young bound: the transferred obstruction costs half the
dissipation plus `(A²/ν)` times the increment energy, for any pointwise bound
`A` on the velocity at time `t`. -/
theorem incrEnergy_balance_le_of_amplitude (nu : ℝ) (hnu : 0 < nu) (V : STime → E3)
    (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (t : ℝ) (A : ℝ) (hA : ∀ x : E3, (∑ a, V (t, x) a * V (t, x) a) ≤ A ^ 2) :
    - (nu * incrDissipInt h V t) + incrTransferInt h V t
      ≤ - (nu / 2 * incrDissipInt h V t) + A ^ 2 / nu * incrEnergy h V t := by
  have hptb : ∀ x : E3, incrTransfer h V (t, x)
      ≤ nu / 2 * incrDissip h V (t, x) + A ^ 2 / nu * incrQuad h V (t, x) := by
    intro x
    have hy := (le_abs_self (incrTransfer h V (t, x))).trans
      (incrTransfer_abs_le h V (t, x) hnu)
    rw [sum_sq_incrComp] at hy
    have hq0 : 0 ≤ incrQuad h V (t, x) := by
      have : incrQuad h V (t, x) = (1 / 2 : ℝ) * ∑ a, incrComp h V a (t, x) * incrComp h V a (t, x) :=
        rfl
      rw [this]
      have : (0 : ℝ) ≤ ∑ a, incrComp h V a (t, x) * incrComp h V a (t, x) :=
        Finset.sum_nonneg fun a _ => mul_self_nonneg _
      linarith
    have hAx := hA x
    have hnu' : nu ≠ 0 := ne_of_gt hnu
    have hkey : 1 / nu * ((∑ a, V (t, x) a * V (t, x) a) * incrQuad h V (t, x))
        ≤ 1 / nu * (A ^ 2 * incrQuad h V (t, x)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAx hq0) (by positivity)
    have e1 : 1 / (2 * nu) * ((∑ a, V (t, x) a * V (t, x) a) * (2 * incrQuad h V (t, x)))
        = 1 / nu * ((∑ a, V (t, x) a * V (t, x) a) * incrQuad h V (t, x)) := by
      field_simp
      try ring
    have e2 : A ^ 2 / nu * incrQuad h V (t, x) = 1 / nu * (A ^ 2 * incrQuad h V (t, x)) := by
      field_simp
      try ring
    have hstep : 1 / (2 * nu) * ((∑ a, V (t, x) a * V (t, x) a) * (2 * incrQuad h V (t, x)))
        ≤ A ^ 2 / nu * incrQuad h V (t, x) := by
      rw [e1, e2]
      exact hkey
    linarith
  have hcont_tr : Continuous fun x : E3 => incrTransfer h V (t, x) :=
    continuous_slice (contDiff_incrTransfer h hV) t
  have hcont_rhs : Continuous fun x : E3 =>
      nu / 2 * incrDissip h V (t, x) + A ^ 2 / nu * incrQuad h V (t, x) :=
    (continuous_const.mul (continuous_slice (contDiff_incrDissip h hV) t)).add
      (continuous_const.mul (continuous_slice (contDiff_incrQuad h hV) t))
  have hc1 : Continuous fun x : E3 => nu / 2 * incrDissip h V (t, x) :=
    continuous_const.mul (continuous_slice (contDiff_incrDissip h hV) t)
  have hc2 : Continuous fun x : E3 => A ^ 2 / nu * incrQuad h V (t, x) :=
    continuous_const.mul (continuous_slice (contDiff_incrQuad h hV) t)
  have hmono := cellInt_mono hcont_tr hcont_rhs hptb
  rw [cellInt_add hc1 hc2,
    cellInt_const_mul (nu / 2) (fun x => incrDissip h V (t, x)),
    cellInt_const_mul (A ^ 2 / nu) (fun x => incrQuad h V (t, x))] at hmono
  have htr : incrTransferInt h V t ≤ nu / 2 * incrDissipInt h V t
      + A ^ 2 / nu * incrEnergy h V t := hmono
  have hdis0 : 0 ≤ incrDissipInt h V t := by
    refine cellInt_nonneg fun x => ?_
    exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun a _ => mul_self_nonneg _
  linarith

/-- **The amplitude form of the increment energy inequality.**  If `|u(t,·)| ≤ A`
pointwise on the cell then

`d/dt ∫½|δ_h u|² ≤ −(ν/2)∫|∇δ_h u|² + (A²/ν)∫½|δ_h u|²`.

No bound on `∇u` is used: the pressure and transport terms were fluxes, and the
stretching term was transferred onto the increment.  In particular the `L²`
modulus of continuity of a smooth periodic solution can grow at most at the
exponential rate `A²/ν`. -/
theorem deriv_incrEnergy_le_of_amplitude (nu : ℝ) (hnu : 0 < nu) (V : STime → E3)
    (P : STime → ℝ) (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (t : ℝ) (A : ℝ) (hA : ∀ x : E3, (∑ a, V (t, x) a * V (t, x) a) ≤ A ^ 2) :
    deriv (incrEnergy h V) t
      ≤ - (nu / 2 * incrDissipInt h V t) + A ^ 2 / nu * incrEnergy h V t := by
  rw [(hasDerivAt_incrEnergy_transfer nu V P h hV hP hVper hPper hdiv hmom t).deriv]
  exact incrEnergy_balance_le_of_amplitude nu hnu V h hV t A hA

/-! ## Grönwall: growth of the `L²` modulus of continuity -/

lemma incrDissipInt_nonneg (h : E3) (V : STime → E3) (t : ℝ) : 0 ≤ incrDissipInt h V t := by
  refine cellInt_nonneg fun x => ?_
  exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun a _ => mul_self_nonneg _

/-- The exponential Lyapunov functional for the increment energy: with
`c = A²/ν` and a uniform amplitude bound `A`, the quantity `e^{-ct}∫½|δ_h u|²`
is nonincreasing. -/
theorem exp_incrEnergy_antitone (nu : ℝ) (hnu : 0 < nu) (V : STime → E3) (P : STime → ℝ)
    (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (A : ℝ) (hA : ∀ (t : ℝ) (x : E3), (∑ a, V (t, x) a * V (t, x) a) ≤ A ^ 2) :
    Antitone (fun t : ℝ => Real.exp (-(A ^ 2 / nu) * t) * incrEnergy h V t) := by
  set c : ℝ := A ^ 2 / nu with hc
  have hderiv : ∀ t : ℝ, HasDerivAt (fun r : ℝ => Real.exp (-c * r) * incrEnergy h V r)
      (Real.exp (-c * t) * (-c) * incrEnergy h V t
        + Real.exp (-c * t) * (- (nu * incrDissipInt h V t) + incrTransferInt h V t)) t := by
    intro t
    have h1 : HasDerivAt (fun r : ℝ => Real.exp (-c * r)) (Real.exp (-c * t) * (-c)) t := by
      simpa using (((hasDerivAt_id t).const_mul (-c)).exp)
    exact h1.mul (hasDerivAt_incrEnergy_transfer nu V P h hV hP hVper hPper hdiv hmom t)
  refine antitone_of_deriv_nonpos (fun t => (hderiv t).differentiableAt) fun t => ?_
  rw [(hderiv t).deriv]
  have hbal := incrEnergy_balance_le_of_amplitude nu hnu V h hV t A (hA t)
  have hexp : 0 < Real.exp (-c * t) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_left hbal hexp.le
  have hgood : 0 ≤ Real.exp (-c * t) * (nu / 2 * incrDissipInt h V t) :=
    mul_nonneg hexp.le (mul_nonneg (by positivity) (incrDissipInt_nonneg h V t))
  nlinarith [hmul, hgood]

/-- **Grönwall bound for the increment energy.**  With a uniform amplitude bound
`|u| ≤ A`, for `s ≤ t`

`∫½|δ_h u(t)|² ≤ e^{(A²/ν)(t−s)} ∫½|δ_h u(s)|²`.

The `L²` modulus of continuity of a smooth periodic solution therefore grows at
most exponentially, at a rate determined by the amplitude and the viscosity
alone — no gradient bound enters. -/
theorem incrEnergy_le_exp (nu : ℝ) (hnu : 0 < nu) (V : STime → E3) (P : STime → ℝ)
    (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (A : ℝ) (hA : ∀ (t : ℝ) (x : E3), (∑ a, V (t, x) a * V (t, x) a) ≤ A ^ 2)
    {s t : ℝ} (hst : s ≤ t) :
    incrEnergy h V t ≤ Real.exp (A ^ 2 / nu * (t - s)) * incrEnergy h V s := by
  set c : ℝ := A ^ 2 / nu with hc
  have hmono := exp_incrEnergy_antitone nu hnu V P h hV hP hVper hPper hdiv hmom A hA hst
  simp only [← hc] at hmono
  have hexp : 0 < Real.exp (-c * t) := Real.exp_pos _
  have hprod : Real.exp (c * (t - s)) * Real.exp (-c * t) = Real.exp (-c * s) := by
    rw [← Real.exp_add]
    ring_nf
  calc incrEnergy h V t
      = (Real.exp (-c * t) * incrEnergy h V t) / Real.exp (-c * t) := by
        field_simp
    _ ≤ (Real.exp (-c * s) * incrEnergy h V s) / Real.exp (-c * t) :=
        div_le_div_of_nonneg_right hmono hexp.le
    _ = Real.exp (c * (t - s)) * incrEnergy h V s := by
        rw [← hprod]
        field_simp

end ClayNS

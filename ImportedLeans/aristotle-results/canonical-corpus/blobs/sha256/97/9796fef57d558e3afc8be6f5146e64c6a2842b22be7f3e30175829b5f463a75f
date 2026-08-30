/-
# The transverse viscous coercivity of the modulus variable

The modulus tranche bounds the surviving transverse stretching pairing by the
transverse surplus `T_ε = |∇δ_hu|² − |∇r_ε|²` divided by `r_ε`.  What that
argument does *not* yet say is that `T_ε/r_ε` is exactly what the **viscous term
itself** produces once it is written in the modulus variable.  This file proves
that, as an identity.

Writing `q = ½|δ_hu|²`, `r_ε = √(2q + ε²)` and `W_ε = 1/r_ε`, the two
second-order identities

  `Δq = |∇δ_hu|² + δ_hu·Δδ_hu`      (`ClayNS.lap_incrQuad_eq`),
  `Δq = |∇r_ε|² + r_ε·Δr_ε`        (`ClayNS.lap_incrQuad_eq_modulus`)

combine into the pointwise identity
(`ClayNS.modulusEps_viscous_transverse_identity`)

  `W_ε·(δ_hu·Δδ_hu) = Δr_ε − T_ε/r_ε`,

whose spatial mean on the torus is
(`ClayNS.modulusEps_viscous_transverse_cell_identity`)

  `∫_cell W_ε·(δ_hu·Δδ_hu) = −∫_cell T_ε/r_ε`,

because the cell integral of a Laplacian vanishes.  So the transverse surplus is
*precisely* the viscous coercivity available in the modulus variable — it is not
an upper bound that has been thrown away, as `|w^T S w| ≤ |S||w|²` would do.

Combining this with the regularized Caccioppoli budget gives
`ClayNS.modulusEps_viscous_dominates_stretching`: the viscous transverse
coercivity beats the whole stretching source with a *fixed fraction* to spare,
uniformly in `ε`, with only the `r_ε|u|²` term left over.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.ModulusLevelSplit
import RequestProject.NavierStokes.EnergyIdentity
import RequestProject.NavierStokes.IncrementEnergyPeriodic

open scoped BigOperators

noncomputable section

namespace ClayNS

/-! ## The viscous pairing of the increment -/

/-- The viscous pairing `δ_hu·Δδ_hu`. -/
def incrLapPair (h : E3) (V : STime → E3) : STime → ℝ :=
  fun z => ∑ a, incrComp h V a z * lap (incrComp h V a) z

lemma lap_eq_sum_dvec (f : STime → ℝ) (z : STime) :
    lap f z = ∑ k, dvec (0, ee k) (dvec (0, ee k) f) z := rfl

/-- **The quadratic chain rule.** `Δ(½|δ_hu|²) = |∇δ_hu|² + δ_hu·Δδ_hu`. -/
theorem lap_incrQuad_eq (h : E3) {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (z : STime) :
    lap (incrQuad h V) z = incrDissip h V z + incrLapPair h V z := by
  have hW : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (incrComp h V a) := fun a => contDiff_incrComp h hV a
  have hbase := lap_quad (incrComp h V) hW z
  have hform : incrQuad h V = quad (incrComp h V) := rfl
  have hsplit : ∀ k : Fin 3, (∑ a, (dvec (0, ee k) (incrComp h V a) z
        * dvec (0, ee k) (incrComp h V a) z
      + incrComp h V a z * dvec (0, ee k) (dvec (0, ee k) (incrComp h V a)) z))
      = (∑ a, dvec (0, ee k) (incrComp h V a) z * dvec (0, ee k) (incrComp h V a) z)
        + ∑ a, incrComp h V a z * dvec (0, ee k) (dvec (0, ee k) (incrComp h V a)) z :=
    fun k => Finset.sum_add_distrib
  have hL : (∑ k, ∑ a, incrComp h V a z
        * dvec (0, ee k) (dvec (0, ee k) (incrComp h V a)) z)
      = incrLapPair h V z := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => by
      rw [lap_eq_sum_dvec, Finset.mul_sum]
  rw [hform, hbase, Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_add_distrib, hL,
    incrDissip]

/-! ## The modulus chain rule -/

/-- **The modulus chain rule.** `Δq = |∇r_ε|² + r_ε·Δr_ε`: differentiating the
first-order identity `r_ε·∇r_ε = ∇q` once more. -/
theorem lap_incrQuad_eq_modulus {eps : ℝ} (heps : 0 < eps) {h : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (z : STime) :
    lap (incrQuad h V) z
      = (∑ k, (dvec (0, ee k) (incrModEps eps h V) z) ^ 2)
        + incrModEps eps h V z * lap (incrModEps eps h V) z := by
  have hmod : ContDiff ℝ (⊤ : ℕ∞) (incrModEps eps h V) := contDiff_incrModEps heps hV
  have hfun : ∀ k : Fin 3,
      (fun w => incrModEps eps h V w * dvec (0, ee k) (incrModEps eps h V) w)
        = dvec (0, ee k) (incrQuad h V) := by
    intro k
    funext w
    have hrne : incrModEps eps h V w ≠ 0 := ne_of_gt (incrModEps_pos' heps h V w)
    have h1 := dvec_incrModEps (h := h) heps hV w (0, ee k)
    have h2 : dvec (0, ee k) (incrQuad h V) w
        = ∑ i, incrComp h V i w * dvec (0, ee k) (incrComp h V i) w :=
      dvec_quad (incrComp h V) (fun i => contDiff_incrComp h hV i) (0, ee k) w
    rw [h1, h2]
    field_simp
  have hstep : ∀ k : Fin 3,
      dvec (0, ee k) (dvec (0, ee k) (incrQuad h V)) z
        = (dvec (0, ee k) (incrModEps eps h V) z) ^ 2
          + incrModEps eps h V z
              * dvec (0, ee k) (dvec (0, ee k) (incrModEps eps h V)) z := by
    intro k
    rw [← hfun k,
      dvec_mul _ _ z ((differentiable_of_contDiffTop hmod) z)
        ((differentiable_of_contDiffTop (contDiff_dvec _ hmod (0, ee k))) z) (0, ee k)]
    ring
  rw [lap_eq_sum_dvec (incrQuad h V) z, lap_eq_sum_dvec (incrModEps eps h V) z,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => hstep k

/-! ## The exact viscous identity in the modulus variable -/

/-- **The transverse viscous identity.**  `W_ε·(δ_hu·Δδ_hu) = Δr_ε − T_ε/r_ε`:
the viscous term, written in the modulus variable, produces the transverse
surplus `T_ε = |∇δ_hu|² − |∇r_ε|²` divided by `r_ε`, up to an exact Laplacian. -/
theorem modulusEps_viscous_transverse_identity {eps : ℝ} (heps : 0 < eps) {h : E3}
    {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (z : STime) :
    incrModEpsWeight eps h V z * incrLapPair h V z
      = lap (incrModEps eps h V) z
        - incrTransDissipEps eps h V z / incrModEps eps h V z := by
  have hrne : incrModEps eps h V z ≠ 0 := ne_of_gt (incrModEps_pos' heps h V z)
  have hWz : incrModEpsWeight eps h V z = 1 / incrModEps eps h V z := by
    rw [incrModEpsWeight_value, incrModEps, one_div]
  have hq := lap_incrQuad_eq h hV z
  have hm := lap_incrQuad_eq_modulus (h := h) heps hV z
  have hT : incrTransDissipEps eps h V z
      = incrDissip h V z - ∑ k, (dvec (0, ee k) (incrModEps eps h V) z) ^ 2 := rfl
  have hkey : incrLapPair h V z
      = (∑ k, (dvec (0, ee k) (incrModEps eps h V) z) ^ 2)
        + incrModEps eps h V z * lap (incrModEps eps h V) z - incrDissip h V z := by
    linarith
  rw [hWz, hT, hkey]
  field_simp
  ring

/-- **The integrated transverse viscous identity on the cell.**
`∫_cell W_ε·(δ_hu·Δδ_hu) = −∫_cell T_ε/r_ε`. -/
theorem modulusEps_viscous_transverse_cell_identity {eps : ℝ} (heps : 0 < eps) {h : E3}
    {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVper : SpacePeriodic V) (t : ℝ) :
    cellInt (fun x => incrModEpsWeight eps h V (t, x) * incrLapPair h V (t, x))
      = - cellInt (fun x =>
          incrTransDissipEps eps h V (t, x) / incrModEps eps h V (t, x)) := by
  have hslice : Continuous (fun x : E3 => ((t, x) : STime)) :=
    continuous_const.prodMk continuous_id
  have hmod : ContDiff ℝ (⊤ : ℕ∞) (incrModEps eps h V) := contDiff_incrModEps heps hV
  have hcr : Continuous (fun x : E3 => incrModEps eps h V (t, x)) :=
    hmod.continuous.comp hslice
  have hne : ∀ x : E3, incrModEps eps h V (t, x) ≠ 0 :=
    fun x => ne_of_gt (incrModEps_pos' heps h V (t, x))
  have hcT : Continuous (fun x : E3 => incrTransDissipEps eps h V (t, x)) := by
    have hdis : ContDiff ℝ (⊤ : ℕ∞) (incrDissip h V) := contDiff_incrDissip h hV
    have hrad : ContDiff ℝ (⊤ : ℕ∞)
        (fun w => ∑ j, (dvec (0, ee j) (incrModEps eps h V) w) ^ 2) :=
      ContDiff.sum fun j _ => (contDiff_dvec _ hmod _).pow 2
    exact ((hdis.sub hrad).continuous).comp hslice
  have hclap : Continuous (fun x : E3 => lap (incrModEps eps h V) (t, x)) := by
    have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun w => lap (incrModEps eps h V) w) :=
      ContDiff.sum fun k _ => contDiff_dvec _ (contDiff_dvec _ hmod _) _
    exact hcd.continuous.comp hslice
  have hpt : ∀ x : E3, incrModEpsWeight eps h V (t, x) * incrLapPair h V (t, x)
      = lap (incrModEps eps h V) (t, x)
        - incrTransDissipEps eps h V (t, x) / incrModEps eps h V (t, x) :=
    fun x => modulusEps_viscous_transverse_identity heps hV (t, x)
  have hlapzero : cellInt (fun x => lap (incrModEps eps h V) (t, x)) = 0 :=
    cellInt_lap_eq_zero _ hmod (spacePeriodic_incrModEps (eps := eps) (h := h) hVper) t
  have hquot : Continuous (fun x : E3 =>
      incrTransDissipEps eps h V (t, x) / incrModEps eps h V (t, x)) := hcT.div hcr hne
  rw [cellInt_congr hpt, cellInt_sub hclap hquot, hlapzero, zero_sub]

/-! ## The viscous term dominates the stretching source -/

/-- **The transverse viscous coercivity beats the stretching source.**  Adding
the exact viscous identity to the regularized Caccioppoli budget leaves half the
transverse dissipation on the good side, uniformly in `ε`, with only the term
linear in `r_ε` as a source. -/
theorem modulusEps_viscous_dominates_stretching {nu eps : ℝ} (hnu : 0 < nu) (heps : 0 < eps)
    {h : E3} {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hVper : SpacePeriodic V)
    (hdiv : ∀ z : STime, divg V z = 0) (t : ℝ) :
    nu / 2 * cellInt (fun x =>
        incrTransDissipEps eps h V (t, x) / incrModEps eps h V (t, x))
      ≤ - (nu * cellInt (fun x =>
            incrModEpsWeight eps h V (t, x) * incrLapPair h V (t, x)))
        - cellInt (fun x => incrModEpsWeight eps h V (t, x) * incrStretch h V (t, x))
        + 1 / (2 * nu)
            * cellInt (fun x => incrModEps eps h V (t, x) * (∑ a, (V (t, x) a) ^ 2)) := by
  have hid := modulusEps_viscous_transverse_cell_identity (h := h) heps hV hVper t
  have hbud := modulusEps_caccioppoli_cell_budget (h := h) hnu heps hV hVper hdiv t
  rw [hid]
  linarith

end ClayNS

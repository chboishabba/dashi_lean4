/-
# Physical calibration of a dimensionless lattice gap

A dimensionless lattice spectral gap `δ_k` at spacing `a_k` is not a mass.  The
conversion is

    κ_k = δ_k / a_k      (an inverse correlation length),
    ξ_k = κ_k⁻¹,
    E_k = ħ c κ_k,       m_k = ħ κ_k / c = E_k / c²,

and a continuum SI mass exists only if the scale-setting limit
`κ_k → κ > 0` exists.  This file makes each of those steps a theorem rather
than an identification, and adds the standard lattice extraction of the gap
from a correlator:

* `invCorrLength`, `corrLength`, `gapEnergy`, `gapMass` — the four quantities,
  with `corrLength_mul_invCorrLength`, `gapMass_eq_gapEnergy_div_cSq`,
  `gapMass_eq_hbar_div_c_mul_invCorrLength`, and positivity lemmas;
* `tendsto_gapMass` — if the dimensionless gaps and spacings are such that
  `δ_k / a_k → κ`, then `m_k → ħ κ / c`: the SI mass of the continuum theory is
  the limit, and it is positive exactly when `κ > 0`;
* `effectiveMass`, `effectiveMass_of_pure_exponential` — the effective mass
  read off a Euclidean correlator, `m_eff(t) = (ħ / c a) log (C(t)/C(t+1))`,
  is exactly `ħ κ / c` for a pure exponential correlator `C(t) = A e^{-κ a t}`.

Nothing here claims a value for the Yang–Mills gap: these are the conversion
theorems that any such value must pass through.
-/
import Mathlib

namespace RequestProject.YangMills.RouteS

open Filter Topology

/-- The inverse correlation length `κ = δ / a` of a dimensionless gap `δ` at
lattice spacing `a`. -/
noncomputable def invCorrLength (delta a : ℝ) : ℝ := delta / a

/-- The correlation length `ξ = a / δ`. -/
noncomputable def corrLength (delta a : ℝ) : ℝ := a / delta

/-- The physical gap energy `E = ħ c κ`. -/
noncomputable def gapEnergy (hbar c delta a : ℝ) : ℝ := hbar * c * invCorrLength delta a

/-- The SI mass equivalent `m = ħ κ / c`. -/
noncomputable def gapMass (hbar c delta a : ℝ) : ℝ := hbar * invCorrLength delta a / c

theorem corrLength_mul_invCorrLength {delta a : ℝ} (hd : delta ≠ 0) (ha : a ≠ 0) :
    corrLength delta a * invCorrLength delta a = 1 := by
  simp only [corrLength, invCorrLength]
  field_simp

theorem invCorrLength_pos {delta a : ℝ} (hd : 0 < delta) (ha : 0 < a) :
    0 < invCorrLength delta a := div_pos hd ha

/-- `m = E / c²`. -/
theorem gapMass_eq_gapEnergy_div_cSq {hbar c delta a : ℝ} (hc : c ≠ 0) :
    gapMass hbar c delta a = gapEnergy hbar c delta a / c ^ 2 := by
  simp only [gapMass, gapEnergy, invCorrLength]
  field_simp

/-- `m = ħ / (c ξ)`. -/
theorem gapMass_eq_hbar_div_c_mul_corrLength {hbar c delta a : ℝ} (hd : delta ≠ 0)
    (ha : a ≠ 0) :
    gapMass hbar c delta a = hbar / (c * corrLength delta a) := by
  simp only [gapMass, invCorrLength, corrLength]
  field_simp

/-- The SI mass is positive exactly when the dimensionless gap is. -/
theorem gapMass_pos {hbar c delta a : ℝ} (hh : 0 < hbar) (hc : 0 < c) (hd : 0 < delta)
    (ha : 0 < a) : 0 < gapMass hbar c delta a :=
  div_pos (mul_pos hh (invCorrLength_pos hd ha)) hc

/-- **Scale setting.**  If the dimensionless gaps and spacings have a positive
limiting ratio `κ`, the SI masses converge to `ħκ/c`. -/
theorem tendsto_gapMass {hbar c kappa : ℝ} {delta a : ℕ → ℝ}
    (h : Tendsto (fun k => invCorrLength (delta k) (a k)) atTop (𝓝 kappa)) :
    Tendsto (fun k => gapMass hbar c (delta k) (a k)) atTop (𝓝 (hbar * kappa / c)) := by
  simpa [gapMass] using ((tendsto_const_nhds.mul h).div_const c)

theorem gapMass_limit_pos {hbar c kappa : ℝ} (hh : 0 < hbar) (hc : 0 < c) (hk : 0 < kappa) :
    0 < hbar * kappa / c := div_pos (mul_pos hh hk) hc

/-! ## Reading the gap off a Euclidean correlator -/

/-- The effective mass at lattice separation `t`, extracted from a Euclidean
correlator `C` at spacing `a`: `m_eff(t) = (ħ / (c a)) log (C(t)/C(t+1))`. -/
noncomputable def effectiveMass (hbar c a : ℝ) (C : ℕ → ℝ) (t : ℕ) : ℝ :=
  hbar / (c * a) * Real.log (C t / C (t + 1))

/-- For a pure exponential correlator `C(t) = A e^{-κ a t}` with `A > 0`, the
effective mass is exactly the SI mass `ħκ/c` at every separation. -/
theorem effectiveMass_of_pure_exponential {hbar c a A kappa : ℝ} (hA : 0 < A) (ha : a ≠ 0)
    (hc : c ≠ 0) (t : ℕ) :
    effectiveMass hbar c a (fun s => A * Real.exp (-(kappa * a * s))) t = hbar * kappa / c := by
  simp only [effectiveMass]
  rw [mul_div_mul_left _ _ (ne_of_gt hA), ← Real.exp_sub, Real.log_exp]
  push_cast
  field_simp
  ring

end RequestProject.YangMills.RouteS

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.RouteS

#print axioms gapMass_eq_gapEnergy_div_cSq
#print axioms tendsto_gapMass
#print axioms effectiveMass_of_pure_exponential

end Audit

/-
# The localized level-set (Caccioppoli) inequality for the increment density

`IncrementConvexSubsolution.lean` gives the pointwise subsolution property of
`β(q)`, `q = ½|δ_h u|²`, and `IncrementLevelSetEnergy.lean` integrates it over
the whole periodic cell — where both structural terms disappear for free.  The
De Giorgi iteration needs the *localized* version instead: the same inequality
against a nonnegative, time-independent cutoff `Φ`, with every `Φ`-derivative
displayed, so that the energy on a smaller cylinder is controlled by the energy
on a larger one.

This file proves it.  With

`F_β = Φ·β(q)·u(·+h) − ν(Φ∇β(q) − β(q)∇Φ)`

the localized inequality is

`∂_t(Φ β(q)) + div F_β
   ≤ ∇Φ·(β(q)·u(·+h)) + ν β(q) ΔΦ + Φ·β'(q)·(source)`.

Three structural facts make it work and are exactly what the iteration
consumes: the transporting field `u(·+h)` is divergence free (so the drift
costs only `∇Φ`), the second-order terms combine into `ΦΔβ(q) − β(q)ΔΦ` with
the cross terms cancelling, and the pressure never appears alone — it sits
inside the `β'(q)`-weighted source, where the gauge freedom proved in
`KarmanHowarthPressureGauge.lean` applies.

## What is proved here

* `ClayNS.incrBetaLocFlux` — the localized level-set flux `F_β`.
* `ClayNS.increment_localized_level_set_inequality` — the inequality above,
  valid for every smooth convex `β` and every nonnegative time-independent
  cutoff.
* `ClayNS.increment_localized_level_set_strain` — the potential form: with an
  entrywise strain bound `K` and `β' ≥ 0`, the stretching part of the source is
  at most `6K·β'(q)·q`, so the localized inequality is that of a linear
  parabolic operator with potential coefficient.
* `ClayNS.incr_pressure_weighted_divergence`,
  `ClayNS.incr_pressure_localized_split` — the `C_a` structure: the pressure
  source is a divergence plus pairings with `∇Φ` and with `β''(q)∇q` only.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.IncrementLevelSetEnergy

open scoped BigOperators

noncomputable section

namespace ClayNS

/-- The localized level-set flux `Φ·β(q)·u(·+h) − ν(Φ∇β(q) − β(q)∇Φ)`. -/
def incrBetaLocFlux (nu : ℝ) (beta : ℝ → ℝ) (h : E3) (V : STime → E3) (Phi : STime → ℝ) :
    STime → E3 :=
  fun z => (Phi z * beta (incrQuad h V z)) • shift h V z
    - nu • (Phi z • grad (fun w => beta (incrQuad h V w)) z
        - beta (incrQuad h V z) • grad Phi z)

/-- **The localized level-set energy inequality.**  For `ν ≥ 0`, a smooth convex
`β` and a nonnegative time-independent cutoff `Φ`,

`∂_t(Φβ(q)) + div(Φβ(q)u(·+h) − ν(Φ∇β(q) − β(q)∇Φ))
   ≤ ∇Φ·(β(q)u(·+h)) + νβ(q)ΔΦ + Φβ'(q)·(source)`.

Every term on the right is either paid for by a derivative of the cutoff or is
the `β'(q)`-weighted interior source; there is no uncontrolled interior
contribution and no free-standing pressure term. -/
theorem increment_localized_level_set_inequality (nu : ℝ) (hnu : 0 ≤ nu) (V : STime → E3)
    (P Phi : STime → ℝ) (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (hPhiT : ∀ z : STime, dvec (1, 0) Phi z = 0)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    {beta b1 b2 : ℝ → ℝ} (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta)
    (hb1 : ∀ x, HasDerivAt beta (b1 x) x) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hconv : ∀ x, 0 ≤ b2 x) (z : STime) (hPhi0 : 0 ≤ Phi z) :
    dvec (1, 0) (fun w => Phi w * beta (incrQuad h V w)) z
        + divg (incrBetaLocFlux nu beta h V Phi) z
      ≤ (∑ i, dvec (0, ee i) Phi z * (beta (incrQuad h V z) * shift h V z i))
        + nu * beta (incrQuad h V z) * lap Phi z
        + Phi z * (b1 (incrQuad h V z) * incrSource nu h V P z) := by
  set Q : STime → ℝ := incrQuad h V with hQdef
  have hQ : ContDiff ℝ (⊤ : ℕ∞) Q := contDiff_incrQuad h hV
  set B : STime → ℝ := fun w => beta (Q w) with hBdef
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := hbeta.comp hQ
  have hshift : ContDiff ℝ (⊤ : ℕ∞) (shift h V) := contDiff_shift h hV
  have hgB : ContDiff ℝ (⊤ : ℕ∞) (fun w => grad B w) := contDiff_grad hB
  have hgPhi : ContDiff ℝ (⊤ : ℕ∞) (fun w => grad Phi w) := contDiff_grad hPhi
  have hPhiB : ContDiff ℝ (⊤ : ℕ∞) (fun w => Phi w * B w) := hPhi.mul hB
  -- the pointwise subsolution property
  have hsub := increment_convex_subsolution nu hnu V P h hV hP hmom hb1 hb2 hconv z
  -- the time derivative of the localized density
  have htime : dvec (1, 0) (fun w => Phi w * B w) z = Phi z * dvec (1, 0) B z := by
    rw [dvec_mul Phi B z ((differentiable_of_contDiffTop hPhi) z)
      ((differentiable_of_contDiffTop hB) z) (1, 0), hPhiT z]
    ring
  -- the three divergences
  have hd1 : divg (fun w => (Phi w * B w) • shift h V w) z
      = ∑ i, (dvec (0, ee i) Phi z * B z + Phi z * dvec (0, ee i) B z) * shift h V z i := by
    rw [divg_smul (fun w => Phi w * B w) (shift h V) hPhiB hshift z,
      shift_incompressible h hdiv z, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dvec_mul Phi B z ((differentiable_of_contDiffTop hPhi) z)
      ((differentiable_of_contDiffTop hB) z) (0, ee i)]
  have hd2 : divg (fun w => Phi w • grad B w) z
      = (∑ i, dvec (0, ee i) Phi z * dvec (0, ee i) B z) + Phi z * lap B z := by
    rw [divg_smul Phi (fun w => grad B w) hPhi hgB z, divg_grad B hB z]
    simp
  have hd3 : divg (fun w => B w • grad Phi w) z
      = (∑ i, dvec (0, ee i) Phi z * dvec (0, ee i) B z) + B z * lap Phi z := by
    rw [divg_smul B (fun w => grad Phi w) hB hgPhi z, divg_grad Phi hPhi z]
    simp only [grad_coord]
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hd4 : divg (incrBetaLocFlux nu beta h V Phi) z
      = divg (fun w => (Phi w * B w) • shift h V w) z
        - nu * (divg (fun w => Phi w • grad B w) z - divg (fun w => B w • grad Phi w) z) := by
    have hinner : ContDiff ℝ (⊤ : ℕ∞)
        (fun w => Phi w • grad B w - B w • grad Phi w) :=
      (hPhi.smul hgB).sub (hB.smul hgPhi)
    have hfun : incrBetaLocFlux nu beta h V Phi = fun w => (Phi w * B w) • shift h V w
        - nu • (Phi w • grad B w - B w • grad Phi w) := rfl
    rw [hfun,
      divg_sub (fun w => (Phi w * B w) • shift h V w)
        (fun w => nu • (Phi w • grad B w - B w • grad Phi w))
        (hPhiB.smul hshift) (hinner.const_smul nu) z,
      divg_cmul nu (fun w => Phi w • grad B w - B w • grad Phi w) hinner z,
      divg_sub (fun w => Phi w • grad B w) (fun w => B w • grad Phi w)
        (hPhi.smul hgB) (hB.smul hgPhi) z]
  -- multiply the subsolution inequality by the (nonnegative) cutoff
  have hmul : Phi z * (dvec (1, 0) B z + ∑ j, shift h V z j * dvec (0, ee j) B z)
      ≤ Phi z * (nu * lap B z + b1 (Q z) * incrSource nu h V P z) := by
    refine mul_le_mul_of_nonneg_left ?_ hPhi0
    have hs : incrSource nu h V P z = - incrStretch h V z
        - (∑ a, incrComp h V a z * dvec (0, ee a) (incrPres h P) z)
        - nu * incrDissip h V z := rfl
    rw [hs]
    exact hsub
  -- reorganise the drift sum
  have hdrift : (∑ i, (dvec (0, ee i) Phi z * B z + Phi z * dvec (0, ee i) B z)
        * shift h V z i)
      = (∑ i, dvec (0, ee i) Phi z * (B z * shift h V z i))
        + Phi z * ∑ j, shift h V z j * dvec (0, ee j) B z := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [htime, hd4, hd1, hd2, hd3, hdrift]
  linarith [hmul]

/-- **Potential form of the localized level-set inequality.**  With an entrywise
bound `K` on `∇u` at the point and `β' ≥ 0`, the stretching part of the source
is at most `6K·q`, so the localized inequality is that of a linear parabolic
operator with potential coefficient `6K` — the shape a De Giorgi iteration
consumes once a local strain bound is available. -/
theorem increment_localized_level_set_strain (nu : ℝ) (hnu : 0 ≤ nu) (V : STime → E3)
    (P Phi : STime → ℝ) (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (hPhiT : ∀ z : STime, dvec (1, 0) Phi z = 0)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    {beta b1 b2 : ℝ → ℝ} (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta)
    (hb1 : ∀ x, HasDerivAt beta (b1 x) x) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hconv : ∀ x, 0 ≤ b2 x) (hmono : ∀ x, 0 ≤ b1 x) {K : ℝ} (z : STime) (hPhi0 : 0 ≤ Phi z)
    (hK : ∀ i a : Fin 3, |dvec (0, ee i) (fun w => V w a) z| ≤ K) :
    dvec (1, 0) (fun w => Phi w * beta (incrQuad h V w)) z
        + divg (incrBetaLocFlux nu beta h V Phi) z
      ≤ (∑ i, dvec (0, ee i) Phi z * (beta (incrQuad h V z) * shift h V z i))
        + nu * beta (incrQuad h V z) * lap Phi z
        + Phi z * (b1 (incrQuad h V z) * (6 * K * incrQuad h V z
            - (∑ a, incrComp h V a z * dvec (0, ee a) (incrPres h P) z)
            - nu * incrDissip h V z)) := by
  have hbase := increment_localized_level_set_inequality nu hnu V P Phi h hV hP hPhi hPhiT
    hdiv hmom hbeta hb1 hb2 hconv z hPhi0
  have hstr : |incrStretch h V z| ≤ 3 * K * ∑ a, incrComp h V a z * incrComp h V a z :=
    incrStretch_abs_le h V z K hK
  have hquad : incrQuad h V z = (1 / 2 : ℝ) * ∑ a, incrComp h V a z * incrComp h V a z := rfl
  have hle : - incrStretch h V z ≤ 6 * K * incrQuad h V z := by
    have := abs_le.mp hstr
    rw [hquad]
    linarith [this.1]
  have hsrc : incrSource nu h V P z = - incrStretch h V z
      - (∑ a, incrComp h V a z * dvec (0, ee a) (incrPres h P) z)
      - nu * incrDissip h V z := rfl
  have hmul1 : b1 (incrQuad h V z) * incrSource nu h V P z
      ≤ b1 (incrQuad h V z) * (6 * K * incrQuad h V z
          - (∑ a, incrComp h V a z * dvec (0, ee a) (incrPres h P) z)
          - nu * incrDissip h V z) := by
    rw [hsrc]
    exact mul_le_mul_of_nonneg_left (by linarith) (hmono _)
  have hmul2 := mul_le_mul_of_nonneg_left hmul1 hPhi0
  linarith [hbase, hmul2]

/-! ## `C_a`: where the pressure can appear

The pressure enters the localized inequality only through the source term
`β'(q)·δ_h u·∇δ_h p`.  Because the increment is divergence free, that term is a
*divergence* up to derivatives falling on the weight `W = Φ·β'(q)`.  Writing it
out shows that after integration the pressure is only ever paired with `∇Φ` and
with `β''(q)∇q` — never with `q` itself.  The first pairing is exactly where the
gauge freedom `δ_h p ↦ δ_h p − c` of `KarmanHowarthPressureGauge.lean` applies
(so only the pressure *oscillation* on the support of `∇Φ` matters), and the
second is paired with a gradient, i.e. absorbable against the dissipation.
-/

/-- **Weighted pressure cancellation.**  For any smooth weight `W`,

`W·(δ_h u·∇δ_h p) = div(W·δ_h p·δ_h u) − δ_h p·(δ_h u·∇W)`,

using only that the increment is divergence free. -/
lemma incr_pressure_weighted_divergence {V : STime → E3} {P W : STime → ℝ} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hdiv : ∀ z : STime, divg V z = 0) (z : STime) :
    W z * (∑ a, incrComp h V a z * dvec (0, ee a) (incrPres h P) z)
      = divg (fun w => (W w * incrPres h P w) • incrVec h V w) z
        - incrPres h P z * ∑ a, incrComp h V a z * dvec (0, ee a) W z := by
  have hWP : ContDiff ℝ (⊤ : ℕ∞) (fun w => W w * incrPres h P w) :=
    hW.mul (contDiff_incrPres h hP)
  have hbase := pressure_work_divergence (incrVec h V) (fun w => W w * incrPres h P w)
    (contDiff_incrVec h hV) hWP (divg_incrVec h hV hdiv) z
  have hexp : ∀ a : Fin 3,
      incrVec h V z a * dvec (0, ee a) (fun w => W w * incrPres h P w) z
        = dvec (0, ee a) W z * (incrComp h V a z * incrPres h P z)
          + W z * (incrComp h V a z * dvec (0, ee a) (incrPres h P) z) := by
    intro a
    rw [dvec_mul W (incrPres h P) z ((differentiable_of_contDiffTop hW) z)
      ((differentiable_of_contDiffTop (contDiff_incrPres h hP)) z) (0, ee a), incrVec_coord]
    ring
  rw [hbase, Finset.sum_congr rfl (fun a _ => hexp a), Finset.sum_add_distrib,
    ← Finset.mul_sum]
  have hswap : (∑ a, dvec (0, ee a) W z * (incrComp h V a z * incrPres h P z))
      = incrPres h P z * ∑ a, incrComp h V a z * dvec (0, ee a) W z := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hswap]
  ring

/-- **The gauge-fixed pressure structure of the localized level-set
inequality.**  With the weight `W = Φ·β'(q)` the pressure source splits into a
divergence and two pairings: one against `∇Φ` (the cutoff annulus, where the
pressure gauge freedom lets one subtract a local constant) and one against
`β''(q)∇q` (a gradient, absorbable against the dissipation).  The pressure is
never paired with `q` itself. -/
theorem incr_pressure_localized_split {V : STime → E3} {P Phi : STime → ℝ} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    {b1 b2 : ℝ → ℝ} (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1)
    (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hdiv : ∀ z : STime, divg V z = 0) (z : STime) :
    Phi z * (b1 (incrQuad h V z)
        * ∑ a, incrComp h V a z * dvec (0, ee a) (incrPres h P) z)
      = divg (fun w => ((Phi w * b1 (incrQuad h V w)) * incrPres h P w) • incrVec h V w) z
        - incrPres h P z * ∑ a, incrComp h V a z
            * (dvec (0, ee a) Phi z * b1 (incrQuad h V z)
              + Phi z * (b2 (incrQuad h V z) * dvec (0, ee a) (incrQuad h V) z)) := by
  have hQ : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  have hb1q : ContDiff ℝ (⊤ : ℕ∞) (fun w => b1 (incrQuad h V w)) := hb1c.comp hQ
  have hW : ContDiff ℝ (⊤ : ℕ∞) (fun w => Phi w * b1 (incrQuad h V w)) := hPhi.mul hb1q
  have hbase := incr_pressure_weighted_divergence (W := fun w => Phi w * b1 (incrQuad h V w))
    h hV hP hW hdiv z
  have hdW : ∀ a : Fin 3, dvec (0, ee a) (fun w => Phi w * b1 (incrQuad h V w)) z
      = dvec (0, ee a) Phi z * b1 (incrQuad h V z)
        + Phi z * (b2 (incrQuad h V z) * dvec (0, ee a) (incrQuad h V) z) := by
    intro a
    rw [dvec_mul Phi (fun w => b1 (incrQuad h V w)) z
      ((differentiable_of_contDiffTop hPhi) z)
      ((differentiable_of_contDiffTop hb1q) z) (0, ee a),
      dvec_comp_scalar hQ hb2 (0, ee a) z]
  simp only [hdW] at hbase
  rw [← mul_assoc]
  exact hbase


end ClayNS

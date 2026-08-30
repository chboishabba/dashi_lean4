/-
# Convex compositions of the increment energy are subsolutions

`IncrementLocalEnergy.lean` proves the exact local energy identity for the
increment energy density `q = ½|δ_h u|²`,

`∂_t q + div(q·u(·+h) + δ_h p·δ_h u) = ν(Δq − |∇δ_h u|²) − δ_h u·(δ_h u·∇)u`,

equivalently, in transport form (both the advective and the pressure terms are
divergences of divergence-free vector fields),

`∂_t q + u(·+h)·∇q = νΔq − ν|∇δ_h u|² − δ_h u·(δ_h u·∇)u − δ_h u·∇δ_h p`.

The De Giorgi programme (`C_localDG`) needs the **level-set truncations** of `q`
to inherit this structure.  The truncations `(q−k)_+` are not smooth, but every
smooth convex nondecreasing `β` is an admissible surrogate, and this file proves
that `β(q)` is a subsolution of the same operator, uniformly in `β`:

`∂_t β(q) + u(·+h)·∇β(q) ≤ νΔβ(q) + β'(q)·(source)`,

the loss being exactly the good term `−νβ''(q)|∇q|² ≤ 0` produced by convexity.
This is the pointwise, PDE-level half of the level-set energy inequality `C_b`.

## What is proved here

* `ClayNS.dvec_comp_scalar` — the chain rule in the development's directional
  derivative calculus: `∂_a β(Q) = β'(Q)·∂_a Q`.
* `ClayNS.lap_comp_scalar` — the second-order chain rule:
  `Δβ(Q) = β'(Q)·ΔQ + β''(Q)·|∇Q|²`.
* `ClayNS.increment_convex_subsolution` — for `ν ≥ 0` and any smooth convex
  `β` (`β'' ≥ 0`), the composed density `β(q)` satisfies

  `∂_t β(q) + u(·+h)·∇β(q) ≤ ν Δβ(q)
        + β'(q)·(−δ_h u·(δ_h u·∇)u − δ_h u·∇δ_h p − ν|∇δ_h u|²)`.

  No sign is imposed on `β'`, so the statement covers both the truncation
  family and its reflections.
* `ClayNS.increment_convex_subsolution_strain` — the *potential form*: if the
  entries of `∇u` are bounded by `K` on the region of interest and `β' ≥ 0`,
  the stretching source is dominated by `6K·q`, so

  `∂_t β(q) + u(·+h)·∇β(q) ≤ νΔβ(q) + β'(q)·(6K q − δ_h u·∇δ_h p − ν|∇δ_h u|²)`,

  i.e. the increment equation is a linear parabolic inequality with a potential
  coefficient once a local strain bound is available.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.IncrementLocalEnergy

open scoped BigOperators

noncomputable section

namespace ClayNS

/-! ## Chain rules in the directional-derivative calculus -/

/-- **Chain rule.**  `∂_a β(Q) = β'(Q)·∂_a Q`. -/
lemma dvec_comp_scalar {Q : STime → ℝ} (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    {beta b1 : ℝ → ℝ} (hb1 : ∀ x, HasDerivAt beta (b1 x) x) (a : STime) (z : STime) :
    dvec a (fun w => beta (Q w)) z = b1 (Q z) * dvec a Q z := by
  have hQd : DifferentiableAt ℝ Q z := (differentiable_of_contDiffTop hQ) z
  have h : HasFDerivAt (fun w => beta (Q w)) (b1 (Q z) • fderiv ℝ Q z) z :=
    (hb1 (Q z)).comp_hasFDerivAt z hQd.hasFDerivAt
  show (fderiv ℝ (fun w => beta (Q w)) z) a = _
  rw [h.fderiv]
  simp [dvec]

/-- Differentiability of a smooth scalar function composed with a smooth
spacetime function. -/
lemma differentiableAt_comp_scalar {Q : STime → ℝ} (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    {beta b1 : ℝ → ℝ} (hb1 : ∀ x, HasDerivAt beta (b1 x) x) (z : STime) :
    DifferentiableAt ℝ (fun w => beta (Q w)) z := by
  have hQd : DifferentiableAt ℝ Q z := (differentiable_of_contDiffTop hQ) z
  exact ((hb1 (Q z)).comp_hasFDerivAt z hQd.hasFDerivAt).differentiableAt

/-- **Second-order chain rule.**  `Δβ(Q) = β'(Q)·ΔQ + β''(Q)·|∇Q|²`. -/
lemma lap_comp_scalar {Q : STime → ℝ} (hQ : ContDiff ℝ (⊤ : ℕ∞) Q)
    {beta b1 b2 : ℝ → ℝ} (hb1 : ∀ x, HasDerivAt beta (b1 x) x)
    (hb2 : ∀ x, HasDerivAt b1 (b2 x) x) (z : STime) :
    lap (fun w => beta (Q w)) z
      = b1 (Q z) * lap Q z
        + b2 (Q z) * ∑ k, dvec (0, ee k) Q z * dvec (0, ee k) Q z := by
  have hfun : ∀ k : Fin 3,
      (fun w => dvec (0, ee k) (fun w' => beta (Q w')) w)
        = fun w => b1 (Q w) * dvec (0, ee k) Q w :=
    fun k => funext fun w => dvec_comp_scalar hQ hb1 (0, ee k) w
  have hstep : ∀ k : Fin 3,
      dvec (0, ee k) (fun w => dvec (0, ee k) (fun w' => beta (Q w')) w) z
        = b2 (Q z) * (dvec (0, ee k) Q z * dvec (0, ee k) Q z)
          + b1 (Q z) * dvec (0, ee k) (dvec (0, ee k) Q) z := by
    intro k
    rw [hfun k]
    have hb1Q : DifferentiableAt ℝ (fun w => b1 (Q w)) z :=
      differentiableAt_comp_scalar hQ hb2 z
    have hdQ : DifferentiableAt ℝ (dvec (0, ee k) Q) z :=
      (differentiable_of_contDiffTop (contDiff_dvec Q hQ (0, ee k))) z
    rw [dvec_mul (fun w => b1 (Q w)) (dvec (0, ee k) Q) z hb1Q hdQ (0, ee k),
      dvec_comp_scalar hQ hb2 (0, ee k) z]
    ring
  have hlap : lap (fun w => beta (Q w)) z
      = ∑ k, dvec (0, ee k) (fun w => dvec (0, ee k) (fun w' => beta (Q w')) w) z := rfl
  have hlapQ : lap Q z = ∑ k, dvec (0, ee k) (dvec (0, ee k) Q) z := rfl
  rw [hlap, Finset.sum_congr rfl (fun k _ => hstep k), Finset.sum_add_distrib, hlapQ,
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-! ## The subsolution property -/

/-- **Convex compositions of the increment energy are subsolutions.**  For
`ν ≥ 0` and a smooth convex `β`, the density `β(q)`, `q = ½|δ_h u|²`, satisfies

`∂_t β(q) + u(·+h)·∇β(q) ≤ νΔβ(q)
      + β'(q)·(−stretching − δ_h u·∇δ_h p − ν|∇δ_h u|²)`.

The only inequality used is `−νβ''(q)|∇q|² ≤ 0`, i.e. exactly convexity; every
other step is the exact increment identity. -/
theorem increment_convex_subsolution (nu : ℝ) (hnu : 0 ≤ nu) (V : STime → E3)
    (P : STime → ℝ) (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    {beta b1 b2 : ℝ → ℝ} (hb1 : ∀ x, HasDerivAt beta (b1 x) x)
    (hb2 : ∀ x, HasDerivAt b1 (b2 x) x) (hconv : ∀ x, 0 ≤ b2 x) (z : STime) :
    dvec (1, 0) (fun w => beta (incrQuad h V w)) z
        + ∑ j, shift h V z j * dvec (0, ee j) (fun w => beta (incrQuad h V w)) z
      ≤ nu * lap (fun w => beta (incrQuad h V w)) z
        + b1 (incrQuad h V z) * (- incrStretch h V z
            - (∑ a, incrComp h V a z * dvec (0, ee a) (incrPres h P) z)
            - nu * incrDissip h V z) := by
  set Q : STime → ℝ := incrQuad h V with hQdef
  have hQ : ContDiff ℝ (⊤ : ℕ∞) Q := contDiff_incrQuad h hV
  -- the exact transported identity
  have hid := increment_quadratic_identity nu V P h hV hP hmom z
  have hQsrc : (∑ a, incrComp h V a z *
        (-(∑ j, incrComp h V j z * dvec (0, ee j) (fun w => V w a) z)
          - dvec (0, ee a) (incrPres h P) z))
      = - incrStretch h V z
        - ∑ a, incrComp h V a z * dvec (0, ee a) (incrPres h P) z := by
    rw [incrStretch, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hQsrc] at hid
  -- the chain rules
  have hLHS : dvec (1, 0) (fun w => beta (Q w)) z
      + ∑ j, shift h V z j * dvec (0, ee j) (fun w => beta (Q w)) z
      = b1 (Q z) * (dvec (1, 0) Q z + ∑ j, shift h V z j * dvec (0, ee j) Q z) := by
    have hsum : ∑ j, shift h V z j * dvec (0, ee j) (fun w => beta (Q w)) z
        = b1 (Q z) * ∑ j, shift h V z j * dvec (0, ee j) Q z := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        rw [dvec_comp_scalar hQ hb1 (0, ee j) z]; ring
    rw [dvec_comp_scalar hQ hb1 (1, 0) z, hsum, mul_add]
  have hlap := lap_comp_scalar hQ hb1 hb2 z
  -- the convexity loss
  have hG : 0 ≤ ∑ k, dvec (0, ee k) Q z * dvec (0, ee k) Q z :=
    Finset.sum_nonneg fun k _ => mul_self_nonneg _
  have hloss : 0 ≤ nu * (b2 (Q z) * ∑ k, dvec (0, ee k) Q z * dvec (0, ee k) Q z) :=
    mul_nonneg hnu (mul_nonneg (hconv _) hG)
  rw [hLHS, hlap, hid]
  nlinarith [hloss]

/-- **Potential form.**  With an entrywise bound `K` on `∇u` at the point and
`β' ≥ 0`, the stretching source is dominated by `6K·q`, so the increment
inequality becomes a linear parabolic inequality with a potential coefficient. -/
theorem increment_convex_subsolution_strain (nu : ℝ) (hnu : 0 ≤ nu) (V : STime → E3)
    (P : STime → ℝ) (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    {beta b1 b2 : ℝ → ℝ} (hb1 : ∀ x, HasDerivAt beta (b1 x) x)
    (hb2 : ∀ x, HasDerivAt b1 (b2 x) x) (hconv : ∀ x, 0 ≤ b2 x) (hmono : ∀ x, 0 ≤ b1 x)
    {K : ℝ} (z : STime)
    (hK : ∀ i a : Fin 3, |dvec (0, ee i) (fun w => V w a) z| ≤ K) :
    dvec (1, 0) (fun w => beta (incrQuad h V w)) z
        + ∑ j, shift h V z j * dvec (0, ee j) (fun w => beta (incrQuad h V w)) z
      ≤ nu * lap (fun w => beta (incrQuad h V w)) z
        + b1 (incrQuad h V z) * (6 * K * incrQuad h V z
            - (∑ a, incrComp h V a z * dvec (0, ee a) (incrPres h P) z)
            - nu * incrDissip h V z) := by
  have hbase := increment_convex_subsolution nu hnu V P h hV hP hmom hb1 hb2 hconv z
  have hstr : |incrStretch h V z| ≤ 3 * K * ∑ a, incrComp h V a z * incrComp h V a z :=
    incrStretch_abs_le h V z K hK
  have hquad : incrQuad h V z = (1 / 2 : ℝ) * ∑ a, incrComp h V a z * incrComp h V a z := rfl
  have hle : - incrStretch h V z ≤ 6 * K * incrQuad h V z := by
    have := abs_le.mp hstr
    rw [hquad]
    linarith [this.1]
  have hmul := mul_le_mul_of_nonneg_left
    (by linarith : - incrStretch h V z
        - (∑ a, incrComp h V a z * dvec (0, ee a) (incrPres h P) z)
        - nu * incrDissip h V z
      ≤ 6 * K * incrQuad h V z
        - (∑ a, incrComp h V a z * dvec (0, ee a) (incrPres h P) z)
        - nu * incrDissip h V z)
    (hmono (incrQuad h V z))
  linarith [hbase, hmul]

end ClayNS

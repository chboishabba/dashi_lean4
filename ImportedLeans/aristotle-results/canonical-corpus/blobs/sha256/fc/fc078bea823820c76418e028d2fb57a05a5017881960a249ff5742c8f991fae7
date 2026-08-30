/-
# The adjoint-weighted localized increment identity

The static-cutoff Caccioppoli identity for the increment density
`q = ½|δ_h u|²` carries three separate localization terms,

  `∂_tΦ·β(q)`,   `u(·+h)·∇Φ·β(q)`,   `νΔΦ·β(q)`,

each of which has to be estimated by hand.  They cancel **as one package** if
the weight is not an arbitrary cutoff but a solution of the backward adjoint
transport–diffusion equation of the increment,

  `−∂_tΦ − u(x+h,t)·∇_xΦ − νΔ_xΦ = 0`.                                (Adj)

This file proves that, exactly:

* `ClayNS.increment_convex_identity` — the **sharp** (equality) form of the
  convex-composition identity.  `increment_convex_subsolution` throws away the
  good term `−νβ''(q)|∇q|²`; the De Giorgi budget needs it, so here it is kept:

  `∂_tβ(q) + u(·+h)·∇β(q) = νΔβ(q) − νβ''(q)|∇q|² + β'(q)·source`.

* `ClayNS.adjoint_localized_increment_identity` — **`AdjointLocalizedIncrementIdentity`**.
  For a weight satisfying (Adj) and any smooth `β`,

  `∂_t(Φβ(q)) + div(Φβ(q)u(·+h) − ν(Φ∇β(q) − β(q)∇Φ))
      = −νΦβ''(q)|∇q|² + Φβ'(q)·source`,

  with the *entire* ordinary transport/localization bill gone: no `∂_tΦ`, no
  `∇Φ·u(·+h)`, no `ΔΦ` term survives.  The right-hand side is exactly the
  dissipation package plus the (stretching + pressure) source.

* `ClayNS.adjoint_localized_increment_budget` — the same statement rearranged
  as the localized Caccioppoli budget: the two good terms `νΦβ''(q)|∇q|²` and
  `νΦβ'(q)|∇δ_hu|²` on the left, the stretching and the pressure work on the
  right.

* `ClayNS.static_cutoff_localization_bill` — for comparison, the same identity
  for an arbitrary weight, exhibiting the localization bill
  `β(q)·(∂_tΦ + u(·+h)·∇Φ + νΔΦ)` that (Adj) annihilates.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.IncrementLocalizedLevelSet

open scoped BigOperators

noncomputable section

namespace ClayNS

/-! ## The sharp convex-composition identity -/

/-- **The sharp convex-composition identity** (no inequality taken):

`∂_tβ(q) + u(·+h)·∇β(q) = νΔβ(q) − νβ''(q)|∇q|² + β'(q)·source`,

`q = ½|δ_hu|²`, `source = −stretching − δ_hu·∇δ_hp − ν|∇δ_hu|²`.  The term
`−νβ''(q)|∇q|²` is the one `increment_convex_subsolution` discards; the
Caccioppoli budget of the De Giorgi iteration consumes it. -/
theorem increment_convex_identity (nu : ℝ) (V : STime → E3) (P : STime → ℝ) (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    {beta b1 b2 : ℝ → ℝ} (hb1 : ∀ x, HasDerivAt beta (b1 x) x)
    (hb2 : ∀ x, HasDerivAt b1 (b2 x) x) (z : STime) :
    dvec (1, 0) (fun w => beta (incrQuad h V w)) z
        + ∑ j, shift h V z j * dvec (0, ee j) (fun w => beta (incrQuad h V w)) z
      = nu * lap (fun w => beta (incrQuad h V w)) z
        - nu * (b2 (incrQuad h V z)
            * ∑ k, dvec (0, ee k) (incrQuad h V) z * dvec (0, ee k) (incrQuad h V) z)
        + b1 (incrQuad h V z) * incrSource nu h V P z := by
  set Q : STime → ℝ := incrQuad h V with hQdef
  have hQ : ContDiff ℝ (⊤ : ℕ∞) Q := contDiff_incrQuad h hV
  have hid := increment_quadratic_identity nu V P h hV hP hmom z
  have hQsrc : (∑ a, incrComp h V a z *
        (-(∑ j, incrComp h V j z * dvec (0, ee j) (fun w => V w a) z)
          - dvec (0, ee a) (incrPres h P) z))
      = - incrStretch h V z
        - ∑ a, incrComp h V a z * dvec (0, ee a) (incrPres h P) z := by
    rw [incrStretch, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hQsrc] at hid
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
  have hsrc : incrSource nu h V P z = - incrStretch h V z
      - (∑ a, incrComp h V a z * dvec (0, ee a) (incrPres h P) z)
      - nu * incrDissip h V z := rfl
  rw [hLHS, hlap, hid, hsrc]
  ring

/-! ## The localization bill of an arbitrary weight -/

/-- **The localization bill.**  For an arbitrary smooth weight `Φ` (in
particular time dependent), the localized identity reads

`∂_t(Φβ(q)) + div(Φβ(q)u(·+h) − ν(Φ∇β(q) − β(q)∇Φ))
   = β(q)·(∂_tΦ + u(·+h)·∇Φ + νΔΦ) − νΦβ''(q)|∇q|² + Φβ'(q)·source`.

The first bracket is exactly the (negative of the) adjoint operator applied to
`Φ`: it is the whole transport/localization bill. -/
theorem static_cutoff_localization_bill (nu : ℝ) (V : STime → E3) (P Phi : STime → ℝ)
    (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    {beta b1 b2 : ℝ → ℝ} (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta)
    (hb1 : ∀ x, HasDerivAt beta (b1 x) x) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (z : STime) :
    dvec (1, 0) (fun w => Phi w * beta (incrQuad h V w)) z
        + divg (incrBetaLocFlux nu beta h V Phi) z
      = beta (incrQuad h V z)
          * (dvec (1, 0) Phi z + (∑ j, shift h V z j * dvec (0, ee j) Phi z)
              + nu * lap Phi z)
        - nu * Phi z * (b2 (incrQuad h V z)
            * ∑ k, dvec (0, ee k) (incrQuad h V) z * dvec (0, ee k) (incrQuad h V) z)
        + Phi z * (b1 (incrQuad h V z) * incrSource nu h V P z) := by
  set Q : STime → ℝ := incrQuad h V with hQdef
  have hQ : ContDiff ℝ (⊤ : ℕ∞) Q := contDiff_incrQuad h hV
  set B : STime → ℝ := fun w => beta (Q w) with hBdef
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := hbeta.comp hQ
  have hshift : ContDiff ℝ (⊤ : ℕ∞) (shift h V) := contDiff_shift h hV
  have hgB : ContDiff ℝ (⊤ : ℕ∞) (fun w => grad B w) := contDiff_grad hB
  have hgPhi : ContDiff ℝ (⊤ : ℕ∞) (fun w => grad Phi w) := contDiff_grad hPhi
  have hPhiB : ContDiff ℝ (⊤ : ℕ∞) (fun w => Phi w * B w) := hPhi.mul hB
  -- the sharp pointwise identity
  have hsharp := increment_convex_identity nu V P h hV hP hmom hb1 hb2 z
  -- the time derivative of the localized density
  have htime : dvec (1, 0) (fun w => Phi w * B w) z
      = dvec (1, 0) Phi z * B z + Phi z * dvec (1, 0) B z :=
    dvec_mul Phi B z ((differentiable_of_contDiffTop hPhi) z)
      ((differentiable_of_contDiffTop hB) z) (1, 0)
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
  have hdrift : (∑ i, (dvec (0, ee i) Phi z * B z + Phi z * dvec (0, ee i) B z)
        * shift h V z i)
      = B z * (∑ j, shift h V z j * dvec (0, ee j) Phi z)
        + Phi z * ∑ j, shift h V z j * dvec (0, ee j) B z := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [htime, hd4, hd1, hd2, hd3, hdrift]
  linear_combination Phi z * hsharp

/-! ## The adjoint weight -/

/-- The adjoint (backward transport–diffusion) operator of the increment
equation, applied to a weight `Φ`:  `−∂_tΦ − u(·+h)·∇Φ − νΔΦ`. -/
def adjointOp (nu : ℝ) (h : E3) (V : STime → E3) (Phi : STime → ℝ) : STime → ℝ :=
  fun z => - dvec (1, 0) Phi z - (∑ j, shift h V z j * dvec (0, ee j) Phi z) - nu * lap Phi z

/-- **`AdjointLocalizedIncrementIdentity`.**  If the weight solves the backward
adjoint transport–diffusion equation `−∂_tΦ − u(·+h)·∇Φ − νΔΦ = 0`, then the
localized increment identity has **no** localization terms at all:

`∂_t(Φβ(q)) + div(Φβ(q)u(·+h) − ν(Φ∇β(q) − β(q)∇Φ)) = −νΦβ''(q)|∇q|² + Φβ'(q)·source`.

Every cutoff error (`∂_tΦ`, `u(·+h)·∇Φ`, `νΔΦ`) has cancelled as one package. -/
theorem adjoint_localized_increment_identity (nu : ℝ) (V : STime → E3) (P Phi : STime → ℝ)
    (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (hadj : ∀ z : STime, adjointOp nu h V Phi z = 0)
    {beta b1 b2 : ℝ → ℝ} (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta)
    (hb1 : ∀ x, HasDerivAt beta (b1 x) x) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (z : STime) :
    dvec (1, 0) (fun w => Phi w * beta (incrQuad h V w)) z
        + divg (incrBetaLocFlux nu beta h V Phi) z
      = - nu * Phi z * (b2 (incrQuad h V z)
            * ∑ k, dvec (0, ee k) (incrQuad h V) z * dvec (0, ee k) (incrQuad h V) z)
        + Phi z * (b1 (incrQuad h V z) * incrSource nu h V P z) := by
  have hbill := static_cutoff_localization_bill nu V P Phi h hV hP hPhi hdiv hmom hbeta hb1 hb2 z
  have hzero : dvec (1, 0) Phi z + (∑ j, shift h V z j * dvec (0, ee j) Phi z)
      + nu * lap Phi z = 0 := by
    have := hadj z
    simp only [adjointOp] at this
    linarith
  rw [hbill, hzero]
  ring

/-- **An approximate adjoint weight costs exactly its residual.**  For an
arbitrary smooth weight, the deviation from the exact adjoint-localized
identity is `β(q)` times the adjoint residual `−(∂_tΦ + u(·+h)·∇Φ + νΔΦ)`.  So
a compactly supported weight which solves (Adj) up to a residual `R` supported
in the cutoff annulus pays only `|β(q)|·R` there — nothing else. -/
theorem adjoint_localized_increment_residual (nu : ℝ) (V : STime → E3) (P Phi : STime → ℝ)
    (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    {beta b1 b2 : ℝ → ℝ} (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta)
    (hb1 : ∀ x, HasDerivAt beta (b1 x) x) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (z : STime) {R : ℝ} (hR : |adjointOp nu h V Phi z| ≤ R) :
    |dvec (1, 0) (fun w => Phi w * beta (incrQuad h V w)) z
        + divg (incrBetaLocFlux nu beta h V Phi) z
        - (- nu * Phi z * (b2 (incrQuad h V z)
              * ∑ k, dvec (0, ee k) (incrQuad h V) z * dvec (0, ee k) (incrQuad h V) z)
            + Phi z * (b1 (incrQuad h V z) * incrSource nu h V P z))|
      ≤ |beta (incrQuad h V z)| * R := by
  have hbill := static_cutoff_localization_bill nu V P Phi h hV hP hPhi hdiv hmom hbeta hb1 hb2 z
  have hres : dvec (1, 0) Phi z + (∑ j, shift h V z j * dvec (0, ee j) Phi z) + nu * lap Phi z
      = - adjointOp nu h V Phi z := by
    simp only [adjointOp]; ring
  rw [hbill, hres]
  have : beta (incrQuad h V z) * -adjointOp nu h V Phi z
      - nu * Phi z * (b2 (incrQuad h V z)
          * ∑ k, dvec (0, ee k) (incrQuad h V) z * dvec (0, ee k) (incrQuad h V) z)
      + Phi z * (b1 (incrQuad h V z) * incrSource nu h V P z)
      - (- nu * Phi z * (b2 (incrQuad h V z)
            * ∑ k, dvec (0, ee k) (incrQuad h V) z * dvec (0, ee k) (incrQuad h V) z)
          + Phi z * (b1 (incrQuad h V z) * incrSource nu h V P z))
      = beta (incrQuad h V z) * -adjointOp nu h V Phi z := by ring
  rw [this, abs_mul, abs_neg]
  exact mul_le_mul_of_nonneg_left hR (abs_nonneg _)

/-- **The adjoint-weighted Caccioppoli budget.**  Rearranged: with a
nonnegative weight and a convex nondecreasing entropy, both good terms appear
with the right sign on the left, and the only sources on the right are the
stretching and the pressure work — no cutoff error of any kind. -/
theorem adjoint_localized_increment_budget (nu : ℝ) (V : STime → E3) (P Phi : STime → ℝ)
    (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (hadj : ∀ z : STime, adjointOp nu h V Phi z = 0)
    {beta b1 b2 : ℝ → ℝ} (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta)
    (hb1 : ∀ x, HasDerivAt beta (b1 x) x) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (z : STime) :
    dvec (1, 0) (fun w => Phi w * beta (incrQuad h V w)) z
        + divg (incrBetaLocFlux nu beta h V Phi) z
        + nu * Phi z * (b2 (incrQuad h V z)
            * ∑ k, dvec (0, ee k) (incrQuad h V) z * dvec (0, ee k) (incrQuad h V) z)
        + nu * Phi z * (b1 (incrQuad h V z) * incrDissip h V z)
      = Phi z * (b1 (incrQuad h V z)
          * (- incrStretch h V z
              - ∑ a, incrComp h V a z * dvec (0, ee a) (incrPres h P) z)) := by
  have hid := adjoint_localized_increment_identity nu V P Phi h hV hP hPhi hdiv hmom hadj
    hbeta hb1 hb2 z
  have hsrc : incrSource nu h V P z = - incrStretch h V z
      - (∑ a, incrComp h V a z * dvec (0, ee a) (incrPres h P) z)
      - nu * incrDissip h V z := rfl
  rw [hid, hsrc]
  ring

end ClayNS

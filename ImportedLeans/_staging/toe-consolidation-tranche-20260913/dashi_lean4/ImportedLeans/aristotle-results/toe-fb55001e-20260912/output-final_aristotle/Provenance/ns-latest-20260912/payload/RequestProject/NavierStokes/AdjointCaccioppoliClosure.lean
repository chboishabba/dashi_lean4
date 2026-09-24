/-
# The adjoint-weighted Caccioppoli budget with a *linear* source

This file assembles the two halves of the C-side experiment into one
inequality.

* `AdjointLocalizedIncrement.lean` produced the localized identity whose
  **entire** cutoff bill is annihilated by the backward adjoint weight
  `−∂_tΦ − u(·+h)·∇Φ − νΔΦ = 0`, leaving only the two good terms and the
  (stretching + pressure-work) source.

* `IncrementStretchingTransfer.lean` showed that the stretching source
  `Φβ'(q)·wᵀS(U)w` — the term the route asked to *inspect* rather than bound by
  `|S||w|²` — admits a further divergence/commutator representation whose
  non-divergence remainder is controlled using only amplitude bounds
  `|u_a| ≤ A`, `|w_a| ≤ B`, with no `∇u` bound and no critical `L^{5/2}` norm of
  the strain.

Integrating over the periodicity cell kills both divergences and gives
`ClayNS.adjoint_caccioppoli_linear_budget`:

```
∫ ∂_t(Φβ(q)) + (1−η)ν ∫ Φβ''(q)|∇q|² + (ν/2) ∫ Φβ'(q)|∇δ_hu|²
    ≤ C₁ ∫ Φβ''(q) + (C₂ + 3BG_p) ∫ Φβ'(q) + C₃ ∫ β'(q),
```

`C₁ = 27A²B⁴/(4ην)`, `C₂ = 9A²B²/(2ν)`, `C₃ = 9AB²G`, where `G` bounds `|∇Φ|`
entrywise and `G_p` bounds `|∇δ_hp|` entrywise.

For the quadratic De Giorgi entropy `β_k(q) = v_k²` (`β' = 2v_k`,
`β'' = 2·1_{A_k}`) every right-hand term is **linear** in the truncation data —
a level-set measure plus a first power of `v_k`.  That is the shape the De
Giorgi engine consumes (`linear_budget_superlinear_recurrence`), and it is
strictly better than the *sublinear* `Y_k^{3/5}` that the critical Hölder
triple `1/(5/2)+1/(10/3)+1/(10/3)=1` yields from a generic critical `L^{5/2}`
strain bound (`increment_stretching_critical_estimate`,
`sublinear_recurrence_no_decay`).

**What is still not proved.**  This is a conditional budget, not `C*`.  Its
hypotheses include the existence of a weight `Φ ≥ 0` solving (Adj) exactly with
`|∇Φ| ≤ G` — a backward-caloric-transport kernel, which is *not* constructed
here — and it says nothing about the smallness needed to launch the recurrence,
nor about the scale-invariance requirement recorded in `RescalingAudit.lean`.
The Clay target is **not** proved.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.IncrementStretchingTransfer
import RequestProject.NavierStokes.KarmanHowarth

open scoped BigOperators

noncomputable section

namespace ClayNS

/-! ## Regularity and periodicity of the localized level-set flux -/

lemma contDiff_incrBetaLocFlux (nu : ℝ) {beta : ℝ → ℝ} (h : E3) {V : STime → E3}
    {Phi : STime → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta) :
    ContDiff ℝ (⊤ : ℕ∞) (incrBetaLocFlux nu beta h V Phi) := by
  have hbq : ContDiff ℝ (⊤ : ℕ∞) (fun w => beta (incrQuad h V w)) :=
    hbeta.comp (contDiff_incrQuad h hV)
  exact (hPhi.mul hbq).smul (contDiff_shift h hV) |>.sub
    (((hPhi.smul (contDiff_grad hbq)).sub (hbq.smul (contDiff_grad hPhi))).const_smul nu)

lemma spacePeriodic_incrBetaLocFlux (nu : ℝ) {beta : ℝ → ℝ} (h : E3) {V : STime → E3}
    {Phi : STime → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta)
    (hVper : SpacePeriodic V) (hPhiper : SpacePeriodic Phi) :
    SpacePeriodic (incrBetaLocFlux nu beta h V Phi) := by
  have hbq : ContDiff ℝ (⊤ : ℕ∞) (fun w => beta (incrQuad h V w)) :=
    hbeta.comp (contDiff_incrQuad h hV)
  have hbqper : SpacePeriodic (fun w => beta (incrQuad h V w)) := by
    intro z j
    show beta (incrQuad h V (z.1, z.2 + ee j)) = beta (incrQuad h V z)
    rw [spacePeriodic_incrQuad h hVper z j]
  intro z j
  have hgb : grad (fun w => beta (incrQuad h V w)) (z.1, z.2 + ee j)
      = grad (fun w => beta (incrQuad h V w)) z :=
    spacePeriodic_grad (differentiable_of_contDiffTop hbq) hbqper z j
  have hgPhi : grad Phi (z.1, z.2 + ee j) = grad Phi z :=
    spacePeriodic_grad (differentiable_of_contDiffTop hPhi) hPhiper z j
  show (Phi (z.1, z.2 + ee j) * beta (incrQuad h V (z.1, z.2 + ee j)))
        • shift h V (z.1, z.2 + ee j)
      - nu • (Phi (z.1, z.2 + ee j) • grad (fun w => beta (incrQuad h V w)) (z.1, z.2 + ee j)
          - beta (incrQuad h V (z.1, z.2 + ee j)) • grad Phi (z.1, z.2 + ee j))
    = (Phi z * beta (incrQuad h V z)) • shift h V z
      - nu • (Phi z • grad (fun w => beta (incrQuad h V w)) z
          - beta (incrQuad h V z) • grad Phi z)
  rw [hPhiper z j, spacePeriodic_incrQuad h hVper z j, spacePeriodic_shift h hVper z j,
    hgb, hgPhi]

/-! ## Splitting a cell integral into finitely many pieces -/

lemma cellInt_split5 {f f1 f2 f3 f4 f5 : E3 → ℝ}
    (hf : ∀ x, f x = f1 x + f2 x + f3 x + f4 x + f5 x)
    (h1 : Continuous f1) (h2 : Continuous f2) (h3 : Continuous f3) (h4 : Continuous f4)
    (h5 : Continuous f5) :
    cellInt f = cellInt f1 + cellInt f2 + cellInt f3 + cellInt f4 + cellInt f5 := by
  have s2 : cellInt (fun x => f1 x + f2 x) = cellInt f1 + cellInt f2 := cellInt_add h1 h2
  have s3 : cellInt (fun x => f1 x + f2 x + f3 x)
      = cellInt (fun x => f1 x + f2 x) + cellInt f3 := cellInt_add (h1.add h2) h3
  have s4 : cellInt (fun x => f1 x + f2 x + f3 x + f4 x)
      = cellInt (fun x => f1 x + f2 x + f3 x) + cellInt f4 :=
    cellInt_add ((h1.add h2).add h3) h4
  have s5 : cellInt (fun x => f1 x + f2 x + f3 x + f4 x + f5 x)
      = cellInt (fun x => f1 x + f2 x + f3 x + f4 x) + cellInt f5 :=
    cellInt_add (((h1.add h2).add h3).add h4) h5
  rw [cellInt_congr hf, s5, s4, s3, s2]

lemma cellInt_split6 {f f1 f2 f3 f4 f5 f6 : E3 → ℝ}
    (hf : ∀ x, f x = f1 x + f2 x + f3 x + f4 x + f5 x + f6 x)
    (h1 : Continuous f1) (h2 : Continuous f2) (h3 : Continuous f3) (h4 : Continuous f4)
    (h5 : Continuous f5) (h6 : Continuous f6) :
    cellInt f = cellInt f1 + cellInt f2 + cellInt f3 + cellInt f4 + cellInt f5 + cellInt f6 := by
  have s6 : cellInt (fun x => f1 x + f2 x + f3 x + f4 x + f5 x + f6 x)
      = cellInt (fun x => f1 x + f2 x + f3 x + f4 x + f5 x) + cellInt f6 :=
    cellInt_add ((((h1.add h2).add h3).add h4).add h5) h6
  rw [cellInt_congr hf, s6, cellInt_split5 (fun _ => rfl) h1 h2 h3 h4 h5]

lemma cellInt_zero : cellInt (fun _ : E3 => (0 : ℝ)) = 0 := by simp [cellInt]

/-! ## The closed budget -/

/-- **The adjoint-weighted Caccioppoli budget with a linear source.**

With a nonnegative weight `Φ` solving the backward adjoint transport–diffusion
equation `−∂_tΦ − u(·+h)·∇Φ − νΔΦ = 0` (so the localization bill vanishes
identically), with a nonnegative nondecreasing convex entropy `β`, and with only
*amplitude* bounds `|u_a| ≤ A`, `|δ_hu_a| ≤ B`, `|∂_jΦ| ≤ G`, `|∂_aδ_hp| ≤ G_p`:

`∫ ∂_t(Φβ(q)) + (1−η)ν ∫ Φβ''(q)|∇q|² + (ν/2) ∫ Φβ'(q)|∇δ_hu|²`
`  ≤ 27A²B⁴/(4ην) ∫ Φβ''(q) + (9A²B²/(2ν) + 3BG_p) ∫ Φβ'(q) + 9AB²G ∫ β'(q)`

for every `η > 0`.  No bound on `∇u` and no critical norm of the strain enters;
every source is linear in the truncation data. -/
theorem adjoint_caccioppoli_linear_budget {nu eta A B G Gp : ℝ} (hnu : 0 < nu) (heta : 0 < eta)
    {V : STime → E3} {P Phi : STime → ℝ} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hVper : SpacePeriodic V) (hPhiper : SpacePeriodic Phi)
    {beta b1 b2 : ℝ → ℝ} (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta)
    (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1) (hb2c : ContDiff ℝ (⊤ : ℕ∞) b2)
    (hb1 : ∀ x, HasDerivAt beta (b1 x) x) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (hadj : ∀ z : STime, adjointOp nu h V Phi z = 0)
    (hPhi0 : ∀ z, 0 ≤ Phi z) (hB1 : ∀ x, 0 ≤ b1 x) (hB2 : ∀ x, 0 ≤ b2 x)
    (hA : ∀ (z : STime) (a : Fin 3), |V z a| ≤ A)
    (hB : ∀ (z : STime) (a : Fin 3), |incrComp h V a z| ≤ B)
    (hG : ∀ (z : STime) (j : Fin 3), |dvec (0, ee j) Phi z| ≤ G)
    (hGp : ∀ (z : STime) (a : Fin 3), |dvec (0, ee a) (incrPres h P) z| ≤ Gp)
    (t : ℝ) :
    cellInt (fun x => dvec (1, 0) (fun w => Phi w * beta (incrQuad h V w)) (t, x))
        + (1 - eta) * nu * cellInt (fun x => Phi (t, x) * (b2 (incrQuad h V (t, x))
            * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
                * dvec (0, ee k) (incrQuad h V) (t, x)))
        + nu / 2 * cellInt (fun x =>
            Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x)))
      ≤ 27 * A ^ 2 * B ^ 4 / (4 * eta * nu)
            * cellInt (fun x => Phi (t, x) * b2 (incrQuad h V (t, x)))
        + (9 * A ^ 2 * B ^ 2 / (2 * nu) + 3 * B * Gp)
            * cellInt (fun x => Phi (t, x) * b1 (incrQuad h V (t, x)))
        + 9 * A * B ^ 2 * G * cellInt (fun x => b1 (incrQuad h V (t, x))) := by
  classical
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
      (fun w => ∑ a, incrComp h V a w * dvec (0, ee a) (incrPres h P) w) :=
    ContDiff.sum fun a _ => (contDiff_incrComp h hV a).mul
      (contDiff_dvec _ (contDiff_incrPres h hP) _)
  -- the flux
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
      * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x)) :=
    continuous_slice (hPhi.mul (hb1q.mul hpres)) t
  have cK2 : Continuous fun x : E3 => Phi (t, x) * b2 (incrQuad h V (t, x)) :=
    continuous_slice (hPhi.mul hb2q) t
  have cK1 : Continuous fun x : E3 => Phi (t, x) * b1 (incrQuad h V (t, x)) :=
    continuous_slice (hPhi.mul hb1q) t
  have cK0 : Continuous fun x : E3 => b1 (incrQuad h V (t, x)) := continuous_slice hb1q t
  set IT := cellInt (fun x => dvec (1, 0) (fun w => Phi w * beta (incrQuad h V w)) (t, x)) with hIT
  set J2 := cellInt (fun x => Phi (t, x) * (b2 (incrQuad h V (t, x))
      * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
          * dvec (0, ee k) (incrQuad h V) (t, x))) with hJ2
  set J1 := cellInt (fun x =>
      Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x))) with hJ1
  set ST := cellInt (fun x =>
      Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x))) with hST
  set PW := cellInt (fun x => Phi (t, x) * (b1 (incrQuad h V (t, x))
      * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x))) with hPW
  set K2 := cellInt (fun x => Phi (t, x) * b2 (incrQuad h V (t, x))) with hK2
  set K1 := cellInt (fun x => Phi (t, x) * b1 (incrQuad h V (t, x))) with hK1
  set K0 := cellInt (fun x => b1 (incrQuad h V (t, x))) with hK0
  -- (1) the exact cell-integrated adjoint balance
  have hbal : IT + nu * J2 + nu * J1 + ST + PW = 0 := by
    have hpt : ∀ x : E3,
        dvec (1, 0) (fun w => Phi w * beta (incrQuad h V w)) (t, x)
          + divg F (t, x)
          + nu * (Phi (t, x) * (b2 (incrQuad h V (t, x))
              * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
                  * dvec (0, ee k) (incrQuad h V) (t, x)))
          + nu * (Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x)))
          + Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x))
          + Phi (t, x) * (b1 (incrQuad h V (t, x))
              * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x)) = 0 := by
      intro x
      have := adjoint_localized_increment_budget nu V P Phi h hV hP hPhi hdiv hmom hadj
        hbeta hb1 hb2 (t, x)
      rw [hFdef]; linarith [this]
    have hsplit := cellInt_split6 (f := fun _ : E3 => (0 : ℝ))
      (f1 := fun x : E3 => dvec (1, 0) (fun w => Phi w * beta (incrQuad h V w)) (t, x))
      (f2 := fun x : E3 => divg F (t, x))
      (f3 := fun x : E3 => nu * (Phi (t, x) * (b2 (incrQuad h V (t, x))
          * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
              * dvec (0, ee k) (incrQuad h V) (t, x))))
      (f4 := fun x : E3 => nu * (Phi (t, x)
          * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x))))
      (f5 := fun x : E3 => Phi (t, x)
          * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x)))
      (f6 := fun x : E3 => Phi (t, x) * (b1 (incrQuad h V (t, x))
          * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x)))
      (fun x => (hpt x).symm) cT cF (continuous_const.mul cJ2) (continuous_const.mul cJ1)
      cSt cPw
    have e3 : cellInt (fun x : E3 => nu * (Phi (t, x) * (b2 (incrQuad h V (t, x))
        * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
            * dvec (0, ee k) (incrQuad h V) (t, x)))) = nu * J2 := by
      rw [hJ2]; exact cellInt_const_mul nu _
    have e4 : cellInt (fun x : E3 => nu * (Phi (t, x)
        * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x)))) = nu * J1 := by
      rw [hJ1]; exact cellInt_const_mul nu _
    rw [cellInt_zero, e3, e4, hFzero, ← hIT, ← hST, ← hPW] at hsplit
    linarith [hsplit]
  -- (2) the transferred stretching budget, integrated
  have hstrb : |ST| ≤ eta * nu * J2 + nu / 2 * J1
      + 27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * K2
      + 9 * A ^ 2 * B ^ 2 / (2 * nu) * K1 + 9 * A * B ^ 2 * G * K0 := by
    have hcell := increment_stretching_transfer_cell_budget (nu := nu) (eta := eta) (A := A)
      (B := B) (G := G) hnu heta h hV hPhi hVper hPhiper hb1c hb2c hb2 hdiv hPhi0 hB1 hB2
      hA hB hG t
    have hexp : cellInt (fun x => stretchBudget nu eta A B G h V Phi b1 b2 (t, x))
        = eta * nu * J2 + nu / 2 * J1
          + 27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * K2
          + 9 * A ^ 2 * B ^ 2 / (2 * nu) * K1 + 9 * A * B ^ 2 * G * K0 := by
      have hrw : ∀ x : E3, stretchBudget nu eta A B G h V Phi b1 b2 (t, x)
          = eta * nu * (Phi (t, x) * (b2 (incrQuad h V (t, x))
              * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
                  * dvec (0, ee k) (incrQuad h V) (t, x)))
            + nu / 2 * (Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x)))
            + 27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * (Phi (t, x) * b2 (incrQuad h V (t, x)))
            + 9 * A ^ 2 * B ^ 2 / (2 * nu) * (Phi (t, x) * b1 (incrQuad h V (t, x)))
            + 9 * A * B ^ 2 * G * b1 (incrQuad h V (t, x)) := fun x => rfl
      have hsplit := cellInt_split5
        (f := fun x : E3 => stretchBudget nu eta A B G h V Phi b1 b2 (t, x))
        (f1 := fun x : E3 => eta * nu * (Phi (t, x) * (b2 (incrQuad h V (t, x))
            * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
                * dvec (0, ee k) (incrQuad h V) (t, x))))
        (f2 := fun x : E3 => nu / 2 * (Phi (t, x)
            * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x))))
        (f3 := fun x : E3 => 27 * A ^ 2 * B ^ 4 / (4 * eta * nu)
            * (Phi (t, x) * b2 (incrQuad h V (t, x))))
        (f4 := fun x : E3 => 9 * A ^ 2 * B ^ 2 / (2 * nu)
            * (Phi (t, x) * b1 (incrQuad h V (t, x))))
        (f5 := fun x : E3 => 9 * A * B ^ 2 * G * b1 (incrQuad h V (t, x)))
        hrw (continuous_const.mul cJ2) (continuous_const.mul cJ1) (continuous_const.mul cK2)
        (continuous_const.mul cK1) (continuous_const.mul cK0)
      have e1 : cellInt (fun x : E3 => eta * nu * (Phi (t, x) * (b2 (incrQuad h V (t, x))
          * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
              * dvec (0, ee k) (incrQuad h V) (t, x)))) = eta * nu * J2 := by
        rw [hJ2]; exact cellInt_const_mul _ _
      have e2 : cellInt (fun x : E3 => nu / 2 * (Phi (t, x)
          * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x)))) = nu / 2 * J1 := by
        rw [hJ1]; exact cellInt_const_mul _ _
      have e3 : cellInt (fun x : E3 => 27 * A ^ 2 * B ^ 4 / (4 * eta * nu)
          * (Phi (t, x) * b2 (incrQuad h V (t, x))))
          = 27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * K2 := by
        rw [hK2]; exact cellInt_const_mul _ _
      have e4 : cellInt (fun x : E3 => 9 * A ^ 2 * B ^ 2 / (2 * nu)
          * (Phi (t, x) * b1 (incrQuad h V (t, x))))
          = 9 * A ^ 2 * B ^ 2 / (2 * nu) * K1 := by
        rw [hK1]; exact cellInt_const_mul _ _
      have e5 : cellInt (fun x : E3 => 9 * A * B ^ 2 * G * b1 (incrQuad h V (t, x)))
          = 9 * A * B ^ 2 * G * K0 := by
        rw [hK0]; exact cellInt_const_mul _ _
      rw [e1, e2, e3, e4, e5] at hsplit
      exact hsplit
    rw [hexp] at hcell
    exact hcell
  -- (3) the pressure work is linear in `Φβ'`
  have hpw : -PW ≤ 3 * B * Gp * K1 := by
    have hle : ∀ x : E3, - (3 * B * Gp * (Phi (t, x) * b1 (incrQuad h V (t, x))))
        ≤ Phi (t, x) * (b1 (incrQuad h V (t, x))
            * ∑ a, incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x)) := by
      intro x
      have hbd : |∑ a, incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x)|
          ≤ 3 * (B * Gp) := by
        have := Finset.abs_sum_le_sum_abs
          (fun a : Fin 3 => incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x))
          Finset.univ
        refine this.trans ?_
        have hterm : ∀ a : Fin 3, |incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x)|
            ≤ B * Gp := by
          intro a
          rw [abs_mul]
          exact mul_le_mul (hB _ a) (hGp _ a) (abs_nonneg _)
            ((abs_nonneg _).trans (hB (t, x) a))
        calc ∑ a : Fin 3, |incrComp h V a (t, x) * dvec (0, ee a) (incrPres h P) (t, x)|
            ≤ ∑ _a : Fin 3, B * Gp := Finset.sum_le_sum fun a _ => hterm a
          _ = 3 * (B * Gp) := by simp [Finset.sum_const, nsmul_eq_mul]
      have hw : 0 ≤ Phi (t, x) * b1 (incrQuad h V (t, x)) :=
        mul_nonneg (hPhi0 _) (hB1 _)
      have := (abs_le.mp hbd).1
      nlinarith [hw, this]
    have cneg : Continuous
        (fun x : E3 => -(3 * B * Gp * (Phi (t, x) * b1 (incrQuad h V (t, x))))) :=
      (continuous_const.mul cK1).neg
    have hmono := cellInt_mono cneg cPw hle
    rw [cellInt_neg (fun x : E3 => 3 * B * Gp * (Phi (t, x) * b1 (incrQuad h V (t, x)))),
      cellInt_const_mul] at hmono
    linarith [hmono]
  have hSTle : ST ≥ -(eta * nu * J2 + nu / 2 * J1
      + 27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * K2
      + 9 * A ^ 2 * B ^ 2 / (2 * nu) * K1 + 9 * A * B ^ 2 * G * K0) := (abs_le.mp hstrb).1
  nlinarith [hbal, hSTle, hpw]

end ClayNS

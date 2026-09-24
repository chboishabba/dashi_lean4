/-
# C₄₆–C₄₇: the radial stretching channel cancels for the modulus entropy

`IncrementModulusGram.lean` isolated the transverse geometry.  This file
performs the second half of the experiment: the **exact cancellation of the
radial (marginal) stretching channel** for the modulus entropy.

Starting from the already-proved weighted transfer identity
(`ClayNS.incrStretch_weighted_transfer`)

  `W·δ_hu·(δ_hu·∇)u = div(W(u·δ_hu)δ_hu) − (u·δ_hu)(δ_hu·∇W) − W·u·(δ_hu·∇)δ_hu`,

decomposing `u·(δ_hu·∇)δ_hu` along and transverse to `δ_hu` gives
(`ClayNS.increment_modulus_radial_stretching_split`), for a weight whose value
and gradient at the point are `W = c₁`, `∇W = c₂∇q`,

  `W·δ_hu·(δ_hu·∇)u = div(…) − c₁·u_⊥·d_⊥ − (u·δ_hu)(δ_hu·∇q)·(c₂ + c₁/2q)`,

so the whole radial channel carries the single scalar factor `c₂ + c₁/2q`.

* **C₄₆** (`ClayNS.modulus_entropy_ode`, `ClayNS.modEntropy_hasDerivAt`,
  `ClayNS.modEntropy_deriv_hasDerivAt`) — the modulus entropy
  `β_λ(q) = (√(2q) − λ)_+` satisfies `β_λ'' + β_λ'/(2q) = 0` **exactly on the
  active set** `{|δ_hu| > λ}`, for every truncation level `λ ≥ 0`: subtracting
  the constant `λ` changes no derivative, so the cancellation survives on each
  De Giorgi level set.

* **C₄₇** (`ClayNS.increment_modulus_radial_stretching_cancellation`) — whenever
  the weight satisfies that ODE at the point, the radial channel disappears
  identically and the *only* surviving stretching source is the transverse
  pairing `c₁·u_⊥·d_⊥`, which
  `ClayNS.modulus_transverse_absorption` absorbs into the transverse viscous
  term.  `ClayNS.adjoint_modulus_caccioppoli_pointwise` is the combination: the
  full stretching source, minus a divergence, is bounded by
  `ν(|∇δ_hu|²−|∇|δ_hu||²)/2r + r|u|²/2ν` — one half of the transverse
  dissipation plus a source **linear** in the modulus.

Because `s ↦ (√(2s) − λ)_+` is not smooth at `s = 0`, the globally smooth
weight actually used is the regularization `W_ε = (2q+ε²)^{-1/2}`
(`ClayNS.incrModEpsWeight`), which is `ContDiff` everywhere
(`ClayNS.contDiff_incrModEpsWeight`); its radial factor is not `0` but
`ε²/(2q·r_ε³)` (`ClayNS.incrModEpsWeight_radial_factor`), and that defect tends
to `0` as `ε ↓ 0` at every point where the increment does not vanish
(`ClayNS.incrModEpsWeight_radial_factor_tendsto_zero`).

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.IncrementModulusGram

open scoped BigOperators Topology
open Filter

noncomputable section

namespace ClayNS

/-! ## C₄₆: the modulus entropy and its exact second-order ODE -/

/-- The truncated modulus entropy `β_λ(q) = (√(2q) − λ)_+`. -/
def modEntropy (lam : ℝ) : ℝ → ℝ := fun s => max (Real.sqrt (2 * s) - lam) 0

/-- Its derivative on the active set, `β_λ'(q) = 1/√(2q) = 1/r`. -/
def modEntropyDeriv : ℝ → ℝ := fun s => 1 / Real.sqrt (2 * s)

/-- Its second derivative on the active set, `β_λ''(q) = −(2q)^{-3/2} = −1/r³`. -/
def modEntropySecond : ℝ → ℝ := fun s => -(1 / (2 * s * Real.sqrt (2 * s)))

/-- On the active set `{√(2s) > λ}` the truncation is inactive. -/
lemma modEntropy_active (lam : ℝ) {s : ℝ} (hs : lam ^ 2 / 2 < s) (hlam : 0 ≤ lam) :
    modEntropy lam s = Real.sqrt (2 * s) - lam := by
  have h2 : lam ^ 2 < 2 * s := by linarith
  have hlt : lam < Real.sqrt (2 * s) := by
    have := Real.sqrt_lt_sqrt (by positivity) h2
    rwa [Real.sqrt_sq hlam] at this
  rw [modEntropy, max_eq_left (by linarith : (0:ℝ) ≤ Real.sqrt (2 * s) - lam)]

/-- **C₄₆, first derivative.**  `β_λ'(q) = 1/√(2q)` on the active set — the
truncation level `λ` has disappeared. -/
theorem modEntropy_hasDerivAt {lam s : ℝ} (hlam : 0 ≤ lam) (hs : lam ^ 2 / 2 < s) :
    HasDerivAt (modEntropy lam) (modEntropyDeriv s) s := by
  have hspos : 0 < s := lt_of_le_of_lt (by positivity) hs
  have hbase : HasDerivAt (fun y : ℝ => Real.sqrt (2 * y) - lam) (modEntropyDeriv s) s := by
    simpa [modEntropyDeriv] using (hasDerivAt_sqrt_two_mul hspos).sub_const lam
  refine hbase.congr_of_eventuallyEq ?_
  have hopen : IsOpen {y : ℝ | lam ^ 2 / 2 < y} := isOpen_lt continuous_const continuous_id
  refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hs) ?_
  intro y hy
  exact modEntropy_active lam hy hlam

/-- **C₄₆, second derivative.**  `β_λ''(q) = −(2q)^{-3/2}`. -/
theorem modEntropy_deriv_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt modEntropyDeriv (modEntropySecond s) s := by
  have h2 : (0:ℝ) < 2 * s := by linarith
  have hr : 0 < Real.sqrt (2 * s) := Real.sqrt_pos.2 h2
  have hsq : Real.sqrt (2 * s) ^ 2 = 2 * s := Real.sq_sqrt h2.le
  have hinv := (hasDerivAt_sqrt_two_mul hs).inv (ne_of_gt hr)
  have hform : modEntropyDeriv = fun y : ℝ => (Real.sqrt (2 * y))⁻¹ := by
    funext y; simp [modEntropyDeriv, one_div]
  rw [hform]
  convert hinv using 1
  rw [modEntropySecond, hsq]
  field_simp

/-- **C₄₆ — the exact modulus ODE.**  `β'' + β'/(2q) = 0`: the entropy
`β(q) = √(2q) = |δ_hu|`, and every truncation `(√(2q) − λ)_+` of it, kills the
radial stretching channel identically. -/
theorem modulus_entropy_ode {s : ℝ} (hs : 0 < s) :
    modEntropySecond s + modEntropyDeriv s / (2 * s) = 0 := by
  have h2 : (0:ℝ) < 2 * s := by linarith
  have hr : 0 < Real.sqrt (2 * s) := Real.sqrt_pos.2 h2
  rw [modEntropySecond, modEntropyDeriv]
  field_simp
  ring

/-- **C₄₆, truncation invariance.**  For every level `λ ≥ 0` the derivative data
of `β_λ` on its own active set is the *same* pair `(1/√(2q), −(2q)^{-3/2})`, and
that pair solves the radial ODE.  So the cancellation holds simultaneously on
every De Giorgi level set. -/
theorem modEntropy_level_ode {lam s : ℝ} (hlam : 0 ≤ lam) (hs : lam ^ 2 / 2 < s) :
    HasDerivAt (modEntropy lam) (modEntropyDeriv s) s
      ∧ HasDerivAt modEntropyDeriv (modEntropySecond s) s
      ∧ modEntropySecond s + modEntropyDeriv s / (2 * s) = 0 := by
  have hspos : 0 < s := lt_of_le_of_lt (by positivity) hs
  exact ⟨modEntropy_hasDerivAt hlam hs, modEntropy_deriv_hasDerivAt hspos,
    modulus_entropy_ode hspos⟩

/-! ## C₄₇: the radial channel carries a single scalar factor -/

/-- **The radial/transverse split of the weighted stretching term.**  For any
smooth weight whose value and gradient at `z` are `W = c₁`, `∇W = c₂∇q`, the
weighted stretching density is a divergence, minus the transverse pairing
`c₁u_⊥·d_⊥`, minus the *radial* channel — which carries the single scalar
factor `c₂ + c₁/(2q)`. -/
theorem increment_modulus_radial_stretching_split {h : E3} {V : STime → E3}
    {W : STime → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hdiv : ∀ z : STime, divg V z = 0) {z : STime} (hz : 0 < incrQuad h V z)
    {c1 c2 : ℝ} (hWz : W z = c1)
    (hdW : ∀ j : Fin 3, dvec (0, ee j) W z = c2 * dvec (0, ee j) (incrQuad h V) z) :
    W z * incrStretch h V z
      = divg (fun w => (W w * incrPair h V w) • incrVec h V w) z
        - c1 * incrPerpPair h V z
        - incrPair h V z * (∑ j, incrComp h V j z * dvec (0, ee j) (incrQuad h V) z)
            * (c2 + c1 / (2 * incrQuad h V z)) := by
  have hbase := incrStretch_weighted_transfer (W := W) h hV hW hdiv z
  have hgrad : (∑ j, incrComp h V j z * dvec (0, ee j) W z)
      = c2 * ∑ j, incrComp h V j z * dvec (0, ee j) (incrQuad h V) z := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hdW j]; ring
  have hperp : incrTransfer h V z = incrPerpPair h V z
      + incrPair h V z * (∑ j, incrComp h V j z * dvec (0, ee j) (incrQuad h V) z)
          / (2 * incrQuad h V z) := by
    rw [incrPerpPair]; ring
  rw [hbase, hgrad, hperp, hWz]
  have hq : (2 * incrQuad h V z) ≠ 0 := by positivity
  field_simp
  ring

/-- **The radial/transverse split with an arbitrary normalization `R`.**  The
same algebra as `ClayNS.increment_modulus_radial_stretching_split`, but the
radial direction is normalized by an arbitrary `R ≠ 0` rather than by `2q`.
With `R = |δ_hu|² + ε²` this is the regularized decomposition, which has no
singularity where the increment vanishes. -/
theorem increment_stretching_radial_split_gen {h : E3} {V : STime → E3}
    {W : STime → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hdiv : ∀ z : STime, divg V z = 0) (z : STime) {R c1 c2 : ℝ} (hR : R ≠ 0)
    (hWz : W z = c1)
    (hdW : ∀ j : Fin 3, dvec (0, ee j) W z = c2 * dvec (0, ee j) (incrQuad h V) z) :
    W z * incrStretch h V z
      = divg (fun w => (W w * incrPair h V w) • incrVec h V w) z
        - c1 * (incrTransfer h V z
            - incrPair h V z
              * (∑ j, incrComp h V j z * dvec (0, ee j) (incrQuad h V) z) / R)
        - incrPair h V z * (∑ j, incrComp h V j z * dvec (0, ee j) (incrQuad h V) z)
            * (c2 + c1 / R) := by
  have hbase := incrStretch_weighted_transfer (W := W) h hV hW hdiv z
  have hgrad : (∑ j, incrComp h V j z * dvec (0, ee j) W z)
      = c2 * ∑ j, incrComp h V j z * dvec (0, ee j) (incrQuad h V) z := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hdW j]; ring
  rw [hbase, hgrad, hWz]
  field_simp
  ring

/-- **C₄₇ — the radial stretching cancellation.**  If the weight satisfies the
modulus ODE `c₂ + c₁/(2q) = 0` at the point, the marginal radial channel
cancels *identically* and the only surviving stretching source is the
transverse pairing. -/
theorem increment_modulus_radial_stretching_cancellation {h : E3} {V : STime → E3}
    {W : STime → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hdiv : ∀ z : STime, divg V z = 0) {z : STime} (hz : 0 < incrQuad h V z)
    {c1 c2 : ℝ} (hWz : W z = c1)
    (hdW : ∀ j : Fin 3, dvec (0, ee j) W z = c2 * dvec (0, ee j) (incrQuad h V) z)
    (hODE : c2 + c1 / (2 * incrQuad h V z) = 0) :
    W z * incrStretch h V z
      = divg (fun w => (W w * incrPair h V w) • incrVec h V w) z
        - c1 * incrPerpPair h V z := by
  rw [increment_modulus_radial_stretching_split hV hW hdiv hz hWz hdW, hODE]
  ring

/-- **The pointwise modulus Caccioppoli source.**  With a weight realizing the
modulus entropy (`c₁ = 1/r`, radial ODE satisfied) the entire stretching source,
after removing an exact divergence, is bounded by half the transverse
dissipation plus a term **linear** in the modulus:

`|W·δ_hu·(δ_hu·∇)u − div(…)| ≤ ν(|∇δ_hu|²−|∇|δ_hu||²)/2r + r|u|²/2ν`.

No bound on `∇u`, no critical strain norm, and no level-set exponent `θ`. -/
theorem adjoint_modulus_caccioppoli_pointwise {nu : ℝ} (hnu : 0 < nu) {h : E3}
    {V : STime → E3} {W : STime → ℝ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (hdiv : ∀ z : STime, divg V z = 0)
    {z : STime} (hz : 0 < incrQuad h V z)
    {c2 : ℝ} (hWz : W z = 1 / incrMod h V z)
    (hdW : ∀ j : Fin 3, dvec (0, ee j) W z = c2 * dvec (0, ee j) (incrQuad h V) z)
    (hODE : c2 + (1 / incrMod h V z) / (2 * incrQuad h V z) = 0) :
    |W z * incrStretch h V z
        - divg (fun w => (W w * incrPair h V w) • incrVec h V w) z|
      ≤ nu / 2 * (incrTransDissip h V z / incrMod h V z)
        + incrMod h V z * (∑ a, (V z a) ^ 2) / (2 * nu) := by
  have hcanc := increment_modulus_radial_stretching_cancellation hV hW hdiv hz hWz hdW hODE
  have habs := modulus_transverse_absorption hnu hV hz
  have hr : 0 < incrMod h V z := incrMod_pos hz
  have hrw : W z * incrStretch h V z
      - divg (fun w => (W w * incrPair h V w) • incrVec h V w) z
      = -((1 / incrMod h V z) * incrPerpPair h V z) := by
    rw [hcanc]; ring
  rw [hrw, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / incrMod h V z)]
  calc 1 / incrMod h V z * |incrPerpPair h V z|
      = |incrPerpPair h V z| / incrMod h V z := by ring
    _ ≤ _ := habs

/-! ## The modulus weight exists: the cancellation hypotheses are satisfiable -/

/-- **Non-vacuity of C₄₇.**  At every point where the increment does not vanish
there is a globally smooth weight realizing the modulus entropy to first order:
value `1/r`, gradient `−r^{-3}∇q`, hence radial ODE `c₂ + c₁/(2q) = 0`.  (The
first-order Taylor polynomial of `s ↦ (2s)^{-1/2}` at `q(z)` does it; the exact
entropy itself is singular only where the increment vanishes.) -/
theorem exists_modulus_entropy_weight {h : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) {z : STime} (hz : 0 < incrQuad h V z) :
    ∃ (W : STime → ℝ) (c2 : ℝ), ContDiff ℝ (⊤ : ℕ∞) W ∧ W z = 1 / incrMod h V z
      ∧ (∀ j : Fin 3, dvec (0, ee j) W z = c2 * dvec (0, ee j) (incrQuad h V) z)
      ∧ c2 + (1 / incrMod h V z) / (2 * incrQuad h V z) = 0 := by
  have hQ : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  have hr : 0 < incrMod h V z := incrMod_pos hz
  have hrne : incrMod h V z ≠ 0 := ne_of_gt hr
  have hqne : incrQuad h V z ≠ 0 := ne_of_gt hz
  refine ⟨fun w => 1 / incrMod h V z
      + (-(1 / (2 * incrQuad h V z * incrMod h V z)))
        * (incrQuad h V w - incrQuad h V z),
    -(1 / (2 * incrQuad h V z * incrMod h V z)), ?_, ?_, ?_, ?_⟩
  · exact contDiff_const.add (contDiff_const.mul (hQ.sub contDiff_const))
  · simp
  · intro j
    have hderiv : ∀ x : ℝ, HasDerivAt (fun s : ℝ => 1 / incrMod h V z
        + (-(1 / (2 * incrQuad h V z * incrMod h V z))) * (s - incrQuad h V z))
        (-(1 / (2 * incrQuad h V z * incrMod h V z))) x := by
      intro x
      simpa using ((((hasDerivAt_id x).sub_const (incrQuad h V z)).const_mul
        (-(1 / (2 * incrQuad h V z * incrMod h V z)))).const_add (1 / incrMod h V z))
    exact dvec_comp_scalar hQ hderiv (0, ee j) z
  · field_simp
    ring

/-- **C₄₇, unconditional pointwise form.**  At every point where the increment
does not vanish there *is* a smooth modulus-entropy weight, and for it the whole
stretching source, after removing an exact divergence, is bounded by half the
transverse dissipation plus a source linear in the modulus. -/
theorem modulus_caccioppoli_source_bound {nu : ℝ} (hnu : 0 < nu) {h : E3}
    {V : STime → E3} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hdiv : ∀ z : STime, divg V z = 0)
    {z : STime} (hz : 0 < incrQuad h V z) :
    ∃ W : STime → ℝ, ContDiff ℝ (⊤ : ℕ∞) W ∧ W z = 1 / incrMod h V z ∧
      |W z * incrStretch h V z
          - divg (fun w => (W w * incrPair h V w) • incrVec h V w) z|
        ≤ nu / 2 * (incrTransDissip h V z / incrMod h V z)
          + incrMod h V z * (∑ a, (V z a) ^ 2) / (2 * nu) := by
  obtain ⟨W, c2, hW, hWz, hdW, hODE⟩ := exists_modulus_entropy_weight hV hz
  exact ⟨W, hW, hWz,
    adjoint_modulus_caccioppoli_pointwise hnu hV hW hdiv hz hWz hdW hODE⟩

/-! ## A globally smooth weight realizing the modulus entropy up to `ε` -/

/-- The regularized modulus weight `W_ε = (2q + ε²)^{-1/2} = 1/r_ε`. -/
def incrModEpsWeight (eps : ℝ) (h : E3) (V : STime → E3) : STime → ℝ :=
  fun w => (Real.sqrt (2 * incrQuad h V w + eps ^ 2))⁻¹

lemma incrModEps_pos {eps : ℝ} (heps : 0 < eps) (h : E3) (V : STime → E3) (w : STime) :
    0 < 2 * incrQuad h V w + eps ^ 2 := by
  have := incrQuad_nonneg h V w
  positivity

/-- The regularized weight is smooth everywhere — unlike the exact modulus
entropy, which is singular where the increment vanishes. -/
theorem contDiff_incrModEpsWeight {eps : ℝ} (heps : 0 < eps) {h : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) : ContDiff ℝ (⊤ : ℕ∞) (incrModEpsWeight eps h V) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  have hg : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => 2 * incrQuad h V w + eps ^ 2) z :=
    (((contDiff_const.mul (contDiff_incrQuad h hV)).add contDiff_const)).contDiffAt
  have hgpos : 0 < 2 * incrQuad h V z + eps ^ 2 := incrModEps_pos heps h V z
  have hsqrt : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℝ => Real.sqrt y)
      ((fun w => 2 * incrQuad h V w + eps ^ 2) z) := Real.contDiffAt_sqrt (ne_of_gt hgpos)
  have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => Real.sqrt (2 * incrQuad h V w + eps ^ 2)) z := hsqrt.comp z hg
  exact hcomp.inv (ne_of_gt (Real.sqrt_pos.2 hgpos))

/-- The scalar derivative behind the regularized weight. -/
lemma hasDerivAt_invSqrtAff {eps s : ℝ} (hpos : 0 < 2 * s + eps ^ 2) :
    HasDerivAt (fun y : ℝ => (Real.sqrt (2 * y + eps ^ 2))⁻¹)
      (-(((2 * s + eps ^ 2) * Real.sqrt (2 * s + eps ^ 2))⁻¹)) s := by
  have haff : HasDerivAt (fun y : ℝ => 2 * y + eps ^ 2) 2 s := by
    simpa using ((hasDerivAt_id s).const_mul (2:ℝ)).add_const (eps ^ 2)
  have hsqrt := (Real.hasDerivAt_sqrt (ne_of_gt hpos)).comp s haff
  have hr : 0 < Real.sqrt (2 * s + eps ^ 2) := Real.sqrt_pos.2 hpos
  have hsq : Real.sqrt (2 * s + eps ^ 2) ^ 2 = 2 * s + eps ^ 2 := Real.sq_sqrt hpos.le
  have hinv := hsqrt.inv (ne_of_gt hr)
  simp only [Function.comp_def, Pi.inv_def] at hinv
  convert hinv using 1
  rw [hsq]
  field_simp

/-- Value of the regularized weight: `c₁ = 1/r_ε`. -/
lemma incrModEpsWeight_value (eps : ℝ) (h : E3) (V : STime → E3) (z : STime) :
    incrModEpsWeight eps h V z = (Real.sqrt (2 * incrQuad h V z + eps ^ 2))⁻¹ := rfl

/-- Gradient of the regularized weight: `∇W_ε = c₂∇q` with `c₂ = −1/r_ε³`. -/
lemma incrModEpsWeight_grad {eps : ℝ} (heps : 0 < eps) {h : E3} {V : STime → E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (z : STime) (a : STime) :
    dvec a (incrModEpsWeight eps h V) z
      = (-(((2 * incrQuad h V z + eps ^ 2)
            * Real.sqrt (2 * incrQuad h V z + eps ^ 2))⁻¹)) * dvec a (incrQuad h V) z := by
  have hQ : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  exact dvec_comp_scalar_at hQ (hasDerivAt_invSqrtAff (incrModEps_pos heps h V z)) a

/-- **The radial factor of the regularized weight is exactly `ε²/(2q·r_ε³)`.**
It vanishes in the limit `ε ↓ 0`: the exact modulus entropy is the `ε = 0`
member of the family, and the ODE `β'' + β'/(2q) = 0` is its defining
property. -/
theorem incrModEpsWeight_radial_factor {eps : ℝ} (heps : 0 < eps) {h : E3}
    {V : STime → E3} {z : STime} (hz : 0 < incrQuad h V z) :
    (-(((2 * incrQuad h V z + eps ^ 2)
          * Real.sqrt (2 * incrQuad h V z + eps ^ 2))⁻¹))
        + (Real.sqrt (2 * incrQuad h V z + eps ^ 2))⁻¹ / (2 * incrQuad h V z)
      = eps ^ 2 / (2 * incrQuad h V z * ((2 * incrQuad h V z + eps ^ 2)
          * Real.sqrt (2 * incrQuad h V z + eps ^ 2))) := by
  have hpos : 0 < 2 * incrQuad h V z + eps ^ 2 := by nlinarith
  have hr : 0 < Real.sqrt (2 * incrQuad h V z + eps ^ 2) := Real.sqrt_pos.2 hpos
  have hq : (0:ℝ) < 2 * incrQuad h V z := by linarith
  field_simp
  ring

/-- The radial defect of the regularized weight tends to `0` with `ε`. -/
theorem incrModEpsWeight_radial_factor_tendsto_zero {h : E3} {V : STime → E3} {z : STime}
    (hz : 0 < incrQuad h V z) :
    Tendsto (fun eps : ℝ => eps ^ 2 / (2 * incrQuad h V z
        * ((2 * incrQuad h V z + eps ^ 2)
          * Real.sqrt (2 * incrQuad h V z + eps ^ 2)))) (𝓝 0) (𝓝 0) := by
  have hq : (0:ℝ) < 2 * incrQuad h V z := by linarith
  have hr0 : 0 < Real.sqrt (2 * incrQuad h V z) := Real.sqrt_pos.2 hq
  have hcont : ContinuousAt (fun eps : ℝ => eps ^ 2 / (2 * incrQuad h V z
      * ((2 * incrQuad h V z + eps ^ 2)
        * Real.sqrt (2 * incrQuad h V z + eps ^ 2)))) 0 := by
    have hden : ContinuousAt (fun eps : ℝ => 2 * incrQuad h V z
        * ((2 * incrQuad h V z + eps ^ 2)
          * Real.sqrt (2 * incrQuad h V z + eps ^ 2))) 0 := by
      fun_prop
    refine ContinuousAt.div (by fun_prop) hden ?_
    simp only [ne_eq]
    have : (0:ℝ) < 2 * incrQuad h V z * ((2 * incrQuad h V z + 0 ^ 2)
        * Real.sqrt (2 * incrQuad h V z + 0 ^ 2)) := by
      have : (0:ℝ) < 2 * incrQuad h V z + 0 ^ 2 := by simpa using hq
      have hs : 0 < Real.sqrt (2 * incrQuad h V z + 0 ^ 2) := Real.sqrt_pos.2 this
      positivity
    exact ne_of_gt this
  have := hcont.tendsto
  simpa using this

end ClayNS

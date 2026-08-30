/-
# The truncated stretching term admits a divergence/commutator representation

This is the experiment the route asked for: *derive the weighted truncation
identity and inspect the `wᵀS(U)w` term before bounding it*, rather than
replacing it immediately by `|S||w|²`.

The answer is affirmative.  Because the increment `w = δ_hu` is divergence
free, the stretching density transfers the derivative off `u`
(`incrStretch_divergence_transfer`), and that transfer survives multiplication
by the De Giorgi weight `W = Φ·β'(q)`:

  `W·wᵀS(U)w = div( W(u·w)w ) − (u·w)(w·∇W) − W·∑_{a,j}u_a w_j ∂_j w_a`,
  `∇W = β'(q)∇Φ + Φβ''(q)∇q`.                                          (T)

`ClayNS.incrStretch_weighted_transfer` and
`ClayNS.incrStretch_localized_split` are (T).

Consequences, all proved here (`ClayNS.increment_stretching_transfer_budget`):
with amplitude bounds `|u_a| ≤ A`, `|w_a| ≤ B` — which the KNSŠ normalization
`‖U‖_∞ ≤ 1` supplies with `A = 1`, `B = 2`, with **no** bound on `∇u` and **no**
critical norm of the strain — the non-divergence remainder of (T) is bounded by

  `ην·Φβ''(q)|∇q|² + (ν/2)·Φβ'(q)|∇w|²`      (absorbed by the two good terms
                                              of the adjoint-weighted budget)
  `+ C₁·Φβ''(q) + C₂·Φβ'(q) + C₃·β'(q)|∇Φ|`,

with `C₁ = 27A²B⁴/(4ην)`, `C₂ = 9A²B²/(2ν)`, `C₃ = 9AB²`.

The point is the *shape* of the remainder.  For the quadratic entropy
`β_k(q) = v_k²` one has `β' = 2v_k` and `β'' = 2·1_{A_k}`, so the remainder is

  `C₁·|A_k| + C₂·∫v_k + C₃·∫_{∇Φ≠0} v_k`,

i.e. **linear** in the truncation data (a level-set measure plus a first power
of `v_k`) — not the *sublinear* `Y_k^{3/5}` produced by a generic critical
`L^{5/2}` bound on the strain (`sublinear_recurrence_no_decay`).  A linear
Caccioppoli budget is exactly what the De Giorgi engine of
`DeGiorgiRecurrence.lean` consumes: `linear_budget_superlinear_recurrence`
records that step abstractly, `K ≲ Y + m` with Chebyshev `m ≲ 4ⁿY` gives the
superlinear recurrence `Y_{n+1} ≲ bⁿ Y_n^{7/5}`.

What is *not* claimed: nothing here supplies the weight `Φ` (see
`AdjointLocalizedIncrement.lean` for the identity it must satisfy), the
space-time integration of the divergence terms, or the pressure bound (that is
`IncrementPressureAbsorption.lean`).

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.AdjointLocalizedIncrement

open scoped BigOperators

noncomputable section

namespace ClayNS

/-! ## Elementary estimates -/

/-- A three-term sum is bounded by three times the entrywise bound. -/
lemma abs_sum3_le {x : Fin 3 → ℝ} {c : ℝ} (h : ∀ i, |x i| ≤ c) : |∑ i, x i| ≤ 3 * c := by
  calc |∑ i, x i| ≤ ∑ i, |x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, c := Finset.sum_le_sum fun i _ => h i
    _ = 3 * c := by simp [Finset.sum_const, nsmul_eq_mul]

/-- Entrywise bound for a three-term bilinear sum. -/
lemma abs_sum3_mul_le {x y : Fin 3 → ℝ} {cx cy : ℝ} (hx : ∀ i, |x i| ≤ cx)
    (hy : ∀ i, |y i| ≤ cy) : |∑ i, x i * y i| ≤ 3 * (cx * cy) := by
  refine abs_sum3_le fun i => ?_
  rw [abs_mul]
  have h0 : (0:ℝ) ≤ cy := le_trans (abs_nonneg _) (hy i)
  exact mul_le_mul (hx i) (hy i) (abs_nonneg _) (le_trans (abs_nonneg _) (hx i))

/-- Young's inequality summed over the three coordinates:
`c·∑|g_a| ≤ λ∑g_a² + 3c²/(4λ)`. -/
lemma young_sum3 {c lam : ℝ} (hlam : 0 < lam) (g : Fin 3 → ℝ) :
    c * ∑ a, |g a| ≤ lam * ∑ a, g a * g a + 3 * c ^ 2 / (4 * lam) := by
  have hterm : ∀ a : Fin 3, c * |g a| ≤ lam * (g a * g a) + c ^ 2 / (4 * lam) := by
    intro a
    have habs : |g a| * |g a| = g a * g a := abs_mul_abs_self (g a)
    have hexp : lam * (|g a| * |g a|) + c ^ 2 / (4 * lam) - c * |g a|
        = (2 * lam * |g a| - c) ^ 2 / (4 * lam) := by
      field_simp
      ring
    have hnn : 0 ≤ (2 * lam * |g a| - c) ^ 2 / (4 * lam) := by positivity
    rw [habs] at hexp
    linarith [hexp ▸ hnn]
  calc c * ∑ a, |g a| = ∑ a, c * |g a| := by rw [Finset.mul_sum]
    _ ≤ ∑ a : Fin 3, (lam * (g a * g a) + c ^ 2 / (4 * lam)) :=
        Finset.sum_le_sum fun a _ => hterm a
    _ = lam * ∑ a, g a * g a + 3 * c ^ 2 / (4 * lam) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [Finset.sum_const, nsmul_eq_mul]
        ring

/-! ## The weighted divergence transfer (T) -/

/-- Product rule for a weighted flux:
`div((W f)G) = f·(G·∇W) + W·div(fG)`. -/
lemma divg_weighted_smul {W f : STime → ℝ} {G : STime → E3} (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (z : STime) :
    divg (fun w => (W w * f w) • G w) z
      = f z * (∑ j, G z j * dvec (0, ee j) W z) + W z * divg (fun w => f w • G w) z := by
  have hd : ∀ i : Fin 3, dvec (0, ee i) (fun w => W w * f w) z
      = dvec (0, ee i) W z * f z + W z * dvec (0, ee i) f z := fun i =>
    dvec_mul W f z ((differentiable_of_contDiffTop hW) z)
      ((differentiable_of_contDiffTop hf) z) (0, ee i)
  rw [divg_smul (fun w => W w * f w) G (hW.mul hf) hG z, divg_smul f G hf hG z]
  have hsum : ∑ i, dvec (0, ee i) (fun w => W w * f w) z * G z i
      = f z * (∑ j, G z j * dvec (0, ee j) W z) + W z * ∑ i, dvec (0, ee i) f z * G z i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hd i]; ring
  rw [hsum]
  ring

/-- **(T), weighted form.**  For any smooth weight `W`,

`W·δ_hu·(δ_hu·∇)u = div(W(u·δ_hu)δ_hu) − (u·δ_hu)(δ_hu·∇W) − W·∑ u_a δ_hu_j ∂_j δ_hu_a`.

Only the divergence-freeness of `u` and of the increment is used; no bound on
`∇u` appears anywhere. -/
theorem incrStretch_weighted_transfer {V : STime → E3} {W : STime → ℝ} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hdiv : ∀ z : STime, divg V z = 0) (z : STime) :
    W z * incrStretch h V z
      = divg (fun w => (W w * incrPair h V w) • incrVec h V w) z
        - incrPair h V z * (∑ j, incrComp h V j z * dvec (0, ee j) W z)
        - W z * incrTransfer h V z := by
  have hbase := incrStretch_divergence_transfer (V := V) h hV hdiv z
  have hprod := divg_weighted_smul (W := W) (f := incrPair h V) (G := incrVec h V)
    hW (contDiff_incrPair h hV) (contDiff_incrVec h hV) z
  simp only [incrVec_coord] at hprod
  rw [hbase]
  rw [hprod]
  ring

/-- **(T) with the De Giorgi weight `W = Φ·β'(q)`**, the gradient of the weight
expanded: `∇W = β'(q)∇Φ + Φβ''(q)∇q`.  So the stretching source is a
divergence, a pairing against `∇Φ` (the cutoff annulus), a pairing against
`β''(q)∇q` (absorbable against the good term of the adjoint-weighted budget)
and the transferred commutator. -/
theorem incrStretch_localized_split {V : STime → E3} {Phi : STime → ℝ} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    {b1 b2 : ℝ → ℝ} (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hdiv : ∀ z : STime, divg V z = 0) (z : STime) :
    Phi z * (b1 (incrQuad h V z) * incrStretch h V z)
      = divg (fun w => ((Phi w * b1 (incrQuad h V w)) * incrPair h V w) • incrVec h V w) z
        - incrPair h V z * ∑ j, incrComp h V j z
            * (dvec (0, ee j) Phi z * b1 (incrQuad h V z)
              + Phi z * (b2 (incrQuad h V z) * dvec (0, ee j) (incrQuad h V) z))
        - (Phi z * b1 (incrQuad h V z)) * incrTransfer h V z := by
  have hQ : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  have hb1q : ContDiff ℝ (⊤ : ℕ∞) (fun w => b1 (incrQuad h V w)) := hb1c.comp hQ
  have hW : ContDiff ℝ (⊤ : ℕ∞) (fun w => Phi w * b1 (incrQuad h V w)) := hPhi.mul hb1q
  have hbase := incrStretch_weighted_transfer (W := fun w => Phi w * b1 (incrQuad h V w))
    h hV hW hdiv z
  have hdW : ∀ j : Fin 3, dvec (0, ee j) (fun w => Phi w * b1 (incrQuad h V w)) z
      = dvec (0, ee j) Phi z * b1 (incrQuad h V z)
        + Phi z * (b2 (incrQuad h V z) * dvec (0, ee j) (incrQuad h V) z) := by
    intro j
    rw [dvec_mul Phi (fun w => b1 (incrQuad h V w)) z
      ((differentiable_of_contDiffTop hPhi) z)
      ((differentiable_of_contDiffTop hb1q) z) (0, ee j),
      dvec_comp_scalar hQ hb2 (0, ee j) z]
  simp only [hdW] at hbase
  rw [← mul_assoc]
  exact hbase

/-! ## The budget: the remainder of (T) is *linear* in the truncation data -/

/-- **The transferred stretching budget.**  With amplitude bounds `|u_a| ≤ A`,
`|δ_hu_a| ≤ B` and `|∂_jΦ| ≤ G` — and **no** bound on `∇u`, no critical norm of
the strain — the non-divergence remainder of the weighted transfer identity is
at most

`ην·Φβ''|∇q|² + (ν/2)·Φβ'|∇δ_hu|² + (27A²B⁴/4ην)·Φβ'' + (9A²B²/2ν)·Φβ' + 9AB²G·β'`.

The first two terms are absorbed by the two good terms of
`adjoint_localized_increment_budget`; the last three are *linear* in `β''` and
`β'`, i.e. in the level-set measure and the first power of the truncation. -/
theorem increment_stretching_transfer_budget {nu eta A B G : ℝ} (hnu : 0 < nu) (heta : 0 < eta)
    {V : STime → E3} {Phi : STime → ℝ} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    {b1 b2 : ℝ → ℝ} (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hdiv : ∀ z : STime, divg V z = 0) (z : STime)
    (hPhi0 : 0 ≤ Phi z) (hB1 : 0 ≤ b1 (incrQuad h V z)) (hB2 : 0 ≤ b2 (incrQuad h V z))
    (hA : ∀ a : Fin 3, |V z a| ≤ A) (hB : ∀ a : Fin 3, |incrComp h V a z| ≤ B)
    (hG : ∀ j : Fin 3, |dvec (0, ee j) Phi z| ≤ G) :
    |Phi z * (b1 (incrQuad h V z) * incrStretch h V z)
        - divg (fun w => ((Phi w * b1 (incrQuad h V w)) * incrPair h V w) • incrVec h V w) z|
      ≤ eta * nu * (Phi z * (b2 (incrQuad h V z)
            * ∑ k, dvec (0, ee k) (incrQuad h V) z * dvec (0, ee k) (incrQuad h V) z))
        + nu / 2 * (Phi z * (b1 (incrQuad h V z) * incrDissip h V z))
        + 27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * (Phi z * b2 (incrQuad h V z))
        + 9 * A ^ 2 * B ^ 2 / (2 * nu) * (Phi z * b1 (incrQuad h V z))
        + 9 * A * B ^ 2 * G * b1 (incrQuad h V z) := by
  set Q : ℝ := incrQuad h V z with hQ
  set B1 : ℝ := b1 Q with hB1def
  set B2 : ℝ := b2 Q with hB2def
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA 0)
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hG0 : 0 ≤ G := le_trans (abs_nonneg _) (hG 0)
  -- the exact split
  have hsplit := incrStretch_localized_split h hV hPhi hb1c hb2 hdiv z
  -- the two remainder terms
  set T1 : ℝ := incrPair h V z * ∑ j, incrComp h V j z
      * (dvec (0, ee j) Phi z * B1 + Phi z * (B2 * dvec (0, ee j) (incrQuad h V) z)) with hT1
  set T2 : ℝ := (Phi z * B1) * incrTransfer h V z with hT2
  have hrewrite : Phi z * (B1 * incrStretch h V z)
      - divg (fun w => ((Phi w * b1 (incrQuad h V w)) * incrPair h V w) • incrVec h V w) z
      = -T1 - T2 := by rw [hsplit]; ring
  rw [hrewrite]
  -- bound on the pair `u·δ_hu`
  have hpair : |incrPair h V z| ≤ 3 * (A * B) := by
    refine abs_sum3_mul_le (x := fun a => V z a) (y := fun a => incrComp h V a z) hA hB
  -- split `T1`
  have hT1split : T1 = incrPair h V z * (B1 * ∑ j, incrComp h V j z * dvec (0, ee j) Phi z)
      + incrPair h V z * (Phi z * B2
          * ∑ j, incrComp h V j z * dvec (0, ee j) (incrQuad h V) z) := by
    have hs : (∑ j, incrComp h V j z
          * (dvec (0, ee j) Phi z * B1 + Phi z * (B2 * dvec (0, ee j) (incrQuad h V) z)))
        = B1 * (∑ j, incrComp h V j z * dvec (0, ee j) Phi z)
          + (Phi z * B2) * ∑ j, incrComp h V j z * dvec (0, ee j) (incrQuad h V) z := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hT1, hs]
    ring
  -- the `∇Φ` pairing
  have hTa : |incrPair h V z * (B1 * ∑ j, incrComp h V j z * dvec (0, ee j) Phi z)|
      ≤ 9 * A * B ^ 2 * G * B1 := by
    have h1 : |∑ j, incrComp h V j z * dvec (0, ee j) Phi z| ≤ 3 * (B * G) :=
      abs_sum3_mul_le hB hG
    have h2 : |incrPair h V z * (B1 * ∑ j, incrComp h V j z * dvec (0, ee j) Phi z)|
        = |incrPair h V z| * (B1 * |∑ j, incrComp h V j z * dvec (0, ee j) Phi z|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hB1]
    rw [h2]
    have hmul : |incrPair h V z| * (B1 * |∑ j, incrComp h V j z * dvec (0, ee j) Phi z|)
        ≤ (3 * (A * B)) * (B1 * (3 * (B * G))) := by
      refine mul_le_mul hpair (by nlinarith [abs_nonneg (∑ j, incrComp h V j z
        * dvec (0, ee j) Phi z)]) (by positivity) (by positivity)
    nlinarith [hmul]
  -- the `β''∇q` pairing
  have hTb : |incrPair h V z * (Phi z * B2
        * ∑ j, incrComp h V j z * dvec (0, ee j) (incrQuad h V) z)|
      ≤ eta * nu * (Phi z * (B2 * ∑ k, dvec (0, ee k) (incrQuad h V) z
            * dvec (0, ee k) (incrQuad h V) z))
        + 27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * (Phi z * B2) := by
    set g : Fin 3 → ℝ := fun j => dvec (0, ee j) (incrQuad h V) z with hg
    have hstep1 : |∑ j, incrComp h V j z * g j| ≤ B * ∑ j, |g j| := by
      calc |∑ j, incrComp h V j z * g j| ≤ ∑ j, |incrComp h V j z * g j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, B * |g j| := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hB j) (abs_nonneg _)
        _ = B * ∑ j, |g j| := by rw [Finset.mul_sum]
    have hyoung := young_sum3 (c := 3 * A * B ^ 2) (lam := eta * nu) (by positivity) g
    have habs : |incrPair h V z * (Phi z * B2 * ∑ j, incrComp h V j z * g j)|
        = |incrPair h V z| * ((Phi z * B2) * |∑ j, incrComp h V j z * g j|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ Phi z * B2)]
    rw [habs]
    have hchain : |incrPair h V z| * ((Phi z * B2) * |∑ j, incrComp h V j z * g j|)
        ≤ (Phi z * B2) * ((3 * (A * B)) * (B * ∑ j, |g j|)) := by
      have hnn : (0:ℝ) ≤ Phi z * B2 := by positivity
      have h1 : |incrPair h V z| * |∑ j, incrComp h V j z * g j|
          ≤ (3 * (A * B)) * (B * ∑ j, |g j|) := by
        refine mul_le_mul hpair hstep1 (abs_nonneg _) (by positivity)
      nlinarith [abs_nonneg (∑ j, incrComp h V j z * g j), abs_nonneg (incrPair h V z)]
    refine hchain.trans ?_
    have hrw : (3 * (A * B)) * (B * ∑ j, |g j|) = (3 * A * B ^ 2) * ∑ j, |g j| := by ring
    rw [hrw]
    have hmul : (Phi z * B2) * ((3 * A * B ^ 2) * ∑ j, |g j|)
        ≤ (Phi z * B2) * (eta * nu * ∑ a, g a * g a + 3 * (3 * A * B ^ 2) ^ 2 / (4 * (eta * nu))) :=
      mul_le_mul_of_nonneg_left hyoung (by positivity)
    refine hmul.trans ?_
    have hconst : 3 * (3 * A * B ^ 2) ^ 2 / (4 * (eta * nu)) = 27 * A ^ 2 * B ^ 4 / (4 * eta * nu) := by
      field_simp
      ring
    rw [hconst]
    ring_nf
    nlinarith [mul_nonneg hPhi0 hB2]
  -- the transferred commutator
  have hTc : |T2| ≤ nu / 2 * (Phi z * (B1 * incrDissip h V z))
      + 9 * A ^ 2 * B ^ 2 / (2 * nu) * (Phi z * B1) := by
    have htr := incrTransfer_abs_le h V z hnu
    have hVsq : (∑ a, V z a * V z a) ≤ 3 * A ^ 2 := by
      have hpt : ∀ a : Fin 3, V z a * V z a ≤ A ^ 2 := by
        intro a
        calc V z a * V z a = |V z a| * |V z a| := (abs_mul_abs_self (V z a)).symm
          _ ≤ A * A := mul_self_le_mul_self (abs_nonneg _) (hA a)
          _ = A ^ 2 := (sq A).symm
      calc (∑ a, V z a * V z a) ≤ ∑ _a : Fin 3, A ^ 2 := Finset.sum_le_sum fun a _ => hpt a
        _ = 3 * A ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
    have hWsq : (∑ j, incrComp h V j z * incrComp h V j z) ≤ 3 * B ^ 2 := by
      have hpt : ∀ j : Fin 3, incrComp h V j z * incrComp h V j z ≤ B ^ 2 := by
        intro j
        calc incrComp h V j z * incrComp h V j z
            = |incrComp h V j z| * |incrComp h V j z| := (abs_mul_abs_self _).symm
          _ ≤ B * B := mul_self_le_mul_self (abs_nonneg _) (hB j)
          _ = B ^ 2 := (sq B).symm
      calc (∑ j, incrComp h V j z * incrComp h V j z) ≤ ∑ _j : Fin 3, B ^ 2 :=
            Finset.sum_le_sum fun j _ => hpt j
        _ = 3 * B ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
    have hVsq0 : 0 ≤ ∑ a, V z a * V z a := Finset.sum_nonneg fun a _ => mul_self_nonneg _
    have hWsq0 : 0 ≤ ∑ j, incrComp h V j z * incrComp h V j z :=
      Finset.sum_nonneg fun j _ => mul_self_nonneg _
    have hprodle : (∑ a, V z a * V z a) * ∑ j, incrComp h V j z * incrComp h V j z
        ≤ 9 * A ^ 2 * B ^ 2 := by
      calc (∑ a, V z a * V z a) * ∑ j, incrComp h V j z * incrComp h V j z
          ≤ (3 * A ^ 2) * (3 * B ^ 2) :=
            mul_le_mul hVsq hWsq hWsq0 (by positivity)
        _ = 9 * A ^ 2 * B ^ 2 := by ring
    have hbound : |incrTransfer h V z|
        ≤ nu / 2 * incrDissip h V z + 9 * A ^ 2 * B ^ 2 / (2 * nu) := by
      refine htr.trans ?_
      have : 1 / (2 * nu) * ((∑ a, V z a * V z a)
          * ∑ j, incrComp h V j z * incrComp h V j z)
          ≤ 1 / (2 * nu) * (9 * A ^ 2 * B ^ 2) :=
        mul_le_mul_of_nonneg_left hprodle (by positivity)
      have heq : 1 / (2 * nu) * (9 * A ^ 2 * B ^ 2) = 9 * A ^ 2 * B ^ 2 / (2 * nu) := by
        field_simp
      linarith [this, heq ▸ this]
    have habs : |T2| = (Phi z * B1) * |incrTransfer h V z| := by
      rw [hT2, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ Phi z * B1)]
    rw [habs]
    have := mul_le_mul_of_nonneg_left hbound (by positivity : (0:ℝ) ≤ Phi z * B1)
    calc (Phi z * B1) * |incrTransfer h V z|
        ≤ (Phi z * B1) * (nu / 2 * incrDissip h V z + 9 * A ^ 2 * B ^ 2 / (2 * nu)) := this
      _ = nu / 2 * (Phi z * (B1 * incrDissip h V z))
            + 9 * A ^ 2 * B ^ 2 / (2 * nu) * (Phi z * B1) := by ring
  -- assemble
  have htri : |(-T1) - T2| ≤ |T1| + |T2| := by
    have hadd := abs_add_le (-T1) (-T2)
    simpa [sub_eq_add_neg, abs_neg] using hadd
  have hT1le : |T1| ≤ 9 * A * B ^ 2 * G * B1
      + (eta * nu * (Phi z * (B2 * ∑ k, dvec (0, ee k) (incrQuad h V) z
            * dvec (0, ee k) (incrQuad h V) z))
        + 27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * (Phi z * B2)) := by
    rw [hT1split]
    exact (abs_add_le _ _).trans (add_le_add hTa hTb)
  linarith [htri, hT1le, hTc]

/-! ## The integrated (cell) form of the budget -/

/-- The pointwise budget of `increment_stretching_transfer_budget`, as a
spacetime function. -/
def stretchBudget (nu eta A B G : ℝ) (h : E3) (V : STime → E3) (Phi : STime → ℝ)
    (b1 b2 : ℝ → ℝ) : STime → ℝ := fun w =>
  eta * nu * (Phi w * (b2 (incrQuad h V w)
      * ∑ k, dvec (0, ee k) (incrQuad h V) w * dvec (0, ee k) (incrQuad h V) w))
    + nu / 2 * (Phi w * (b1 (incrQuad h V w) * incrDissip h V w))
    + 27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * (Phi w * b2 (incrQuad h V w))
    + 9 * A ^ 2 * B ^ 2 / (2 * nu) * (Phi w * b1 (incrQuad h V w))
    + 9 * A * B ^ 2 * G * b1 (incrQuad h V w)

lemma contDiff_stretchBudget (nu eta A B G : ℝ) {V : STime → E3} {Phi : STime → ℝ} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    {b1 b2 : ℝ → ℝ} (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1) (hb2c : ContDiff ℝ (⊤ : ℕ∞) b2) :
    ContDiff ℝ (⊤ : ℕ∞) (stretchBudget nu eta A B G h V Phi b1 b2) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  have hb1q : ContDiff ℝ (⊤ : ℕ∞) (fun w => b1 (incrQuad h V w)) := hb1c.comp hq
  have hb2q : ContDiff ℝ (⊤ : ℕ∞) (fun w => b2 (incrQuad h V w)) := hb2c.comp hq
  have hdq : ∀ k : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (dvec (0, ee k) (incrQuad h V)) :=
    fun k => contDiff_dvec _ hq _
  have hgr : ContDiff ℝ (⊤ : ℕ∞)
      (fun w => ∑ k, dvec (0, ee k) (incrQuad h V) w * dvec (0, ee k) (incrQuad h V) w) :=
    ContDiff.sum fun k _ => (hdq k).mul (hdq k)
  have hdiss : ContDiff ℝ (⊤ : ℕ∞) (incrDissip h V) := contDiff_incrDissip h hV
  exact ((((contDiff_const.mul (hPhi.mul (hb2q.mul hgr))).add
      (contDiff_const.mul (hPhi.mul (hb1q.mul hdiss)))).add
      (contDiff_const.mul (hPhi.mul hb2q))).add
      (contDiff_const.mul (hPhi.mul hb1q))).add (contDiff_const.mul hb1q)

/-- If `|f| ≤ g` pointwise then `|∫_cell f| ≤ ∫_cell g`. -/
lemma abs_cellInt_le {f g : E3 → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hle : ∀ x, |f x| ≤ g x) : |cellInt f| ≤ cellInt g := by
  have hup : cellInt f ≤ cellInt g :=
    cellInt_mono hf hg fun x => (abs_le.mp (hle x)).2
  have hdown : cellInt (fun x => -g x) ≤ cellInt f :=
    cellInt_mono hg.neg hf fun x => (abs_le.mp (hle x)).1
  rw [cellInt_neg] at hdown
  exact abs_le.mpr ⟨by linarith, hup⟩

/-- **The integrated transferred stretching budget.**  On the periodic cell the
divergence of the transfer flux integrates away, so the whole weighted
stretching source is controlled by the budget:

`|∫_cell Φβ'(q)·δ_hu·(δ_hu·∇)u| ≤ ∫_cell [ ην Φβ''|∇q|² + (ν/2)Φβ'|∇δ_hu|²
    + C₁Φβ'' + C₂Φβ' + C₃β' ]`,

with `C₁ = 27A²B⁴/4ην`, `C₂ = 9A²B²/2ν`, `C₃ = 9AB²G`.  No bound on `∇u` and no
critical norm of the strain is used; the first two terms are absorbed by the
good terms of the adjoint-weighted budget and the last three are linear in the
truncation data. -/
theorem increment_stretching_transfer_cell_budget {nu eta A B G : ℝ} (hnu : 0 < nu)
    (heta : 0 < eta) {V : STime → E3} {Phi : STime → ℝ} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hVper : SpacePeriodic V) (hPhiper : SpacePeriodic Phi)
    {b1 b2 : ℝ → ℝ} (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1) (hb2c : ContDiff ℝ (⊤ : ℕ∞) b2)
    (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hPhi0 : ∀ z, 0 ≤ Phi z) (hB1 : ∀ x, 0 ≤ b1 x) (hB2 : ∀ x, 0 ≤ b2 x)
    (hA : ∀ (z : STime) (a : Fin 3), |V z a| ≤ A)
    (hB : ∀ (z : STime) (a : Fin 3), |incrComp h V a z| ≤ B)
    (hG : ∀ (z : STime) (j : Fin 3), |dvec (0, ee j) Phi z| ≤ G) (t : ℝ) :
    |cellInt (fun x => Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x)))|
      ≤ cellInt (fun x => stretchBudget nu eta A B G h V Phi b1 b2 (t, x)) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  have hb1q : ContDiff ℝ (⊤ : ℕ∞) (fun w => b1 (incrQuad h V w)) := hb1c.comp hq
  -- the transfer flux
  set Fl : STime → E3 :=
    fun w => ((Phi w * b1 (incrQuad h V w)) * incrPair h V w) • incrVec h V w with hFl
  have hFlC : ContDiff ℝ (⊤ : ℕ∞) Fl :=
    ((hPhi.mul hb1q).mul (contDiff_incrPair h hV)).smul (contDiff_incrVec h hV)
  have hFlper : SpacePeriodic Fl := by
    intro z j
    show ((Phi (z.1, z.2 + ee j) * b1 (incrQuad h V (z.1, z.2 + ee j)))
        * incrPair h V (z.1, z.2 + ee j)) • incrVec h V (z.1, z.2 + ee j)
      = ((Phi z * b1 (incrQuad h V z)) * incrPair h V z) • incrVec h V z
    rw [hPhiper z j, spacePeriodic_incrQuad h hVper z j, spacePeriodic_incrPair h hVper z j,
      spacePeriodic_incrVec h hVper z j]
  -- the divergence integrates away
  have hdivzero : cellInt (fun x => divg Fl (t, x)) = 0 :=
    cellInt_divg_eq_zero Fl hFlC hFlper t
  -- continuity
  have hfC : Continuous fun x : E3 =>
      Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x)) :=
    continuous_slice (hPhi.mul (hb1q.mul (contDiff_incrStretch h hV))) t
  have hgC : Continuous fun x : E3 => divg Fl (t, x) :=
    continuous_slice (contDiff_divgFun hFlC) t
  have hRC : Continuous fun x : E3 => stretchBudget nu eta A B G h V Phi b1 b2 (t, x) :=
    continuous_slice (contDiff_stretchBudget nu eta A B G h hV hPhi hb1c hb2c) t
  -- the pointwise budget
  have hpt : ∀ x : E3,
      |Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x)) - divg Fl (t, x)|
        ≤ stretchBudget nu eta A B G h V Phi b1 b2 (t, x) := by
    intro x
    exact increment_stretching_transfer_budget hnu heta h hV hPhi hb1c hb2 hdiv (t, x)
      (hPhi0 _) (hB1 _) (hB2 _) (hA _) (hB _) (hG _)
  have hsub : cellInt (fun x => Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x))
      - divg Fl (t, x))
      = cellInt (fun x => Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x))) := by
    rw [cellInt_sub hfC hgC, hdivzero, sub_zero]
  have habs := abs_cellInt_le (f := fun x =>
      Phi (t, x) * (b1 (incrQuad h V (t, x)) * incrStretch h V (t, x)) - divg Fl (t, x))
    (g := fun x => stretchBudget nu eta A B G h V Phi b1 b2 (t, x)) (hfC.sub hgC) hRC hpt
  rwa [hsub] at habs

/-! ## Why a *linear* budget suffices -/

/-- **A linear Caccioppoli budget produces the superlinear De Giorgi
recurrence.**  If the budget at stage `n` is bounded by a fixed multiple of the
level energy plus a fixed multiple of the level measure, and Chebyshev bounds
the level measure by `4ⁿ` times the level energy, then the budget is
`≤ c·4ⁿ·Y_n` — exactly the shape `K = 4ⁿY_n` required by
`deGiorgi_dyadic_recurrence` (up to the constant), hence the recurrence
`Y_{n+1} ≤ C bⁿ Y_n^{1+2/5}` with the superlinear exponent.  This is the step
that a *sublinear* source (`sublinear_recurrence_no_decay`) cannot provide. -/
theorem linear_budget_superlinear_recurrence {Y m K : ℕ → ℝ} {c1 c2 kappa : ℝ}
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hY : ∀ n, 0 ≤ Y n)
    (hbudget : ∀ n, K n ≤ c1 * Y n + c2 * m n)
    (hcheb : ∀ n, m n ≤ (4 : ℝ) ^ n * kappa * Y n) (n : ℕ) :
    K n ≤ (c1 + c2 * kappa) * (4 : ℝ) ^ n * Y n := by
  have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have h1 : c2 * m n ≤ c2 * ((4 : ℝ) ^ n * kappa * Y n) :=
    mul_le_mul_of_nonneg_left (hcheb n) hc2
  have h2 : c1 * Y n ≤ c1 * ((4 : ℝ) ^ n * Y n) := by
    have := mul_le_mul_of_nonneg_right h4 (hY n)
    nlinarith [hY n, hc1]
  calc K n ≤ c1 * Y n + c2 * m n := hbudget n
    _ ≤ c1 * ((4 : ℝ) ^ n * Y n) + c2 * ((4 : ℝ) ^ n * kappa * Y n) := by linarith
    _ = (c1 + c2 * kappa) * (4 : ℝ) ^ n * Y n := by ring

end ClayNS

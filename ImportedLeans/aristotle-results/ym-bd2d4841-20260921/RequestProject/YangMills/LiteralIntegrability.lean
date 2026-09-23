/-
# Row A1a — integrability of the *interacting* literal one-loop integrand

`WardIntegrability` discharges the integrability obligation of `A1_beta_pos_ward`
in the free case, where the closed form `(3/2)sin(2πx_ρ)²/(q̂²)²` is available.
This file removes that restriction and, in doing so, identifies exactly which
structural property of the source data makes the shell Gaussian coefficient
finite at all.

The constrained propagator is `G(q) = (q̂²)⁻¹P(q)`, and `q̂² ≥ 16‖q‖²` on the
cell, so `G` blows up like `‖q‖⁻²`.  Counting powers in

    I = ½Tr(GVGV) − ½Tr(GS)

gives `‖q‖⁻⁴|V|² + ‖q‖⁻²|S|`.  In four dimensions `‖q‖⁻²` is integrable and
`‖q‖⁻⁴` is not.  Hence:

* a **bounded** seagull insertion `S = −WᵀW` is harmless; but
* the first variation `V` must **vanish at zero momentum**, at least linearly,
  for the bubble term to be integrable.

That is not an extra assumption imposed by hand: it is the momentum-space form of
`AnnihilatesZero`, the property the literal transforms of Bałaban's averaging and
constrained-projection operators are already known to have, and the Wilson and
gauge parts of the vertex vanish linearly at `q = 0` because every entry is built
from `p̂_μ = 2sin(πq_μ)` and `sin(2πq_ρ)`.

Main results:

* `abs_betaTrace_le` — an entrywise bound for the one-loop trace of a `4 × 4`
  system, in terms of entry bounds for the propagator, the vertex and the
  seagull.
* `literalOneLoopIntegrand_integrableOn_of_entryBounds` — if `|V(q)_{ab}| ≤ K‖q‖`
  and `|W(q)_{ab}| ≤ K` on the cell, the literal integrand is integrable on the
  punctured cell.
* `sourceVariationMatrix_entry_bound` — the literal source vertex does satisfy
  the linear bound, with an explicit constant, provided the Lorentz-diagonal
  averaging/constrained-projection contribution does.
* `A1_beta_pos_ward_of_linearVanishing` — Row A1a from the literal one-loop trace
  with the integrability hypothesis discharged, for interacting source data.

**Row A1 is not closed.**  What remains is the diagonal size bound on the
averaging/constrained-projection variation and the five remainder-channel
majorants, together with the source-identification chain itself.  Scoreboard
unchanged: `A, B, C, D` open, frozen research count 4.
-/
import RequestProject.YangMills.WardIntegrability

namespace YangMills

open Real Matrix Finset MeasureTheory Set

/-! ## 1. Entrywise arithmetic for `4 × 4` matrices -/

theorem abs_entry_mul_le {M N : Matrix (Fin 4) (Fin 4) ℝ} {p q : ℝ} (hp : 0 ≤ p)
    (hM : ∀ a b, |M a b| ≤ p) (hN : ∀ a b, |N a b| ≤ q) (a b : Fin 4) :
    |(M * N) a b| ≤ 4 * (p * q) := by
  rw [Matrix.mul_apply]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ c ∈ (Finset.univ : Finset (Fin 4)), |M a c * N c b| ≤ p * q := by
    intro c _
    rw [abs_mul]
    exact mul_le_mul (hM a c) (hN c b) (abs_nonneg _) hp
  calc ∑ c : Fin 4, |M a c * N c b| ≤ ∑ _c : Fin 4, p * q := Finset.sum_le_sum hterm
    _ = 4 * (p * q) := by simp

theorem abs_trace_le {M : Matrix (Fin 4) (Fin 4) ℝ} {p : ℝ} (hM : ∀ a b, |M a b| ≤ p) :
    |M.trace| ≤ 4 * p := by
  simp only [Matrix.trace, Matrix.diag_apply]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ c : Fin 4, |M c c| ≤ ∑ _c : Fin 4, p := Finset.sum_le_sum fun c _ => hM c c
    _ = 4 * p := by simp

/-- **An entrywise bound for the one-loop trace.**  With entry bounds `g`, `v`,
`s` for the propagator, the vertex and the seagull, the trace is at most
`128g²v² + 8gs`. -/
theorem abs_betaTrace_le {G V S : Matrix (Fin 4) (Fin 4) ℝ} {g v s : ℝ}
    (hg0 : 0 ≤ g) (hv0 : 0 ≤ v)
    (hG : ∀ a b, |G a b| ≤ g) (hV : ∀ a b, |V a b| ≤ v) (hS : ∀ a b, |S a b| ≤ s) :
    |betaTrace G V V S| ≤ 128 * g ^ 2 * v ^ 2 + 8 * (g * s) := by
  have h1 : ∀ a b, |(G * V) a b| ≤ 4 * (g * v) := abs_entry_mul_le hg0 hG hV
  have h2 : ∀ a b, |(G * V * G) a b| ≤ 4 * (4 * (g * v) * g) :=
    abs_entry_mul_le (by positivity) h1 hG
  have h3 : ∀ a b, |(G * V * G * V) a b| ≤ 4 * (4 * (4 * (g * v) * g) * v) :=
    abs_entry_mul_le (by positivity) h2 hV
  have h4 : |(G * V * G * V).trace| ≤ 4 * (4 * (4 * (4 * (g * v) * g) * v)) := abs_trace_le h3
  have h5 : ∀ a b, |(G * S) a b| ≤ 4 * (g * s) := abs_entry_mul_le hg0 hG hS
  have h6 : |(G * S).trace| ≤ 4 * (4 * (g * s)) := abs_trace_le h5
  rw [betaTrace]
  calc |1 / 2 * (G * V * G * V).trace - 1 / 2 * (G * S).trace|
      ≤ |1 / 2 * (G * V * G * V).trace| + |1 / 2 * (G * S).trace| := abs_sub _ _
    _ = 1 / 2 * |(G * V * G * V).trace| + 1 / 2 * |(G * S).trace| := by
        rw [abs_mul, abs_mul]; norm_num
    _ ≤ 1 / 2 * (4 * (4 * (4 * (4 * (g * v) * g) * v))) + 1 / 2 * (4 * (4 * (g * s))) := by
        have := h4; have := h6; linarith
    _ = 128 * g ^ 2 * v ^ 2 + 8 * (g * s) := by ring

/-! ## 2. Entry bounds for the constrained lattice propagator -/

theorem abs_transverseProjector_entry_le {u : Fin 4 → ℝ} (hu : 0 < normSqVec u) (a b : Fin 4) :
    |transverseProjector u a b| ≤ 2 := by
  have hab : |u a * u b| ≤ normSqVec u := by
    have hsum : (u a) ^ 2 + (u b) ^ 2 ≤ 2 * normSqVec u := by
      rcases eq_or_ne a b with h | h
      · subst h
        have : (u a) ^ 2 ≤ normSqVec u := by
          rw [normSqVec]
          have := Finset.single_le_sum (f := fun c : Fin 4 => u c * u c)
            (fun c _ => mul_self_nonneg _) (mem_univ a)
          nlinarith [this]
        linarith
      · have hle : (u a) ^ 2 + (u b) ^ 2 ≤ normSqVec u := by
          rw [normSqVec]
          have hsub : ({a, b} : Finset (Fin 4)) ⊆ Finset.univ := Finset.subset_univ _
          have hle2 := Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun c _ _ => mul_self_nonneg (u c))
          have hpair : ∑ c ∈ ({a, b} : Finset (Fin 4)), u c * u c = (u a) ^ 2 + (u b) ^ 2 := by
            rw [Finset.sum_pair h]; ring
          linarith [hpair ▸ hle2]
        linarith [hu.le]
    have habs : 2 * |u a * u b| ≤ (u a) ^ 2 + (u b) ^ 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|u a| - |u b|), sq_abs (u a), sq_abs (u b),
        abs_nonneg (u a), abs_nonneg (u b)]
    linarith
  have hone : |(1 : Matrix (Fin 4) (Fin 4) ℝ) a b| ≤ 1 := by
    rw [Matrix.one_apply]
    split <;> norm_num
  have hsec : |(normSqVec u)⁻¹ * (u a * u b)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hu.le)]
    rw [inv_mul_le_iff₀ hu]
    linarith
  rw [transverseProjector, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul]
  calc |(1 : Matrix (Fin 4) (Fin 4) ℝ) a b - (normSqVec u)⁻¹ * (u a * u b)|
      ≤ |(1 : Matrix (Fin 4) (Fin 4) ℝ) a b| + |(normSqVec u)⁻¹ * (u a * u b)| := abs_sub _ _
    _ ≤ 1 + 1 := by linarith
    _ = 2 := by norm_num

theorem latticeSymbolOf_eq {x : Fin 4 → ℝ} (hx : phatSq x ≠ 0) :
    latticeSymbolOf x = (phatSq x)⁻¹ • transverseProjector (phatVec x) :=
  constrainedPropagator_lattice x hx

/-- **The propagator entry bound on the cell.** -/
theorem abs_latticeSymbolOf_entry_le {x : Fin 4 → ℝ} (hx : x ∈ momentumCell) (hne : 0 < ‖x‖)
    (a b : Fin 4) : |latticeSymbolOf x a b| ≤ 1 / (8 * ‖x‖ ^ 2) := by
  have hnormsq : 0 < ‖x‖ ^ 2 := by positivity
  have h16 := sixteen_mul_normSq_le_phatSq hx
  have hq : 0 < phatSq x := lt_of_lt_of_le (by linarith) h16
  have hu : 0 < normSqVec (phatVec x) := by rwa [normSqVec_phatVec]
  rw [latticeSymbolOf_eq (ne_of_gt hq), Matrix.smul_apply, smul_eq_mul, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr hq.le)]
  have hP := abs_transverseProjector_entry_le hu a b
  have hstep : (phatSq x)⁻¹ * |transverseProjector (phatVec x) a b|
      ≤ (phatSq x)⁻¹ * 2 := by
    exact mul_le_mul_of_nonneg_left hP (inv_nonneg.mpr hq.le)
  refine le_trans hstep ?_
  rw [inv_mul_eq_div, div_le_div_iff₀ hq (by positivity)]
  linarith

/-! ## 3. Measurability of the literal integrand -/

variable {α : Type*} [MeasurableSpace α]

theorem measurable_entry_mul {M N : α → Matrix (Fin 4) (Fin 4) ℝ}
    (hM : ∀ a b, Measurable fun x => M x a b) (hN : ∀ a b, Measurable fun x => N x a b)
    (a b : Fin 4) : Measurable fun x => (M x * N x) a b := by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun c _ => (hM a c).mul (hN c b)

theorem measurable_entry_trace {M : α → Matrix (Fin 4) (Fin 4) ℝ}
    (hM : ∀ a b, Measurable fun x => M x a b) : Measurable fun x => (M x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Finset.measurable_sum _ fun c _ => hM c c

theorem measurable_phatSq : Measurable phatSq := by
  have : Continuous phatSq := by unfold phatSq phat sinAtom; fun_prop
  exact this.measurable

theorem measurable_phatVec_apply (c : Fin 4) :
    Measurable fun x : Fin 4 → ℝ => phatVec x c := by
  have : Continuous fun x : Fin 4 → ℝ => phatVec x c := by unfold phatVec phat sinAtom; fun_prop
  exact this.measurable

theorem measurable_latticeSymbolOf_entry (a b : Fin 4) :
    Measurable fun x : Fin 4 → ℝ => (phatSq x)⁻¹ • transverseProjector (phatVec x) a b := by
  simp only [transverseProjector, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, normSqVec_phatVec]
  exact measurable_phatSq.inv.mul ((measurable_const).sub
    (measurable_phatSq.inv.mul ((measurable_phatVec_apply a).mul (measurable_phatVec_apply b))))

theorem measurable_transpose_entry {M : α → Matrix (Fin 4) (Fin 4) ℝ}
    (hM : ∀ a b, Measurable fun x => M x a b) (a b : Fin 4) :
    Measurable fun x => (M x)ᵀ a b := hM b a

theorem measurable_neg_entry {M : α → Matrix (Fin 4) (Fin 4) ℝ}
    (hM : ∀ a b, Measurable fun x => M x a b) (a b : Fin 4) :
    Measurable fun x => (-(M x)) a b := (hM a b).neg

/-- The literal one-loop integrand, with the propagator written in its explicit
transverse form, is measurable. -/
theorem measurable_literalOneLoopModel
    {Vm Wm : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    (hV : ∀ a b, Measurable fun x => Vm x a b)
    (hW : ∀ a b, Measurable fun x => Wm x a b) :
    Measurable fun x : Fin 4 → ℝ =>
      betaTrace ((phatSq x)⁻¹ • transverseProjector (phatVec x)) (Vm x) (Vm x)
        (-((Wm x)ᵀ * Wm x)) := by
  set G : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ :=
    fun x => (phatSq x)⁻¹ • transverseProjector (phatVec x) with hGdef
  have hG : ∀ a b, Measurable fun x => G x a b := measurable_latticeSymbolOf_entry
  have hS : ∀ a b, Measurable fun x : Fin 4 → ℝ => (-((Wm x)ᵀ * Wm x)) a b :=
    measurable_neg_entry (measurable_entry_mul (measurable_transpose_entry hW) hW)
  simp only [betaTrace]
  refine (measurable_const.mul (measurable_entry_trace ?_)).sub
    (measurable_const.mul (measurable_entry_trace ?_))
  · exact measurable_entry_mul (measurable_entry_mul (measurable_entry_mul hG hV) hG) hV
  · exact measurable_entry_mul hG hS

/-! ## 4. Integrability of the interacting literal integrand -/

/-- **Pointwise radial majorant for the literal one-loop integrand.**  On the
punctured cell, with a linearly vanishing transverse conjugate of the vertex and
a bounded seagull insertion, the integrand is dominated by
`(cV²/32 + 4KW²)·‖q‖⁻²`.  This is the single estimate behind both the
integrability of the integrand and the *upper* bound on the shell Gaussian
coefficient. -/
theorem abs_literalOneLoopIntegrand_le_radial
    {Vm Wm : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {cV KW : ℝ}
    (hcV : 0 ≤ cV) (hKW : 0 ≤ KW)
    (hsym : ∀ x, (Vm x)ᵀ = Vm x)
    (hconj : ∀ x ∈ puncturedCell, ∀ a b,
      |(transverseProjector (phatVec x) * Vm x * transverseProjector (phatVec x)) a b|
        ≤ cV * ‖x‖)
    (hWbd : ∀ x ∈ puncturedCell, ∀ a b, |Wm x a b| ≤ KW)
    {x : Fin 4 → ℝ} (hx : x ∈ puncturedCell) :
    |literalOneLoopIntegrand Vm Wm x| ≤ (cV ^ 2 / 32 + 4 * KW ^ 2) * radialCutoff ‖x‖ := by
  have hcell : x ∈ momentumCell := hx.1
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx.2
  have hnormsq : 0 < ‖x‖ ^ 2 := by positivity
  have hq : phatSq x ≠ 0 := phatSq_ne_zero_of_mem_puncturedCell hx
  have h16 := sixteen_mul_normSq_le_phatSq hcell
  have hqpos : 0 < phatSq x := lt_of_lt_of_le (by linarith) h16
  have hcut : radialCutoff ‖x‖ = (‖x‖ ^ 2)⁻¹ := by
    rw [radialCutoff, if_pos (by linarith [norm_le_half_of_mem_momentumCell hcell])]
  rw [literalOneLoopIntegrand, betaTrace]
  -- the bubble, as a Frobenius norm of the reduced kernel
  have hG : latticeSymbolOf x = (latticeGramFactor x)ᵀ * latticeGramFactor x :=
    latticeSymbol_eq_gram x hq
  have hbub := bubble_eq_frobenius (G := latticeSymbolOf x) (V := Vm x)
    (C := latticeGramFactor x) hG (hsym x)
  have hM : latticeGramFactor x * Vm x * (latticeGramFactor x)ᵀ
      = (phatSq x)⁻¹ • (transverseProjector (phatVec x) * Vm x
          * transverseProjector (phatVec x)) := latticeReducedBubble_eq x hqpos.le (Vm x)
  have hMb : ∀ a b, |(latticeGramFactor x * Vm x * (latticeGramFactor x)ᵀ) a b|
      ≤ cV / (16 * ‖x‖) := by
    intro a b
    rw [hM, Matrix.smul_apply, smul_eq_mul, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr hqpos.le)]
    have hstep : (phatSq x)⁻¹
        * |(transverseProjector (phatVec x) * Vm x * transverseProjector (phatVec x)) a b|
        ≤ (phatSq x)⁻¹ * (cV * ‖x‖) :=
      mul_le_mul_of_nonneg_left (hconj x hx a b) (inv_nonneg.mpr hqpos.le)
    refine le_trans hstep ?_
    rw [inv_mul_eq_div, div_le_div_iff₀ hqpos (by positivity)]
    nlinarith [mul_nonneg hcV hpos.le]
  have hsumb : ∑ a : Fin 4, ∑ b : Fin 4,
      ((latticeGramFactor x * Vm x * (latticeGramFactor x)ᵀ) a b) ^ 2
      ≤ cV ^ 2 / (16 * ‖x‖ ^ 2) := by
    have hterm : ∀ a b : Fin 4,
        ((latticeGramFactor x * Vm x * (latticeGramFactor x)ᵀ) a b) ^ 2
          ≤ (cV / (16 * ‖x‖)) ^ 2 := by
      intro a b
      have h1 := hMb a b
      have h2 := abs_nonneg ((latticeGramFactor x * Vm x * (latticeGramFactor x)ᵀ) a b)
      nlinarith [sq_abs ((latticeGramFactor x * Vm x * (latticeGramFactor x)ᵀ) a b)]
    calc ∑ a : Fin 4, ∑ b : Fin 4,
          ((latticeGramFactor x * Vm x * (latticeGramFactor x)ᵀ) a b) ^ 2
        ≤ ∑ _a : Fin 4, ∑ _b : Fin 4, (cV / (16 * ‖x‖)) ^ 2 :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
      _ = cV ^ 2 / (16 * ‖x‖ ^ 2) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Nat.cast_ofNat]
          field_simp
          ring
  -- the seagull
  have hGb : ∀ a b, |latticeSymbolOf x a b| ≤ 1 / (8 * ‖x‖ ^ 2) :=
    abs_latticeSymbolOf_entry_le hcell hpos
  have hSb : ∀ a b, |(-((Wm x)ᵀ * Wm x)) a b| ≤ 4 * (KW * KW) := by
    intro a b
    rw [Matrix.neg_apply, abs_neg]
    exact abs_entry_mul_le hKW (fun c d => hWbd x hx d c)
      (fun c d => hWbd x hx c d) a b
  have htr : |(latticeSymbolOf x * (-((Wm x)ᵀ * Wm x))).trace| ≤ 4 * (4 * (1 / (8 * ‖x‖ ^ 2)
      * (4 * (KW * KW)))) :=
    abs_trace_le (abs_entry_mul_le (by positivity) hGb hSb)
  -- assemble
  have hb1 : |1 / 2 * (latticeSymbolOf x * Vm x * latticeSymbolOf x * Vm x).trace|
      ≤ 1 / 2 * (cV ^ 2 / (16 * ‖x‖ ^ 2)) := by
    rw [abs_mul, hbub]
    have hnn : (0 : ℝ) ≤ ∑ a : Fin 4, ∑ b : Fin 4,
        ((latticeGramFactor x * Vm x * (latticeGramFactor x)ᵀ) a b) ^ 2 :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
    rw [abs_of_nonneg hnn]
    have habs2 : |(1 : ℝ) / 2| = 1 / 2 := by norm_num
    rw [habs2]
    linarith
  have hb2 : |1 / 2 * (latticeSymbolOf x * (-((Wm x)ᵀ * Wm x))).trace|
      ≤ 1 / 2 * (16 * (1 / (8 * ‖x‖ ^ 2) * (4 * (KW * KW)))) := by
    rw [abs_mul]
    have habs2 : |(1 : ℝ) / 2| = 1 / 2 := by norm_num
    rw [habs2]
    linarith
  have hfin : 1 / 2 * (cV ^ 2 / (16 * ‖x‖ ^ 2))
      + 1 / 2 * (16 * (1 / (8 * ‖x‖ ^ 2) * (4 * (KW * KW))))
      = (cV ^ 2 / 32 + 4 * KW ^ 2) * (‖x‖ ^ 2)⁻¹ := by
    field_simp; ring
  rw [hcut, ← hfin]
  calc |1 / 2 * (latticeSymbolOf x * Vm x * latticeSymbolOf x * Vm x).trace
          - 1 / 2 * (latticeSymbolOf x * (-((Wm x)ᵀ * Wm x))).trace|
      ≤ |1 / 2 * (latticeSymbolOf x * Vm x * latticeSymbolOf x * Vm x).trace|
        + |1 / 2 * (latticeSymbolOf x * (-((Wm x)ᵀ * Wm x))).trace| := abs_sub _ _
    _ ≤ _ := by linarith

/-- **The literal one-loop integrand is integrable on the punctured cell** as
soon as the *transverse conjugate* of the first variation vanishes linearly at
zero momentum and the seagull insertion is bounded.

The conjugate — not the vertex itself — is the right object: the gauge-projection
variation has entries of size `‖q‖⁻¹`, and it is only after conjugation with the
constrained propagator that it disappears (`transverseProjector_conj_gaugeVariationMatrix`).
-/
theorem literalOneLoopIntegrand_integrableOn_of_conjBound
    {Vm Wm : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {cV KW : ℝ}
    (hcV : 0 ≤ cV) (hKW : 0 ≤ KW)
    (hVm : ∀ a b, Measurable fun x => Vm x a b)
    (hWm : ∀ a b, Measurable fun x => Wm x a b)
    (hsym : ∀ x, (Vm x)ᵀ = Vm x)
    (hconj : ∀ x ∈ puncturedCell, ∀ a b,
      |(transverseProjector (phatVec x) * Vm x * transverseProjector (phatVec x)) a b|
        ≤ cV * ‖x‖)
    (hWbd : ∀ x ∈ puncturedCell, ∀ a b, |Wm x a b| ≤ KW) :
    IntegrableOn (literalOneLoopIntegrand Vm Wm) puncturedCell := by
  set F : (Fin 4 → ℝ) → ℝ := fun x =>
    betaTrace ((phatSq x)⁻¹ • transverseProjector (phatVec x)) (Vm x) (Vm x)
      (-((Wm x)ᵀ * Wm x)) with hFdef
  have heq : ∀ x ∈ puncturedCell, F x = literalOneLoopIntegrand Vm Wm x := by
    intro x hx
    rw [hFdef, literalOneLoopIntegrand,
      latticeSymbolOf_eq (phatSq_ne_zero_of_mem_puncturedCell hx)]
  have hbound : ∀ x ∈ puncturedCell, |F x| ≤ (cV ^ 2 / 32 + 4 * KW ^ 2) * radialCutoff ‖x‖ := by
    intro x hx
    rw [heq x hx]
    exact abs_literalOneLoopIntegrand_le_radial hcV hKW hsym hconj hWbd hx
  have hg : IntegrableOn
      (fun x : Fin 4 → ℝ => (cV ^ 2 / 32 + 4 * KW ^ 2) * radialCutoff ‖x‖) puncturedCell :=
    (integrable_radialCutoff_norm.const_mul (cV ^ 2 / 32 + 4 * KW ^ 2)).integrableOn
  have hFint : IntegrableOn F puncturedCell := by
    refine hg.mono' ((measurable_literalOneLoopModel hVm hWm).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_puncturedCell).mpr ?_
    filter_upwards with x hx
    exact hbound x hx
  exact hFint.congr_fun heq measurableSet_puncturedCell

/-! ## 5. The transverse conjugate of the literal source vertex -/

theorem abs_sinAtom_two_mul_le {t : ℝ} : |sinAtom (2 * t)| ≤ 2 * (π * |t|) := by
  rw [sinAtom]
  calc |Real.sin (π * (2 * t))| ≤ |π * (2 * t)| := Real.abs_sin_le_abs
    _ = 2 * (π * |t|) := by
        rw [show π * (2 * t) = 2 * (π * t) by ring, abs_mul, abs_mul, abs_two,
          abs_of_nonneg Real.pi_pos.le]

/-- **The transverse conjugate of the literal source first variation vanishes
linearly at zero momentum.**  The gauge-projection part drops out entirely, the
Wilson part contributes `sin(2πq_ρ)·P`, and the Lorentz-diagonal part is assumed
to vanish linearly. -/
theorem sourceVariation_conj_bound {f KD : ℝ} {rho : Fin 4}
    {D : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} (hKD : 0 ≤ KD)
    (hD : ∀ x a b, |D x a b| ≤ KD * ‖x‖)
    {x : Fin 4 → ℝ} (hx : phatSq x ≠ 0) (a b : Fin 4) :
    |(transverseProjector (phatVec x) * sourceVariationMatrix f rho D x
        * transverseProjector (phatVec x)) a b| ≤ (4 * π + 64 * KD) * ‖x‖ := by
  have hu : 0 < normSqVec (phatVec x) := by
    rw [normSqVec_phatVec]
    exact lt_of_le_of_ne (phatSq_nonneg x) (Ne.symm hx)
  have hPb : ∀ c d : Fin 4, |transverseProjector (phatVec x) c d| ≤ 2 :=
    abs_transverseProjector_entry_le hu
  have hsplit : transverseProjector (phatVec x) * sourceVariationMatrix f rho D x
      * transverseProjector (phatVec x)
      = sinAtom (2 * x rho) • transverseProjector (phatVec x)
        + transverseProjector (phatVec x) * D x * transverseProjector (phatVec x) := by
    have he : transverseProjector (phatVec x) * sourceVariationMatrix f rho D x
        * transverseProjector (phatVec x)
        = transverseProjector (phatVec x) * wilsonBgZeroMatrix x rho
            * transverseProjector (phatVec x)
          + transverseProjector (phatVec x) * gaugeVariationMatrix f (phatVec x) rho
              * transverseProjector (phatVec x)
          + transverseProjector (phatVec x) * D x * transverseProjector (phatVec x) := by
      simp only [sourceVariationMatrix, Matrix.mul_add, Matrix.add_mul]
    rw [he, transverseProjector_conj_wilsonBgZeroMatrix x rho hx,
      transverseProjector_conj_gaugeVariationMatrix f x rho hx, add_zero]
  have hxr : |x rho| ≤ ‖x‖ := by
    have := norm_le_pi_norm x rho
    rwa [Real.norm_eq_abs] at this
  have hnorm0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hpi := Real.pi_pos
  have hsin : |sinAtom (2 * x rho)| ≤ 2 * π * ‖x‖ := by
    refine le_trans abs_sinAtom_two_mul_le ?_
    nlinarith
  have hPDP : |(transverseProjector (phatVec x) * D x * transverseProjector (phatVec x)) a b|
      ≤ 64 * KD * ‖x‖ := by
    have h1 : ∀ c d, |(transverseProjector (phatVec x) * D x) c d| ≤ 4 * (2 * (KD * ‖x‖)) :=
      abs_entry_mul_le (by norm_num) hPb (hD x)
    have h2 := abs_entry_mul_le (p := 4 * (2 * (KD * ‖x‖))) (q := 2)
      (by positivity) h1 hPb a b
    calc |(transverseProjector (phatVec x) * D x * transverseProjector (phatVec x)) a b|
        ≤ 4 * (4 * (2 * (KD * ‖x‖)) * 2) := h2
      _ = 64 * KD * ‖x‖ := by ring
  rw [hsplit, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  calc |sinAtom (2 * x rho) * transverseProjector (phatVec x) a b
        + (transverseProjector (phatVec x) * D x * transverseProjector (phatVec x)) a b|
      ≤ |sinAtom (2 * x rho) * transverseProjector (phatVec x) a b|
        + |(transverseProjector (phatVec x) * D x * transverseProjector (phatVec x)) a b| :=
        abs_add_le _ _
    _ = |sinAtom (2 * x rho)| * |transverseProjector (phatVec x) a b|
        + |(transverseProjector (phatVec x) * D x * transverseProjector (phatVec x)) a b| := by
        rw [abs_mul]
    _ ≤ (2 * π * ‖x‖) * 2 + 64 * KD * ‖x‖ := by
        have hprod : |sinAtom (2 * x rho)| * |transverseProjector (phatVec x) a b|
            ≤ (2 * π * ‖x‖) * 2 :=
          mul_le_mul hsin (hPb a b) (abs_nonneg _) (by positivity)
        linarith
    _ = (4 * π + 64 * KD) * ‖x‖ := by ring

/-! ## 6. Measurability of the literal source vertex -/

theorem measurable_wilsonBgZeroMatrix_entry (rho a b : Fin 4) :
    Measurable fun x : Fin 4 → ℝ => wilsonBgZeroMatrix x rho a b := by
  simp only [wilsonBgZeroMatrix_eq, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  have hsin : Measurable fun x : Fin 4 → ℝ => sinAtom (2 * x rho) := by
    have hc : Continuous fun x : Fin 4 → ℝ => sinAtom (2 * x rho) := by unfold sinAtom; fun_prop
    exact hc.measurable
  have hcos : Measurable fun x : Fin 4 → ℝ => Real.cos (π * x rho) / 2 := by
    have hc : Continuous fun x : Fin 4 → ℝ => Real.cos (π * x rho) / 2 := by fun_prop
    exact hc.measurable
  exact (hsin.mul measurable_const).sub (hcos.mul
    (((measurable_phatVec_apply a).mul measurable_const).add
      (measurable_const.mul (measurable_phatVec_apply b))))

theorem measurable_gaugeVariationMatrix_entry (f : ℝ) (rho a b : Fin 4) :
    Measurable fun x : Fin 4 → ℝ => gaugeVariationMatrix f (phatVec x) rho a b := by
  simp only [gaugeVariationMatrix_eq, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  have hs : Measurable fun x : Fin 4 → ℝ => ∑ ga : Fin 4, (phatVec x ga) ^ 2 :=
    Finset.measurable_sum _ fun c _ => (measurable_phatVec_apply c).pow_const 2
  exact ((measurable_const.div hs).mul
      ((measurable_const.mul (measurable_phatVec_apply b)).add
        ((measurable_phatVec_apply a).mul measurable_const))).sub
    (((measurable_const.mul (measurable_phatVec_apply rho)).div (hs.pow_const 2)).mul
      ((measurable_phatVec_apply a).mul (measurable_phatVec_apply b)))

theorem measurable_sourceVariationMatrix_entry (f : ℝ) (rho : Fin 4)
    {D : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    (hD : ∀ a b, Measurable fun x => D x a b) (a b : Fin 4) :
    Measurable fun x : Fin 4 → ℝ => sourceVariationMatrix f rho D x a b := by
  simp only [sourceVariationMatrix, Matrix.add_apply]
  exact ((measurable_wilsonBgZeroMatrix_entry rho a b).add
    (measurable_gaugeVariationMatrix_entry f rho a b)).add (hD a b)

/-! ## 7. Row A1a with the integrability obligation discharged -/

/-- **Row A1a from the literal one-loop trace, for interacting source data.**
The integrability hypothesis of `A1_beta_pos_ward` is now a theorem: it follows
from the linear vanishing of the Lorentz-diagonal averaging/constrained-projection
variation at zero momentum together with boundedness of the seagull insertion. -/
theorem A1_beta_pos_ward_of_linearVanishing
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {Adm : (ℕ → ℝ) → Prop} {g : ℕ → ℝ} {f d KD KW : ℝ}
    {Dm Wm : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {lamDet : ℕ → (ℕ → ℝ) → ι → ℝ} {lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ}
    {aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    {AInt AChart ALoc : ℕ → ℝ} {N : ℕ} {LamDet LamGauge theta : ℝ}
    (hKD : 0 ≤ KD) (hKW : 0 ≤ KW)
    (hDmeas : ∀ j h a b, Measurable fun x => Dm j h x a b)
    (hWmeas : ∀ j h a b, Measurable fun x => Wm j h x a b)
    (hD : ∀ j h x a b, a ≠ b → Dm j h x a b = 0)
    (hd : ∀ j h x a, |Dm j h x a a| ≤ d) (hd4 : d ≤ 1 / 4)
    (hDlin : ∀ j h x a b, |Dm j h x a b| ≤ KD * ‖x‖)
    (hWbd : ∀ j h, ∀ x ∈ puncturedCell, ∀ a b, |Wm j h x a b| ≤ KW)
    (hLd : ∀ j h i, |lamDet j h i| ≤ LamDet)
    (hLg : ∀ j h i, |lamGauge j h i| ≤ LamGauge)
    (hAInt : ∀ j h n, |aInt j h n| ≤ AInt n)
    (hAChart : ∀ j h n, |aChart j h n| ≤ AChart n)
    (hALoc : ∀ j h n, |aLoc j h n| ≤ ALoc n)
    (hsmall : ∀ j h, Adm h → 0 ≤ h j ∧ h j ≤ theta ∧
        h j * LamDet ≤ theta ∧ h j * LamGauge ≤ theta)
    (hth : theta < 1) (hth0 : 0 ≤ theta)
    (hadm : Adm g) (hg0 : ∀ j, 0 ≤ g j)
    (hgg : ∀ j, g j ≤ criticalCoupling (1 / 8388608 : ℝ)
      (Cbeta (sourceChannelCoefficient (Fintype.card ι) (Fintype.card κ)
        LamDet LamGauge theta AInt AChart ALoc N)))
    (j : ℕ) :
    (1 : ℝ) / 16777216 ≤ shellBetaOfSources
      (fun j' h => literalOneLoopIntegrand (sourceVariationMatrix f 1 (Dm j' h)) (Wm j' h))
      lamDet lamGauge aInt aChart aLoc N j g := by
  refine A1_beta_pos_ward (d := d) (Dm := Dm) (Wm := Wm) hD hd hd4 ?_
    hLd hLg hAInt hAChart hALoc hsmall hth hth0 hadm hg0 hgg j
  intro j' h
  refine literalOneLoopIntegrand_integrableOn_of_conjBound
    (cV := 4 * π + 64 * KD) (KW := KW) (by positivity) hKW
    (measurable_sourceVariationMatrix_entry f 1 (hDmeas j' h))
    (hWmeas j' h)
    (fun x => sourceVariationMatrix_transpose (hD j' h) x) ?_ (hWbd j' h)
  intro x hx a b
  exact sourceVariation_conj_bound hKD (hDlin j' h)
    (phatSq_ne_zero_of_mem_puncturedCell hx) a b

end YangMills

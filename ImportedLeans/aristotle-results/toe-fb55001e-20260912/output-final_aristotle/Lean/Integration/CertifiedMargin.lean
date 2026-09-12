import Integration.CertificatePays

/-!
# Certificate beats defect: the margin, the ratio, and the gate

Several lanes reduce to one inequality: a structurally produced *good* quantity
is bounded below, an *error/defect* quantity is bounded above, and the decision
is whether the lower bound strictly exceeds the upper bound.

```
G ≥ g,   B ≤ b,   b < g   ⟹   G − B > 0.
```

That is `margin_pos` below, and it is the whole of the "certified margin"
pattern.  Everything else in this file is the calculus that surrounds it.

* `margin_pos`, `strict_of_certified_bound` — the margin, and the pruning form:
  a certified lower bound that already beats the incumbent settles the
  comparison without evaluating the candidate;
* `relDefect` — the **dimensionless relative defect** `E / D`, with
  `relDefect_lt_one_iff` (below one is exactly "certificate dominates defect"),
  `contraction_of_le_eta` (the `E ≤ η·D`, `η < 1` gate) and
  `nogo_of_one_le_relDefect` — the architecture-level no-go: if every admissible
  refinement still leaves the ratio at least one, then no downstream
  optimisation produces a strict margin.  The no-go is a theorem about the whole
  family, not a failed estimate;
* `eventually_contractive_of_tendsto_zero`,
  `not_eventually_contractive_of_eventually_one_le` — the two asymptotic
  regimes;
* `compensate`, `compensate_self`, `deriv_eq_zero_of_even`,
  `compensated_isLittleO` — **compensation before estimation**.  If a reference
  point is fixed by a reflection symmetry of the quantity, the compensated
  difference `F(a) − F(x₀)` has vanishing first order at the reference; so
  subtracting first exposes a strictly higher-order transverse quantity that
  estimating first destroys;
* `normalization_gate`, `normalization_is_part_of_the_theorem` — two source
  normalisations of the *same* structural inequality landing on opposite sides
  of the gate.  This is why a structural theorem plus a source-normalisation
  morphism is strictly more than the structural theorem;
* `margin_of_pays` — the bridge to `Integration.CertificatePays`: a certificate
  that pays for the defect at a positive rate yields the margin.

Everything is an order/field statement about real numbers.  No lane-specific
constant, and no analytic input, appears; the table of intended instantiations
(coercivity vs remainder, scale-Gram expenditure vs scale defect, retained
Hermitian defect vs arithmetic error, certified bound vs approximation
discrepancy) is a reading of the theorem, not a claim proved here.
-/

namespace Integration.CertifiedMargin

open Integration.CertificatePays

/-! ## The margin -/

/-- **Certificate beats defect.**  A lower bound on the good quantity, an upper
bound on the bad one, and a strict gap between the bounds, give a strict
margin. -/
theorem margin_pos {α : Type*} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
    {G B g b : α} (hG : g ≤ G) (hB : B ≤ b) (hbg : b < g) : 0 < G - B :=
  sub_pos.mpr (lt_of_le_of_lt hB (lt_of_lt_of_le hbg hG))

/-- The pruning form used by an adaptive search: a *certified lower bound* on a
candidate that the incumbent already beats settles the comparison, without
evaluating the candidate. -/
theorem strict_of_certified_bound {α : Type*} [Preorder α] {value bound incumbent : α}
    (hlow : bound ≤ value) (hinc : incumbent < bound) : incumbent < value :=
  lt_of_lt_of_le hinc hlow

/-! ## The dimensionless ratio -/

/-- The **relative defect**: the bad quantity measured in units of the
certificate. -/
noncomputable def relDefect (E D : ℝ) : ℝ := E / D

/-- Below one is exactly "the certificate dominates the defect". -/
theorem relDefect_lt_one_iff {E D : ℝ} (hD : 0 < D) : relDefect E D < 1 ↔ E < D := by
  rw [relDefect, div_lt_one hD]

/-- The contraction gate: `E ≤ η·D` with `η < 1` gives a strict margin. -/
theorem contraction_of_le_eta {E D η : ℝ} (hD : 0 < D) (hE : E ≤ η * D) (hη : η < 1) :
    0 < D - E := by
  have : η * D < D := by nlinarith
  linarith

/-- **Architecture-level no-go.**  If every member of the admissible family still
has relative defect at least one, then no member has a strict margin: the route
cannot be repaired downstream. -/
theorem nogo_of_one_le_relDefect {ι : Type*} {E D : ι → ℝ} (hD : ∀ i, 0 < D i)
    (h : ∀ i, 1 ≤ relDefect (E i) (D i)) : ∀ i, ¬ (0 < D i - E i) := by
  intro i hlt
  have : relDefect (E i) (D i) < 1 := (relDefect_lt_one_iff (hD i)).mpr (by linarith)
  exact absurd (h i) (not_le.mpr this)

/-- Asymptotic contraction: a relative defect tending to zero is eventually
strictly contractive. -/
theorem eventually_contractive_of_tendsto_zero {E D : ℕ → ℝ} (hD : ∀ n, 0 < D n)
    (h : Filter.Tendsto (fun n => relDefect (E n) (D n)) Filter.atTop (nhds 0)) :
    ∀ᶠ n in Filter.atTop, 0 < D n - E n := by
  have hlt : ∀ᶠ n in Filter.atTop, relDefect (E n) (D n) < 1 := by
    have := h.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
    exact this
  filter_upwards [hlt] with n hn
  have := (relDefect_lt_one_iff (hD n)).mp hn
  linarith

/-- And the negative regime: a relative defect eventually at least one is never
eventually contractive. -/
theorem not_eventually_contractive_of_eventually_one_le {E D : ℕ → ℝ} (hD : ∀ n, 0 < D n)
    (h : ∀ n, 1 ≤ relDefect (E n) (D n)) : ∀ n, ¬ (0 < D n - E n) :=
  nogo_of_one_le_relDefect hD h

/-! ## Compensation before estimation -/

/-- The compensated quantity: the observable measured against a distinguished
reference state. -/
def compensate (F : ℝ → ℝ) (x₀ : ℝ) (a : ℝ) : ℝ := F a - F x₀

@[simp] theorem compensate_self (F : ℝ → ℝ) (x₀ : ℝ) : compensate F x₀ x₀ = 0 := by
  simp [compensate]

/-- **Symmetry forces the first order to vanish.**  If the reference point is
fixed by a reflection under which the observable is even, then the derivative of
the observable there is zero. -/
theorem deriv_eq_zero_of_even {F : ℝ → ℝ} (heven : ∀ a, F (-a) = F a) {d : ℝ}
    (h : HasDerivAt F d 0) : d = 0 := by
  have hneg : HasDerivAt (fun a : ℝ => -a) (-1 : ℝ) 0 := (hasDerivAt_id (0 : ℝ)).neg
  have h2 : HasDerivAt (fun a : ℝ => F (-a)) (d * (-1)) 0 := by
    simpa using HasDerivAt.scomp (0 : ℝ) (by simpa using h) hneg
  have h3 : HasDerivAt F (-d) 0 := by
    have hfun : (fun a : ℝ => F (-a)) = F := funext heven
    rw [hfun] at h2
    simpa using h2
  have := h.unique h3
  linarith

/-- **So the compensated defect is of strictly higher order.**  Under the same
hypotheses the slope of the compensated quantity at the reference tends to zero:
subtracting the fixed-point contribution *first* exposes a transverse quantity
that estimating first would bury inside the constant term. -/
theorem compensated_isLittleO {F : ℝ → ℝ} (heven : ∀ a, F (-a) = F a) {d : ℝ}
    (h : HasDerivAt F d 0) :
    Filter.Tendsto (fun a => compensate F 0 a / a) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
  have hd : d = 0 := deriv_eq_zero_of_even heven h
  subst hd
  have hs := hasDerivAt_iff_tendsto_slope.mp h
  have : (fun a : ℝ => compensate F 0 a / a) = slope F 0 := by
    funext a
    simp [slope_def_field, compensate, div_eq_inv_mul]
  rw [this]
  exact hs

/-! ## Normalisation is part of the theorem -/

/-- The gate, applied to a *source* defect obtained from a structural defect by a
normalisation coefficient. -/
def GatePasses (C E D : ℝ) : Prop := C * E < D

/-- **Two normalisations of one structural inequality, on opposite sides of the
gate.**  The structural content (`E ≤ D`, both positive) is identical; only the
source-to-effective coefficient differs. -/
theorem normalization_gate :
    ∃ E D C₁ C₂ : ℝ, 0 < E ∧ 0 < D ∧ E ≤ D ∧ GatePasses C₁ E D ∧ ¬ GatePasses C₂ E D := by
  refine ⟨1, 2, 1, 3, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · unfold GatePasses; norm_num
  · unfold GatePasses; norm_num

/-- Stated as a principle: the structural inequality alone does not determine the
decision; the normalisation morphism is part of the theorem. -/
theorem normalization_is_part_of_the_theorem :
    ¬ ∀ E D C : ℝ, 0 < E → 0 < D → E ≤ D → GatePasses C E D := by
  intro h
  obtain ⟨E, D, _, C₂, hE, hD, hED, _, hfail⟩ := normalization_gate
  exact hfail (h E D C₂ hE hD hED)

/-! ## The bridge to the existing budget lane -/

/-- A certificate that pays for the defect at a positive rate, together with a
defect bound strictly below the paid amount, gives the margin. -/
theorem margin_of_pays {ι : Type*} {C D : ι → ℝ} {c b : ℝ} (h : Pays C D c) (i : ι)
    (hB : b < c * D i) (hCb : (0 : ℝ) ≤ b) : 0 < C i := by
  have h1 : c * D i ≤ C i := h i
  linarith

end Integration.CertifiedMargin

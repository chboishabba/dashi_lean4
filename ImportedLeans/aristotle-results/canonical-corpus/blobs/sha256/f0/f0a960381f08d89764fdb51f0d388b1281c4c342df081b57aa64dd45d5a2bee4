/-
# Assembling the De Giorgi iteration into an oscillation contraction

`DeGiorgiRecurrence.lean` produces the fast-convergence recurrence for the
level-set energies `Y_n = ∫_{w>k_n}(w−k_n)²` along the dyadic levels
`k_n = k_∞(1−2^{-n})`, and `DeGiorgiIteration.lean` produces `Y_n → 0`.
`AncientOscillationContraction.lean` shows that a *scale-independent*
oscillation contraction `osc_{Q_{θR}}U ≤ (1−σ)osc_{Q_R}U` forces a bounded
ancient field to be constant, and reduces that contraction to a single
unit-scale improvement.

This file supplies the two assembly steps that sit between them, and which the
final `ScaleInvariantModulusOscillationContraction` statement has to traverse.

* `ClayNS.ae_le_of_levelEnergy_tendsto_zero` — the De Giorgi *conclusion*:
  once the level-set energies along the dyadic levels tend to `0`, the density
  actually satisfies the pointwise (a.e.) bound `w ≤ k_∞`.  This is the step
  that converts the iteration into a genuine supremum bound.
* `ClayNS.deGiorgi_ae_le_of_embedding` — the same statement fed directly by the
  parabolic embedding hypothesis and the smallness of `Y_0`: the complete
  "energy smallness ⇒ pointwise level bound" package.
* `ClayNS.norm_le_of_forall_unit_inner_le`, `ClayNS.oscOn_le_of_forall_direction`,
  `ClayNS.inner_sub_le_oscOn` — the reduction of the *vector-valued* oscillation
  to the scalar oscillations of the directional components `⟪e,U⟫`, `‖e‖ = 1`.
  This is what lets a scalar De Giorgi improvement, applied to each component,
  contract the oscillation of the field itself.
* `ClayNS.oscOn_contract_of_directional_dichotomy` — the *assembly with
  constants*: given, for every direction `e`, the standard De Giorgi
  alternative (either the supremum of `⟪e,U⟫` drops by `σ·osc` on the smaller
  set, or the infimum rises by `σ·osc`), the vector oscillation contracts by
  the factor `1−σ`, with the *same* `σ`.
* `ClayNS.OscDichotomy`, `ClayNS.unit_step_of_dichotomy` — the same statement at
  the unit parabolic scale.
* `ClayNS.scaleInvariant_modulus_oscillation_contraction` — combined with the
  parabolic rescaling closure of the ancient class, the directional dichotomy at
  the *unit* scale yields the scale-independent contraction at **every** scale,
  with `σ` independent of `R`.
* `ClayNS.le_of_ae_le_restrict_of_continuous`, `ClayNS.parCyl_subset_closure_interior`,
  `ClayNS.oscDichotomy_of_ae_dichotomy` — the upgrade of the *almost-everywhere*
  De Giorgi conclusion to the pointwise statement the dichotomy requires, using
  continuity of the ancient profile and the fact that the parabolic cylinder is
  the closure of its interior.
* `ClayNS.ancient_constant_of_directional_dichotomy`,
  `ClayNS.false_of_defect_and_directional_dichotomy` — the resulting Liouville
  statement and the contradiction with a normalized defect.

What is *not* proved here is the directional dichotomy itself for the ancient
Navier–Stokes profile: that is the analytic input (the Caccioppoli/level-set
estimate for the modulus increments), and it enters every statement below as an
explicit hypothesis.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.DeGiorgiRecurrence
import RequestProject.NavierStokes.AncientOscillationContraction

open MeasureTheory Filter Topology Metric Set

open scoped BigOperators ENNReal

noncomputable section

namespace ClayNS

/-! ## From vanishing level-set energy to a pointwise level bound -/

section DeGiorgiTail

variable {X : Type*} [MeasurableSpace X]

/-- The dyadic De Giorgi levels lie below their limit. -/
lemma deGiorgiLevel_le (kinf : ℝ) (hk : 0 ≤ kinf) (n : ℕ) : deGiorgiLevel kinf n ≤ kinf := by
  have h2 : (0:ℝ) < (2 : ℝ) ^ (-(n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have : deGiorgiLevel kinf n = kinf - kinf * (2 : ℝ) ^ (-(n : ℝ)) := by
    simp only [deGiorgiLevel]; ring
  rw [this]
  nlinarith

/-- The truncation energy at the limiting level is below every energy along the
dyadic sequence. -/
lemma levelEnergy_limit_le {mu : Measure X} [IsFiniteMeasure mu] {w : X → ℝ}
    (hw : Measurable w) {Mb : ℝ} (hb : ∀ x, |w x| ≤ Mb) {kinf : ℝ} (hk : 0 ≤ kinf) (n : ℕ) :
    (∫ x in levelSet w kinf, (w x - kinf) ^ 2 ∂mu)
      ≤ levelEnergy mu w (deGiorgiLevel kinf n) := by
  set k := deGiorgiLevel kinf n with hkdef
  have hkle : k ≤ kinf := deGiorgiLevel_le kinf hk n
  have hsub : levelSet w kinf ⊆ levelSet w k := levelSet_subset hkle
  have hintk : IntegrableOn (fun x => (w x - k) ^ 2) (levelSet w k) mu :=
    ((memLp_sub_sq hw hb k 1).integrable (le_refl 1)).integrableOn
  have hintinf : IntegrableOn (fun x => (w x - kinf) ^ 2) (levelSet w kinf) mu :=
    ((memLp_sub_sq hw hb kinf 1).integrable (le_refl 1)).integrableOn
  have hstep1 : (∫ x in levelSet w kinf, (w x - kinf) ^ 2 ∂mu)
      ≤ ∫ x in levelSet w kinf, (w x - k) ^ 2 ∂mu := by
    refine setIntegral_mono_on hintinf (hintk.mono_set hsub)
      (measurableSet_levelSet hw kinf) ?_
    intro x hx
    have hx' : kinf < w x := hx
    nlinarith
  have hstep2 : (∫ x in levelSet w kinf, (w x - k) ^ 2 ∂mu)
      ≤ ∫ x in levelSet w k, (w x - k) ^ 2 ∂mu := by
    refine setIntegral_mono_set hintk ?_ (HasSubset.Subset.eventuallyLE hsub)
    exact Filter.Eventually.of_forall fun x => sq_nonneg _
  exact le_trans hstep1 hstep2

/-- **The De Giorgi conclusion.**  If the level-set energies along the dyadic
levels `k_n = k_∞(1−2^{-n})` tend to zero, then `w ≤ k_∞` almost everywhere.
This is the step that turns the iteration into a genuine supremum bound. -/
theorem ae_le_of_levelEnergy_tendsto_zero {mu : Measure X} [IsFiniteMeasure mu] {w : X → ℝ}
    (hw : Measurable w) {Mb : ℝ} (hb : ∀ x, |w x| ≤ Mb) {kinf : ℝ} (hk : 0 ≤ kinf)
    (hY : Tendsto (fun n => levelEnergy mu w (deGiorgiLevel kinf n)) atTop (nhds 0)) :
    ∀ᵐ x ∂mu, w x ≤ kinf := by
  set A : Set X := levelSet w kinf with hA
  have hAm : MeasurableSet A := measurableSet_levelSet hw kinf
  have hint : IntegrableOn (fun x => (w x - kinf) ^ 2) A mu :=
    ((memLp_sub_sq hw hb kinf 1).integrable (le_refl 1)).integrableOn
  have hle0 : (∫ x in A, (w x - kinf) ^ 2 ∂mu) ≤ 0 :=
    ge_of_tendsto hY (Filter.Eventually.of_forall
      fun n => levelEnergy_limit_le hw hb hk n)
  have hge0 : 0 ≤ ∫ x in A, (w x - kinf) ^ 2 ∂mu :=
    setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall fun _x => sq_nonneg _)
  have hzero : (∫ x in A, (w x - kinf) ^ 2 ∂mu) = 0 := le_antisymm hle0 hge0
  have hae : (fun x => (w x - kinf) ^ 2) =ᵐ[mu.restrict A] 0 := by
    refine (integral_eq_zero_iff_of_nonneg_ae ?_ hint).1 hzero
    exact Filter.Eventually.of_forall fun _x => sq_nonneg _
  have hae' : ∀ᵐ x ∂mu, x ∈ A → (w x - kinf) ^ 2 = 0 := by
    have := (ae_restrict_iff' hAm).1 hae
    filter_upwards [this] with x hx hxA
    simpa using hx hxA
  filter_upwards [hae'] with x hx
  by_contra hcon
  push_neg at hcon
  have hxA : x ∈ A := hcon
  have := hx hxA
  have : w x = kinf := by nlinarith
  exact absurd hxA (by simp [hA, levelSet, this])

/-- **The complete De Giorgi package.**  The parabolic embedding hypothesis plus
smallness of the initial level energy give the pointwise bound `w ≤ k_∞` a.e. -/
theorem deGiorgi_ae_le_of_embedding {mu : Measure X} [IsFiniteMeasure mu] {w : X → ℝ}
    (hw : Measurable w) {Mb : ℝ} (hb : ∀ x, |w x| ≤ Mb) {kinf CS : ℝ} (hk : 0 < kinf)
    (hCS : 0 < CS)
    (hEmb : ∀ n : ℕ,
      (∫ x in levelSet w (deGiorgiLevel kinf (n + 1)),
          ((w x - deGiorgiLevel kinf (n + 1)) ^ 2) ^ (5 / 3 : ℝ) ∂mu)
        ≤ CS * ((4 : ℝ) ^ (n : ℝ) * levelEnergy mu w (deGiorgiLevel kinf n)) ^ (5 / 3 : ℝ))
    (hsmall : levelEnergy mu w (deGiorgiLevel kinf 0)
      ≤ (CS ^ (3 / 5 : ℝ) * (4 : ℝ) ^ (2 / 5 : ℝ) * kinf ^ (-4 / 5 : ℝ)) ^ (-1 / (2 / 5 : ℝ))
        * ((4 : ℝ) ^ (7 / 5 : ℝ)) ^ (-1 / (2 / 5 : ℝ) ^ 2)) :
    ∀ᵐ x ∂mu, w x ≤ kinf := by
  refine ae_le_of_levelEnergy_tendsto_zero hw hb hk.le ?_
  refine deGiorgi_recurrence_tendsto_zero
    (Y := fun n => levelEnergy mu w (deGiorgiLevel kinf n))
    (M := fun n => levelMeasure mu w (deGiorgiLevel kinf n))
    (fun n => levelEnergy_nonneg mu w _) (fun n => levelMeasure_nonneg mu w _) hCS hk
    (fun n => deGiorgi_level_step_measure hw hb (hEmb n))
    (fun n => chebyshev_deGiorgiLevel hw hb hk n) hsmall

end DeGiorgiTail

/-! ## Reduction of the vector oscillation to directional components -/

/-- A vector whose inner product against every unit vector is `≤ c` has norm
`≤ c`. -/
lemma norm_le_of_forall_unit_inner_le {v : E3} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ e : E3, ‖e‖ = 1 → inner ℝ e v ≤ c) : ‖v‖ ≤ c := by
  rcases eq_or_ne v 0 with rfl | hv
  · simpa using hc
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hne : ‖(‖v‖⁻¹ • v : E3)‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have hkey := h _ hne
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at hkey
    have hveq : ‖v‖ = ‖v‖⁻¹ * ‖v‖ ^ 2 := by field_simp
    rw [hveq]
    exact hkey

/-- **Directional control of the oscillation.**  If every directional component
`⟪e,f⟫`, `‖e‖ = 1`, oscillates by at most `c` on `S`, then so does `f`. -/
theorem oscOn_le_of_forall_direction {α : Type*} (f : α → E3) (S : Set α) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ e : E3, ‖e‖ = 1 → ∀ x ∈ S, ∀ y ∈ S,
      inner ℝ e (f x) - inner ℝ e (f y) ≤ c) :
    oscOn f S ≤ c := by
  refine Metric.diam_le_of_forall_dist_le hc ?_
  rintro p ⟨x, hx, rfl⟩ q ⟨y, hy, rfl⟩
  rw [dist_eq_norm]
  refine norm_le_of_forall_unit_inner_le hc ?_
  intro e he
  rw [inner_sub_right]
  exact h e he x hx y hy

/-- Conversely, each directional increment is below the oscillation. -/
lemma inner_sub_le_oscOn {α : Type*} {f : α → E3} {S : Set α}
    (hb : Bornology.IsBounded (f '' S)) {e : E3} (he : ‖e‖ ≤ 1) {x y : α}
    (hx : x ∈ S) (hy : y ∈ S) :
    inner ℝ e (f x) - inner ℝ e (f y) ≤ oscOn f S := by
  have h1 : inner ℝ e (f x) - inner ℝ e (f y) = inner ℝ e (f x - f y) :=
    (inner_sub_right e (f x) (f y)).symm
  rw [h1]
  calc inner ℝ e (f x - f y) ≤ ‖e‖ * ‖f x - f y‖ := real_inner_le_norm _ _
    _ ≤ 1 * ‖f x - f y‖ := by nlinarith [norm_nonneg (f x - f y)]
    _ = ‖f x - f y‖ := one_mul _
    _ ≤ oscOn f S := norm_sub_le_oscOn hb hx hy

/-! ## The contraction from the De Giorgi alternative -/

/-- **Assembly with constants.**  Suppose that for every direction `e` the
standard De Giorgi alternative holds on the pair `S' ⊆ S`: either the component
`⟪e,f⟫` stays `σ·osc_S f` below a level `Me` that is within `osc_S f` of all its
values on `S`, or it stays `σ·osc_S f` above a level `me` that is within
`osc_S f` of all its values on `S`.  Then the *vector* oscillation contracts,
with the same `σ`:

`osc_{S'} f ≤ (1−σ)·osc_S f`. -/
theorem oscOn_contract_of_directional_dichotomy {α : Type*} (f : α → E3) (S S' : Set α)
    {sig : ℝ} (hs1 : sig ≤ 1) (hS' : S' ⊆ S)
    (hdich : ∀ e : E3, ‖e‖ = 1 →
      (∃ Me : ℝ, (∀ x ∈ S, Me - oscOn f S ≤ inner ℝ e (f x)) ∧
        (∀ x ∈ S', inner ℝ e (f x) ≤ Me - sig * oscOn f S)) ∨
      (∃ me : ℝ, (∀ x ∈ S, inner ℝ e (f x) ≤ me + oscOn f S) ∧
        (∀ x ∈ S', me + sig * oscOn f S ≤ inner ℝ e (f x)))) :
    oscOn f S' ≤ (1 - sig) * oscOn f S := by
  have hD : 0 ≤ oscOn f S := oscOn_nonneg f S
  have hc : 0 ≤ (1 - sig) * oscOn f S := mul_nonneg (by linarith) hD
  refine oscOn_le_of_forall_direction f S' hc ?_
  intro e he x hx y hy
  have hexp : (1 - sig) * oscOn f S = oscOn f S - sig * oscOn f S := by ring
  rw [hexp]
  rcases hdich e he with ⟨Me, hlow, hup⟩ | ⟨me, hup, hlow⟩
  · have h1 := hup x hx
    have h2 := hlow y (hS' hy)
    linarith
  · have h1 := hup x (hS' hx)
    have h2 := hlow y hy
    linarith

/-! ## The unit-scale statement and its scale-invariant consequence -/

/-- Parabolic cylinders are nested. -/
lemma parCyl_subset {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    parCyl theta ⊆ parCyl 1 := by
  rintro z ⟨ht1, ht2, hx⟩
  refine ⟨?_, ht2, ?_⟩
  · have : theta ^ 2 ≤ 1 ^ 2 := by nlinarith
    linarith
  · linarith

/-- **The De Giorgi alternative at the unit parabolic scale.**  For each unit
direction `e`, the component `⟪e,U⟫` either loses `σ·osc_{Q_1}U` from the top or
gains `σ·osc_{Q_1}U` from the bottom when passing from `Q_1` to `Q_θ`. -/
def OscDichotomy (U : STime → E3) (theta sig : ℝ) : Prop :=
  ∀ e : E3, ‖e‖ = 1 →
    (∃ Me : ℝ, (∀ z ∈ parCyl 1, Me - oscCyl U 1 ≤ inner ℝ e (U z)) ∧
      (∀ z ∈ parCyl theta, inner ℝ e (U z) ≤ Me - sig * oscCyl U 1)) ∨
    (∃ me : ℝ, (∀ z ∈ parCyl 1, inner ℝ e (U z) ≤ me + oscCyl U 1) ∧
      (∀ z ∈ parCyl theta, me + sig * oscCyl U 1 ≤ inner ℝ e (U z)))

/-- The unit-scale improvement produced by the De Giorgi alternative. -/
theorem unit_step_of_dichotomy (U : STime → E3) {theta sig : ℝ}
    (hth0 : 0 ≤ theta) (hth1 : theta ≤ 1) (hs1 : sig ≤ 1)
    (h : OscDichotomy U theta sig) :
    oscCyl U theta ≤ (1 - sig) * oscCyl U 1 :=
  oscOn_contract_of_directional_dichotomy U (parCyl 1) (parCyl theta) hs1
    (parCyl_subset hth0 hth1) h

/-- **`ScaleInvariantModulusOscillationContraction`.**  If the ancient class is
closed under the parabolic rescaling `U ↦ λU(λ²·,λ·)` and every member satisfies
the unit-scale De Giorgi alternative with parameters `θ, σ`, then every member
contracts its oscillation at **every** scale, with `σ` independent of `R`:

`osc_{Q_{θR}}U ≤ (1−σ)·osc_{Q_R}U`  for all `R > 0`. -/
theorem scaleInvariant_modulus_oscillation_contraction
    (Cls : (STime → E3) → Prop) {theta sig : ℝ}
    (hth0 : 0 ≤ theta) (hth1 : theta ≤ 1) (hs1 : sig ≤ 1)
    (hclosed : ∀ (U : STime → E3) (lam : ℝ), Cls U → 0 < lam → Cls (parRescale U lam))
    (hdich : ∀ U : STime → E3, Cls U → OscDichotomy U theta sig)
    (U : STime → E3) (hU : Cls U) {R : ℝ} (hR : 0 < R) :
    oscCyl U (theta * R) ≤ (1 - sig) * oscCyl U R :=
  contraction_of_unit_step Cls hclosed
    (fun V hV => unit_step_of_dichotomy V hth0 hth1 hs1 (hdich V hV)) U hU hR

/-- **Liouville from the De Giorgi alternative.**  A bounded member of a
rescaling-closed class satisfying the unit-scale alternative with `0 < σ ≤ 1`
and `0 < θ < 1` is constant on the ancient region. -/
theorem ancient_constant_of_directional_dichotomy
    (Cls : (STime → E3) → Prop) {theta sig : ℝ}
    (hth0 : 0 < theta) (hth1 : theta < 1) (hs0 : 0 < sig) (hs1 : sig ≤ 1)
    (hclosed : ∀ (U : STime → E3) (lam : ℝ), Cls U → 0 < lam → Cls (parRescale U lam))
    (hdich : ∀ U : STime → E3, Cls U → OscDichotomy U theta sig)
    (U : STime → E3) (hU : Cls U) {K : ℝ} (hK : 0 ≤ K) (hb : ∀ z, ‖U z‖ ≤ K) :
    ∃ b : E3, ∀ z : STime, z.1 ≤ 0 → U z = b :=
  ancient_constant_of_oscillation_contraction U hK hb hth0 hth1 hs0 hs1
    (fun _R hR => scaleInvariant_modulus_oscillation_contraction Cls hth0.le hth1.le hs1
      hclosed hdich U hU hR)

/-- **The C arrow closes the route.**  A bounded ancient member of the class
cannot simultaneously satisfy the unit-scale De Giorgi alternative and carry a
nonzero normalized oscillation defect. -/
theorem false_of_defect_and_directional_dichotomy
    (Cls : (STime → E3) → Prop) {theta sig R0 c0 : ℝ}
    (hth0 : 0 < theta) (hth1 : theta < 1) (hs0 : 0 < sig) (hs1 : sig ≤ 1)
    (hclosed : ∀ (U : STime → E3) (lam : ℝ), Cls U → 0 < lam → Cls (parRescale U lam))
    (hdich : ∀ U : STime → E3, Cls U → OscDichotomy U theta sig)
    (U : STime → E3) (hU : Cls U) {K : ℝ} (hK : 0 ≤ K) (hb : ∀ z, ‖U z‖ ≤ K)
    (hc0 : 0 < c0)
    (hdefect : c0 ≤ oscOn (fun x : E3 => U (0, x)) (Metric.ball 0 R0)) : False :=
  false_of_defect_and_oscillation_contraction U hK hb hth0 hth1 hs0 hs1
    (fun _R hR => scaleInvariant_modulus_oscillation_contraction Cls hth0.le hth1.le hs1
      hclosed hdich U hU hR) hc0 hdefect

/-! ## From the almost-everywhere level bound to the pointwise one -/

/-- A continuous function that satisfies a level bound almost everywhere on a
set satisfies it *everywhere* on that set, provided the set is contained in the
closure of its interior.  This is the step that converts the (measure-theoretic)
De Giorgi conclusion into the pointwise supremum bound the oscillation
dichotomy needs. -/
lemma le_of_ae_le_restrict_of_continuous {w : STime → ℝ} (hw : Continuous w)
    {S : Set STime} {k : ℝ} (hS : S ⊆ closure (interior S))
    (hae : ∀ᵐ z ∂(volume.restrict S), w z ≤ k) : ∀ z ∈ S, w z ≤ k := by
  intro z0 hz0
  by_contra hcon
  push_neg at hcon
  set O : Set STime := {z | k < w z} with hO
  have hOopen : IsOpen O := isOpen_lt continuous_const hw
  have hOmeas : MeasurableSet O := hOopen.measurableSet
  have hne : (O ∩ interior S).Nonempty :=
    mem_closure_iff.1 (hS hz0) O hOopen hcon
  have hpos : 0 < volume (O ∩ interior S) :=
    (hOopen.inter isOpen_interior).measure_pos volume hne
  have h0 : (volume.restrict S) {z : STime | ¬ w z ≤ k} = 0 := ae_iff.1 hae
  have hEq : {z : STime | ¬ w z ≤ k} = O := by
    ext z; simp [hO, not_le]
  rw [hEq, Measure.restrict_apply hOmeas] at h0
  have hle : volume (O ∩ interior S) ≤ volume (O ∩ S) :=
    measure_mono (Set.inter_subset_inter_right _ interior_subset)
  rw [h0] at hle
  exact absurd (le_antisymm hle (zero_le _)) (ne_of_gt hpos)

/-- The parabolic cylinder is the closure of its interior: its only boundary
points inside it are the final-time ones, which are limits from below. -/
lemma parCyl_subset_closure_interior (theta : ℝ) :
    parCyl theta ⊆ closure (interior (parCyl theta)) := by
  set O : Set STime := {z : STime | -(theta ^ 2) < z.1 ∧ z.1 < 0 ∧ ‖z.2‖ < theta} with hOdef
  have hOopen : IsOpen O := by
    have h1 : IsOpen {z : STime | -(theta ^ 2) < z.1} :=
      isOpen_lt continuous_const continuous_fst
    have h2 : IsOpen {z : STime | z.1 < 0} := isOpen_lt continuous_fst continuous_const
    have h3 : IsOpen {z : STime | ‖z.2‖ < theta} :=
      isOpen_lt continuous_snd.norm continuous_const
    have : O = {z : STime | -(theta ^ 2) < z.1} ∩
        ({z : STime | z.1 < 0} ∩ {z : STime | ‖z.2‖ < theta}) := by
      ext z; simp [hOdef]
    rw [this]
    exact h1.inter (h2.inter h3)
  have hOsub : O ⊆ parCyl theta := by
    rintro z ⟨h1, h2, h3⟩
    exact ⟨h1, h2.le, h3⟩
  have hOint : O ⊆ interior (parCyl theta) :=
    interior_maximal hOsub hOopen
  refine fun z hz => closure_mono hOint ?_
  obtain ⟨h1, h2, h3⟩ := hz
  refine Metric.mem_closure_iff.2 ?_
  intro eps heps
  set d : ℝ := min (eps / 2) ((z.1 + theta ^ 2) / 2) with hd
  have hd1 : 0 < eps / 2 := by linarith
  have hd2 : 0 < (z.1 + theta ^ 2) / 2 := by linarith
  have hdpos : 0 < d := lt_min hd1 hd2
  refine ⟨(z.1 - d, z.2), ⟨?_, ?_, h3⟩, ?_⟩
  · have : d ≤ (z.1 + theta ^ 2) / 2 := min_le_right _ _
    linarith
  · linarith
  · have hdist : dist ((z.1 - d, z.2) : STime) z = max (dist (z.1 - d) z.1) (dist z.2 z.2) :=
      Prod.dist_eq
    have h1' : dist (z.1 - d) z.1 = d := by
      rw [Real.dist_eq]; simp [abs_of_nonneg hdpos.le]
    have h2' : d ≤ eps / 2 := min_le_left _ _
    rw [dist_comm, hdist, h1']
    simp only [dist_self, max_eq_left hdpos.le]
    linarith

/-- **The De Giorgi alternative from its almost-everywhere form.**  For a
continuous ancient field, an alternative holding almost everywhere on the small
parabolic cylinder upgrades to the pointwise `OscDichotomy` used by the
contraction. -/
theorem oscDichotomy_of_ae_dichotomy (U : STime → E3) (hU : Continuous U)
    {theta sig : ℝ}
    (h : ∀ e : E3, ‖e‖ = 1 →
      (∃ Me : ℝ, (∀ z ∈ parCyl 1, Me - oscCyl U 1 ≤ inner ℝ e (U z)) ∧
        (∀ᵐ z ∂(volume.restrict (parCyl theta)),
          inner ℝ e (U z) ≤ Me - sig * oscCyl U 1)) ∨
      (∃ me : ℝ, (∀ z ∈ parCyl 1, inner ℝ e (U z) ≤ me + oscCyl U 1) ∧
        (∀ᵐ z ∂(volume.restrict (parCyl theta)),
          me + sig * oscCyl U 1 ≤ inner ℝ e (U z)))) :
    OscDichotomy U theta sig := by
  intro e he
  have hcont : Continuous fun z : STime => inner ℝ e (U z) :=
    (continuous_const.inner hU)
  rcases h e he with ⟨Me, hlow, hae⟩ | ⟨me, hup, hae⟩
  · refine Or.inl ⟨Me, hlow, ?_⟩
    exact le_of_ae_le_restrict_of_continuous hcont (parCyl_subset_closure_interior theta) hae
  · refine Or.inr ⟨me, hup, ?_⟩
    have hcont' : Continuous fun z : STime => -inner ℝ e (U z) := hcont.neg
    have hae' : ∀ᵐ z ∂(volume.restrict (parCyl theta)),
        (fun z : STime => -inner ℝ e (U z)) z ≤ -(me + sig * oscCyl U 1) := by
      filter_upwards [hae] with z hz
      simpa using hz
    have := le_of_ae_le_restrict_of_continuous hcont'
      (parCyl_subset_closure_interior theta) hae'
    intro z hz
    have := this z hz
    simpa using this

end ClayNS

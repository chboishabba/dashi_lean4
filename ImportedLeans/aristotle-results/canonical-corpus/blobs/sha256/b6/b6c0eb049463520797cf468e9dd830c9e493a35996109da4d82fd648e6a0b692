/-
# The directional level drop: the exact remaining C obligation

`DeGiorgiOscillationAssembly.lean` proves everything downstream of the
De Giorgi alternative: `OscDichotomy U θ σ` gives the oscillation contraction
`osc_{Q_{θR}}U ≤ (1−σ)·osc_{Q_R}U` at *every* scale, hence constancy of a
bounded ancient profile, hence the contradiction with a normalized defect.

`OscDichotomy` is stated with an *existentially quantified* level `Me` (resp.
`me`) that has to be within `osc_{Q_1}U` of every value of the component on
`Q_1`.  This file removes that existential: the natural level is the directional
supremum (resp. infimum) itself,

  `S_e = sup_{Q_1} ⟪e,U⟫`,   `I_e = inf_{Q_1} ⟪e,U⟫`,     (`ClayNS.dirSup`, `ClayNS.dirInf`)

and `ClayNS.dirSup_sub_oscCyl_le` / `ClayNS.le_dirInf_add_oscCyl` show these
levels automatically satisfy the required proximity condition, for any bounded
field.  So the whole of the De Giorgi side of the Clay route reduces to the
single statement

  `ClayNS.DirectionalLevelDrop U θ σ`:
    for every unit direction `e`, either
      `⟪e,U⟫ ≤ S_e − σ·osc_{Q_1}U` a.e. on `Q_θ`,
    or
      `I_e + σ·osc_{Q_1}U ≤ ⟪e,U⟫` a.e. on `Q_θ`.

`ClayNS.oscDichotomy_of_directionalLevelDrop` proves
`DirectionalLevelDrop ⟹ OscDichotomy`, and
`ClayNS.ancient_constant_of_directionalLevelDrop`,
`ClayNS.false_of_defect_and_directionalLevelDrop` carry that all the way to the
Liouville statement and the contradiction.

`ClayNS.measure_dichotomy_at_level` is the first (measure-theoretic) step of the
classical De Giorgi alternative, proved here in the form it is used: at any
level, one of the two complementary occupation sets has at most half the measure
of the cylinder.

**What is not proved here.**  `DirectionalLevelDrop` for the actual ancient
Navier–Stokes class is *not* established, and it is the exact remaining
obligation on the C side.  Its classical proof (measure smallness ⇒ pointwise
drop) needs a Caccioppoli inequality for the truncations of the scalar component
`⟪e,U⟫`, and for the Navier–Stokes system the components are coupled through the
nonlocal pressure, so no such component-wise Caccioppoli inequality is available
from the material in this repository.  Nothing below assumes it: it appears as
an explicit hypothesis wherever it is used.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.DeGiorgiOscillationAssembly

open MeasureTheory Filter Topology Metric Set

open scoped BigOperators ENNReal

noncomputable section

namespace ClayNS

/-! ## The directional supremum and infimum on the unit cylinder -/

/-- The supremum of the component `⟪e,U⟫` over the unit parabolic cylinder. -/
def dirSup (U : STime → E3) (e : E3) : ℝ := sSup ((fun z => inner ℝ e (U z)) '' parCyl 1)

/-- The infimum of the component `⟪e,U⟫` over the unit parabolic cylinder. -/
def dirInf (U : STime → E3) (e : E3) : ℝ := sInf ((fun z => inner ℝ e (U z)) '' parCyl 1)

lemma zero_mem_parCyl_one : ((0 : ℝ), (0 : E3)) ∈ parCyl 1 := by
  refine ⟨by norm_num, le_refl 0, ?_⟩
  simp

lemma parCyl_one_nonempty : (parCyl 1).Nonempty := ⟨_, zero_mem_parCyl_one⟩

lemma dirImage_nonempty (U : STime → E3) (e : E3) :
    ((fun z => inner ℝ e (U z)) '' parCyl 1).Nonempty :=
  parCyl_one_nonempty.image _

lemma isBounded_image_of_bound {U : STime → E3} {K : ℝ} (hb : ∀ z, ‖U z‖ ≤ K)
    (S : Set STime) : Bornology.IsBounded (U '' S) := by
  refine (Metric.isBounded_closedBall (x := (0 : E3)) (r := K)).subset ?_
  rintro p ⟨z, _, rfl⟩
  simpa [Metric.mem_closedBall, dist_eq_norm] using hb z

lemma dirImage_bddAbove {U : STime → E3} {K : ℝ} (hb : ∀ z, ‖U z‖ ≤ K) {e : E3}
    (he : ‖e‖ ≤ 1) : BddAbove ((fun z => inner ℝ e (U z)) '' parCyl 1) := by
  refine ⟨K, ?_⟩
  rintro p ⟨z, _, rfl⟩
  calc (inner ℝ e (U z) : ℝ) ≤ ‖e‖ * ‖U z‖ := real_inner_le_norm _ _
    _ ≤ 1 * K := by nlinarith [norm_nonneg (U z), hb z, norm_nonneg e]
    _ = K := one_mul _

lemma dirImage_bddBelow {U : STime → E3} {K : ℝ} (hb : ∀ z, ‖U z‖ ≤ K) {e : E3}
    (he : ‖e‖ ≤ 1) : BddBelow ((fun z => inner ℝ e (U z)) '' parCyl 1) := by
  refine ⟨-K, ?_⟩
  rintro p ⟨z, _, rfl⟩
  have h1 : (-(inner ℝ e (U z)) : ℝ) = inner ℝ (-e) (U z) := by
    rw [inner_neg_left]
  have h2 : (inner ℝ (-e) (U z) : ℝ) ≤ ‖-e‖ * ‖U z‖ := real_inner_le_norm _ _
  have h3 : ‖-e‖ = ‖e‖ := norm_neg e
  have h4 : (-(inner ℝ e (U z)) : ℝ) ≤ K := by
    rw [h1]
    calc (inner ℝ (-e) (U z) : ℝ) ≤ ‖-e‖ * ‖U z‖ := h2
      _ ≤ 1 * K := by
        rw [h3]; nlinarith [norm_nonneg (U z), hb z, norm_nonneg e]
      _ = K := one_mul _
  linarith

/-- **The directional supremum is an admissible De Giorgi level.**  For a bounded
field, every value of the component on `Q_1` is within `osc_{Q_1}U` of the
directional supremum. -/
theorem dirSup_sub_oscCyl_le {U : STime → E3} {K : ℝ} (hb : ∀ z, ‖U z‖ ≤ K)
    {e : E3} (he : ‖e‖ ≤ 1) {z : STime} (hz : z ∈ parCyl 1) :
    dirSup U e - oscCyl U 1 ≤ inner ℝ e (U z) := by
  have hbdd : Bornology.IsBounded (U '' parCyl 1) := isBounded_image_of_bound hb _
  have hle : dirSup U e ≤ (inner ℝ e (U z) : ℝ) + oscCyl U 1 := by
    refine csSup_le (dirImage_nonempty U e) ?_
    rintro p ⟨w, hw, rfl⟩
    have := inner_sub_le_oscOn (f := U) (S := parCyl 1) hbdd he hw hz
    have hocc : oscOn U (parCyl 1) = oscCyl U 1 := rfl
    linarith [this]
  linarith

/-- **The directional infimum is an admissible De Giorgi level.** -/
theorem le_dirInf_add_oscCyl {U : STime → E3} {K : ℝ} (hb : ∀ z, ‖U z‖ ≤ K)
    {e : E3} (he : ‖e‖ ≤ 1) {z : STime} (hz : z ∈ parCyl 1) :
    (inner ℝ e (U z) : ℝ) ≤ dirInf U e + oscCyl U 1 := by
  have hbdd : Bornology.IsBounded (U '' parCyl 1) := isBounded_image_of_bound hb _
  have hle : (inner ℝ e (U z) : ℝ) - oscCyl U 1 ≤ dirInf U e := by
    refine le_csInf (dirImage_nonempty U e) ?_
    rintro p ⟨w, hw, rfl⟩
    have := inner_sub_le_oscOn (f := U) (S := parCyl 1) hbdd he hz hw
    have hocc : oscOn U (parCyl 1) = oscCyl U 1 := rfl
    linarith [this]
  linarith

/-! ## The remaining obligation, and the reduction it discharges -/

/-- **The directional level drop.**  For every unit direction `e`, either the
component `⟪e,U⟫` stays `σ·osc_{Q_1}U` below its supremum over `Q_1`, almost
everywhere on the smaller cylinder `Q_θ`, or it stays `σ·osc_{Q_1}U` above its
infimum there.

This is the exact analytic content of the De Giorgi alternative for the ancient
profile; everything else on the C side of the Clay route is proved. -/
def DirectionalLevelDrop (U : STime → E3) (theta sig : ℝ) : Prop :=
  ∀ e : E3, ‖e‖ = 1 →
    (∀ᵐ z ∂(volume.restrict (parCyl theta)),
      (inner ℝ e (U z) : ℝ) ≤ dirSup U e - sig * oscCyl U 1) ∨
    (∀ᵐ z ∂(volume.restrict (parCyl theta)),
      dirInf U e + sig * oscCyl U 1 ≤ (inner ℝ e (U z) : ℝ))

/-- **The reduction.**  For a continuous bounded field the directional level
drop *is* the De Giorgi alternative: the existentially quantified levels of
`ClayNS.OscDichotomy` may be taken to be the directional supremum and
infimum. -/
theorem oscDichotomy_of_directionalLevelDrop (U : STime → E3) (hU : Continuous U)
    {K : ℝ} (hb : ∀ z, ‖U z‖ ≤ K) {theta sig : ℝ}
    (h : DirectionalLevelDrop U theta sig) :
    OscDichotomy U theta sig := by
  refine oscDichotomy_of_ae_dichotomy U hU ?_
  intro e he
  have he1 : ‖e‖ ≤ 1 := le_of_eq he
  rcases h e he with hsup | hinf
  · exact Or.inl ⟨dirSup U e, fun z hz => dirSup_sub_oscCyl_le hb he1 hz, hsup⟩
  · exact Or.inr ⟨dirInf U e, fun z hz => le_dirInf_add_oscCyl hb he1 hz, hinf⟩

/-- **Liouville from the directional level drop.**  A bounded member of a
rescaling-closed ancient class all of whose members satisfy the directional
level drop with universal `0 < θ < 1`, `0 < σ ≤ 1` is constant on the ancient
region. -/
theorem ancient_constant_of_directionalLevelDrop
    (Cls : (STime → E3) → Prop) {theta sig : ℝ}
    (hth0 : 0 < theta) (hth1 : theta < 1) (hs0 : 0 < sig) (hs1 : sig ≤ 1)
    (hclosed : ∀ (U : STime → E3) (lam : ℝ), Cls U → 0 < lam → Cls (parRescale U lam))
    {K : ℝ} (hK : 0 ≤ K)
    (hbcls : ∀ U : STime → E3, Cls U → Continuous U ∧ ∀ z, ‖U z‖ ≤ K)
    (hdrop : ∀ U : STime → E3, Cls U → DirectionalLevelDrop U theta sig)
    (U : STime → E3) (hU : Cls U) :
    ∃ b : E3, ∀ z : STime, z.1 ≤ 0 → U z = b := by
  refine ancient_constant_of_directional_dichotomy Cls hth0 hth1 hs0 hs1 hclosed
    (fun V hV => ?_) U hU hK (hbcls U hU).2
  exact oscDichotomy_of_directionalLevelDrop V (hbcls V hV).1 (hbcls V hV).2 (hdrop V hV)

/-- **The C arrow, in terms of the remaining obligation.**  A bounded ancient
member of the class cannot both satisfy the directional level drop and carry a
nonzero normalized oscillation defect. -/
theorem false_of_defect_and_directionalLevelDrop
    (Cls : (STime → E3) → Prop) {theta sig R0 c0 : ℝ}
    (hth0 : 0 < theta) (hth1 : theta < 1) (hs0 : 0 < sig) (hs1 : sig ≤ 1)
    (hclosed : ∀ (U : STime → E3) (lam : ℝ), Cls U → 0 < lam → Cls (parRescale U lam))
    {K : ℝ} (hK : 0 ≤ K)
    (hbcls : ∀ U : STime → E3, Cls U → Continuous U ∧ ∀ z, ‖U z‖ ≤ K)
    (hdrop : ∀ U : STime → E3, Cls U → DirectionalLevelDrop U theta sig)
    (U : STime → E3) (hU : Cls U) (hc0 : 0 < c0)
    (hdefect : c0 ≤ oscOn (fun x : E3 => U (0, x)) (Metric.ball 0 R0)) : False := by
  refine false_of_defect_and_directional_dichotomy Cls hth0 hth1 hs0 hs1 hclosed
    (fun V hV => ?_) U hU hK (hbcls U hU).2 hc0 hdefect
  exact oscDichotomy_of_directionalLevelDrop V (hbcls V hV).1 (hbcls V hV).2 (hdrop V hV)

/-! ## The measure-theoretic first step of the De Giorgi alternative -/

/-- **The occupation dichotomy.**  At any level, one of the two complementary
occupation sets of a measurable scalar occupies at most half of the cylinder.
This is the entry point of the classical De Giorgi alternative: the direction of
the alternative is decided by which of the two sets is small. -/
theorem measure_dichotomy_at_level {v : STime → ℝ} (hv : Measurable v) (m : ℝ)
    {S : Set STime} (hS : MeasurableSet S) :
    volume (S ∩ {z | m < v z}) * 2 ≤ volume S ∨ volume (S ∩ {z | v z ≤ m}) * 2 ≤ volume S := by
  classical
  set A : Set STime := S ∩ {z | m < v z} with hA
  set B : Set STime := S ∩ {z | v z ≤ m} with hB
  have hAm : MeasurableSet A := hS.inter (measurableSet_lt measurable_const hv)
  have hdisj : Disjoint A B := by
    refine Set.disjoint_left.2 ?_
    rintro z ⟨_, hz1⟩ ⟨_, hz2⟩
    have h1 : m < v z := hz1
    have h2 : v z ≤ m := hz2
    linarith
  have hunion : A ∪ B = S := by
    ext z
    constructor
    · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
    · intro hz
      by_cases h : v z ≤ m
      · exact Or.inr ⟨hz, h⟩
      · exact Or.inl ⟨hz, not_le.1 h⟩
  have hadd : volume A + volume B = volume S := by
    rw [← hunion, measure_union hdisj (hS.inter (measurableSet_le hv measurable_const))]
  rcases le_total (volume A) (volume B) with hle | hle
  · refine Or.inl ?_
    calc volume A * 2 = volume A + volume A := by ring
      _ ≤ volume A + volume B := add_le_add le_rfl hle
      _ = volume S := hadd
  · refine Or.inr ?_
    calc volume B * 2 = volume B + volume B := by ring
      _ ≤ volume A + volume B := add_le_add hle le_rfl
      _ = volume S := hadd

end ClayNS

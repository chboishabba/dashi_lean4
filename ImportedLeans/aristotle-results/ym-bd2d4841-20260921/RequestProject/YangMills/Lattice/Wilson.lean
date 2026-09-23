/-
# The literal Wilson lattice gauge measure on a periodic four-dimensional lattice

This file builds the actual finite-spacing Yang–Mills objects, with nothing
postulated:

* `Site`, `Link`, `Conf` — the sites, links and gauge-field configurations of the
  periodic four-dimensional lattice with `n+1` points in every direction;
* `plaqHol` — the literal plaquette holonomy
  `U(x,μ) U(x+μ̂,ν) U(x+ν̂,μ)⁻¹ U(x,ν)⁻¹`;
* `wilsonAction` — the literal Wilson action `−β Σ_x Σ_{μ,ν} χ(plaquette)`;
* `gaugeTransform`, `translate` — the lattice gauge transformations and the
  lattice translations, acting on configurations;
* `plaqHol_gaugeTransform`, `wilsonAction_gaugeTransform` — gauge covariance of
  the plaquette and gauge invariance of the action, proved by the group algebra;
* `wilsonAction_translate` — translation invariance of the action, proved by
  reindexing the site sum;
* `gibbs` — the Wilson–Gibbs probability measure `Z⁻¹ e^{−S} dU` built from the
  product of normalised Haar measures, with `0 < Z < ∞` proved from
  continuity of the character on the compact group;
* `measurePreserving_gauge_gibbs`, `measurePreserving_translate_gibbs` — the
  Gibbs measure is invariant under gauge transformations and under lattice
  translations.

The character `χ` is an arbitrary continuous conjugation-invariant real function
on the gauge group; for `G = SU(N)` the physical choice is `χ(g) = Re tr g`,
see `Lattice/SUN.lean`.
-/
import Mathlib
import RequestProject.YangMills.Lattice.Config

namespace RequestProject.YangMills.Lattice

open MeasureTheory
open scoped ENNReal NNReal

/-! ## The lattice -/

/-- Sites of the periodic four-dimensional lattice with `n+1` points in every
direction. -/
abbrev Site (n : ℕ) := Fin 4 → ZMod (n + 1)

/-- Links: a site together with a direction; the link joins `x` to `x + μ̂`. -/
abbrev Link (n : ℕ) := Site n × Fin 4

/-- A gauge-field configuration: one group element per link. -/
abbrev Conf (n : ℕ) (G : Type*) := Link n → G

/-- The unit lattice vector in direction `d`. -/
def unitVec (n : ℕ) (d : Fin 4) : Site n := Pi.single d 1

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

variable {n : ℕ}

/-- The literal plaquette holonomy in the `(μ,ν)` plane based at `x`. -/
def plaqHol (U : Conf n G) (x : Site n) (mu nu : Fin 4) : G :=
  U (x, mu) * U (x + unitVec n mu, nu) * (U (x + unitVec n nu, mu))⁻¹ * (U (x, nu))⁻¹

/-- The literal Wilson action.  The double sum runs over all ordered pairs of
directions; the diagonal terms are constant and the two orders of a plane
contribute `χ(h)` and `χ(h⁻¹)`, so for a character with `χ(g⁻¹) = χ(g)` this is
the usual plaquette sum with `β` rescaled by `2`. -/
noncomputable def wilsonAction (beta : ℝ) (chi : G → ℝ) (U : Conf n G) : ℝ :=
  -beta * ∑ x : Site n, ∑ mu : Fin 4, ∑ nu : Fin 4, chi (plaqHol U x mu nu)

/-! ## Gauge transformations -/

/-- A lattice gauge transformation acting on configurations. -/
def gaugeTransform (g : Site n → G) (U : Conf n G) : Conf n G :=
  fun l => g l.1 * U l * (g (l.1 + unitVec n l.2))⁻¹

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
/-- **Gauge covariance of the plaquette**: the holonomy is conjugated by the
gauge function at the base point. -/
theorem plaqHol_gaugeTransform (g : Site n → G) (U : Conf n G) (x : Site n) (mu nu : Fin 4) :
    plaqHol (gaugeTransform g U) x mu nu = g x * plaqHol U x mu nu * (g x)⁻¹ := by
  have hcomm : x + unitVec n nu + unitVec n mu = x + unitVec n mu + unitVec n nu :=
    add_right_comm _ _ _
  simp only [plaqHol, gaugeTransform, hcomm, mul_inv_rev, inv_inv]
  group

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
/-- **Gauge invariance of the Wilson action** for a conjugation-invariant
character. -/
theorem wilsonAction_gaugeTransform {chi : G → ℝ}
    (hchi : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta : ℝ) (g : Site n → G) (U : Conf n G) :
    wilsonAction beta chi (gaugeTransform g U) = wilsonAction beta chi U := by
  unfold wilsonAction
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun mu _ =>
    Finset.sum_congr rfl fun nu _ => ?_
  rw [plaqHol_gaugeTransform, hchi]

/-! ## Lattice translations -/

/-- Translation of a configuration by a lattice vector. -/
def translate (v : Site n) (U : Conf n G) : Conf n G := fun l => U (l.1 + v, l.2)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
theorem plaqHol_translate (v : Site n) (U : Conf n G) (x : Site n) (mu nu : Fin 4) :
    plaqHol (translate v U) x mu nu = plaqHol U (x + v) mu nu := by
  simp only [plaqHol, translate]
  rw [add_right_comm x (unitVec n mu) v, add_right_comm x (unitVec n nu) v]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
/-- **Translation invariance of the Wilson action.** -/
theorem wilsonAction_translate (beta : ℝ) (chi : G → ℝ) (v : Site n) (U : Conf n G) :
    wilsonAction beta chi (translate v U) = wilsonAction beta chi U := by
  unfold wilsonAction
  congr 1
  rw [← Equiv.sum_comp (Equiv.addRight v) (fun x : Site n => ∑ mu : Fin 4, ∑ nu : Fin 4,
    chi (plaqHol U x mu nu))]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun mu _ =>
    Finset.sum_congr rfl fun nu _ => ?_
  rw [plaqHol_translate]
  rfl

/-! ## Measure preservation -/

omit [SecondCountableTopology G] in
/-- Gauge transformations preserve the product Haar measure on configurations. -/
theorem measurePreserving_gaugeTransform (g : Site n → G) :
    MeasurePreserving (gaugeTransform g) (prodHaar (Link n) G) (prodHaar (Link n) G) :=
  measurePreserving_translate (ι := Link n) (fun l => g l.1)
    (fun l => (g (l.1 + unitVec n l.2))⁻¹)

omit [SecondCountableTopology G] in
/-- Lattice translations preserve the product Haar measure on configurations. -/
theorem measurePreserving_translateConf (v : Site n) :
    MeasurePreserving (translate (G := G) v) (prodHaar (Link n) G) (prodHaar (Link n) G) := by
  have h := measurePreserving_reindex (G := G)
    (e := (Equiv.prodCongr (Equiv.addRight v) (Equiv.refl (Fin 4)) : Equiv.Perm (Link n)))
  exact h

/-! ## Continuity and measurability of the action -/

omit [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] in
theorem continuous_plaqHol (x : Site n) (mu nu : Fin 4) :
    Continuous fun U : Conf n G => plaqHol U x mu nu := by
  unfold plaqHol
  fun_prop

omit [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] in
theorem continuous_wilsonAction {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ) :
    Continuous (wilsonAction (n := n) beta chi) := by
  unfold wilsonAction
  exact continuous_const.mul (continuous_finset_sum _ fun x _ => continuous_finset_sum _
    fun mu _ => continuous_finset_sum _ fun nu _ => hchi.comp (continuous_plaqHol x mu nu))

omit [CompactSpace G] [T2Space G] in
theorem measurable_wilsonAction {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ) :
    Measurable (wilsonAction (n := n) beta chi) := (continuous_wilsonAction hchi beta).measurable

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
/-- The Wilson action is bounded: the configuration space is compact. -/
theorem exists_bound_wilsonAction {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ) :
    ∃ M : ℝ, ∀ U : Conf n G, |wilsonAction beta chi U| ≤ M := by
  have hcont : Continuous fun U : Conf n G => |wilsonAction beta chi U| :=
    (continuous_wilsonAction hchi beta).abs
  obtain ⟨U₀, -, hU₀⟩ :=
    (isCompact_univ (X := Conf n G)).exists_isMaxOn ⟨fun _ => 1, Set.mem_univ _⟩
      hcont.continuousOn
  exact ⟨|wilsonAction beta chi U₀|, fun U => hU₀ (Set.mem_univ U)⟩

/-! ## The Wilson–Gibbs measure -/

/-- The Boltzmann weight of the Wilson action. -/
noncomputable def gibbsDensity (beta : ℝ) (chi : G → ℝ) (U : Conf n G) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-wilsonAction beta chi U))

omit [CompactSpace G] [T2Space G] in
theorem measurable_gibbsDensity {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ) :
    Measurable (gibbsDensity (n := n) beta chi) :=
  (ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp (measurable_wilsonAction hchi beta).neg))

/-- The unnormalised Wilson–Gibbs measure. -/
noncomputable def gibbsUnnorm (n : ℕ) (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (beta : ℝ) (chi : G → ℝ) : Measure (Conf n G) :=
  (prodHaar (Link n) G).withDensity (gibbsDensity beta chi)

/-- The partition function. -/
noncomputable def partition (n : ℕ) (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (beta : ℝ) (chi : G → ℝ) : ℝ≥0∞ :=
  gibbsUnnorm n G beta chi Set.univ

theorem partition_ne_zero {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ) :
    partition n G beta chi ≠ 0 := by
  obtain ⟨M, hM⟩ := exists_bound_wilsonAction (n := n) hchi beta
  have hpos : ∀ U : Conf n G, ENNReal.ofReal (Real.exp (-M)) ≤ gibbsDensity beta chi U := by
    intro U
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have := (abs_le.1 (hM U)).2
    linarith
  have hle : ENNReal.ofReal (Real.exp (-M)) * (1 : ℝ≥0∞) ≤ partition n G beta chi := by
    have : ∫⁻ _ : Conf n G, ENNReal.ofReal (Real.exp (-M)) ∂(prodHaar (Link n) G)
        ≤ ∫⁻ U : Conf n G, gibbsDensity beta chi U ∂(prodHaar (Link n) G) :=
      lintegral_mono hpos
    simpa [partition, gibbsUnnorm, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_const, measure_univ] using this
  intro h
  rw [h] at hle
  simp [ENNReal.ofReal_eq_zero, not_le.2 (Real.exp_pos (-M))] at hle

theorem partition_ne_top {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ) :
    partition n G beta chi ≠ ⊤ := by
  obtain ⟨M, hM⟩ := exists_bound_wilsonAction (n := n) hchi beta
  have hle : ∀ U : Conf n G, gibbsDensity beta chi U ≤ ENNReal.ofReal (Real.exp M) := by
    intro U
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have := (abs_le.1 (hM U)).1
    linarith
  have : partition n G beta chi ≤ ENNReal.ofReal (Real.exp M) := by
    have hmono : ∫⁻ U : Conf n G, gibbsDensity beta chi U ∂(prodHaar (Link n) G)
        ≤ ∫⁻ _ : Conf n G, ENNReal.ofReal (Real.exp M) ∂(prodHaar (Link n) G) :=
      lintegral_mono hle
    simpa [partition, gibbsUnnorm, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_const, measure_univ] using hmono
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top this

/-- **The Wilson–Gibbs probability measure** of the lattice gauge theory. -/
noncomputable def gibbs (n : ℕ) (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (beta : ℝ) (chi : G → ℝ) : Measure (Conf n G) :=
  (partition n G beta chi)⁻¹ • gibbsUnnorm n G beta chi

theorem isProbabilityMeasure_gibbs {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ) :
    IsProbabilityMeasure (gibbs n G beta chi) := by
  constructor
  rw [gibbs, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (partition_ne_zero hchi beta) (partition_ne_top hchi beta)

/-! ## Invariance of the Gibbs measure -/

/-- A measure-preserving transformation that leaves a density invariant
preserves the weighted measure. -/
theorem measurePreserving_withDensity {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {Φ : X → X} (hΦ : MeasurePreserving Φ mu mu) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hinv : ∀ x, f (Φ x) = f x) :
    MeasurePreserving Φ (mu.withDensity f) (mu.withDensity f) := by
  refine ⟨hΦ.measurable, ?_⟩
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply hΦ.measurable hA, withDensity_apply _ (hΦ.measurable hA),
    withDensity_apply _ hA, ← lintegral_indicator (hΦ.measurable hA),
    ← lintegral_indicator hA]
  have hcomp : ∀ x, (Φ ⁻¹' A).indicator f x = (A.indicator f) (Φ x) := by
    intro x
    by_cases hx : Φ x ∈ A
    · simp [Set.indicator_of_mem, hx, Set.mem_preimage.2 hx, hinv x]
    · simp [Set.indicator_of_notMem, fun h : x ∈ Φ ⁻¹' A => hx h]
  simp_rw [hcomp]
  exact hΦ.lintegral_comp (hf.indicator hA)

theorem measurePreserving_scaled {X : Type*} [MeasurableSpace X] {mu : Measure X} {Φ : X → X}
    (hΦ : MeasurePreserving Φ mu mu) (c : ℝ≥0∞) :
    MeasurePreserving Φ (c • mu) (c • mu) := by
  refine ⟨hΦ.measurable, ?_⟩
  rw [Measure.map_smul, hΦ.map_eq]

/-- **The Wilson–Gibbs measure is gauge invariant.** -/
theorem measurePreserving_gauge_gibbs {chi : G → ℝ} (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta : ℝ) (g : Site n → G) :
    MeasurePreserving (gaugeTransform g) (gibbs n G beta chi) (gibbs n G beta chi) :=
  measurePreserving_scaled
    (measurePreserving_withDensity (measurePreserving_gaugeTransform g)
      (measurable_gibbsDensity hchi beta)
      (fun U => by
        simp [gibbsDensity, wilsonAction_gaugeTransform hconj beta g U])) _

/-- **The Wilson–Gibbs measure is translation invariant.** -/
theorem measurePreserving_translate_gibbs {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ)
    (v : Site n) :
    MeasurePreserving (translate (G := G) v) (gibbs n G beta chi) (gibbs n G beta chi) :=
  measurePreserving_scaled
    (measurePreserving_withDensity (measurePreserving_translateConf v)
      (measurable_gibbsDensity hchi beta)
      (fun U => by simp [gibbsDensity, wilsonAction_translate beta chi v U])) _

end RequestProject.YangMills.Lattice

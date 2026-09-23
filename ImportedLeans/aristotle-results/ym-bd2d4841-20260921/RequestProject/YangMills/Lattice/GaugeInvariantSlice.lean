/-
# The gauge-invariant physical Hilbert space of the literal lattice theory

The physical Hilbert space of the lattice theory at a given spacing is not all of
`L²` of the slice measure but its gauge-invariant part, `L²_gauge(μ_a)`.  This
file constructs it for the literal Wilson slice measure, using the carrier
machinery of `GaugeInvariantL2Carrier.lean`:

* `sliceGauge` — the action of a lattice gauge transformation on slice
  configurations, and `slice0_gaugeTransform`: it is the restriction of the
  gauge action on configurations, so the two are the same object;
* `measurePreserving_sliceGauge` — the slice measure is gauge invariant (this
  uses gauge invariance of the Wilson–Gibbs measure, proved in `Wilson.lean`);
* `PhysicalSlice` — the gauge-invariant `L²` carrier, a Hilbert space;
* `physVacuum` — the constant wavefunction is gauge invariant and is a unit
  vector;
* `restrictForm` — a bounded Hermitian form restricts to a closed subspace;
* `physEnergyForm`, `physHamiltonian` — the physical energy form and Hamiltonian
  on the gauge-invariant carrier, with self-adjointness and `H Ω = 0` proved;
* `phys_massGap_of_coercivity` — the mass-gap conclusion on the physical space
  from coercivity there;
* `phys_massGap_zero_coupling` — at zero coupling that coercivity is proved, so
  the physical (gauge-invariant) package is inhabited by the literal objects.
-/
import Mathlib
import RequestProject.YangMills.Lattice.FreeCoupling
import RequestProject.YangMills.GaugeInvariantL2Carrier

namespace RequestProject.YangMills.Lattice

open MeasureTheory
open scoped InnerProductSpace
open RequestProject.YangMills.GaugeInvariantL2Carrier

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] {n : ℕ} {chi : G → ℝ}

/-! ## The gauge action on a time slice -/

/-- A lattice gauge transformation acting on slice configurations. -/
def sliceGauge (g : Site n → G) (v : SliceIdx n → G) : SliceIdx n → G :=
  fun l => g l.1.1 * v l * (g (l.1.1 + unitVec n l.1.2))⁻¹

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
/-- The slice of a gauge-transformed configuration is the gauge transform of its
slice: the two gauge actions are the same object. -/
theorem slice0_gaugeTransform (g : Site n → G) (U : Conf n G) :
    slice0 (gaugeTransform g U) = sliceGauge g (slice0 U) := rfl

/-- **The slice measure is gauge invariant.** -/
theorem measurePreserving_sliceGauge (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta : ℝ) (g : Site n → G) :
    MeasurePreserving (sliceGauge g) (sliceMeasure n G beta chi) (sliceMeasure n G beta chi) := by
  have hmeas : Measurable (sliceGauge (n := n) (G := G) g) := by
    refine measurable_pi_lambda _ fun l => ?_
    exact (measurable_const.mul (measurable_pi_apply l)).mul measurable_const
  refine ⟨hmeas, ?_⟩
  have h1 : Measure.map (sliceGauge g) (sliceMeasure n G beta chi)
      = Measure.map (sliceGauge g ∘ slice0) (gibbs n G beta chi) := by
    rw [sliceMeasure, Measure.map_map hmeas measurable_slice0]
  have h2 : (sliceGauge (n := n) (G := G) g) ∘ slice0 = slice0 ∘ gaugeTransform g := rfl
  rw [h1, h2, ← Measure.map_map measurable_slice0
      (measurePreserving_gauge_gibbs hchi hconj beta g).measurable,
    (measurePreserving_gauge_gibbs hchi hconj beta g).map_eq]
  rfl

/-! ## The gauge-invariant carrier -/

/-- **The physical Hilbert space at spacing `a`**: the gauge-invariant
wavefunctions of the literal Wilson slice measure. -/
noncomputable abbrev PhysicalSlice (n : ℕ) (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta : ℝ) : Type _ :=
  PhysicalCarrier (μ := sliceMeasure n G beta chi) (G := Site n → G) sliceGauge
    (measurePreserving_sliceGauge hchi hconj beta)

/-- The vacuum is gauge invariant. -/
theorem vacuum_mem_invariantSubspace (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta : ℝ) :
    vacuum hchi beta ∈ invariantSubspace (μ := sliceMeasure n G beta chi) (G := Site n → G)
      sliceGauge (measurePreserving_sliceGauge hchi hconj beta) := by
  rw [mem_invariantSubspace_iff]
  intro _
  rfl

/-- **The physical vacuum** of the literal lattice theory. -/
noncomputable def physVacuum (n : ℕ) (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta : ℝ) :
    PhysicalSlice n hchi hconj beta :=
  ⟨vacuum hchi beta, vacuum_mem_invariantSubspace hchi hconj beta⟩

theorem norm_physVacuum (n : ℕ) (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta : ℝ) :
    ‖physVacuum n hchi hconj beta‖ = 1 :=
  norm_vacuum (n := n) hchi beta

/-! ## Restricting the energy form to the physical space -/

/-- A bounded Hermitian form restricts to a closed subspace. -/
noncomputable def restrictForm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (q : Clay.BoundedSesqForm E) (K : Submodule ℂ E) : Clay.BoundedSesqForm K where
  form x y := q.form (x : E) (y : E)
  bound := q.bound
  bound_nonneg := q.bound_nonneg
  add_left := by intro x y z; exact q.add_left _ _ _
  smul_left := by intro c x y; exact q.smul_left _ _ _
  norm_le := by intro x y; exact q.norm_le _ _
  sesq_symm := by intro x y; exact q.sesq_symm _ _

@[simp] theorem restrictForm_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (q : Clay.BoundedSesqForm E) (K : Submodule ℂ E) (x y : K) :
    (restrictForm q K).form x y = q.form (x : E) (y : E) := rfl

/-! ## The physical energy form and Hamiltonian -/

/-- **The physical energy form** of the literal lattice theory at spacing `a`:
the Wilson transfer form restricted to the gauge-invariant carrier. -/
noncomputable def physEnergyForm (n : ℕ) (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta a : ℝ) (ha : 0 ≤ a) :
    Clay.BoundedSesqForm (PhysicalSlice n hchi hconj beta) :=
  restrictForm (scaleForm a⁻¹ (inv_nonneg.2 ha) (energyForm hchi beta)) _

theorem physEnergyForm_vacuum (n : ℕ) (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta a : ℝ) (ha : 0 ≤ a)
    (φ : PhysicalSlice n hchi hconj beta) :
    (physEnergyForm n hchi hconj beta a ha).form φ (physVacuum n hchi hconj beta) = 0 := by
  rw [physEnergyForm, restrictForm_apply, scaleForm_apply]
  rw [show ((physVacuum n hchi hconj beta : PhysicalSlice n hchi hconj beta) :
      SliceL2 n G beta chi) = vacuum hchi beta from rfl]
  rw [energyForm_vacuum hchi beta, mul_zero]

/-- **The physical Hamiltonian** on the gauge-invariant carrier. -/
noncomputable def physHamiltonian (n : ℕ) (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta a : ℝ) (ha : 0 ≤ a) :
    PhysicalSlice n hchi hconj beta →ₗ.[ℂ] PhysicalSlice n hchi hconj beta :=
  (physEnergyForm n hchi hconj beta a ha).hamiltonian

theorem physHamiltonian_isSelfAdjoint (n : ℕ) (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta a : ℝ) (ha : 0 ≤ a) :
    IsSelfAdjoint (physHamiltonian n hchi hconj beta a ha) :=
  (physEnergyForm n hchi hconj beta a ha).isSelfAdjoint_hamiltonian

theorem physHamiltonian_vacuum (n : ℕ) (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta a : ℝ) (ha : 0 ≤ a) :
    (physHamiltonian n hchi hconj beta a ha)
      ⟨physVacuum n hchi hconj beta, Submodule.mem_top⟩ = 0 :=
  (physEnergyForm n hchi hconj beta a ha).hamiltonian_apply_eq_zero
    (physEnergyForm_vacuum n hchi hconj beta a ha)

/-- **The mass-gap conclusion on the physical space** from coercivity there. -/
theorem phys_massGap_of_coercivity (n : ℕ) (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta a : ℝ) (ha : 0 ≤ a) {Δ : ℝ}
    (hΔ : 0 < Δ)
    (hcoer : ∀ ψ : PhysicalSlice n hchi hconj beta, ⟪physVacuum n hchi hconj beta, ψ⟫_ℂ = 0 →
      Δ * ‖ψ‖ ^ 2 ≤ ((physEnergyForm n hchi hconj beta a ha).form ψ ψ).re) :
    Clay.MassGapConclusion (physHamiltonian n hchi hconj beta a ha)
      (physVacuum n hchi hconj beta) Δ :=
  Clay.massGapConclusion_of_datum
    ((physEnergyForm n hchi hconj beta a ha).gapDatum (norm_physVacuum n hchi hconj beta) hΔ
      (physEnergyForm_vacuum n hchi hconj beta a ha) hcoer)

/-- At zero coupling the physical (gauge-invariant) package of the literal
lattice theory has the full mass-gap conclusion with gap `a⁻¹`. -/
theorem phys_massGap_zero_coupling {n : ℕ} (hn : 1 ≤ n) (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) {a : ℝ} (ha : 0 < a) :
    Clay.MassGapConclusion (physHamiltonian n hchi hconj 0 a ha.le)
      (physVacuum n hchi hconj 0) a⁻¹ := by
  refine phys_massGap_of_coercivity n hchi hconj 0 a ha.le (inv_pos.2 ha) ?_
  intro ψ hψ
  have hq := energyForm_coercive_of_zero_coupling (zero_ne_one_zmod hn) hchi
    (ψ : SliceL2 n G 0 chi) hψ
  rw [physEnergyForm, restrictForm_apply, scaleForm_apply, Complex.re_ofReal_mul]
  have hnn : (0 : ℝ) ≤ a⁻¹ := (inv_pos.2 ha).le
  have hnorm : ‖ψ‖ = ‖(ψ : SliceL2 n G 0 chi)‖ := rfl
  rw [hnorm]
  nlinarith [hq]

/-! ## The literal `SU(2)` physical package -/

/-- The physical (gauge-invariant) Hilbert space of four-dimensional `SU(2)`
lattice Yang–Mills at inverse coupling `β`. -/
noncomputable abbrev ymPhysicalSlice (n : ℕ) (beta : ℝ) : Type _ :=
  PhysicalSlice (G := SU2) n continuous_chiSU2 chiSU2_conj beta

/-- The physical vacuum of four-dimensional `SU(2)` lattice Yang–Mills. -/
noncomputable def ymPhysicalVacuum (n : ℕ) (beta : ℝ) : ymPhysicalSlice n beta :=
  physVacuum (G := SU2) n continuous_chiSU2 chiSU2_conj beta

/-- The physical Hamiltonian of four-dimensional `SU(2)` lattice Yang–Mills at
spacing `a`, acting on the gauge-invariant carrier. -/
noncomputable def ymPhysicalHamiltonian (n : ℕ) (beta a : ℝ) (ha : 0 ≤ a) :
    ymPhysicalSlice n beta →ₗ.[ℂ] ymPhysicalSlice n beta :=
  physHamiltonian (G := SU2) n continuous_chiSU2 chiSU2_conj beta a ha

theorem ymPhysicalHamiltonian_isSelfAdjoint (n : ℕ) (beta a : ℝ) (ha : 0 ≤ a) :
    IsSelfAdjoint (ymPhysicalHamiltonian n beta a ha) :=
  physHamiltonian_isSelfAdjoint (G := SU2) n continuous_chiSU2 chiSU2_conj beta a ha

theorem ymPhysicalHamiltonian_vacuum (n : ℕ) (beta a : ℝ) (ha : 0 ≤ a) :
    (ymPhysicalHamiltonian n beta a ha)
      ⟨ymPhysicalVacuum n beta, Submodule.mem_top⟩ = 0 :=
  physHamiltonian_vacuum (G := SU2) n continuous_chiSU2 chiSU2_conj beta a ha

/-- **The literal `SU(2)` physical package at zero coupling satisfies the full
mass-gap conclusion** with gap `a⁻¹` at spacing `a`: on the gauge-invariant
Hilbert space of the literal Wilson slice measure. -/
theorem ym_phys_massGap_zero_coupling {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) :
    Clay.MassGapConclusion (ymPhysicalHamiltonian n 0 a ha.le) (ymPhysicalVacuum n 0) a⁻¹ :=
  phys_massGap_zero_coupling (G := SU2) hn continuous_chiSU2 chiSU2_conj ha

end RequestProject.YangMills.Lattice

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Lattice

#print axioms measurePreserving_sliceGauge
#print axioms norm_physVacuum
#print axioms physHamiltonian_isSelfAdjoint
#print axioms physHamiltonian_vacuum
#print axioms phys_massGap_of_coercivity
#print axioms ym_phys_massGap_zero_coupling

end Audit

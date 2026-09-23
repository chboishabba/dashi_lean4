/-
# The literal finite-spacing Yang–Mills energy form

This file builds the finite-spacing physical data of the Yang–Mills lane out of
the literal Wilson–Gibbs measure of `Lattice/Wilson.lean`:

* `sliceMeasure` — the distribution of the time-zero slice of the gauge field
  under the Wilson–Gibbs measure;
* the physical Hilbert space at spacing `a` is `L²` of that measure,
  `Lp ℂ 2 (sliceMeasure …)`, and the vacuum is the constant wavefunction, a unit
  vector because the measure is a probability measure;
* `slice0`, `slice1` — the time-zero and time-one slice maps, both measure
  preserving onto the slice measure (time-one because the Gibbs measure is
  translation invariant, which was proved in `Wilson.lean`);
* `energyForm` — the literal energy form
  `q(φ,ψ) = ⟪φ,ψ⟫ − ½(⟪φ∘p₀, ψ∘p₁⟫ + ⟪φ∘p₁, ψ∘p₀⟫)`,
  i.e. `q = 1 − ½(T + T*)` for the Euclidean transfer operator `T` of the Wilson
  measure.  It is proved to be a `BoundedSesqForm`: sesquilinear, Hermitian and
  bounded by `2`, the bound coming from the two slice isometries;
* `energyForm_vacuum` — the form annihilates the vacuum, proved from the fact
  that both slice maps send the constant wavefunction to the same constant
  wavefunction, which is the transfer-operator identity `T Ω = Ω`.

Through `Clay.FormHamiltonian` this *produces* the finite-spacing Hamiltonian
`H_a`, its self-adjointness and `H_a Ω_a = 0` for the literal lattice theory.
What is not proved here is coercivity on the vacuum complement: that is the
physical mass gap of the transfer matrix, isolated in `Lattice/Frontier.lean`.
-/
import Mathlib
import RequestProject.YangMills.Lattice.Wilson
import RequestProject.YangMills.Clay.FormHamiltonian

namespace RequestProject.YangMills.Lattice

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
open ComplexConjugate

/-! ## Time slices of the lattice -/

/-- The index set of a time slice: the spatial links based at a site with time
coordinate zero. -/
def SliceIdx (n : ℕ) : Type := {l : Link n // l.2 ≠ 0 ∧ l.1 0 = 0}

instance (n : ℕ) : Fintype (SliceIdx n) := Subtype.fintype _

instance (n : ℕ) : DecidableEq (SliceIdx n) := Subtype.instDecidableEq

section Slices

variable {G : Type*} [Group G] {n : ℕ}

/-- The time-zero slice of a configuration. -/
def slice0 (U : Conf n G) : SliceIdx n → G := fun l => U l.1

/-- The time-one slice of a configuration. -/
def slice1 (U : Conf n G) : SliceIdx n → G := fun l => U (l.1.1 + unitVec n 0, l.1.2)

omit [Group G] in
theorem slice1_eq_slice0_translate (U : Conf n G) :
    slice1 U = slice0 (translate (unitVec n 0) U) := rfl

end Slices

section Measures

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] {n : ℕ}

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [BorelSpace G] [SecondCountableTopology G] in
theorem measurable_slice0 : Measurable (slice0 (n := n) (G := G)) :=
  measurable_pi_lambda _ fun l => measurable_pi_apply l.1

/-- The distribution of the time-zero slice under the Wilson–Gibbs measure: the
literal finite-spacing physical measure of the lattice gauge theory. -/
noncomputable def sliceMeasure (n : ℕ) (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (beta : ℝ) (chi : G → ℝ) : Measure (SliceIdx n → G) :=
  Measure.map slice0 (gibbs n G beta chi)

theorem measurePreserving_slice0 (beta : ℝ) (chi : G → ℝ) :
    MeasurePreserving (slice0 (n := n) (G := G)) (gibbs n G beta chi)
      (sliceMeasure n G beta chi) :=
  ⟨measurable_slice0, rfl⟩

/-- The time-one slice has the same distribution as the time-zero slice: this is
translation invariance of the Wilson–Gibbs measure. -/
theorem measurePreserving_slice1 {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ) :
    MeasurePreserving (slice1 (n := n) (G := G)) (gibbs n G beta chi)
      (sliceMeasure n G beta chi) :=
  (measurePreserving_slice0 beta chi).comp
    (measurePreserving_translate_gibbs hchi beta (unitVec n 0))

theorem isProbabilityMeasure_sliceMeasure {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ) :
    IsProbabilityMeasure (sliceMeasure n G beta chi) := by
  haveI := isProbabilityMeasure_gibbs (n := n) hchi beta
  exact Measure.isProbabilityMeasure_map measurable_slice0.aemeasurable

end Measures

section EnergyForm

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] {n : ℕ} {chi : G → ℝ} {beta : ℝ}

/-- The finite-spacing physical Hilbert space: gauge-field wavefunctions on a
time slice, square integrable for the literal Wilson slice measure. -/
noncomputable abbrev SliceL2 (n : ℕ) (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (beta : ℝ) (chi : G → ℝ) : Type _ :=
  Lp ℂ 2 (sliceMeasure n G beta chi)

/-- Pulling a slice wavefunction back along the time-zero slice map: an isometry
of the slice space into `L²` of the full Wilson–Gibbs measure. -/
noncomputable def embed0 (n : ℕ) (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (beta : ℝ) (chi : G → ℝ) :
    SliceL2 n G beta chi →ₗᵢ[ℂ] Lp ℂ 2 (gibbs n G beta chi) :=
  Lp.compMeasurePreservingₗᵢ ℂ slice0 (measurePreserving_slice0 beta chi)

/-- Pulling a slice wavefunction back along the time-one slice map. -/
noncomputable def embed1 (hchi : Continuous chi) (beta : ℝ) :
    SliceL2 n G beta chi →ₗᵢ[ℂ] Lp ℂ 2 (gibbs n G beta chi) :=
  Lp.compMeasurePreservingₗᵢ ℂ slice1 (measurePreserving_slice1 hchi beta)

/-- **The literal finite-spacing Yang–Mills energy form**
`q(φ,ψ) = ⟪φ,ψ⟫ − ½(⟪φ∘p₀,ψ∘p₁⟫ + ⟪φ∘p₁,ψ∘p₀⟫)`, that is `1 − ½(T + T*)` for
the Euclidean transfer operator `T` of the Wilson–Gibbs measure.  Sesquilinearity,
Hermiticity and the bound `2` are proved; no field is assumed. -/
noncomputable def energyForm (hchi : Continuous chi) (beta : ℝ) :
    Clay.BoundedSesqForm (SliceL2 n G beta chi) where
  form φ ψ := ⟪φ, ψ⟫_ℂ - (1 / 2 : ℂ) *
    (⟪embed0 n G beta chi φ, embed1 hchi beta ψ⟫_ℂ
      + ⟪embed1 hchi beta φ, embed0 n G beta chi ψ⟫_ℂ)
  bound := 2
  bound_nonneg := by norm_num
  add_left := by
    intro x y z
    simp only [map_add, inner_add_left]
    ring
  smul_left := by
    intro c x y
    simp only [map_smul, inner_smul_left]
    ring
  norm_le := by
    intro x y
    have h0x : ‖embed0 n G beta chi x‖ = ‖x‖ := (embed0 n G beta chi).norm_map x
    have h0y : ‖embed0 n G beta chi y‖ = ‖y‖ := (embed0 n G beta chi).norm_map y
    have h1x : ‖embed1 hchi beta x‖ = ‖x‖ := (embed1 hchi beta).norm_map x
    have h1y : ‖embed1 hchi beta y‖ = ‖y‖ := (embed1 hchi beta).norm_map y
    have hA : ‖⟪x, y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm _ _
    have hB : ‖⟪embed0 n G beta chi x, embed1 hchi beta y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ := by
      have := norm_inner_le_norm (𝕜 := ℂ) (embed0 n G beta chi x) (embed1 hchi beta y)
      rwa [h0x, h1y] at this
    have hC : ‖⟪embed1 hchi beta x, embed0 n G beta chi y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ := by
      have := norm_inner_le_norm (𝕜 := ℂ) (embed1 hchi beta x) (embed0 n G beta chi y)
      rwa [h1x, h0y] at this
    have hsum : ‖⟪embed0 n G beta chi x, embed1 hchi beta y⟫_ℂ
        + ⟪embed1 hchi beta x, embed0 n G beta chi y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ + ‖x‖ * ‖y‖ :=
      (norm_add_le _ _).trans (add_le_add hB hC)
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [hhalf]
    linarith [hA, hsum]
  sesq_symm := by
    intro x y
    have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
      rw [map_div₀]
      norm_num [Complex.ext_iff]
    simp only [map_sub, map_mul, map_add, inner_conj_symm, hhalf]
    ring

@[simp] theorem energyForm_apply (hchi : Continuous chi) (beta : ℝ)
    (φ ψ : SliceL2 n G beta chi) :
    (energyForm hchi beta).form φ ψ = ⟪φ, ψ⟫_ℂ - (1 / 2 : ℂ) *
      (⟪embed0 n G beta chi φ, embed1 hchi beta ψ⟫_ℂ
        + ⟪embed1 hchi beta φ, embed0 n G beta chi ψ⟫_ℂ) := rfl

section Vacuum

/-- **The lattice vacuum**: the constant wavefunction of the slice measure. -/
noncomputable def vacuum (hchi : Continuous chi) (beta : ℝ) : SliceL2 n G beta chi :=
  letI := isProbabilityMeasure_sliceMeasure (n := n) hchi beta
  Lp.const 2 (sliceMeasure n G beta chi) (1 : ℂ)

/-- The vacuum is a unit vector: the slice measure is a probability measure. -/
theorem norm_vacuum (hchi : Continuous chi) (beta : ℝ) :
    ‖vacuum hchi beta (n := n)‖ = 1 := by
  haveI := isProbabilityMeasure_sliceMeasure (n := n) hchi beta
  rw [vacuum, Lp.norm_const] <;> simp

/-- Both slice maps send the vacuum to the same constant wavefunction of the
Wilson–Gibbs measure: the transfer-operator identity `T Ω = Ω`. -/
theorem embed_vacuum (hchi : Continuous chi) (beta : ℝ) :
    embed0 n G beta chi (vacuum hchi beta) = embed1 hchi beta (vacuum hchi beta) := rfl

/-- **The energy form annihilates the vacuum.** -/
theorem energyForm_vacuum (hchi : Continuous chi) (beta : ℝ) (φ : SliceL2 n G beta chi) :
    (energyForm hchi beta).form φ (vacuum hchi beta) = 0 := by
  have h1 : ⟪embed0 n G beta chi φ, embed1 hchi beta (vacuum hchi beta)⟫_ℂ
      = ⟪φ, vacuum hchi beta⟫_ℂ := by
    rw [← embed_vacuum hchi beta]
    exact (embed0 n G beta chi).inner_map_map _ _
  have h2 : ⟪embed1 hchi beta φ, embed0 n G beta chi (vacuum hchi beta)⟫_ℂ
      = ⟪φ, vacuum hchi beta⟫_ℂ := by
    rw [embed_vacuum hchi beta]
    exact (embed1 hchi beta).inner_map_map _ _
  rw [energyForm_apply, h1, h2]
  ring

/-- Rescaling a bounded Hermitian form by a nonnegative constant.  The physical
Hamiltonian at lattice spacing `a` is `a⁻¹(1 − ½(T+T*))`, so the scale is where
the lattice spacing enters. -/
noncomputable def scaleForm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c : ℝ) (hc : 0 ≤ c) (q : Clay.BoundedSesqForm E) : Clay.BoundedSesqForm E where
  form x y := (c : ℂ) * q.form x y
  bound := c * q.bound
  bound_nonneg := mul_nonneg hc q.bound_nonneg
  add_left := by intro x y z; rw [q.add_left]; ring
  smul_left := by intro c' x y; rw [q.smul_left]; ring
  norm_le := by
    intro x y
    rw [norm_mul, show ‖(c : ℂ)‖ = c by simp [abs_of_nonneg hc]]
    calc c * ‖q.form x y‖ ≤ c * (q.bound * ‖x‖ * ‖y‖) := by
          exact mul_le_mul_of_nonneg_left (q.norm_le x y) hc
      _ = c * q.bound * ‖x‖ * ‖y‖ := by ring
  sesq_symm := by
    intro x y
    rw [q.sesq_symm x y]
    simp

@[simp] theorem scaleForm_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c : ℝ) (hc : 0 ≤ c) (q : Clay.BoundedSesqForm E) (x y : E) :
    (scaleForm c hc q).form x y = (c : ℂ) * q.form x y := rfl

end Vacuum

end EnergyForm

end RequestProject.YangMills.Lattice

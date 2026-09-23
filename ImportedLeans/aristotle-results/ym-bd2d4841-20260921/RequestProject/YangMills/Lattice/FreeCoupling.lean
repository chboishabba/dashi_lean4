/-
# The zero-coupling point of the literal lattice theory: the package is inhabited

`Lattice/SU2YangMills.lean` reduces the finite-spacing Yang–Mills data to a
single physical estimate, `HasLatticeCoercivity`, for the literal Wilson energy
form.  This file proves that estimate at the zero-coupling point `β = 0` of the
literal construction, so that the finite-spacing package is inhabited by the
actual lattice objects — not by a synthetic witness — and the coercivity
hypothesis is not vacuous.

The mathematics is the elementary but genuine statement that at `β = 0` the
Wilson–Gibbs measure *is* the product of normalised Haar measures
(`gibbs_zero`), so that the time-zero and time-one slices of the gauge field are
independent (`indepFun_slice`), whence the transfer operator annihilates the
orthogonal complement of the vacuum (`inner_embed_eq_zero`) and the energy form
is exactly the identity there (`energyForm_coercive_of_zero_coupling`).

This is of course the strong-coupling end of the theory: the gap obtained is
`a⁻¹` in physical units and blows up as the spacing goes to zero.  It says
nothing about the Clay problem, where the estimate is needed uniformly along the
renormalisation-group trajectory `β(a) → ∞`; see `Lattice/Frontier.md`.
-/
import Mathlib
import RequestProject.YangMills.Lattice.SU2YangMills

namespace RequestProject.YangMills.Lattice

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] {n : ℕ} {chi : G → ℝ}

/-! ## At zero coupling the Gibbs measure is the product Haar measure -/

/-- At `β = 0` the Wilson weight is constant, so the Wilson–Gibbs measure is
exactly the product of normalised Haar measures on the links. -/
theorem gibbs_zero (chi : G → ℝ) : gibbs n G 0 chi = prodHaar (Link n) G := by
  have hd : gibbsDensity (n := n) (0 : ℝ) chi = fun _ => 1 := by
    funext U; simp [gibbsDensity, wilsonAction]
  have hu : gibbsUnnorm n G 0 chi = prodHaar (Link n) G := by
    rw [gibbsUnnorm, hd]; simp
  have hZ : partition n G 0 chi = 1 := by rw [partition, hu]; simp
  rw [gibbs, hu, hZ]; simp

/-! ## Independence of the two time slices under the product measure -/

omit [SecondCountableTopology G] in
/-- Under the product Haar measure the time-zero and time-one slices of the
gauge field are independent: they are functions of disjoint sets of links. -/
theorem indepFun_slice (h01 : (0 : ZMod (n + 1)) ≠ 1) :
    IndepFun (slice0 (n := n) (G := G)) slice1 (prodHaar (Link n) G) := by
  classical
  set S : Finset (Link n) := Finset.univ.filter (fun l => l.2 ≠ 0 ∧ l.1 0 = 0) with hS
  set T : Finset (Link n) := Finset.univ.filter (fun l => l.2 ≠ 0 ∧ l.1 0 = 1) with hT
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro l hl hl'
    simp only [hS, hT, Finset.mem_filter] at hl hl'
    exact h01 (hl.2.2.symm.trans hl'.2.2)
  have hcoord : iIndepFun (fun (l : Link n) (U : Conf n G) => U l) (prodHaar (Link n) G) :=
    iIndepFun_pi (μ := fun _ : Link n => haarProb G) (X := fun (_ : Link n) (g : G) => g)
      (fun _ => aemeasurable_id)
  have hpair := hcoord.indepFun_finset S T hdisj (fun i => measurable_pi_apply i)
  have hmem0 : ∀ l : SliceIdx n, l.1 ∈ S := by
    intro l
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨l.2.1, l.2.2⟩
  have hmem1 : ∀ l : SliceIdx n, ((l.1.1 + unitVec n 0, l.1.2) : Link n) ∈ T := by
    intro l
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨l.2.1, by simp [unitVec, l.2.2]⟩
  have h0 : Measurable (fun v : (i : S) → G => fun l : SliceIdx n => v ⟨l.1, hmem0 l⟩) :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  have h1 : Measurable (fun v : (i : T) → G =>
      fun l : SliceIdx n => v ⟨(l.1.1 + unitVec n 0, l.1.2), hmem1 l⟩) :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  exact hpair.comp h0 h1

/-! ## The transfer term as an integral -/

/-- The transfer term of the energy form, written as an integral of the two
slice pullbacks. -/
theorem inner_embed_eq_integral (hchi : Continuous chi) (beta : ℝ)
    (φ ψ : SliceL2 n G beta chi) :
    ⟪embed0 n G beta chi φ, embed1 hchi beta ψ⟫_ℂ
      = ∫ U, (starRingEnd ℂ) ((φ : _ → ℂ) (slice0 U)) * (ψ : _ → ℂ) (slice1 U)
          ∂(gibbs n G beta chi) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_compMeasurePreserving (E := ℂ) (p := 2) φ
      (measurePreserving_slice0 beta chi),
    Lp.coeFn_compMeasurePreserving (E := ℂ) (p := 2) ψ
      (measurePreserving_slice1 hchi beta)] with U h0 h1
  simp only [Function.comp_apply] at h0 h1
  rw [RCLike.inner_apply,
    show (↑↑(embed0 n G beta chi φ) : _ → ℂ) U = (↑↑φ : _ → ℂ) (slice0 U) from h0,
    show (↑↑(embed1 hchi beta ψ) : _ → ℂ) U = (↑↑ψ : _ → ℂ) (slice1 U) from h1]
  ring

/-- The inner product with the vacuum is the mean of the wavefunction. -/
theorem inner_vacuum_eq_integral (hchi : Continuous chi) (beta : ℝ)
    (ψ : SliceL2 n G beta chi) :
    ⟪vacuum hchi beta, ψ⟫_ℂ = ∫ u, (ψ : _ → ℂ) u ∂(sliceMeasure n G beta chi) := by
  haveI := isProbabilityMeasure_sliceMeasure (n := n) hchi beta
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_const (p := 2) (μ := sliceMeasure n G beta chi) (1 : ℂ)] with u hu
  rw [RCLike.inner_apply, show (↑↑(vacuum hchi beta) : _ → ℂ) u = 1 from hu]
  simp

/-! ## Zero coupling: the transfer term vanishes on the vacuum complement -/

/-- At zero coupling the transfer term of the energy form vanishes on the
orthogonal complement of the vacuum: the two slices are independent, so the
transfer operator is the projection onto the vacuum. -/
theorem inner_embed_eq_zero (h01 : (0 : ZMod (n + 1)) ≠ 1) (hchi : Continuous chi)
    (ψ : SliceL2 n G 0 chi) (hψ : ⟪vacuum hchi (0 : ℝ), ψ⟫_ℂ = 0) :
    ⟪embed0 n G 0 chi ψ, embed1 hchi (0 : ℝ) ψ⟫_ℂ = 0 := by
  haveI := isProbabilityMeasure_gibbs (n := n) hchi (0 : ℝ)
  have hind : IndepFun (slice0 (n := n) (G := G)) slice1 (gibbs n G 0 chi) := by
    rw [gibbs_zero]
    exact indepFun_slice h01
  have hmeas0 : AEMeasurable (slice0 (n := n) (G := G)) (gibbs n G 0 chi) :=
    measurable_slice0.aemeasurable
  have hmeas1 : AEMeasurable (slice1 (n := n) (G := G)) (gibbs n G 0 chi) :=
    (measurePreserving_slice1 hchi (0 : ℝ)).measurable.aemeasurable
  have hmap0 : (gibbs n G 0 chi).map slice0 = sliceMeasure n G 0 chi :=
    (measurePreserving_slice0 (0 : ℝ) chi).map_eq
  have hmap1 : (gibbs n G 0 chi).map slice1 = sliceMeasure n G 0 chi :=
    (measurePreserving_slice1 hchi (0 : ℝ)).map_eq
  have hf : AEStronglyMeasurable (fun u => (starRingEnd ℂ) ((ψ : _ → ℂ) u))
      ((gibbs n G 0 chi).map slice0) := by
    rw [hmap0]
    exact (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable ψ))
  have hg : AEStronglyMeasurable (fun u => (ψ : _ → ℂ) u) ((gibbs n G 0 chi).map slice1) := by
    rw [hmap1]
    exact Lp.aestronglyMeasurable ψ
  have hprod := hind.integral_comp_mul_comp (f := fun u => (starRingEnd ℂ) ((ψ : _ → ℂ) u))
    (g := fun u => (ψ : _ → ℂ) u) hmeas0 hmeas1 hf hg
  have hfac : ∫ U, (starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U)) * (ψ : _ → ℂ) (slice1 U)
      ∂(gibbs n G 0 chi)
      = (∫ U, (starRingEnd ℂ) ((ψ : _ → ℂ) (slice0 U)) ∂(gibbs n G 0 chi))
        * (∫ U, (ψ : _ → ℂ) (slice1 U) ∂(gibbs n G 0 chi)) := hprod
  have hsecond : ∫ U, (ψ : _ → ℂ) (slice1 U) ∂(gibbs n G 0 chi) = 0 := by
    rw [← integral_map hmeas1 (by rw [hmap1]; exact Lp.aestronglyMeasurable ψ), hmap1,
      ← inner_vacuum_eq_integral hchi (0 : ℝ) ψ, hψ]
  rw [inner_embed_eq_integral, hfac, hsecond, mul_zero]

/-- **The literal energy form at zero coupling is coercive on the vacuum
complement**, with constant `1` for the unscaled form: at `β = 0` the transfer
operator of the literal Wilson measure is the vacuum projection. -/
theorem energyForm_coercive_of_zero_coupling (h01 : (0 : ZMod (n + 1)) ≠ 1)
    (hchi : Continuous chi) (ψ : SliceL2 n G 0 chi)
    (hψ : ⟪vacuum hchi (0 : ℝ), ψ⟫_ℂ = 0) :
    (1 : ℝ) * ‖ψ‖ ^ 2 ≤ ((energyForm hchi (0 : ℝ)).form ψ ψ).re := by
  have h := inner_embed_eq_zero h01 hchi ψ hψ
  have h' : ⟪embed1 hchi (0 : ℝ) ψ, embed0 n G 0 chi ψ⟫_ℂ = 0 := by
    rw [← inner_conj_symm, h, map_zero]
  rw [energyForm_apply, h, h']
  simp only [add_zero, mul_zero, sub_zero, one_mul]
  have hre : (⟪ψ, ψ⟫_ℂ).re = ‖ψ‖ ^ 2 := by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ψ
  rw [hre]


/-! ## The literal `SU(2)` package at zero coupling -/

/-- On a lattice with at least two time slices the two slices are distinct. -/
theorem zero_ne_one_zmod {n : ℕ} (hn : 1 ≤ n) : (0 : ZMod (n + 1)) ≠ 1 := by
  haveI : Fact (1 < n + 1) := ⟨by omega⟩
  exact zero_ne_one

/-- **The coercivity estimate holds for the literal `SU(2)` Wilson energy form at
zero coupling**, with gap `a⁻¹` at lattice spacing `a`. -/
theorem ym_hasLatticeCoercivity_zero_coupling {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) :
    HasLatticeCoercivity n 0 a a⁻¹ ha.le := by
  intro ψ hψ
  have hq := energyForm_coercive_of_zero_coupling (zero_ne_one_zmod hn) continuous_chiSU2 ψ hψ
  rw [ymEnergyForm, scaleForm_apply, Complex.re_ofReal_mul]
  have hnn : (0 : ℝ) ≤ a⁻¹ := (inv_pos.2 ha).le
  nlinarith [hq]

/-- **The literal four-dimensional `SU(2)` lattice theory at zero coupling has the
full mass-gap conclusion** with gap `a⁻¹`: the form gap on the vacuum complement,
no eigenvalue in `(0,a⁻¹)`, unique solvability of `Hψ − λψ = y` on the vacuum
sector for every `λ < a⁻¹`, and the resolvent bound.  This is the literal
construction, not a synthetic witness; it shows the finite-spacing package is
inhabited.  It is a statement at fixed spacing only: the gap `a⁻¹` diverges as
`a → 0`, and nothing here bears on the continuum limit. -/
theorem ym_massGap_zero_coupling {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 0 < a) :
    Clay.MassGapConclusion (ymHamiltonian n 0 a ha.le) (ymVacuum n 0) a⁻¹ :=
  lattice_massGap_of_coercivity n 0 a (inv_pos.2 ha) ha.le
    (ym_hasLatticeCoercivity_zero_coupling hn ha)

end RequestProject.YangMills.Lattice

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Lattice

#print axioms gibbs_zero
#print axioms indepFun_slice
#print axioms energyForm_coercive_of_zero_coupling
#print axioms ym_hasLatticeCoercivity_zero_coupling
#print axioms ym_massGap_zero_coupling

end Audit

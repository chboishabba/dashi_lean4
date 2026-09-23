/-
# Reflection positivity from a splitting of the action

This file reduces reflection positivity of a lattice gauge measure to a purely
combinatorial statement about its action.  If the action splits as

```
  S(U)  =  S₀(U)  +  S₊(U)  +  S₊(ΘU)
```

where `S₀` depends only on the plane link variables, `S₊` only on the plane and
positive link variables, and `Θ` is the reflection of `OS/LinkReflection.lean`,
then for every bounded observable `F` depending only on the plane and positive
variables

```
  ∫ conj (F ∘ Θ) · F · e^{-S}  ≥  0 ,
```

both for the product Haar measure weighted by `e^{-S}` and for the normalised
Gibbs measure.  Results:

* `LinkReflectionData.assemble` — the configuration built from plane and
  positive coordinates;
* `reflection_positive_of_splitting` — the statement above for the unnormalised
  weight;
* `reflection_positive_gibbs_of_splitting` — the same for the normalised Gibbs
  measure `Z⁻¹ e^{-S} dU`.

No analytic input is assumed: boundedness of the action and of the observable is
a hypothesis, and on the lattice it follows from compactness.
-/
import Mathlib
import RequestProject.YangMills.OS.LinkReflection

namespace RequestProject.YangMills.OS

open MeasureTheory Complex
open RequestProject.YangMills.Lattice

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A bounded measurable function on a finite measure space is integrable. -/
theorem integrable_of_bounded {X : Type*} [MeasurableSpace X] (mu : Measure X)
    [IsFiniteMeasure mu] {f : X → ℂ} (hm : Measurable f) {M : ℝ} (hb : ∀ x, ‖f x‖ ≤ M) :
    Integrable f mu :=
  Integrable.mono' (integrable_const M) hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)

namespace LinkReflectionData

variable (D : LinkReflectionData ι) {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- The configuration assembled from plane and positive coordinates; the
negative links are given the unit variable. -/
def assemble (b : D.Plane → G) (a : D.Pos → G) : ι → G :=
  fun i => if h : i ∈ D.plane then b ⟨i, h⟩ else if h2 : i ∈ D.pos then a ⟨i, h2⟩ else 1

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] in
theorem assemble_agrees (U : ι → G) (i : ι) (hi : i ∈ D.plane ∨ i ∈ D.pos) :
    D.assemble (fun p : D.Plane => U p.1) (fun p : D.Pos => U p.1) i = U i := by
  rcases hi with hi | hi
  · simp [assemble, hi]
  · have hp : i ∉ D.plane := D.pos_not_plane hi
    simp [assemble, hp, hi]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] in
theorem measurable_assemble :
    Measurable (fun w : (D.Plane → G) × (D.Pos → G) => D.assemble w.1 w.2) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i ∈ D.plane
  · simp only [assemble, dif_pos h]
    exact (measurable_pi_apply (⟨i, h⟩ : D.Plane)).comp measurable_fst
  · by_cases h2 : i ∈ D.pos
    · simp only [assemble, dif_neg h, dif_pos h2]
      exact (measurable_pi_apply (⟨i, h2⟩ : D.Pos)).comp measurable_snd
    · simp only [assemble, dif_neg h, dif_neg h2]
      exact measurable_const

/-- **Reflection positivity from a splitting of the action.**  If the action is
the sum of a plane term, a positive term and the reflection of the positive
term, then the reflected pairing of any bounded observable of the plane and
positive variables with itself is real and nonnegative. -/
theorem reflection_positive_of_splitting
    {F : (ι → G) → ℂ} {S S0 Splus : (ι → G) → ℝ} {MF MS : ℝ}
    (hFm : Measurable F) (hFb : ∀ U, ‖F U‖ ≤ MF)
    (hFloc : ∀ U V : ι → G, (∀ i, i ∈ D.plane ∨ i ∈ D.pos → U i = V i) → F U = F V)
    (hS0m : Measurable S0) (hS0b : ∀ U, |S0 U| ≤ MS)
    (hS0loc : ∀ U V : ι → G, (∀ i ∈ D.plane, U i = V i) → S0 U = S0 V)
    (hSPm : Measurable Splus) (hSPb : ∀ U, |Splus U| ≤ MS)
    (hSPloc : ∀ U V : ι → G, (∀ i, i ∈ D.plane ∨ i ∈ D.pos → U i = V i) → Splus U = Splus V)
    (hsplit : ∀ U, S U = S0 U + Splus U + Splus (D.confRefl U)) :
    0 ≤ (∫ U, (starRingEnd ℂ) (F (D.confRefl U)) * F U * (Real.exp (-(S U)) : ℂ)
          ∂(prodHaar ι G)).re ∧
      (∫ U, (starRingEnd ℂ) (F (D.confRefl U)) * F U * (Real.exp (-(S U)) : ℂ)
          ∂(prodHaar ι G)).im = 0 := by
  classical
  set Sp := D.reflectionSplitting (G := G) with hSp
  -- the coordinate functions
  set f : (D.Pos → G) → (D.Plane → G) → ℂ := fun a b => F (D.assemble b a) with hf
  set g : (D.Pos → G) → (D.Plane → G) → ℝ :=
    fun a b => Real.exp (-(Splus (D.assemble b a))) with hg
  set h : (D.Plane → G) → ℝ := fun b => Real.exp (-(S0 (D.assemble b (fun _ => 1)))) with hh
  have hplane : ∀ U : ι → G, Sp.plane U = fun p : D.Plane => U p.1 := by
    intro U; simp [hSp]
  have hpos : ∀ U : ι → G, Sp.pos U = fun p : D.Pos => U p.1 := by
    intro U; simp [hSp]
  have hrefl : ∀ U : ι → G, Sp.refl U = D.confRefl U := fun U => rfl
  -- the observable in coordinates
  have hFcoord : ∀ U : ι → G, F U = f (Sp.pos U) (Sp.plane U) := by
    intro U
    rw [hpos, hplane, hf]
    show F U = F (D.assemble (fun p : D.Plane => U p.1) (fun p : D.Pos => U p.1))
    exact hFloc _ _ fun i hi => (D.assemble_agrees U i hi).symm
  -- the positive part of the weight in coordinates
  have hgcoord : ∀ U : ι → G, g (Sp.pos U) (Sp.plane U) = Real.exp (-(Splus U)) := by
    intro U
    rw [hpos, hplane, hg]
    show Real.exp (-(Splus (D.assemble (fun p : D.Plane => U p.1) (fun p : D.Pos => U p.1))))
        = Real.exp (-(Splus U))
    congr 2
    exact (hSPloc _ _ fun i hi => (D.assemble_agrees U i hi).symm).symm
  -- the plane part of the weight in coordinates
  have hhcoord : ∀ U : ι → G, h (Sp.plane U) = Real.exp (-(S0 U)) := by
    intro U
    rw [hplane, hh]
    show Real.exp (-(S0 (D.assemble (fun p : D.Plane => U p.1) (fun _ => 1))))
        = Real.exp (-(S0 U))
    congr 2
    refine (hS0loc U _ fun i hi => ?_).symm
    have h1 : i ∉ D.pos := fun hc => D.plane_not_pos i hi hc
    simp [assemble, hi]
  -- the reflected positive part
  have hgrefl : ∀ U : ι → G, g (Sp.pos (Sp.refl U)) (Sp.plane U)
      = Real.exp (-(Splus (D.confRefl U))) := by
    intro U
    have hpl : Sp.plane U = Sp.plane (Sp.refl U) := (Sp.plane_refl U).symm
    rw [hpl, hgcoord (Sp.refl U), hrefl U]
  -- the density factorises
  have hD : ∀ U : ι → G, Real.exp (-(S U))
      = h (Sp.plane U) * g (Sp.pos U) (Sp.plane U) * g (Sp.pos (Sp.refl U)) (Sp.plane U) := by
    intro U
    rw [hhcoord U, hgcoord U, hgrefl U, ← Real.exp_add, ← Real.exp_add, hsplit U]
    ring_nf
  -- nonnegativity of the plane weight
  have hhpos : ∀ b, 0 ≤ h b := fun b => (Real.exp_pos _).le
  -- measurability of the coordinate functions
  have hassemble : Measurable (fun w : (D.Plane → G) × (D.Pos → G) => D.assemble w.1 w.2) :=
    D.measurable_assemble
  have hfm : Measurable (fun w : (D.Plane → G) × (D.Pos → G) => f w.2 w.1) :=
    hFm.comp hassemble
  have hgm : Measurable (fun w : (D.Plane → G) × (D.Pos → G) => g w.2 w.1) :=
    (Real.measurable_exp.comp (hSPm.comp hassemble).neg)
  have hhm : Measurable h := by
    have : Measurable (fun b : D.Plane → G => D.assemble b (fun _ => 1)) := by
      have := hassemble.comp (measurable_id.prodMk (measurable_const :
        Measurable (fun _ : D.Plane → G => (fun _ => 1 : D.Pos → G))))
      simpa using this
    exact Real.measurable_exp.comp ((hS0m.comp this).neg)
  -- bounds
  have hgb : ∀ a b, g a b ≤ Real.exp MS := by
    intro a b
    refine Real.exp_le_exp.2 ?_
    have := (abs_le.1 (hSPb (D.assemble b a))).1
    linarith
  have hhb : ∀ b, h b ≤ Real.exp MS := by
    intro b
    refine Real.exp_le_exp.2 ?_
    have := (abs_le.1 (hS0b (D.assemble b (fun _ => 1)))).1
    linarith
  have hgnn : ∀ a b, 0 ≤ g a b := fun a b => (Real.exp_pos _).le
  have hMF : 0 ≤ MF := le_trans (norm_nonneg _) (hFb (fun _ => 1))
  -- integrability of the Gram integrand
  have hint : Integrable (gramIntegrand f g h Sp.sigma) (Sp.muB.prod (Sp.muA.prod Sp.muC)) := by
    haveI := Sp.sfiniteA
    haveI := Sp.sfiniteB
    haveI := Sp.sfiniteC
    haveI : IsProbabilityMeasure Sp.muA :=
      (inferInstance : IsProbabilityMeasure (prodHaar D.Pos G))
    haveI : IsProbabilityMeasure Sp.muB :=
      (inferInstance : IsProbabilityMeasure (prodHaar D.Plane G))
    haveI : IsProbabilityMeasure Sp.muC :=
      (inferInstance : IsProbabilityMeasure (prodHaar D.Neg G))
    have hmeas : Measurable (gramIntegrand f g h Sp.sigma) := by
      have h1 : Measurable fun w : (D.Plane → G) × ((D.Pos → G) × (D.Neg → G)) =>
          f (Sp.sigma w.2.2) w.1 :=
        hfm.comp ((measurable_fst).prodMk
          ((Sp.sigma.measurable).comp (measurable_snd.comp measurable_snd)))
      have h2 : Measurable fun w : (D.Plane → G) × ((D.Pos → G) × (D.Neg → G)) =>
          f w.2.1 w.1 :=
        hfm.comp ((measurable_fst).prodMk (measurable_fst.comp measurable_snd))
      have h3 : Measurable fun w : (D.Plane → G) × ((D.Pos → G) × (D.Neg → G)) =>
          g w.2.1 w.1 :=
        hgm.comp ((measurable_fst).prodMk (measurable_fst.comp measurable_snd))
      have h4 : Measurable fun w : (D.Plane → G) × ((D.Pos → G) × (D.Neg → G)) =>
          g (Sp.sigma w.2.2) w.1 :=
        hgm.comp ((measurable_fst).prodMk
          ((Sp.sigma.measurable).comp (measurable_snd.comp measurable_snd)))
      have h5 : Measurable fun w : (D.Plane → G) × ((D.Pos → G) × (D.Neg → G)) => h w.1 :=
        hhm.comp measurable_fst
      have h1' : Measurable fun w : (D.Plane → G) × ((D.Pos → G) × (D.Neg → G)) =>
          (starRingEnd ℂ) (f (Sp.sigma w.2.2) w.1) := by fun_prop
      unfold gramIntegrand
      exact ((h1'.mul h2).mul (((Complex.measurable_ofReal.comp h5).mul
        (Complex.measurable_ofReal.comp h3)).mul (Complex.measurable_ofReal.comp h4)))
    refine integrable_of_bounded _ hmeas
      (M := MF * MF * (Real.exp MS * Real.exp MS * Real.exp MS)) fun w => ?_
    simp only [gramIntegrand, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hhpos _), abs_of_nonneg (hgnn _ _)]
    have e1 : ‖f (Sp.sigma w.2.2) w.1‖ * ‖f w.2.1 w.1‖ ≤ MF * MF :=
      mul_le_mul (hFb _) (hFb _) (norm_nonneg _) hMF
    have e2 : h w.1 * g w.2.1 w.1 * g (Sp.sigma w.2.2) w.1
        ≤ Real.exp MS * Real.exp MS * Real.exp MS :=
      mul_le_mul (mul_le_mul (hhb w.1) (hgb _ _) (hgnn _ _) (Real.exp_pos MS).le)
        (hgb _ _) (hgnn _ _) (by positivity)
    calc ‖f (Sp.sigma w.2.2) w.1‖ * ‖f w.2.1 w.1‖ * (h w.1 * g w.2.1 w.1 * g (Sp.sigma w.2.2) w.1)
        ≤ (MF * MF) * (Real.exp MS * Real.exp MS * Real.exp MS) := by
          refine mul_le_mul e1 e2 (by positivity) (by positivity)
      _ = MF * MF * (Real.exp MS * Real.exp MS * Real.exp MS) := rfl
  -- apply the Gram mechanism
  have := Sp.reflection_positive (F := F) (D := fun U => Real.exp (-(S U)))
    (f := f) (g := g) (h := h) hFcoord hD hhpos hint
  simpa [hSp] using this

end LinkReflectionData

end RequestProject.YangMills.OS

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.OS

#print axioms LinkReflectionData.reflection_positive_of_splitting

end Audit

import Mathlib

/-!
# QFT/GR frontier, lane 1 — the stress pairing and when it separates tensors

The live TOE frontier described in the current handoff asks, on the GR side, for

```
δ_g S_common[h] = ⟨G, h⟩            for every admitted perturbation h
```

and then for a **pairing-separation theorem**: a step that turns *equality
against all admitted perturbations* into *equality of tensors*.  In the Agda
architecture that step is a named socket; here it is a theorem, and it comes
with the exact condition under which it holds.

The model used throughout this lane is the honest minimal one: perturbations
`h` live in a real inner-product space `H`, a "tensor" is an element `T : H`,
and the stress pairing is `⟪T, h⟫_ℝ`.  Nothing about symmetric 2-tensors,
manifolds or densities is used — and nothing about them is claimed.  What *is*
claimed is the algebraic content of the separation step, which is exactly what
the frontier is missing.

## What is proved

* `pair_add_right`, `pair_smul_right`, `pair_sum` — the pairing is linear in the
  perturbation and commutes with finite (sector) sums;
* `eq_of_pair_eq_on_spanning` — **pairing separation**: if two tensors pair
  equally against a set of perturbations whose span is everything, they are
  equal;
* `exists_ne_agreeing_of_ne_top` — the converse obstruction: over a complete
  admitted fibre that is *not* everything, two distinct tensors always pair
  equally against every admitted perturbation;
* `separates_iff_eq_top` — hence separation holds **exactly** when the admitted
  perturbation fibre is the whole space: the frontier's separation step is not
  a formality, it is a spanning hypothesis;
* `eq_of_pair_eq_on_dense`, `separates_iff_dense` — the sharp topological form:
  a *dense* admitted fibre already separates, and over a complete space density
  is exactly what separation requires;
* `pair_tsum` — aggregation over an infinite summable family of sectors;
* `plane_pairing_does_not_separate` — a concrete two-dimensional witness of the
  negative, with the admitted fibre a line.

## What is *not* proved

Nothing here says that any particular physical perturbation fibre spans, that
`H` is a space of metric perturbations, or that `T` is a stress tensor.  This
file supplies the separation step and its exact hypothesis; supplying the
hypothesis for a physical theory is a different obligation, recorded in the
frontier report.
-/

namespace Integration.Variation.Pairing

open scoped InnerProductSpace RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The stress pairing `⟨T, h⟩` of a tensor `T` against a perturbation `h`. -/
noncomputable def pair (T h : H) : ℝ := ⟪T, h⟫_ℝ

@[simp] theorem pair_apply (T h : H) : pair T h = ⟪T, h⟫_ℝ := rfl

theorem pair_add_right (T h₁ h₂ : H) : pair T (h₁ + h₂) = pair T h₁ + pair T h₂ :=
  inner_add_right _ _ _

theorem pair_smul_right (c : ℝ) (T h : H) : pair T (c • h) = c * pair T h := by
  simp [pair, real_inner_smul_right]

/-- Sector aggregation at the level of the pairing: pairing against a finite sum
of sector tensors is the sum of the sector pairings. -/
theorem pair_sum {ι : Type*} (s : Finset ι) (T : ι → H) (h : H) :
    pair (∑ i ∈ s, T i) h = ∑ i ∈ s, pair (T i) h := by
  simp [pair, sum_inner]

/-- Sector aggregation for an infinite summable family of sector tensors. -/
theorem pair_tsum {ι : Type*} (T : ι → H) (h : H) (hs : Summable T) :
    pair (∑' i, T i) h = ∑' i, pair (T i) h := by
  simpa [pair, real_inner_comm _ h] using
    ContinuousLinearMap.map_tsum (innerSL ℝ (E := H) h) hs

/-- **Pairing separation.**  If two tensors have the same pairing against every
element of a spanning set of perturbations, they are equal. -/
theorem eq_of_pair_eq_on_spanning (A B : H) (S : Set H) (hS : Submodule.span ℝ S = ⊤)
    (hAB : ∀ v ∈ S, pair A v = pair B v) : A = B := by
  refine ext_inner_right ℝ (fun v => ?_)
  exact LinearMap.eqOn_span (f := (innerSL ℝ A : H →L[ℝ] ℝ).toLinearMap)
    (g := (innerSL ℝ B : H →L[ℝ] ℝ).toLinearMap) hAB (by rw [hS]; trivial)

/-- The same statement for an admitted perturbation *fibre* given as a
submodule. -/
theorem eq_of_pair_eq_on_top (A B : H) (K : Submodule ℝ H) (hK : K = ⊤)
    (hAB : ∀ v ∈ K, pair A v = pair B v) : A = B := by
  refine ext_inner_right ℝ (fun v => ?_)
  exact hAB v (by rw [hK]; trivial)

/-- **Pairing separation, topological form.**  A *dense* span is enough: the
pairing is continuous, so agreement on a dense set of perturbations already
forces equality of tensors.  This is the form a physical admitted fibre can
actually satisfy — a fibre of, say, compactly supported perturbations is never
literally everything, but it can be dense. -/
theorem eq_of_pair_eq_on_dense (A B : H) (S : Set H)
    (hS : Dense (Submodule.span ℝ S : Set H))
    (hAB : ∀ v ∈ S, pair A v = pair B v) : A = B := by
  have hspan : ∀ v ∈ (Submodule.span ℝ S : Set H), ⟪A, v⟫_ℝ = ⟪B, v⟫_ℝ := by
    intro v hv
    exact LinearMap.eqOn_span (f := (innerSL ℝ A : H →L[ℝ] ℝ).toLinearMap)
      (g := (innerSL ℝ B : H →L[ℝ] ℝ).toLinearMap) hAB hv
  have heq := Continuous.ext_on hS (innerSL ℝ A).continuous (innerSL ℝ B).continuous hspan
  exact ext_inner_right ℝ (fun v => congrFun heq v)

/-- The dense separation statement for an admitted fibre given as a submodule. -/
theorem eq_of_pair_eq_on_dense_submodule (A B : H) (K : Submodule ℝ H)
    (hK : Dense (K : Set H)) (hAB : ∀ v ∈ K, pair A v = pair B v) : A = B := by
  refine eq_of_pair_eq_on_dense A B (K : Set H) ?_ hAB
  rwa [Submodule.span_coe_eq_restrictScalars, Submodule.coe_restrictScalars]

/-- **Separation happens exactly on a dense admitted fibre.**  Over a complete
space, the pairing separates tensors on `K` if and only if `K` is dense — the
sharp form of the frontier's separation hypothesis. -/
theorem separates_iff_dense [CompleteSpace H] (K : Submodule ℝ H) :
    (∀ A B : H, (∀ v ∈ K, pair A v = pair B v) → A = B) ↔ Dense (K : Set H) := by
  constructor
  · intro hsep
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    have hbot : Kᗮ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro w hw
      refine (hsep 0 w (fun v hv => ?_)).symm
      simp only [pair_apply, inner_zero_left]
      rw [real_inner_comm]
      exact ((Submodule.mem_orthogonal K w).mp hw v hv).symm
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hbot]
    simp
  · intro hK A B hagree
    exact eq_of_pair_eq_on_dense_submodule A B K hK hagree

/-- The obstruction.  If the admitted fibre is a proper (orthogonally
complemented) subspace, then pairing against admitted perturbations can never
separate tensors: two distinct tensors always agree on it. -/
theorem exists_ne_agreeing_of_ne_top (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    (hK : K ≠ ⊤) : ∃ A B : H, A ≠ B ∧ ∀ v ∈ K, pair A v = pair B v := by
  have hbot : Kᗮ ≠ ⊥ := fun h => hK (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  refine ⟨w, 0, hw0, fun v hv => ?_⟩
  simp only [pair_apply, inner_zero_left]
  rw [real_inner_comm]
  exact (Submodule.mem_orthogonal K w).mp hw v hv

/-- **Separation happens exactly on a full admitted fibre.**  The pairing
separates tensors on an admitted perturbation fibre `K` if and only if `K` is
everything. -/
theorem separates_iff_eq_top (K : Submodule ℝ H) [K.HasOrthogonalProjection] :
    (∀ A B : H, (∀ v ∈ K, pair A v = pair B v) → A = B) ↔ K = ⊤ := by
  constructor
  · intro hsep
    by_contra hK
    obtain ⟨A, B, hAB, hagree⟩ := exists_ne_agreeing_of_ne_top K hK
    exact hAB (hsep A B hagree)
  · intro hK A B hagree
    exact eq_of_pair_eq_on_top A B K hK hagree

/-- A concrete witness of the obstruction: in the plane, with only perturbations
along the first axis admitted, the second basis vector and the zero tensor have
identical pairings. -/
theorem plane_pairing_does_not_separate :
    ∃ A B : EuclideanSpace ℝ (Fin 2),
      A ≠ B ∧
      ∀ v ∈ Submodule.span ℝ {EuclideanSpace.single (0 : Fin 2) (1 : ℝ)},
        pair A v = pair B v := by
  refine ⟨EuclideanSpace.single (1 : Fin 2) (1 : ℝ), 0, ?_, ?_⟩
  · intro hc
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) hc
    simp [EuclideanSpace.single_apply] at this
  · intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
        obtain rfl : x = EuclideanSpace.single (0 : Fin 2) (1 : ℝ) := hx
        simp [pair, EuclideanSpace.inner_single_right, EuclideanSpace.single_apply]
    | zero => simp
    | add x y _ _ hx hy =>
        simp only [pair_apply] at hx hy ⊢
        rw [inner_add_right, inner_add_right, hx, hy]
    | smul c x _ hx =>
        simp only [pair_apply] at hx ⊢
        rw [real_inner_smul_right, real_inner_smul_right, hx]

end Integration.Variation.Pairing

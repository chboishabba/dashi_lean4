/-
# The common carrier is a construction, not a physical hypothesis

`VaryingCarrierTransport.lean` showed that a family of cutoff Hamiltonians on
*different* Hilbert spaces can be fed to the continuum consumer provided only
linear isometric embeddings `J k : E k →ₗᵢ E` into one carrier — no vacuum
compatibility, intertwining or domain-preservation condition is needed, because
the gap hypothesis lives on each cutoff space in its own inner product.

This file removes the remaining half of that obligation: the embeddings
themselves always exist, and are canonical.  For an arbitrary family of Hilbert
spaces the Hilbert-space direct sum `⨁₂ E k = lp E 2` is a Hilbert space into
which every member embeds isometrically and linearly through `lp.single`.

* `carrierEmbedding` — the canonical linear isometry `E i →ₗᵢ[ℂ] lp E 2`;
* `carrierEmbedding_apply_eq_iff_of_ne` etc. are not needed and are not stated:
  the consumer uses nothing but the isometry;
* `exists_isometric_embeddings` — for **every** family of complex inner product
  spaces there is a complete carrier with linear isometric embeddings of all of
  them.

Consequently "a common Hilbert carrier for the cutoff family" is not an open
physical problem: it is discharged here once and for all, for the literal
Yang–Mills family as for any other.  The genuine physical content — the uniform
gap, the convergence of the family, and the identification with the
Osterwalder–Schrader object — is untouched by this file.
-/
import Mathlib

namespace RequestProject.YangMills.CommonCarrier

open scoped InnerProductSpace

universe u v

variable {ι : Type u} [DecidableEq ι] {E : ι → Type v}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]

/-- **The canonical embedding of a member of a family of Hilbert spaces into
their `ℓ²` direct sum**, as a linear isometry. -/
noncomputable def carrierEmbedding (i : ι) : E i →ₗᵢ[ℂ] lp E 2 where
  toFun := lp.single 2 i
  map_add' x y := lp.single_add 2 i x y
  map_smul' c x := lp.single_smul 2 i c x
  norm_map' x := lp.norm_single (by norm_num) i x

@[simp] theorem carrierEmbedding_apply (i : ι) (x : E i) :
    carrierEmbedding i x = lp.single 2 i x := rfl

/-- The `ℓ²` direct sum of complete spaces is complete, so it is a Hilbert
space. -/
instance [∀ i, CompleteSpace (E i)] : CompleteSpace (lp E 2) := by infer_instance

/-- **Common carriers always exist.**  Every family of Hilbert spaces embeds
isometrically and linearly into a single Hilbert space.  This is the entire
content of the "varying carrier" obligation: it is a construction, not a
physical input. -/
theorem exists_isometric_embeddings [∀ i, CompleteSpace (E i)] :
    ∃ (F : Type (max u v)) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℂ F),
      CompleteSpace F ∧ Nonempty (∀ i, E i →ₗᵢ[ℂ] F) :=
  ⟨↥(lp E 2), inferInstance, inferInstance, inferInstance, ⟨fun i => carrierEmbedding i⟩⟩

/-! ## The canonical embeddings are useless for approximation

The `ℓ²` embeddings have pairwise orthogonal ranges, and that makes them unable
to approximate anything: a sequence `k ↦ J k (a k)` converges only to `0`.  So
while a *carrier* always exists, the *particular* embeddings along which the
cutoff family converges are genuine data of the continuum-limit problem, not
something this construction supplies.  The two statements below are what keeps
the recut frontier honest. -/

section Degenerate

variable {E : ℕ → Type v} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]

open Filter Topology

/-- Components of an `ℓ²` vector tend to zero. -/
theorem tendsto_norm_coe_atTop_zero (f : lp E 2) :
    Tendsto (fun n => ‖(f : ∀ i, E i) n‖) atTop (𝓝 0) := by
  have hs : Summable (fun i => ‖(f : ∀ i, E i) i‖ ^ 2) := by
    simpa using (lp.memℓp f).summable (by norm_num)
  have h0 := hs.tendsto_atTop_zero
  have h1 := (Real.continuous_sqrt.tendsto 0).comp h0
  simp only [Real.sqrt_zero] at h1
  exact h1.congr (fun n => Real.sqrt_sq (norm_nonneg _))

/-- **A sequence of canonically embedded vectors can only converge to zero.** -/
theorem eq_zero_of_tendsto_carrierEmbedding {ψ : lp E 2} {a : ∀ n, E n}
    (h : Tendsto (fun n => carrierEmbedding n (a n)) atTop (𝓝 ψ)) : ψ = 0 := by
  have hinner : Tendsto (fun n => ⟪(carrierEmbedding n (a n) : lp E 2), ψ⟫_ℂ) atTop
      (𝓝 ⟪ψ, ψ⟫_ℂ) := h.inner tendsto_const_nhds
  have hnormsq : Tendsto (fun n => ‖⟪(carrierEmbedding n (a n) : lp E 2), ψ⟫_ℂ‖) atTop
      (𝓝 ‖⟪ψ, ψ⟫_ℂ‖) := hinner.norm
  have hnorma : Tendsto (fun n => ‖a n‖) atTop (𝓝 ‖ψ‖) := by
    refine h.norm.congr (fun n => ?_)
    exact (carrierEmbedding n).norm_map (a n)
  have hcomp := tendsto_norm_coe_atTop_zero ψ
  have hprod : Tendsto (fun n => ‖a n‖ * ‖(ψ : ∀ i, E i) n‖) atTop (𝓝 0) := by
    simpa using hnorma.mul hcomp
  have hle : ∀ n, ‖⟪(carrierEmbedding n (a n) : lp E 2), ψ⟫_ℂ‖
      ≤ ‖a n‖ * ‖(ψ : ∀ i, E i) n‖ := by
    intro n
    rw [carrierEmbedding_apply, lp.inner_single_left]
    exact norm_inner_le_norm _ _
  have hle0 : ‖⟪ψ, ψ⟫_ℂ‖ ≤ 0 := le_of_tendsto_of_tendsto' hnormsq hprod hle
  have hzero : ⟪ψ, ψ⟫_ℂ = 0 :=
    norm_eq_zero.1 (le_antisymm hle0 (norm_nonneg _))
  exact inner_self_eq_zero.1 hzero

end Degenerate

end RequestProject.YangMills.CommonCarrier

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.CommonCarrier

#print axioms carrierEmbedding
#print axioms exists_isometric_embeddings
#print axioms eq_zero_of_tendsto_carrierEmbedding

end Audit

/-
# The source rate split composed with the one-sided geometry

Bałaban's differentiated localization delivers the per-domain estimate in the *source's*
own coordinate: the contribution of the localization domain `Y` is bounded by an
amplitude `A_Y` times the geometric weight at the domain tree distance `d_k(Y)`, and the
amplitudes are summable against a source budget `A_src`.  This file composes that shape
with the one-sided geometry proved in `Cluster/DomainPathDistance.lean` and
`Cluster/LatticeTimeSeparation.lean`:

* `rate_split_decay` — from `|commonY Y| ≤ A_Y · η^(d_k(Y))` on connected domains through
  the two source marks and `Σ_Y A_Y ≤ A_src`, the total is bounded by
  `A_src · η^(d(a,b))`, the weight at the *mark separation*.  No expansion bookkeeping is
  used: only connectedness of each domain and the geometric monotonicity of the weight.
* `rate_split_exponential_decay` — the same in the physical exponential coordinate, with
  mass `m = -log η > 0`.
* `rate_split_euclidean_time_decay` — on the literal periodic four-dimensional lattice,
  the bound in the Euclidean time separation of the two marks.

These are the finite-volume clustering statements the mass-gap route consumes; the
constants are independent of the family of domains, hence of the volume.
-/
import RequestProject.YangMills.Cluster.DomainPathDistance
import RequestProject.YangMills.Cluster.LatticeTimeSeparation

namespace RequestProject.YangMills.Cluster

open SimpleGraph
open RequestProject.YangMills.Lattice

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- **The rate split at the source distance implies the bound at the mark separation.**
If every connected localization domain `Y` through the two marks contributes at most
`A_Y · η^(#Y − 1)` and the amplitudes are summable against `A_src`, then the total is
bounded by `A_src · η^(d(a,b))`. -/
theorem rate_split_decay {a b : V} {η Asrc : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1)
    (𝒟 : Finset (Finset V)) (A commonY : Finset V → ℝ)
    (hA : ∀ Y ∈ 𝒟, 0 ≤ A Y)
    (hconn : ∀ Y ∈ 𝒟, IsDomainConnected G Y)
    (ha : ∀ Y ∈ 𝒟, a ∈ Y) (hb : ∀ Y ∈ 𝒟, b ∈ Y)
    (hbound : ∀ Y ∈ 𝒟, |commonY Y| ≤ A Y * η ^ (Y.card - 1))
    (hsum : ∑ Y ∈ 𝒟, A Y ≤ Asrc) :
    |∑ Y ∈ 𝒟, commonY Y| ≤ Asrc * η ^ (G.dist a b) := by
  have hpow : (0 : ℝ) ≤ η ^ (G.dist a b) := pow_nonneg h0 _
  have step : ∀ Y ∈ 𝒟, |commonY Y| ≤ A Y * η ^ (G.dist a b) := by
    intro Y hY
    refine (hbound Y hY).trans ?_
    exact mul_le_mul_of_nonneg_left
      (pow_card_le_pow_dist (hconn Y hY) (ha Y hY) (hb Y hY) h0 h1) (hA Y hY)
  calc |∑ Y ∈ 𝒟, commonY Y| ≤ ∑ Y ∈ 𝒟, |commonY Y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ Y ∈ 𝒟, A Y * η ^ (G.dist a b) := Finset.sum_le_sum step
    _ = (∑ Y ∈ 𝒟, A Y) * η ^ (G.dist a b) := by rw [Finset.sum_mul]
    _ ≤ Asrc * η ^ (G.dist a b) := mul_le_mul_of_nonneg_right hsum hpow

/-- The rate split in the physical exponential coordinate: exponential decay in the
separation of the two source marks with a strictly positive mass. -/
theorem rate_split_exponential_decay {a b : V} {η Asrc : ℝ} (h0 : 0 < η) (h1 : η < 1)
    (𝒟 : Finset (Finset V)) (A commonY : Finset V → ℝ)
    (hA : ∀ Y ∈ 𝒟, 0 ≤ A Y)
    (hconn : ∀ Y ∈ 𝒟, IsDomainConnected G Y)
    (ha : ∀ Y ∈ 𝒟, a ∈ Y) (hb : ∀ Y ∈ 𝒟, b ∈ Y)
    (hbound : ∀ Y ∈ 𝒟, |commonY Y| ≤ A Y * η ^ (Y.card - 1))
    (hsum : ∑ Y ∈ 𝒟, A Y ≤ Asrc) :
    0 < clusterMass η ∧
      |∑ Y ∈ 𝒟, commonY Y| ≤ Asrc * Real.exp (-(clusterMass η * G.dist a b)) := by
  refine ⟨clusterMass_pos h0 h1, ?_⟩
  have := rate_split_decay (G := G) (a := a) (b := b) h0.le h1.le 𝒟 A commonY hA hconn ha hb
    hbound hsum
  rwa [pow_eq_exp_clusterMass h0] at this

/-- **The finite-volume clustering statement in physical Euclidean time.**  On the literal
periodic four-dimensional lattice, Bałaban's per-domain rate split at the domain tree
distance yields exponential decay of the total in the Euclidean time separation of the
two source marks, with mass `m = -log η > 0` and a constant that depends only on the
source amplitude budget. -/
theorem rate_split_euclidean_time_decay {n : ℕ} {a b : Site n} {η Asrc : ℝ}
    (h0 : 0 < η) (h1 : η < 1)
    (𝒟 : Finset (Finset (Site n))) (A commonY : Finset (Site n) → ℝ)
    (hA : ∀ Y ∈ 𝒟, 0 ≤ A Y)
    (hAsrc : 0 ≤ Asrc)
    (hconn : ∀ Y ∈ 𝒟, IsDomainConnected (latticeGraph n) Y)
    (ha : ∀ Y ∈ 𝒟, a ∈ Y) (hb : ∀ Y ∈ 𝒟, b ∈ Y)
    (hbound : ∀ Y ∈ 𝒟, |commonY Y| ≤ A Y * η ^ (Y.card - 1))
    (hsum : ∑ Y ∈ 𝒟, A Y ≤ Asrc) :
    0 < clusterMass η ∧
      |∑ Y ∈ 𝒟, commonY Y| ≤ Asrc * Real.exp (-(clusterMass η * timeSep a b)) := by
  obtain ⟨hmass, hbnd⟩ :=
    rate_split_exponential_decay (G := latticeGraph n) (a := a) (b := b) h0 h1 𝒟 A commonY
      hA hconn ha hb hbound hsum
  refine ⟨hmass, hbnd.trans (mul_le_mul_of_nonneg_left ?_ hAsrc)⟩
  refine Real.exp_le_exp.mpr ?_
  have ht := timeSep_le_dist a b
  nlinarith

end RequestProject.YangMills.Cluster

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Cluster

#print axioms rate_split_decay
#print axioms rate_split_exponential_decay
#print axioms rate_split_euclidean_time_decay

end Audit

import Mathlib
import Integration.StructuredObserver

/-!
# When a positive certificate pays for a defect

The welded spine produces a strictly positive transverse certificate.  On its
own, positivity classifies states; it does not yet *control* anything.  The step
that turns a certificate into quantitative information is always the same
inequality: the certificate dominates a defect pointwise, the certificate has a
budget, and therefore the defect has a budget.

This file owns that step, domain-neutrally.

* `Pays C D c` — the certificate `C` pays for the defect `D` at rate `c > 0`:
  `c · D i ≤ C i` at every site;
* `sum_defect_le_of_budget` — **the theorem**: `∑ C ≤ B` then gives
  `∑ D ≤ B / c`;
* `sites_le_of_budget` — with a uniform floor `c ≤ C i` the budget bounds the
  *number* of sites, `card ≤ B / c`;
* `pointwise_defect_le_of_budget` — and each individual defect is bounded, once
  the other defects are nonnegative.

The last section records the matching negative fact, so the pattern is not
overclaimed: a bounded **weighted** aggregate budget does *not* imply any
uniform bound on the local defect.  `weighted_budget_not_uniform` exhibits
weights and defects with every partial weighted sum at most one and the defects
unbounded.  So an aggregate certificate can hide an arbitrarily large local
defect — the aggregate observer does not descend to scale-local safety.
-/

namespace Integration.CertificatePays

open Finset

variable {ι : Type*}

/-- The certificate `C` **pays for** the defect `D` at rate `c`: at every site the
certificate is at least `c` times the defect. -/
def Pays (C D : ι → ℝ) (c : ℝ) : Prop := ∀ i, c * D i ≤ C i

/-- **A certificate budget is a defect budget.**  If the certificate pays for the
defect at a positive rate and the total certificate is at most `B`, then the
total defect is at most `B / c`. -/
theorem sum_defect_le_of_budget [Fintype ι] {C D : ι → ℝ} {c B : ℝ} (hc : 0 < c)
    (h : Pays C D c) (hB : ∑ i, C i ≤ B) : ∑ i, D i ≤ B / c := by
  have hstep : c * ∑ i, D i ≤ ∑ i, C i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => h i
  rw [le_div_iff₀ hc, mul_comm]
  exact le_trans hstep hB

/-- The same over an arbitrary finite index set. -/
theorem sum_defect_le_of_budget_finset {s : Finset ι} {C D : ι → ℝ} {c B : ℝ} (hc : 0 < c)
    (h : ∀ i ∈ s, c * D i ≤ C i) (hB : ∑ i ∈ s, C i ≤ B) : ∑ i ∈ s, D i ≤ B / c := by
  have hstep : c * ∑ i ∈ s, D i ≤ ∑ i ∈ s, C i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum h
  rw [le_div_iff₀ hc, mul_comm]
  exact le_trans hstep hB

/-- **A uniform certificate floor bounds the number of sites.**  If every site
carries at least `c > 0` of certificate and the total is at most `B`, there are
at most `B / c` sites. -/
theorem sites_le_of_budget [Fintype ι] {C : ι → ℝ} {c B : ℝ} (hc : 0 < c)
    (hfloor : ∀ i, c ≤ C i) (hB : ∑ i, C i ≤ B) : (Fintype.card ι : ℝ) ≤ B / c := by
  have h : Pays C (fun _ => 1) c := fun i => by simpa using hfloor i
  have := sum_defect_le_of_budget (C := C) (D := fun _ => 1) hc h hB
  simpa using this

/-- **And each individual defect is paid for.**  With the other defects
nonnegative, the budget bounds every single defect. -/
theorem pointwise_defect_le_of_budget [Fintype ι] {C D : ι → ℝ} {c B : ℝ} (hc : 0 < c)
    (h : Pays C D c) (hD : ∀ i, 0 ≤ D i) (hB : ∑ i, C i ≤ B) (i : ι) : D i ≤ B / c := by
  refine le_trans ?_ (sum_defect_le_of_budget hc h hB)
  exact Finset.single_le_sum (f := D) (fun j _ => hD j) (Finset.mem_univ i)

/-! ## The matching negative fact -/

/-- **A bounded weighted aggregate does not bound the local defect.**  There are
positive weights and nonnegative defects whose weighted partial sums never
exceed one, while the defects themselves are unbounded.  So a global budget on a
weighted aggregate cannot certify uniform local control. -/
theorem weighted_budget_not_uniform :
    ∃ w D : ℕ → ℝ, (∀ k, 0 < w k) ∧ (∀ k, 0 ≤ D k) ∧
      (∀ n, ∑ k ∈ range n, w k * D k ≤ 1) ∧ (∀ M : ℝ, ∃ k, M ≤ D k) := by
  refine ⟨fun k => (1 / 4 : ℝ) ^ (k + 1), fun k => (2 : ℝ) ^ k, fun k => by positivity,
    fun k => by positivity, fun n => ?_, fun M => ?_⟩
  · have hterm : ∀ k ∈ range n,
        (1 / 4 : ℝ) ^ (k + 1) * (2 : ℝ) ^ k = (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ k := by
      intro k _
      rw [pow_succ, div_pow, div_pow]
      field_simp
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have h2 : ∑ k ∈ range n, (1 / 2 : ℝ) ^ k ≤ 2 := sum_geometric_two_le n
    nlinarith [h2]
  · obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (R := ℝ) M (by norm_num : (1 : ℝ) < 2)
    exact ⟨k, le_of_lt hk⟩

/-! ## The welded certificate has a uniform floor, and therefore pays

The spine's certificate is strictly positive at every state.  On a finite
carrier that upgrades to a uniform positive floor, which is exactly the
hypothesis `sites_le_of_budget` needs: a budget on the total certificate then
bounds how many states the carrier can have. -/

open Integration.StructuredObserver

/-- **A positive certificate on a finite carrier has a uniform floor.** -/
theorem exists_certificate_floor {G Rich Coarse Res : Type} [Monoid G] {n : ℕ} [NeZero n]
    [Fintype Rich] [Nonempty Rich] (O : SymmetryResolvedObserver G Rich Coarse Res n) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ O.nondegeneracy x := by
  classical
  obtain ⟨x₀, -, hx₀⟩ :=
    Finset.exists_min_image (Finset.univ : Finset Rich) O.nondegeneracy ⟨Classical.arbitrary Rich,
      Finset.mem_univ _⟩
  exact ⟨O.nondegeneracy x₀, O.nondegeneracy_pos x₀, fun x => hx₀ x (Finset.mem_univ x)⟩

/-- **The certificate pays for the carrier.**  A budget on the total certificate
of a welded observer bounds the number of states of its rich carrier. -/
theorem welded_sites_le_of_budget {G Rich Coarse Res : Type} [Monoid G] {n : ℕ} [NeZero n]
    [Fintype Rich] [Nonempty Rich] (O : SymmetryResolvedObserver G Rich Coarse Res n) {B : ℝ}
    (hB : ∑ x, O.nondegeneracy x ≤ B) :
    ∃ c : ℝ, 0 < c ∧ (Fintype.card Rich : ℝ) ≤ B / c := by
  obtain ⟨c, hc, hfloor⟩ := exists_certificate_floor O
  exact ⟨c, hc, sites_le_of_budget hc hfloor hB⟩

end Integration.CertificatePays

/-
# The one-sided geometry: Euclidean time separation is bounded by the support distance

This file pays the first half of the one-sided geometry obligation of the selected
CMP116 localization (item `B3`): on the literal periodic four-dimensional lattice of
`Lattice/Wilson.lean`, the Euclidean time separation of two sites is bounded by their
distance in the nearest-neighbour support graph.  Together with the cluster estimate of
`Cluster/CoordinateSeparation.lean` this converts the combinatorial decay in the graph
distance into decay in the physical Euclidean time.

The content is:

* `circNorm` — the periodic (circle) norm on `ZMod m`: the least natural number
  representing the class up to sign.  It is symmetric, vanishes at `0`, is bounded by the
  representative `val`, and satisfies the triangle inequality.  This is the correct
  notion of separation on a periodic lattice: it is exactly the number of unit steps
  needed to move from one time slice to another.
* `latticeGraph` — the literal nearest-neighbour graph on the sites, `x ~ y` iff the two
  sites differ by one unit lattice vector.  Its degree is at most `8 = 2 · 4`
  (`degree_le_eight`), which is the entropy input `Δ` of the cluster expansion, and it is
  connected (`latticeGraph_reachable`), so lattice distances are finite and the estimates
  below are not vacuous.
* `coordSep_le_dist` — for every lattice direction, the periodic coordinate separation is
  at most the graph distance; in particular `timeSep_le_dist` for the Euclidean time
  direction.
* `selected_boundary_clustering_euclidean_time` — the selected CMP116 boundary of the
  cluster expansion decays as `exp (-m · timeSep a b)`, with a strictly positive mass and
  a constant independent of the family of localization domains, in the small-field regime
  `64 η < 1`.

Everything is proved; no lattice-specific estimate is assumed.
-/
import RequestProject.YangMills.Cluster.CoordinateSeparation
import RequestProject.YangMills.RouteS.EuclideanTime

namespace RequestProject.YangMills.Cluster

open SimpleGraph
open RequestProject.YangMills.Lattice

/-! ## The periodic norm on `ZMod m` -/

section CircNorm

variable {m : ℕ} [NeZero m]

/-- The natural numbers that represent `a : ZMod m` up to sign. -/
def circSet (a : ZMod m) : Set ℕ := {k | a = (k : ZMod m) ∨ a = -(k : ZMod m)}

/-- The periodic norm of `a : ZMod m`: the least number of unit steps needed to reach `a`
from `0` on the circle `ZMod m`, in either direction. -/
noncomputable def circNorm (a : ZMod m) : ℕ := sInf (circSet a)

theorem circSet_nonempty (a : ZMod m) : (circSet a).Nonempty :=
  ⟨a.val, Or.inl (ZMod.natCast_zmod_val a).symm⟩

theorem circNorm_mem (a : ZMod m) : circNorm a ∈ circSet a :=
  Nat.sInf_mem (circSet_nonempty a)

omit [NeZero m] in
theorem circNorm_le {a : ZMod m} {k : ℕ} (h : k ∈ circSet a) : circNorm a ≤ k :=
  Nat.sInf_le h

/-- The periodic norm never exceeds the canonical representative. -/
theorem circNorm_le_val (a : ZMod m) : circNorm a ≤ a.val :=
  circNorm_le (Or.inl (ZMod.natCast_zmod_val a).symm)

omit [NeZero m] in
@[simp] theorem circNorm_zero : circNorm (0 : ZMod m) = 0 :=
  Nat.le_zero.mp (circNorm_le (Or.inl (by simp)))

theorem circNorm_neg (a : ZMod m) : circNorm (-a) = circNorm a := by
  have key : ∀ b : ZMod m, circNorm (-b) ≤ circNorm b := by
    intro b
    rcases circNorm_mem b with h | h
    · exact circNorm_le (Or.inr (neg_inj.mpr h))
    · exact circNorm_le (Or.inl ((congrArg Neg.neg h).trans (neg_neg _)))
  exact le_antisymm (key a) (by simpa using key (-a))

omit [NeZero m] in
theorem circNorm_one_le : circNorm (1 : ZMod m) ≤ 1 :=
  circNorm_le (Or.inl (by simp))

omit [NeZero m] in
theorem circNorm_add_le_of {a b : ZMod m} {k l : ℕ} (ha : k ∈ circSet a) (hb : l ∈ circSet b) :
    circNorm (a + b) ≤ k + l := by
  have hcast : ∀ i j : ℕ, j ≤ i → ((i - j : ℕ) : ZMod m) = (i : ZMod m) - (j : ZMod m) := by
    intro i j h; push_cast [Nat.cast_sub h]; ring
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact circNorm_le (Or.inl (by rw [ha, hb]; push_cast; ring))
  · rcases le_total l k with h | h
    · refine le_trans (circNorm_le (a := a + b) (k := k - l) (Or.inl ?_)) (by omega)
      rw [ha, hb, hcast _ _ h]; ring
    · refine le_trans (circNorm_le (a := a + b) (k := l - k) (Or.inr ?_)) (by omega)
      rw [ha, hb, hcast _ _ h]; ring
  · rcases le_total k l with h | h
    · refine le_trans (circNorm_le (a := a + b) (k := l - k) (Or.inl ?_)) (by omega)
      rw [ha, hb, hcast _ _ h]; ring
    · refine le_trans (circNorm_le (a := a + b) (k := k - l) (Or.inr ?_)) (by omega)
      rw [ha, hb, hcast _ _ h]; ring
  · exact circNorm_le (Or.inr (by rw [ha, hb]; push_cast; ring))

/-- **The triangle inequality for the periodic norm.** -/
theorem circNorm_add_le (a b : ZMod m) : circNorm (a + b) ≤ circNorm a + circNorm b :=
  circNorm_add_le_of (circNorm_mem a) (circNorm_mem b)

/-- The periodic norm is `1`-Lipschitz for itself: moving the argument changes the norm by
at most the norm of the displacement. -/
theorem abs_circNorm_sub_circNorm_le (a b c : ZMod m) :
    |(circNorm (a - c) : ℝ) - circNorm (b - c)| ≤ circNorm (a - b) := by
  have h₁ : circNorm (a - c) ≤ circNorm (a - b) + circNorm (b - c) := by
    have := circNorm_add_le (a - b) (b - c)
    simpa using this
  have h₂ : circNorm (b - c) ≤ circNorm (a - b) + circNorm (a - c) := by
    have := circNorm_add_le (b - a) (a - c)
    have hba : circNorm (b - a) = circNorm (a - b) := by
      rw [← circNorm_neg (a - b)]; ring_nf
    simpa [hba] using this
  have e₁ : (circNorm (a - c) : ℝ) ≤ (circNorm (a - b) : ℝ) + circNorm (b - c) := by
    exact_mod_cast h₁
  have e₂ : (circNorm (b - c) : ℝ) ≤ (circNorm (a - b) : ℝ) + circNorm (a - c) := by
    exact_mod_cast h₂
  rw [abs_sub_le_iff]
  constructor <;> linarith

end CircNorm

/-! ## The literal nearest-neighbour support graph of the lattice -/

variable {n : ℕ}

/-- The literal support graph of the periodic four-dimensional lattice: two distinct
sites are adjacent exactly when they differ by one unit lattice vector. -/
def latticeGraph (n : ℕ) : SimpleGraph (Site n) where
  Adj x y := x ≠ y ∧ ∃ d : Fin 4, y = x + unitVec n d ∨ x = y + unitVec n d
  symm := by
    rintro x y ⟨hne, d, h⟩
    exact ⟨hne.symm, d, h.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel (latticeGraph n).Adj := by
  intro x y
  unfold latticeGraph
  infer_instance

/-- **The lattice entropy constant.**  Every site of the four-dimensional lattice has at
most `8 = 2 · 4` neighbours, so the cluster expansion runs with `Δ = 8`. -/
theorem degree_le_eight (x : Site n) : (latticeGraph n).degree x ≤ 8 := by
  classical
  have hsub : (latticeGraph n).neighborFinset x ⊆
      (Finset.univ : Finset (Fin 4 × Bool)).image
        (fun p => if p.2 then x + unitVec n p.1 else x - unitVec n p.1) := by
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨hne, d, h | h⟩ := hy
    · exact Finset.mem_image.mpr ⟨(d, true), Finset.mem_univ _, by simp [h]⟩
    · refine Finset.mem_image.mpr ⟨(d, false), Finset.mem_univ _, ?_⟩
      subst h
      simp
  calc (latticeGraph n).degree x = ((latticeGraph n).neighborFinset x).card := rfl
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin 4 × Bool)).card := Finset.card_image_le
    _ = 8 := by simp

/-! ### Connectivity -/

/-- One unit step is a move in the lattice graph (or no move at all, on the degenerate
one-site lattice). -/
theorem reachable_step (x : Site n) (d : Fin 4) :
    (latticeGraph n).Reachable x (x + unitVec n d) := by
  by_cases h : x = x + unitVec n d
  · exact h ▸ Reachable.refl x
  · exact Adj.reachable ⟨h, d, Or.inl rfl⟩

theorem reachable_add_single (x : Site n) (d : Fin 4) (k : ℕ) :
    (latticeGraph n).Reachable x (x + Pi.single d ((k : ZMod (n + 1)))) := by
  induction k with
  | zero => simp
  | succ k ih =>
    refine ih.trans ?_
    have hstep := reachable_step (x + Pi.single d ((k : ZMod (n + 1)))) d
    have he : x + Pi.single d ((k : ZMod (n + 1))) + unitVec n d
        = x + Pi.single d (((k + 1 : ℕ) : ZMod (n + 1))) := by
      rw [add_assoc, unitVec]
      congr 1
      rw [← Pi.single_add]
      push_cast
      ring_nf
    rwa [he] at hstep

/-- **The lattice support graph is connected.** -/
theorem latticeGraph_reachable (x y : Site n) : (latticeGraph n).Reachable x y := by
  classical
  -- `mix j` agrees with `y` on the first `j` directions and with `x` on the rest
  set mix : ℕ → Site n := fun j e => if (e : ℕ) < j then y e else x e with hmix
  have hstep : ∀ j : ℕ, j < 4 → (latticeGraph n).Reachable (mix j) (mix (j + 1)) := by
    intro j hj
    have hkey : mix (j + 1)
        = mix j + Pi.single (⟨j, hj⟩ : Fin 4)
            (((y ⟨j, hj⟩ - x ⟨j, hj⟩).val : ZMod (n + 1))) := by
      funext e
      by_cases he : e = (⟨j, hj⟩ : Fin 4)
      · subst he
        simp only [hmix, Pi.add_apply, Pi.single_eq_same, ZMod.natCast_zmod_val]
        rw [if_pos (Nat.lt_succ_self j), if_neg (Nat.lt_irrefl j)]
        ring
      · simp only [hmix, Pi.add_apply, Pi.single_eq_of_ne he, add_zero]
        have hne : (e : ℕ) ≠ j := fun h => he (Fin.ext h)
        by_cases hlt : (e : ℕ) < j
        · simp [hlt, Nat.lt_succ_of_lt hlt]
        · have h2 : ¬ ((e : ℕ) < j + 1) := by omega
          simp [hlt, h2]
    rw [hkey]
    exact reachable_add_single _ _ _
  have h0 : mix 0 = x := by funext e; simp [hmix]
  have h4 : mix 4 = y := by
    funext e
    have : (e : ℕ) < 4 := e.isLt
    simp [hmix, this]
  have chain : (latticeGraph n).Reachable (mix 0) (mix 4) :=
    ((hstep 0 (by norm_num)).trans (hstep 1 (by norm_num))).trans
      ((hstep 2 (by norm_num)).trans (hstep 3 (by norm_num)))
  rwa [h0, h4] at chain

/-! ## Coordinate separation on the lattice -/

/-- The periodic separation of two sites in the lattice direction `d`: the number of unit
steps in that direction separating the two coordinates. -/
noncomputable def coordSep (d : Fin 4) (x y : Site n) : ℕ := circNorm (x d - y d)

/-- The Euclidean time separation of two lattice sites. -/
noncomputable def timeSep (x y : Site n) : ℕ := coordSep RouteS.timeDir x y

/-- A single unit lattice vector changes any one coordinate by at most one step. -/
theorem circNorm_unitVec_le_one (d e : Fin 4) :
    circNorm (unitVec n e d) ≤ 1 := by
  by_cases h : e = d
  · subst h
    simpa [unitVec] using (circNorm_one_le (m := n + 1))
  · simp [unitVec, Pi.single_eq_of_ne (Ne.symm h)]

/-- Along an edge of the support graph every coordinate moves by at most one step. -/
theorem circNorm_sub_le_one_of_adj {x y : Site n} (h : (latticeGraph n).Adj x y) (d : Fin 4) :
    circNorm (x d - y d) ≤ 1 := by
  obtain ⟨-, e, he | he⟩ := h
  · have : x d - y d = -(unitVec n e d) := by rw [he]; simp
    rw [this, circNorm_neg]
    exact circNorm_unitVec_le_one d e
  · have : x d - y d = unitVec n e d := by rw [he]; simp
    rw [this]
    exact circNorm_unitVec_le_one d e

/-- **The one-sided geometry.**  The periodic separation of two sites in any lattice
direction is bounded by their distance in the support graph. -/
theorem coordSep_le_dist (d : Fin 4) (a b : Site n) :
    (coordSep d a b : ℝ) ≤ (latticeGraph n).dist a b := by
  classical
  set f : Site n → ℝ := fun z => (circNorm (z d - b d) : ℝ) with hf
  have hlip : ∀ x y, (latticeGraph n).Adj x y → |f x - f y| ≤ 1 := by
    intro x y hxy
    refine (abs_circNorm_sub_circNorm_le (x d) (y d) (b d)).trans ?_
    exact_mod_cast circNorm_sub_le_one_of_adj hxy d
  have hsep := abs_sub_le_dist_of_unitLipschitz hlip (latticeGraph_reachable a b)
  have hb : f b = 0 := by simp [hf]
  rw [hb, sub_zero] at hsep
  calc (coordSep d a b : ℝ) = |f a| := by rw [hf]; simp [coordSep]
    _ ≤ (latticeGraph n).dist a b := hsep

/-- **Euclidean time is bounded by the support distance.** -/
theorem timeSep_le_dist (a b : Site n) :
    (timeSep a b : ℝ) ≤ (latticeGraph n).dist a b :=
  coordSep_le_dist RouteS.timeDir a b

/-! ## The cluster bound in Euclidean time -/

/-- **Exponential clustering of the selected CMP116 boundary in Euclidean time.**  On the
literal periodic lattice, with the entropy constant `Δ = 8` of the four-dimensional
nearest-neighbour graph and in the small-field regime `64 η < 1`, the selected boundary
of the differentiated cluster expansion is bounded by a volume-independent constant times
`exp (-m · t)`, where `t` is the Euclidean time separation of the two source marks and
`m = -log η > 0`. -/
theorem selected_boundary_clustering_euclidean_time {ι : Type*} {a b : Site n}
    (η c : ℝ) (hc : 0 ≤ c) (hη0 : 0 < η) (hη1 : η < 1) (hηΔ : 64 * η < 1)
    (𝒟 : Finset (Finset (Site n))) (terms : Finset (Site n) → Finset ι)
    (wt : ι → (latticeGraph n).Walk a b) (amp term : ι → ℝ)
    (commonY : Finset (Site n) → ℝ)
    (hamp : ∀ t, 0 ≤ amp t)
    (hne : ∀ Y ∈ 𝒟, (terms Y).Nonempty)
    (hsupp : ∀ Y ∈ 𝒟, ∀ t ∈ terms Y, (wt t).support.toFinset = Y)
    (hterm : ∀ Y ∈ 𝒟, ∀ t ∈ terms Y, |term t| ≤ amp t * (η * η) ^ (wt t).length)
    (hact : ∀ Y ∈ 𝒟, ∑ t ∈ terms Y, amp t ≤ c)
    (hcommon : ∀ Y ∈ 𝒟, commonY Y = ∑ t ∈ terms Y, term t) :
    0 < clusterMass η ∧
      |∑ Y ∈ 𝒟, commonY Y|
        ≤ (c * clusterSeries 8 η) * Real.exp (-(clusterMass η * timeSep a b)) := by
  classical
  obtain ⟨hmass, hbound⟩ :=
    selected_boundary_exponential_clustering (latticeGraph n) 8 (by norm_num)
      degree_le_eight a b η c hc hη0 hη1 (by push_cast; linarith)
      𝒟 terms wt amp term commonY hamp hne hsupp hterm hact hcommon
  refine ⟨hmass, hbound.trans (mul_le_mul_of_nonneg_left ?_ ?_)⟩
  · refine Real.exp_le_exp.mpr ?_
    have := timeSep_le_dist a b
    nlinarith
  · exact mul_nonneg hc (clusterSeries_nonneg 8 η hη0.le)

end RequestProject.YangMills.Cluster

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Cluster

#print axioms circNorm_add_le
#print axioms degree_le_eight
#print axioms latticeGraph_reachable
#print axioms coordSep_le_dist
#print axioms selected_boundary_clustering_euclidean_time

end Audit

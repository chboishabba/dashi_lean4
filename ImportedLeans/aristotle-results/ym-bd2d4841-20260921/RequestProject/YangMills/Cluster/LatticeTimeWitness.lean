/-
# The lattice clustering hypotheses are jointly satisfiable

`rate_split_euclidean_time_decay` and `timeSep_le_dist` are statements under hypotheses,
so it is worth checking that those hypotheses can hold on the literal lattice with a
*nonzero* boundary and a *positive* Euclidean time separation.  This file supplies:

* `circNorm_eq_zero_iff` — the periodic norm detects `0`, so a nonzero time displacement
  really has positive separation;
* `adj_add_unitVec`, `timeSep_add_unitVec` — on a lattice with at least two sites per
  direction a site and its time translate are adjacent and at time separation exactly `1`;
* `isDomainConnected_pair` — the two-site domain carried by an edge is domain connected;
* `witness_rate_split_euclidean_time` — a concrete instance of the finite-volume
  clustering bound with a nonzero total and two distinct marks.
-/
import RequestProject.YangMills.Cluster.SourceRateSplitTime

namespace RequestProject.YangMills.Cluster

open SimpleGraph
open RequestProject.YangMills.Lattice

section CircNorm

variable {m : ℕ} [NeZero m]

/-- The periodic norm vanishes only at `0`. -/
theorem circNorm_eq_zero_iff {a : ZMod m} : circNorm a = 0 ↔ a = 0 := by
  constructor
  · intro h
    rcases Nat.sInf_eq_zero.mp h with h0 | hempty
    · rcases h0 with h0 | h0 <;> simpa using h0
    · exact absurd hempty (Set.nonempty_iff_ne_empty.mp (circSet_nonempty a))
  · rintro rfl; simp

end CircNorm

variable {n : ℕ}

/-- On a lattice with at least two sites in every direction, a unit step really moves the
site. -/
theorem ne_add_unitVec (hn : 1 ≤ n) (a : Site n) (d : Fin 4) : a ≠ a + unitVec n d := by
  intro h
  have hzero : unitVec n d = 0 := by
    have := congrArg (fun z => z - a) h
    simpa using this.symm
  have h1 : (1 : ZMod (n + 1)) = 0 := by
    have := congrFun hzero d
    simpa [unitVec] using this
  haveI : Fact (1 < n + 1) := ⟨by omega⟩
  exact one_ne_zero h1

/-- A site and its unit translate are adjacent in the support graph. -/
theorem adj_add_unitVec (hn : 1 ≤ n) (a : Site n) (d : Fin 4) :
    (latticeGraph n).Adj a (a + unitVec n d) :=
  ⟨ne_add_unitVec hn a d, d, Or.inl rfl⟩

/-- The Euclidean time separation of a site and its one-step time translate is `1`. -/
theorem timeSep_add_unitVec (hn : 1 ≤ n) (a : Site n) :
    timeSep a (a + unitVec n RouteS.timeDir) = 1 := by
  have hval : a RouteS.timeDir - (a + unitVec n RouteS.timeDir) RouteS.timeDir
      = -(1 : ZMod (n + 1)) := by
    simp [unitVec]
  have hle : circNorm (-(1 : ZMod (n + 1))) ≤ 1 := by
    rw [circNorm_neg]; exact circNorm_one_le
  have hne : circNorm (-(1 : ZMod (n + 1))) ≠ 0 := by
    intro h
    haveI : Fact (1 < n + 1) := ⟨by omega⟩
    exact one_ne_zero (neg_eq_zero.mp (circNorm_eq_zero_iff.mp h))
  have : timeSep a (a + unitVec n RouteS.timeDir) = circNorm (-(1 : ZMod (n + 1))) := by
    rw [timeSep, coordSep, hval]
  omega

/-- The two-site domain carried by an edge is domain connected. -/
theorem isDomainConnected_pair {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
    (hxy : G.Adj x y) : IsDomainConnected G {x, y} := by
  intro S hS hne hSne
  obtain ⟨u, hu⟩ := hne
  have hux : u = x ∨ u = y := by simpa using hS hu
  have hfull : ∀ {v w : V}, v ∈ S → w ∈ S → v ≠ w → S = ({x, y} : Finset V) → False := by
    intro _ _ _ _ _ h; exact hSne h
  rcases hux with rfl | rfl
  · by_cases hy : y ∈ S
    · exact absurd (Finset.Subset.antisymm hS (by
        intro z hz
        have : z = u ∨ z = y := by simpa using hz
        rcases this with rfl | rfl
        · exact hu
        · exact hy)) hSne
    · exact ⟨u, hu, y, by simp, hy, hxy⟩
  · by_cases hx : x ∈ S
    · exact absurd (Finset.Subset.antisymm hS (by
        intro z hz
        have : z = x ∨ z = u := by simpa using hz
        rcases this with rfl | rfl
        · exact hx
        · exact hu)) hSne
    · exact ⟨u, hu, x, by simp, hx, hxy.symm⟩

/-- **The lattice clustering bound is not vacuous.**  On the `4`-site-per-direction
lattice, the single two-site domain carried by a time edge satisfies every hypothesis of
`rate_split_euclidean_time_decay` with a nonzero total, and the resulting bound is the
genuine exponential decay at time separation `1`. -/
theorem witness_rate_split_euclidean_time :
    0 < clusterMass (1 / 2 : ℝ) ∧
      |(1 / 2 : ℝ)| ≤ 1 * Real.exp (-(clusterMass (1 / 2 : ℝ) * 1)) := by
  classical
  set a : Site 3 := 0
  set b : Site 3 := 0 + unitVec 3 RouteS.timeDir with hb
  have hadj : (latticeGraph 3).Adj a b := adj_add_unitVec (by norm_num) a RouteS.timeDir
  have hne : a ≠ b := hadj.ne
  have hcard : ({a, b} : Finset (Site 3)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  have hmem : ∀ Y ∈ ({({a, b} : Finset (Site 3))} : Finset (Finset (Site 3))),
      Y = ({a, b} : Finset (Site 3)) := by
    intro Y hY; simpa using hY
  have key := rate_split_euclidean_time_decay (a := a) (b := b) (η := 1 / 2) (Asrc := 1)
    (by norm_num) (by norm_num) {({a, b} : Finset (Site 3))} (fun _ => 1) (fun _ => 1 / 2)
    (fun _ _ => zero_le_one) zero_le_one
    (fun Y hY => by rw [hmem Y hY]; exact isDomainConnected_pair hadj)
    (fun Y hY => by rw [hmem Y hY]; simp)
    (fun Y hY => by rw [hmem Y hY]; simp)
    (fun Y hY => by rw [hmem Y hY, hcard]; norm_num)
    (by simp)
  rw [timeSep_add_unitVec (by norm_num)] at key
  simpa using key

end RequestProject.YangMills.Cluster

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Cluster

#print axioms timeSep_add_unitVec
#print axioms isDomainConnected_pair
#print axioms witness_rate_split_euclidean_time

end Audit

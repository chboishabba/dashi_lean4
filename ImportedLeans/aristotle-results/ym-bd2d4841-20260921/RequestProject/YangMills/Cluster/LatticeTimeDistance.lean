/-
# The lattice distance of two time-separated insertions

`Cluster/LatticeTimeSeparation.lean` proves the inequality `timeSep ≤ dist`.  For the
selected two-source estimate one needs it in the concrete form the observables come in:
the left insertion sits at a site `x`, the right insertion is the same-slice site `y`
translated by `t` steps in the Euclidean time direction, and one needs

  `t ≤ dist x (y + timeVec t)`,

so that the cluster weight at the graph distance is at most the weight at the physical
separation `t`.  On a periodic lattice this is true exactly when the separation stays
below half the period — beyond that the two insertions approach each other the other way
round the torus — and that condition is stated explicitly here (`2 * t < n + 1`), not
hidden.

* `circNorm_natCast_eq_self` — below half the period the periodic norm is the number
  itself;
* `latticeGraph_connected`, `dist_add_single_le` — the support graph is connected and a
  `k`-step translation is at distance at most `k`;
* `timeSep_timeVec_of_sameSlice`, `le_dist_timeVec_of_sameSlice` — the Euclidean time
  separation of the two insertions is exactly `t`, hence at most their graph distance;
* `dist_timeVec_eq` — for the same base site the graph distance is exactly `t`.
-/
import RequestProject.YangMills.Cluster.LatticeTimeSeparation

namespace RequestProject.YangMills.Cluster

open SimpleGraph
open RequestProject.YangMills.Lattice

section CircNorm

variable {m : ℕ} [NeZero m]

/-- Below half the period the periodic norm of a natural number is that number. -/
theorem circNorm_natCast_eq_self {k : ℕ} (hk : 2 * k < m) : circNorm ((k : ZMod m)) = k := by
  refine le_antisymm (circNorm_le (Or.inl rfl)) ?_
  obtain ⟨j, hjdef⟩ : ∃ j, circNorm ((k : ZMod m)) = j := ⟨_, rfl⟩
  have hle : j ≤ k := hjdef ▸ circNorm_le (Or.inl rfl)
  have hj : j ∈ circSet ((k : ZMod m)) := hjdef ▸ circNorm_mem ((k : ZMod m))
  rw [hjdef]
  rcases hj with h | h
  · have hval := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hval
    omega
  · have hz : ((k + j : ℕ) : ZMod m) = 0 := by
      push_cast
      rw [h]; ring
    have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have := Nat.eq_zero_of_dvd_of_lt hdvd (show k + j < m by omega)
    omega

end CircNorm

variable {n : ℕ}

/-- The support graph of the lattice is connected. -/
theorem latticeGraph_connected : (latticeGraph n).Connected :=
  ⟨fun x y => latticeGraph_reachable x y⟩

/-- A single unit step moves a site by at most one in the graph distance. -/
theorem dist_step_le_one (z : Site n) (d : Fin 4) :
    (latticeGraph n).dist z (z + unitVec n d) ≤ 1 := by
  by_cases h : z = z + unitVec n d
  · rw [← h]; simp
  · exact le_of_eq (SimpleGraph.dist_eq_one_iff_adj.mpr ⟨h, d, Or.inl rfl⟩)

/-- A translation by `k` steps in one direction moves a site by at most `k`. -/
theorem dist_add_single_le (x : Site n) (d : Fin 4) (k : ℕ) :
    (latticeGraph n).dist x (x + Pi.single d ((k : ZMod (n + 1)))) ≤ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : x + Pi.single d ((k : ZMod (n + 1))) + unitVec n d
        = x + Pi.single d (((k + 1 : ℕ) : ZMod (n + 1))) := by
      rw [add_assoc, unitVec]
      congr 1
      rw [← Pi.single_add]
      push_cast
      ring_nf
    have htri := latticeGraph_connected.dist_triangle (u := x)
      (v := x + Pi.single d ((k : ZMod (n + 1))))
      (w := x + Pi.single d (((k + 1 : ℕ) : ZMod (n + 1))))
    have hstep : (latticeGraph n).dist (x + Pi.single d ((k : ZMod (n + 1))))
        (x + Pi.single d (((k + 1 : ℕ) : ZMod (n + 1)))) ≤ 1 := by
      rw [← he]; exact dist_step_le_one _ d
    omega

/-- **The Euclidean time separation of the two insertions is the separation parameter.**
If the two base sites lie on the same time slice and the separation stays below half the
period, the periodic time separation of `x` and `y + timeVec t` is exactly `t`. -/
theorem timeSep_timeVec_of_sameSlice {x y : Site n} {t : ℕ}
    (hxy : x RouteS.timeDir = y RouteS.timeDir) (ht : 2 * t < n + 1) :
    timeSep x (y + RouteS.timeVec n t) = t := by
  have hcoord : x RouteS.timeDir - (y + RouteS.timeVec n t) RouteS.timeDir
      = -((t : ℕ) : ZMod (n + 1)) := by
    simp [RouteS.timeVec, hxy]
  rw [timeSep, coordSep, hcoord, circNorm_neg, circNorm_natCast_eq_self ht]

/-- **The one-sided geometry in the form the source estimate needs.**  The physical
separation `t` of the two insertions is at most their distance in the support graph. -/
theorem le_dist_timeVec_of_sameSlice {x y : Site n} {t : ℕ}
    (hxy : x RouteS.timeDir = y RouteS.timeDir) (ht : 2 * t < n + 1) :
    t ≤ (latticeGraph n).dist x (y + RouteS.timeVec n t) := by
  have h := timeSep_le_dist x (y + RouteS.timeVec n t)
  rw [timeSep_timeVec_of_sameSlice hxy ht] at h
  exact_mod_cast h

/-- For the same base site the graph distance of the two insertions is exactly the
Euclidean separation. -/
theorem dist_timeVec_eq (x : Site n) {t : ℕ} (ht : 2 * t < n + 1) :
    (latticeGraph n).dist x (x + RouteS.timeVec n t) = t := by
  refine le_antisymm ?_ (le_dist_timeVec_of_sameSlice rfl ht)
  exact dist_add_single_le x RouteS.timeDir t

end RequestProject.YangMills.Cluster

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Cluster

#print axioms circNorm_natCast_eq_self
#print axioms latticeGraph_connected
#print axioms timeSep_timeVec_of_sameSlice
#print axioms le_dist_timeVec_of_sameSlice
#print axioms dist_timeVec_eq

end Audit

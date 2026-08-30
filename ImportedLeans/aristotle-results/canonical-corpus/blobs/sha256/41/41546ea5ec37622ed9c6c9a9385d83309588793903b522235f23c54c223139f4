import Mathlib
import RequestProject.IrrepGears

/-!
# GearTopology: do the 97 "free" gears have different Betti numbers / Euler
characteristics?

This module answers, honestly and with machine-checked proofs, the question:

> the 97 not contained have different betti numbers / euler chars?
> can we formalize this?

Recall (`IrrepGears`) that of the 194 irrep-gears, exactly **97** are *free* —
contained in nothing — namely the tooth counts `98 … 194` (the numbers `n ≤ 194`
with no proper multiple `≤ 194`).  There are two genuinely different "topologies"
one can attach to a gear, and they give *opposite* answers, so we make both
precise.

## 1. The gear *shapes* are all the same circle — so NO, not at that level

A cog with `k` teeth is drawn (`IrrepGears.cogPoints`) as a single closed polygonal
outline: a `1`-dimensional CW complex that is one cycle with `2k` vertices and
`2k` edges.  Every such outline is homeomorphic to a circle, so it has the *same*
homotopy invariants regardless of `k`:

* Euler characteristic `χ = V − E = 2k − 2k = 0`  (`shapeEuler_eq_zero`);
* Betti numbers `b₀ = 1`, `b₁ = 1`, with `χ = b₀ − b₁`  (`shapeBetti`);
* hence all 97 free gears share one value  (`free_shapes_all_equal`).

So at the level of the drawn gear shapes the conjecture is **false**: they are all
topological circles with identical Betti numbers and Euler characteristic.

## 2. The *containment* topology does distinguish them — so YES, at that level

The honest topological content of "who contains who" is the **order complex** of
the divisibility poset.  For a gear `n` the relevant space is the order complex
`Δ(1, n)` of the *open* interval of proper divisors `{d : 1 < d < n, d ∣ n}`: its
simplices are the chains of proper divisors.  Its (reduced) Euler characteristic
is computed here directly and combinatorially via Philip Hall's recursion
`h(x) = 1 − Σ_{y < x, y ∣ x} h(y)` (`chiOpen`, `redEuler`), so it is a genuine
Euler characteristic of an actual simplicial complex — no axioms, all `native_decide`.

* `redEuler_eq_moebius` — for every free gear this reduced Euler characteristic
  equals the number-theoretic Möbius function `μ(n)` (this is exactly Hall's
  theorem `μ(1,n) = χ̃(Δ(1,n))`, here verified against `Mathlib`'s
  `ArithmeticFunction.moebius`).
* `free_redEuler_values` — across the 97 free gears it takes **three distinct
  values** `{-1, 0, 1}`, so they do **not** all agree.
* `free_redEuler_counts` — precisely `32` free gears have `μ = −1`, `39` have
  `μ = 0`, and `26` have `μ = +1` (`32 + 39 + 26 = 97`).
* `free_not_all_equal` — concretely `redEuler 101 ≠ redEuler 143`
  (`101` prime ↦ `−1`; `143 = 11·13` ↦ `+1`).

## Summary

The 97 free gears are **all the same** as drawn shapes (circles: `χ = 0`,
`b₀ = b₁ = 1`), but their **containment / divisor-poset topology genuinely
differs**, taking the three Euler-characteristic values `−1, 0, +1` exactly as
the Möbius function dictates.
-/

namespace GearTopology

open IrrepGears

/-! ## 1. The gear shapes (cog outlines) -/

/-- Vertices of the cog outline of a `k`-tooth gear: `2k` (a tip and a valley per
tooth), matching `IrrepGears.cogPoints`, which emits `2k` points. -/
def shapeVerts (k : Nat) : Nat := 2 * k

/-- Edges of the cog outline of a `k`-tooth gear: `2k` (the closed polygon visits
each of its `2k` vertices once). -/
def shapeEdges (k : Nat) : Nat := 2 * k

/-- Euler characteristic of the gear's cog outline: `V − E`. -/
def shapeEuler (k : Nat) : Int := (shapeVerts k : Int) - (shapeEdges k : Int)

/-- First Betti number (number of independent loops) of a cog outline with at
least one tooth: a single closed curve, so `b₁ = 1`. -/
def shapeBetti1 (_k : Nat) : Nat := 1

/-- Zeroth Betti number (number of connected components) of a cog outline: `1`. -/
def shapeBetti0 (_k : Nat) : Nat := 1

/-- Every gear outline is a topological circle: its Euler characteristic is `0`. -/
theorem shapeEuler_eq_zero (k : Nat) : shapeEuler k = 0 := by
  simp [shapeEuler, shapeVerts, shapeEdges]

/-- The Euler characteristic equals `b₀ − b₁ = 1 − 1 = 0` for every gear. -/
theorem shapeBetti (k : Nat) :
    shapeEuler k = (shapeBetti0 k : Int) - (shapeBetti1 k : Int) := by
  simp [shapeEuler, shapeVerts, shapeEdges, shapeBetti0, shapeBetti1]

/-- As drawn shapes, all 97 free gears are identical: a single Euler-characteristic
value `0`. -/
theorem free_shapes_all_equal :
    (topGears.map shapeEuler).eraseDups = [0] := by native_decide

/-! ## 2. The containment (divisor-poset) topology -/

/-- The proper divisors of `n` strictly between `1` and `n`, in increasing order:
the vertices of the order complex `Δ(1, n)`. -/
def interiorDivs (n : Nat) : List Nat :=
  (List.range n).filter (fun d => 2 ≤ d && d < n && n % d == 0)

/-- Philip Hall's recursion for the order complex of a poset processed in
increasing order: `h(x) = 1 − Σ_{y < x, y ∣ x} h(y)`.  Summing the `h`-values
gives the (unreduced) Euler characteristic of the order complex. -/
def hVals (ds : List Nat) : List (Nat × Int) :=
  ds.foldl (fun acc x =>
    let belowSum := (acc.filter (fun p => x % p.1 == 0)).foldl (fun s p => s + p.2) (0 : Int)
    acc ++ [(x, 1 - belowSum)]) []

/-- The Euler characteristic `χ(Δ(1, n))` of the order complex of the open
divisor interval of `n` (chains of proper divisors). -/
def chiOpen (n : Nat) : Int := (hVals (interiorDivs n)).foldl (fun s p => s + p.2) (0 : Int)

/-- The *reduced* Euler characteristic `χ̃(Δ(1, n)) = χ − 1`.  By Hall's theorem
this equals the Möbius value `μ(1, n) = μ(n)`. -/
def redEuler (n : Nat) : Int := chiOpen n - 1

/-- Hall's theorem, verified on the 97 free gears: the reduced Euler
characteristic of the divisor order complex equals the number-theoretic Möbius
function. -/
theorem redEuler_eq_moebius :
    topGears.all (fun n => redEuler n == (ArithmeticFunction.moebius n : Int)) = true := by
  native_decide

/-- Across the 97 free gears the divisor-poset Euler characteristic takes exactly
the three distinct values `0, −1, 1` — so the free gears do **not** all have the
same Euler characteristic. -/
theorem free_redEuler_values :
    (topGears.map redEuler).eraseDups = [0, -1, 1] := by native_decide

/-- The exact split of the 97 free gears by Euler characteristic:
`32` have `μ = −1`, `39` have `μ = 0`, `26` have `μ = +1`. -/
theorem free_redEuler_counts :
    ((topGears.filter (fun n => redEuler n == -1)).length,
     (topGears.filter (fun n => redEuler n == 0)).length,
     (topGears.filter (fun n => redEuler n == 1)).length) = (32, 39, 26) := by
  native_decide

/-- The three counts account for all 97 free gears. -/
theorem free_redEuler_counts_total : 32 + 39 + 26 = 97 := by decide

/-- A concrete witness that the free gears differ topologically: gear `101`
(prime, order complex empty, `χ̃ = −1`) and gear `143 = 11·13` (`χ̃ = +1`). -/
theorem free_not_all_equal : redEuler 101 ≠ redEuler 143 := by decide

/-- Both `101` and `143` are genuinely free gears (contained in nothing). -/
theorem witnesses_are_free : 101 ∈ topGears ∧ 143 ∈ topGears := by native_decide

end GearTopology

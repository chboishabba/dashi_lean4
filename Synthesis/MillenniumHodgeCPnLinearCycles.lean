import Mathlib.LinearAlgebra.Projectivization.Subspace
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Literal coordinate linear cycles inside complex projective space

The Agda lane already has the finite Hodge basis 1,H,...,H^n and proves
surjectivity of the finite cycle-class model using rational multiples of
coordinate linear subspaces.

This file constructs those linear subspaces on the actual mathlib
projectivization.

For a finite set S of homogeneous coordinates, define the vector subspace

  V_S = { z | z_i = 0 for every i in S }

and projectivize it.  Membership of an actual projective point [z] is proved
equivalent to literal coordinate vanishing.  Union of coordinate constraints
is proved to be intersection of projective subspaces, giving the geometric
intersection law underlying powers of the hyperplane class.
-/

namespace Synthesis.Millennium.Hodge

open scoped LinearAlgebra.Projectivization
open Projectivization

abbrev CPn (n : ℕ) :=
  ℙ ℂ (Fin (n + 1) → ℂ)

def coordinateVanishingSubmodule
    (n : ℕ)
    (S : Finset (Fin (n + 1))) :
    Submodule ℂ (Fin (n + 1) → ℂ) :=
  ⨅ i ∈ S, LinearMap.ker
    (LinearMap.proj i :
      (Fin (n + 1) → ℂ) →ₗ[ℂ] ℂ)

theorem mem_coordinateVanishingSubmodule_iff
    (n : ℕ)
    (S : Finset (Fin (n + 1)))
    (z : Fin (n + 1) → ℂ) :
    z ∈ coordinateVanishingSubmodule n S
      ↔
    ∀ i ∈ S, z i = 0 := by
  simp [coordinateVanishingSubmodule]

def coordinateProjectiveSubspace
    (n : ℕ)
    (S : Finset (Fin (n + 1))) :
    Projectivization.Subspace ℂ (Fin (n + 1) → ℂ) :=
  (coordinateVanishingSubmodule n S).projectivization

theorem mk_mem_coordinateProjectiveSubspace_iff
    (n : ℕ)
    (S : Finset (Fin (n + 1)))
    (z : Fin (n + 1) → ℂ)
    (hz : z ≠ 0) :
    Projectivization.mk ℂ z hz ∈
      coordinateProjectiveSubspace n S
      ↔
    ∀ i ∈ S, z i = 0 := by
  rw [Submodule.mk_mem_projectivization_iff]
  exact mem_coordinateVanishingSubmodule_iff n S z

def coordinateHyperplane
    (n : ℕ)
    (i : Fin (n + 1)) :
    Projectivization.Subspace ℂ (Fin (n + 1) → ℂ) :=
  coordinateProjectiveSubspace n {i}

theorem mk_mem_coordinateHyperplane_iff
    (n : ℕ)
    (i : Fin (n + 1))
    (z : Fin (n + 1) → ℂ)
    (hz : z ≠ 0) :
    Projectivization.mk ℂ z hz ∈ coordinateHyperplane n i
      ↔
    z i = 0 := by
  simp [coordinateHyperplane,
    mk_mem_coordinateProjectiveSubspace_iff]

theorem coordinateVanishingSubmodule_union
    (n : ℕ)
    (S T : Finset (Fin (n + 1))) :
    coordinateVanishingSubmodule n (S ∪ T)
      =
    coordinateVanishingSubmodule n S
      ⊓ coordinateVanishingSubmodule n T := by
  ext z
  simp [mem_coordinateVanishingSubmodule_iff,
    Finset.mem_union]

theorem coordinateProjectiveSubspace_union
    (n : ℕ)
    (S T : Finset (Fin (n + 1))) :
    coordinateProjectiveSubspace n (S ∪ T)
      =
    coordinateProjectiveSubspace n S
      ⊓ coordinateProjectiveSubspace n T := by
  apply Projectivization.Subspace.submodule.injective
  simp [coordinateProjectiveSubspace,
    coordinateVanishingSubmodule_union]

theorem coordinateHyperplane_intersection
    (n : ℕ)
    (i j : Fin (n + 1)) :
    coordinateProjectiveSubspace n ({i} ∪ {j})
      =
    coordinateHyperplane n i
      ⊓ coordinateHyperplane n j := by
  simpa [coordinateHyperplane] using
    coordinateProjectiveSubspace_union n {i} {j}

def firstCoordinates
    (n p : ℕ) :
    Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => i.1 < p)

def canonicalCoordinateLinearCycle
    (n p : ℕ) :
    Projectivization.Subspace ℂ (Fin (n + 1) → ℂ) :=
  coordinateProjectiveSubspace n (firstCoordinates n p)

theorem mk_mem_canonicalCoordinateLinearCycle_iff
    (n p : ℕ)
    (z : Fin (n + 1) → ℂ)
    (hz : z ≠ 0) :
    Projectivization.mk ℂ z hz ∈
      canonicalCoordinateLinearCycle n p
      ↔
    ∀ i : Fin (n + 1), i.1 < p → z i = 0 := by
  rw [canonicalCoordinateLinearCycle,
    mk_mem_coordinateProjectiveSubspace_iff]
  simp [firstCoordinates]

theorem canonicalCoordinateLinearCycle_zero
    (n : ℕ) :
    canonicalCoordinateLinearCycle n 0 = ⊤ := by
  apply Projectivization.Subspace.submodule.injective
  ext z
  simp [canonicalCoordinateLinearCycle,
    coordinateProjectiveSubspace,
    firstCoordinates,
    coordinateVanishingSubmodule]

end Synthesis.Millennium.Hodge

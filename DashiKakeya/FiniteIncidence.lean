import Mathlib

/-!
# Finite Kakeya incidence: reusable non-promoting bridge

Attribution: Cauchy and Schwarz (finite CS); Wolff and Guth (geometric
Kakeya); Wang and Zahl (2025, arXiv:2502.17655); Guth, Wang and
Zahl (2026, arXiv:2601.14411). DASHI-original work is the small
incidence adapter, not a new Kakeya dimension proof.

Project Numina: https://github.com/project-numina/kakeya-3d
Nankai/ByteDance sticky source: https://github.com/M32026/3d-sticky-kakeya
These are separate proof sources, not imported or assumed here.
-/

namespace DashiKakeya

universe u v
variable {Cell : Type u} {Tube : Type v}

/-- Total weighted incidence, cells first. -/
def incidenceMass (cells : Finset Cell) (tubes : Finset Tube)
    (w : Cell → Tube → ℚ) : ℚ :=
  ∑ c ∈ cells, ∑ t ∈ tubes, w c t

/-- Total weighted incidence, tubes first. -/
def tubeMass (cells : Finset Cell) (tubes : Finset Tube)
    (w : Cell → Tube → ℚ) : ℚ :=
  ∑ t ∈ tubes, ∑ c ∈ cells, w c t

/-- Finite incidence Fubini, reusing Mathlib finite-sum commutation. -/
theorem incidenceMass_eq_tubeMass (cells : Finset Cell)
    (tubes : Finset Tube) (w : Cell → Tube → ℚ) :
    incidenceMass cells tubes w = tubeMass cells tubes w := by
  unfold incidenceMass tubeMass
  exact Finset.sum_comm

/-- A selected cell-tube incidence, with no unjustified geometric meaning. -/
def rationalIncidence (inside : Cell → Tube → Prop)
    [DecidableRel inside] (cellWeight : Cell → ℚ)
    (c : Cell) (t : Tube) : ℚ :=
  if inside c t then cellWeight c else 0

/-- First-moment double counting for the same selected incidence relation. -/
theorem rationalIncidence_firstMoment (cells : Finset Cell)
    (tubes : Finset Tube) (inside : Cell → Tube → Prop)
    [DecidableRel inside] (cellWeight : Cell → ℚ) :
    incidenceMass cells tubes (rationalIncidence inside cellWeight)
      = tubeMass cells tubes (rationalIncidence inside cellWeight) :=
  incidenceMass_eq_tubeMass cells tubes (rationalIncidence inside cellWeight)

-- NOT ESTABLISHED: continuum delta-tube correspondence, geometric
-- measure coverage, convex Wolff bounds, sticky Kakeya, or dimension.
-- For the Agda second moment, sqrt(cell volume) must be represented
-- (or the cell volumes constrained to rational squares).

end DashiKakeya

import Mathlib

/-!
# Hatcher horn → original A5 quotient: one marked short branch obstruction

OWNERS: Hatcher, Algebraic Topology Example 2B.2 supplies the perfect
binary commutator direct limit. Agda PR #1244 supplies a real
nontrivial SURJECTIVE A5 quotient of each selected horn factor and
an independent 180-coordinate zero-derivative c=0 VOA.

The faithful icosahedral A5 < SO(3) < SU(3) action is external
standard representation theory. Nonidentity elements are uniformly
separated from I by kappa = sqrt((5-sqrt(5))/2), >1 in operator norm.
This module DOES NOT construct that representation, a physical smooth
connection, marked source curves, the topology of a chosen wild
embedding, or any full CFT/Witten/Monster equivalence.

Result: a nontrivial root in a FINITE-image horn representation forces
EVERY descendant nontrivial. A single genuinely marked descendant of
length < kappa/M therefore refutes a bounded compatible connection,
provided the external uniform finite-group gap and parallel-transport
length inequality are supplied. This is stronger than the general SU3
half-radius bound needing all leaves short.
-/

namespace DASHIHornFiniteImage

/-- Each commutator has two genuinely nonidentity factors if it is
nonidentity. No perfectness, flatness or analytic assumptions needed. -/
theorem commutatorNontrivialForcesBoth
    {H : Type*} [Group H] (a b : H)
    (h : a * b * a⁻¹ * b⁻¹ ≠ 1) :
    a ≠ 1 ∧ b ≠ 1 := by
  constructor
  · intro ha
    subst a
    simp at h
  · intro hb
    subst b
    simp at h

/-- The source group equality is a HYPOTHESIS: g is the actual marked
Hatcher binary-word representation, not an arbitrary spatial labeling.
The finite root could be the independently constructed Agda #1244 A5
quotient; its Agda proof object does not live on this Lean PR branch. -/
theorem everyMarkedDescendantNontrivial
    {H : Type*} [Group H]
    (g : List Bool → H)
    (hrec : ∀ w : List Bool,
      g w = g (false :: w) * g (true :: w) *
        (g (false :: w))⁻¹ * (g (true :: w))⁻¹)
    (hroot : g [] ≠ 1) :
    ∀ w : List Bool, g w ≠ 1 := by
  intro w
  induction w with
  | nil => exact hroot
  | cons b w ih =>
      have hc :
          g (false :: w) * g (true :: w) *
          (g (false :: w))⁻¹ * (g (true :: w))⁻¹ ≠ 1 := by
        rw [← hrec w]
        exact ih
      obtain ⟨h0, h1⟩ :=
        commutatorNontrivialForcesBoth (g (false :: w)) (g (true :: w)) hc
      cases b with
      | false => exact h0
      | true => exact h1

/-- ONE marked, source-verified short descendant is a no-go for a
finite-image representation: supply a nonidentity group element gap,
a uniform bound on its geometric parallel transport and real length
of the actual representative. None of these physical geometric
hypotheses is silently constructed by this theorem. -/
theorem oneShortMarkedDescendantObstructsFiniteImage
    {H : Type*} [Group H]
    (g : List Bool → H)
    (hrec : ∀ w : List Bool,
      g w = g (false :: w) * g (true :: w) *
        (g (false :: w))⁻¹ * (g (true :: w))⁻¹)
    (hroot : g [] ≠ 1)
    (d : H → ℝ)
    (κ M ell : ℝ) (w : List Bool)
    (hfiniteGap : ∀ h : H, h ≠ 1 → κ ≤ d h)
    (htransport : d (g w) ≤ M * ell)
    (hshort : M * ell < κ) : False := by
  have hnonzero := everyMarkedDescendantNontrivial g hrec hroot w
  have hgap := hfiniteGap (g w) hnonzero
  linarith

/-- Exact conservative upper bound for a circular collar at radius
R_n=1/(8*3^n). Archimedes pi <22/7 gives 2pi R_n <
11/(14*3^n); this theorem checks that bound's rational coefficient
and the M=100 synthetic stage-four acceptance calculation.
It does NOT witness an actual LINKED Hatcher collar or mark. -/
def syntheticCollarLengthUpper (n : ℕ) : ℚ :=
  11 / (14 * (3 : ℚ)^n)

theorem localCollarStageFourPassesConservativeGap :
    100 * syntheticCollarLengthUpper 4 < 1 := by
  norm_num [syntheticCollarLengthUpper]

theorem localCollarStageThreeDoesNotPassConservativeGap :
    1 < 100 * syntheticCollarLengthUpper 3 := by
  norm_num [syntheticCollarLengthUpper]

end DASHIHornFiniteImage

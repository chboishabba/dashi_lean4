import Integration.EisensteinJZeroPrimaryNormalizationExact
import Integration.EisensteinJZeroSplitPrimeEisensteinCarrierExact

/-!
# Main-owned CM source integration: ORIGINAL Jacobi → ORIGINAL unique primary unit

Both formerly separate topic-branch owners are already present at
byte-identical source blobs on dashi_lean4/main.

* #69: `splitJacobiEisensteinElement` / `..._norm` and the same j=0
  curve's Frobenius trace; canonically selected cubic/quadratic Jacobi.
* #73: `IsJZeroPrimary` and the universal
  `splitPrime_primary_associate_existsUnique` for actual norm-p
  EisensteinQA elements, using original six-unit set.

This integration applies the existing unconditional #73 theorem
DIRECTLY to #69's canonical Jacobi value, proving unique primary-unit
existence for every p>3 split rational prime. It is not a new primary
character, not a second normalization, and not a global Hecke Ψ.

The stronger SPECIFIC unit = -1 is intentionally not asserted:
it requires an actual all-prime Frobenius trace mod-six proof on
the same finite-field elliptic curve, and the primary↔ray ideal
congruence adapter from the newer topic branch remains pending
a main-based imported source closure.

Source written against current main, kernel/axiom receipt pending.
No CI.
-/

namespace Integration.EisensteinJZeroMainJacobiPrimaryWeldExact

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinJZeroPrimaryNormalizationExact
open Dashi.EisensteinSixUnitsExact
open Integration.EisensteinJZeroSplitPrimeEisensteinCarrierExact
open Integration.EisensteinJZeroFiniteFieldTraceExact

/-- Only an alias of the ORIGINAL Jacobi-in-EisensteinQA source.
No new choice or abstract ring is introduced. -/
noncomputable abbrev originalJacobi
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p)
    (hmod : p % 3 = 1) : EisensteinQA :=
  splitJacobiEisensteinElement p (by omega) hmod

/-- Original #69 norm theorem, on the identical source element. -/
theorem originalJacobi_norm
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p)
    (hmod : p % 3 = 1) :
    QuadraticAlgebra.norm (originalJacobi p hp3 hmod) = p :=
  splitJacobiEisensteinElement_norm p (by omega) hmod

/-- Unconditional all-split-prime original owner-to-owner theorem:
the canonical original cubic Jacobi element has exactly one primary
associate among the six actual Eisenstein units. This no longer
requires a separate branch merge or a sampled-prime hypothesis. -/
theorem originalJacobi_primary_unit_existsUnique
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p)
    (hmod : p % 3 = 1) :
    ∃! u : EisensteinQA,
      u ∈ eisensteinUnits ∧
      IsJZeroPrimary (u * originalJacobi p hp3 hmod) :=
  splitPrime_primary_associate_existsUnique
    p Fact.out hmod (originalJacobi p hp3 hmod)
    (originalJacobi_norm p hp3 hmod)

/-- The original j=0 Frobenius trace belongs to the SAME Jacobi
element consumed by the primary unique-unit theorem. -/
theorem originalJacobi_trace_eq_negative_frobenius
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p)
    (hmod : p % 3 = 1) :
    jZeroTrace (originalJacobi p hp3 hmod) =
      -jZeroFrobeniusTraceInt (ZMod p) := by
  have h :=
    splitPrime_jZero_trace_formula p (by omega) hmod
  simp only [originalJacobi, jZeroTrace]
  omega

/-- Source-typed P1 next proof obligation. It is an actual same-curve
trace congruence, NOT an arbitrary chosen character phase. -/
def OriginalSplitTraceModSixTarget : Prop :=
  ∀ (p : Nat) [Fact p.Prime] (hp3 : 3 < p)
    (hmod : p % 3 = 1),
    jZeroFrobeniusTraceInt (ZMod p) % 6 = 2

/-- Arithmetic consequence of the source-side trace congruence,
without asserting that the universal target has yet been proved. -/
theorem jacobi_trace_mod_six_of_original_source
    (h : OriginalSplitTraceModSixTarget)
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p)
    (hmod : p % 3 = 1) :
    jZeroTrace (originalJacobi p hp3 hmod) % 6 = 4 := by
  have htrace :=
    originalJacobi_trace_eq_negative_frobenius p hp3 hmod
  have hmod6 := h p hp3 hmod
  omega

#print axioms originalJacobi_norm
#print axioms originalJacobi_primary_unit_existsUnique
#print axioms originalJacobi_trace_eq_negative_frobenius
#print axioms jacobi_trace_mod_six_of_original_source

end Integration.EisensteinJZeroMainJacobiPrimaryWeldExact

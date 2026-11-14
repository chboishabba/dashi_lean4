import Mathlib

/-!
# Selected SU3 Wilson: original finite-order CP no-go and independent norm receipt

ORIGINAL OWNER: Agda sibling #1247,
DASHI.Physics.QFT.NeutrinoExistingCPFiniteResidualNoGoExact,
already records the exact same noninteger field trace and the
infinite-order consequence (conditional on standard algebraic
integrality). This module does NOT claim to discover that theorem.

PRIOR MATH: eigenvalues of finite-order matrices are roots of unity,
their matrix trace is an algebraic integer, and field traces/norms of
algebraic integers are ordinary integers. Q(zeta3) is Eisenstein.
NEW local independent check: the SAME selected source trace has
noninteger quadratic field NORM in (1,2), as well as the known field
trace in (2,3). The ordinary number-theory link is an explicitly
declared source-premise rather than a phantom theorem.

Further source: A5 inverse-conjugacy implies all its unitary
characters are real. Full 60-element A5 inverse-conjugator audit
is exact executable Python on Agda #1249; this generic Lean
implication does not construct A5 inside Mathlib.
-/

namespace DASHISelectedWilsonInfiniteOrder

def originalTraceCoeffOne : ℚ :=
  176093404722400 / 181846007130841

def originalTraceCoeffZeta : ℚ :=
  -(19836986431118 / 181846007130841)

/-- Tr_K/Q(a+bζ)=2a-b (ζ²+ζ+1=0). -/
def fieldTrace : ℚ :=
  2 * originalTraceCoeffOne - originalTraceCoeffZeta

/-- N_K/Q(a+bζ)=a²-ab+b². -/
def fieldNorm : ℚ :=
  originalTraceCoeffOne ^ 2
    - originalTraceCoeffOne * originalTraceCoeffZeta
    + originalTraceCoeffZeta ^ 2

theorem sourceExactFieldTrace :
    fieldTrace = 442358853598 / 216225930001 := by
  norm_num [fieldTrace, originalTraceCoeffOne, originalTraceCoeffZeta]

theorem sourceExactFieldNorm :
    fieldNorm =
      34895555697482945411132133124 /
      33067970309429875820893367281 := by
  norm_num [fieldNorm, originalTraceCoeffOne, originalTraceCoeffZeta]

theorem fieldTraceStrictNonintegerBounds :
    (2 : ℚ) < fieldTrace ∧ fieldTrace < 3 := by
  rw [sourceExactFieldTrace]
  norm_num

theorem fieldNormStrictNonintegerBounds :
    (1 : ℚ) < fieldNorm ∧ fieldNorm < 2 := by
  rw [sourceExactFieldNorm]
  norm_num

theorem fieldTraceNotIntegral (z : ℤ) :
    (z : ℚ) ≠ fieldTrace := by
  intro hz
  have h := fieldTraceStrictNonintegerBounds
  have h2 : (2 : ℚ) < (z : ℚ) := by rw [hz]; exact h.1
  have h3 : (z : ℚ) < 3 := by rw [hz]; exact h.2
  have hlo : (2 : ℤ) < z := by exact_mod_cast h2
  have hhi : z < (3 : ℤ) := by exact_mod_cast h3
  omega

theorem fieldNormNotIntegral (z : ℤ) :
    (z : ℚ) ≠ fieldNorm := by
  intro hz
  have h := fieldNormStrictNonintegerBounds
  have h1 : (1 : ℚ) < (z : ℚ) := by rw [hz]; exact h.1
  have h2 : (z : ℚ) < 2 := by rw [hz]; exact h.2
  have hlo : (1 : ℤ) < z := by exact_mod_cast h1
  have hhi : z < (2 : ℤ) := by exact_mod_cast h2
  omega

/-- Unconditional rational conclusion under a transparent standard
external number-theory bridge. The GENUINE selected W^n≠I is
established mathematically by algebraic integrality; that
general theorem was already cited by #1247 and is not
formally reproved by this arithmetic-only module. -/
theorem finiteOrderContradictsFieldTrace
    (FiniteOrderClaim : Prop)
    (integralFieldTraceIfFinite :
      FiniteOrderClaim → ∃ z : ℤ, (z : ℚ) = fieldTrace) :
    ¬ FiniteOrderClaim := by
  intro h
  obtain ⟨z,hz⟩ := integralFieldTraceIfFinite h
  exact fieldTraceNotIntegral z hz

theorem finiteOrderContradictsFieldNorm
    (FiniteOrderClaim : Prop)
    (integralFieldNormIfFinite :
      FiniteOrderClaim → ∃ z : ℤ, (z : ℚ) = fieldNorm) :
    ¬ FiniteOrderClaim := by
  intro h
  obtain ⟨z,hz⟩ := integralFieldNormIfFinite h
  exact fieldNormNotIntegral z hz

/-- Generic classical character-theory firewall: a unitary
character on an inverse-conjugacy ("ambivalent") group has real
values. The instance A5 is externally sourced and checked
with 60 explicit conjugators by the original Python script. -/
theorem inverseConjugateUnitaryCharacterReal
    {G : Type*} [Group G]
    (inverseConjugate : ∀ g : G, ∃ x : G, x * g * x⁻¹ = g⁻¹)
    (χ : G → ℂ)
    (traceIsClassFunction : ∀ (g x : G),
      χ (x * g * x⁻¹) = χ g)
    (unitaryInverseTrace : ∀ g : G,
      χ (g⁻¹) = Complex.conj (χ g))
    (g : G) :
    χ g = Complex.conj (χ g) := by
  obtain ⟨x,hx⟩ := inverseConjugate g
  calc
    χ g = χ (x * g * x⁻¹) := (traceIsClassFunction g x).symm
    _ = χ (g⁻¹) := by rw [hx]
    _ = Complex.conj (χ g) := unitaryInverseTrace g

end DASHISelectedWilsonInfiniteOrder
